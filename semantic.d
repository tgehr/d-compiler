// Written in the D programming language.

import std.array, std.conv, std.algorithm, std.string;

import lexer, parser, expression, statement, declaration, scope_, util;

import analyze;

import variant;

public import operators;
public import interpret;
public import scheduler;

// TODO: this is just a stub
string uniqueIdent(string base){
	shared static id=0;
	return base~to!string(id++);
}

// helper macros

string[2] splitScope(string s){
	if(!s.startsWith("sc=")) return ["sc",s];
	string[2] r;
	alias std.string.indexOf indexOf;
	auto i = indexOf(s,";");
	return [s[3..i], s[i+1..$]];
}

enum SemRet = q{
	static if(is(typeof(return)==void)) return;
	else static if(is(typeof(this):typeof(return))) return this;
	else static if(is(typeof(return)==bool)) return true;
	else return null;
};

template MultiArgument(alias a,string s) if(s.canFind(",")){
	enum sp = splitScope(s);
	enum ss=sp[1].split(",");
	enum MultiArgument={
		string r;
		foreach(t;ToTuple!ss) r~=a!(mixin(X!q{sc=@(sp[0]);@(t)}));
		return r;
	}();
}

template Rewrite(string s) if(!s.canFind(",")){
	enum Rewrite=mixin(X!q{
		while(@(s).rewrite){
			assert(!!cast(typeof(@(s)))@(s).rewrite, "rewrite");
			assert(@(s)!is @(s).rewrite, "non-terminating rewrite! "~to!string(@(s)));
			//assert(!!cast(typeof(@(s)))@(s).rewrite,"cannot store "~to!string(typeid(@(s).rewrite))~" into reference of type "~to!string(typeid(typeof(@(s)))));
			@(s)=cast(typeof(@(s)))cast(void*)@(s).rewrite;
		}
	});
}

template ConstFold(string s) if(!s.canFind(",")){
	enum sp = splitScope(s);
	enum ConstFold=mixin(X!q{
		@(sp[1]).constFold(@(sp[0]));
		mixin(Rewrite!q{@(sp[1])});
	});
}

template FinishDeductionProp(string s) if(!s.canFind(",")){
	enum FinishDeductionProp=mixin(X!q{
		if(!@(s).finishDeduction(sc)) mixin(ErrEplg);
	});
}
template FinishDeduction(string s) if(!s.canFind(",")){
	enum FinishDeduction=mixin(X!q{
		if(!@(s).finishDeduction(sc)) mixin(SetErr!q{@(s)});
	});
}

template PropErr(string s) if(!s.canFind(",")){
	enum sp = splitScope(s);
	enum PropErr=s.length?mixin(X!q{
		static if(is(typeof(@(sp[1])): Node)){
			if(@(sp[1]).sstate==SemState.error){
				//dw("propagated error from ",@(sp[1])," to ",this);
				@(ErrEplg)
			}
		}else{
			foreach(x;@(sp[1])){
				if(x.sstate==SemState.error){
					//dw("propagated error from ",x," to ",this);
					@(ErrEplg)
				}
			}
		}
	}):mixin(X!q{if(sstate==SemState.error){@(NoRetry)mixin(SemRet);}});
}
template PropErr(string s) if(s.canFind(",")){ alias MultiArgument!(.PropErr,s) PropErr; }

template PropRetryNoRew(string s) if(!s.canFind(",")){
	enum sp = splitScope(s);
	enum PropRetryNoRew=mixin(X!q{
		static assert(!is(typeof(_nR)));
		if(auto _nR=@(sp[1]).needRetry){
			assert(_nR!=2 || sstate != SemState.error,"error in cdep");
			if(sstate != SemState.error){
				needRetry = _nR;
				if(_nR==2){mixin(SetErr!q{@(sp[1])});}
				// dw("propagated retry ",_nR," from ",@(sp[1])," to ",toString()," ",__LINE__);
				Scheduler().await(this, @(sp[1]), @(sp[0]));
			}
			mixin(SemRet);
		}
	});
}

template PropRetry(string s) if(!s.canFind(",")){
	enum sp = splitScope(s);
	enum PropRetry=Rewrite!(sp[1])~PropRetryNoRew!s;
}

template PropRetry(string s) if(s.canFind(",")){ alias MultiArgument!(.PropRetry,s) PropRetry; }

template SemProp(string s){
	enum sp = splitScope(s);
	enum SemProp = PropRetry!s~PropErr!(sp[1]);
}

enum CheckRewrite=mixin(X!q{ if(rewrite) mixin(SemRet); });

enum SemCheck=mixin(X!q{ if(needRetry||rewrite||sstate==SemState.error){mixin(SemRet);} });

private template _SemChldImpl(string s, string op, string sc){ // TODO: get rid of duplication
	template Doit(string v){
		enum Doit=mixin(X!((op[0..3]!="exp"?q{
						if(@(v).sstate != SemState.completed)
							}:"")~q{@(v).@(op)(@(sc));@(Rewrite!v);}));
	}
	enum ss=s.split(",");
	enum _SemChldImpl={
		string r;
		foreach(t;ToTuple!ss){
			r~=mixin(X!q{
				static if(is(typeof(@(t)): Node)){
					@(Doit!t)
					if(@(t).sstate != SemState.completed) mixin(PropRetryNoRew!q{sc=@(sc);@(t)});
					else{
						static if(is(typeof(@(t)): Expression) && !is(typeof(@(t)):Type)
						          &&(!is(typeof(this):Expression)||is(typeof(this):Type))){
							if(@(t).sstate==SemState.completed) mixin(ConstFold!q{sc=@(sc);@(t)});
						}
					}
				}else{
					foreach(ref x;@(t)){
						@(Doit!q{x})
						if(x.sstate != SemState.completed) mixin(PropRetryNoRew!q{sc=@(sc);x});
						else{
							static if(is(typeof(x): Expression) && !is(typeof(x):Type)
							          &&(!is(typeof(this):Expression)||is(typeof(this):Type)))
								if(x.sstate == SemState.completed) mixin(ConstFold!q{sc=@(sc);x});
						}
					}
					static if(is(typeof(@(t)): Expression[])){
						pragma(msg, typeof(this)," @(t)");
						@(t)=Tuple.expand(@(t));
						//foreach(ref x;@(t)) mixin(PropRetry!q{x});
						mixin(PropErr!q{@(t)});
					}
				}
			});
		}
		return r;
	}();
}

template SemChld(string s){ // perform semantic analysis on child node, propagate all errors
	enum sp = splitScope(s);
	enum SemChld=_SemChldImpl!(sp[1],q{semantic},sp[0])~PropErr!s;
}

template SemChldPar(string s){
	enum sp = splitScope(s);
	enum SemChldPar=_SemChldImpl!(sp[1],q{semantic},sp[0]);
}

template SemChldExp(string s){ // perform semantic analysis on child node, require that it is an expression
	enum sp = splitScope(s);
	enum SemChldExp=_SemChldImpl!(sp[1],q{expSemantic},sp[0])~PropErr!s;
}

template SemChldExpPar(string s){
	enum sp = splitScope(s);
	enum SemChldExpPar=_SemChldImpl!(sp[1],q{expSemantic},sp[0]);
}

template ConvertTo(string s) if(s.split(",").length==2){
	enum ss = s.split(",");
	enum ConvertTo=mixin(X!q{
		assert(!@(ss[0]).rewrite && @(ss[0]).sstate == SemState.completed,"ConvertTo!q{@(s)}");
		@(ss[0])=@(ss[0]).convertTo(@(ss[1]));
		mixin(SemChldExp!q{@(ss[0])});
		assert(!@(ss[0]).rewrite,"ConvertTo!q{@(s)}");
	});
}

template ImplConvertTo(string s) if(s.split(",").length==2){
	enum ss = s.split(",");
	enum ImplConvertTo=mixin(X!q{
		assert(!@(ss[0]).rewrite && @(ss[0]).sstate == SemState.completed,@(ss[0]).toString()~" "~to!string(@(ss[0]).rewrite)~" "~to!string(@(ss[0]).sstate));
		@(ss[0])=@(ss[0]).implicitlyConvertTo(@(ss[1]));
		mixin(SemChldExp!q{@(ss[0])});
		assert(!@(ss[0]).rewrite,"ImplConvertTo!q{@(s)}");
	});
}

template ImplConvertToPar(string s) if(s.split(",").length==2){
	enum ss = s.split(",");
	enum ImplConvertToPar=mixin(X!q{
		assert(!@(ss[0]).rewrite && @(ss[0]).sstate == SemState.completed);
		@(ss[0])=@(ss[0]).implicitlyConvertTo(@(ss[1]));
		mixin(SemChldExpPar!q{@(ss[0])});
		assert(!@(ss[0]).rewrite,"ImplConvertToPar!q{@(s)}");
	});
}

template CreateBinderForDependent(string name, string fun){
	mixin(mixin(X!q{
		template @(name)(string s, bool propErr = true) if(s.split(",")[0].split(";").length==2){
			enum ss = s.split(";");
			enum var = ss[0];
			enum spl = var.split(" ");
			enum varn = strip(spl.length==1?var:spl[$-1]);
			enum sss = ss[1].split(",");
			enum e1 = sss[0];
			enum er = sss[1..$].join(" , ");
			enum @(name)=`
				auto _@(name)_`~varn~`=`~e1~`.@(fun)(`~er~`);
				if(auto d=_@(name)_`~varn~`.dependee){
					static if(is(typeof(return) A: Dependent!T,T)) return d.dependent!T;
					else mixin(`~(propErr?q{SemProp}:q{PropRetry})~`!q{sc=d.scope_;d.node});
				}
				`~(propErr?`assert(!_@(name)_`~varn~`.dependee,"illegal dependee "~_@(name)_`~varn~`.dependee.node.toString());`:``)~`
				static if(!is(typeof(_@(name)_`~varn~`)==Dependent!void))`~var~`=_@(name)_`~varn~`.value;
			`;
		}

	}));
}
mixin CreateBinderForDependent!("ImplConvertsTo","implicitlyConvertsTo");
mixin CreateBinderForDependent!("RefConvertsTo","refConvertsTo");
mixin CreateBinderForDependent!("ConstConvertsTo","constConvertsTo");
mixin CreateBinderForDependent!("ConvertsTo","convertsTo");
mixin CreateBinderForDependent!("TypeMostGeneral","typeMostGeneral");
mixin CreateBinderForDependent!("TypeCombine","typeCombine");
mixin CreateBinderForDependent!("Combine","combine");
mixin CreateBinderForDependent!("Unify","unify");
mixin CreateBinderForDependent!("TypeMatch","typeMatch");
mixin CreateBinderForDependent!("RefCombine","refCombine");
mixin CreateBinderForDependent!("MatchCall","matchCall");
mixin CreateBinderForDependent!("MatchCallHelper","matchCallHelper");
mixin CreateBinderForDependent!("AtLeastAsSpecialized","atLeastAsSpecialized");
mixin CreateBinderForDependent!("DetermineMostSpecialized","determineMostSpecialized");
mixin CreateBinderForDependent!("Lookup","lookup");
mixin CreateBinderForDependent!("LookupHere","lookupHere");
mixin CreateBinderForDependent!("GetUnresolved","getUnresolved");
mixin CreateBinderForDependent!("IsDeclAccessible","isDeclAccessible");
mixin CreateBinderForDependent!("DetermineOverride","determineOverride");
mixin CreateBinderForDependent!("FindOverrider","findOverrider");

template IntChld(string s) if(!s.canFind(",")){
	enum IntChld=mixin(X!q{
		@(s).interpret(sc);
		mixin(SemProp!q{@(s)});
	});
}


template Configure(string s){
	enum Configure={
		string r;
		auto ss=s.split(".");
		auto ss2=ss[1].split("=");
		if(ss2[1][$-1]==';') ss2[1]=ss2[1][0..$-1];
		r~="auto _old_"~ss[0]~"_"~ss2[0]~"="~ss[0]~"."~ss2[0]~";\n";
		r~="scope(exit) "~ss[0]~"."~ss2[0]~"="~"_old_"~ss[0]~"_"~ss2[0]~";\n";
		r~=s~";";
		return r;
	}();
}

template RevEpoLkup(string e){
	enum RevEpoLkup=mixin(X!q{
		if(auto ident=@(e).isIdentifier()){
			if(ident.recursiveLookup && !ident.isLookupIdentifier()){
				if(!ident.meaning && ident.sstate != SemState.error){
					//ident.lookup(sc);
					mixin(Lookup!q{_; ident, sc});
					if(auto nr=ident.needRetry) { needRetry = nr; return; }
				}
				if(ident.sstate == SemState.failed){
					// show lookup error
					ident.sstate = SemState.begin;
					mixin(SemChld!q{@(e)});
				}

				if(ident.sstate != SemState.error && ident.meaning){
					@(e) = ident.reverseEponymousLookup(sc);
				}
			}
		}
	});
}

template RevEpoNoHope(string e){
	enum RevEpoNoHope=mixin(X!q{
		if(auto ident = e.isIdentifier()){
			if(ident.recursiveLookup && !ident.isLookupIdentifier()){
				if(!ident.meaning && ident.sstate != SemState.error){
					ident.noHope(sc);
				}
			}			
		}
	});
}

/+
// alternative implementation using an additional flag (firstlookup):
template RevEpoLkup(string e){
	enum RevEpoLkup=mixin(X!q{
		if(firstlookup){
			auto ident = e.isIdentifier();
			if(!ident) firstlookup=false;
			else{
				if(!ident.meaning){
					ident.lookup(sc);
					mixin(PropRetry!q{e});
				}
				if(e.sstate == SemState.failed){
					mixin(SemChld!q{e});
					assert(0);
				}else{
			assert(!!cast(Identifier)ident);
			writeln(typeid(ident)); sc.note(ident.toString()~" here",ident.loc);
			e = ident.reverseEponymousLookup(sc);
			writeln(typeid(this.e));sc.note(e.toString()~" here",e.loc);
			firstlookup = false;
				}
			}
		}
	});
}
+/


enum SemState:ubyte{
	error,
	failed, // identifier lookup failed
	pre,
	begin,
	started,
	completed,
}
enum SemPrlg=mixin(X!q{
	if(sstate == SemState.error||sstate == SemState.completed||rewrite){mixin(SemRet);}
	Scheduler().add(this,sc);
	//dw(cccc++); if(!champ||cccc>champ.cccc) champ=this;
	//dw(champ);
/+	debug scope(failure){
		if(loc.line) write("here! ",loc," ",typeid(this));
		else write("here! ",toString()," ",typeid(this));
		static if(is(typeof(meaning))) write(" meaning: ",meaning," ",typeid(this.meaning)," ",meaning.sstate);
		writeln();
	}+/
});
//static if(is(typeof(dw(this)))) dw(this);

// removed because they crash the program when compiled with DMD sometimes
/+	debug scope(failure){
		static if(is(typeof(sc))) if(sc) sc.note("here!",loc);
		static if(is(typeof(this):Declaration)) writeln(scope_);
	}+/
/+	debug scope(exit){
		if(sstate != SemState.completed && returns_this){
			assert(needRetry||sstate == SemState.error,toString()~" is not done but returns");
		}
	}+/




//static if(is(typeof(sc))) if(sc){
//	sc.note("prolog "~this.to!string~"@"~__LINE__.to!string,loc);
//	writeln(sc);
//}
//if(sstate>SemState.begin){sc.error("cyclic dependency",loc);sstate=SemState.error;return this;}

enum NoRetry=q{
	needRetry = false;
	Scheduler().remove(this);
};

enum SemEplg=q{
	mixin(NoRetry);
	sstate = SemState.completed;
	mixin(SemRet);
};

template RewEplg(string s) if(!s.canFind(",")){
	enum RewEplg=mixin(X!q{
		assert(!rewrite," rewrite mustn't be set already "~toString()~" "~rewrite.toString());
		rewrite = @(s);
		// dw("rewriting ",this," to ",rewrite," ",__LINE__);
		static assert(is(typeof(return)==void)||is(typeof(return)==bool));

		Scheduler().remove(this);
		mixin(SemRet);
	});
}

enum ErrEplg=q{
	mixin(NoRetry);
	//dw(this," ",__LINE__);
	sstate=SemState.error;
	mixin(SemRet);
};

template SetErr(string s) if(!s.canFind(",")){
	enum t=s.length?s~".":"";
	enum SetErr=mixin(X!q{
		@(t)needRetry=false; // TODO: macrolize?
		Scheduler().remove(@(s.length?s:"this"));
		@(t)sstate=SemState.error;
	});
}

enum RetryEplg=q{
	/+if(!needRetry)+/
	assert(sstate != SemState.error,"1");
	Identifier.tryAgain = true;
	needRetry = true;
	mixin(SemRet);
};

enum RetryBreakEplg=q{
	assert(sstate != SemState.error,"2");
	needRetry = true;
	mixin(SemRet);
};

template Semantic(T) if(is(T==Node)){
	// TODO: needRetry and sstate could be final properties to save one byte of space
	// profile to see if it is worth it.
	Node rewrite;
	SemState sstate = SemState.begin;
	ubyte needRetry = false; // needRetry == 2: unwind stack for circular dep handling
	/+ubyte _needRetry = false;
	@property ubyte needRetry(){ return _needRetry; }
	@property void needRetry(ubyte val){
		assert(!val||sstate!=SemState.error);
		_needRetry=val;
	}+/

	invariant(){
		assert(sstate!=SemState.error||needRetry!=1, "needRetry and error "~to!string(loc)~" "~to!string(typeid(this))~(cast(Identifier)this?" "~(cast(Identifier)this).name:"")~" Identifier.tryAgain: "~to!string(Identifier.tryAgain)~" needRetry: "~to!string(needRetry));}

	void semantic(Scope s)in{assert(sstate>=SemState.begin);}body{
		s.error("feature not implemented",loc);
		mixin(ErrEplg);
	}
}

// error nodes (TODO: file bug against covariance error)

mixin template Semantic(T) if(is(T==ErrorDecl)||is(T==ErrorExp)||is(T==ErrorStm)||is(T==ErrorTy)){
	override void semantic(Scope sc){ }
	static if(is(T:Declaration))
	override void presemantic(Scope sc){assert(0);}
}


// expressions
mixin template Semantic(T) if(is(T==Expression)){
	Type type;
	invariant(){
		assert(sstate != SemState.completed || type && type.sstate == SemState.completed,to!string(typeid(this)));
	}

	// run before semantic if the address of an expression will be taken/if it will be called/
	void willTakeAddress(){}
	void willCall(){}

	void initOfVar(VarDecl decl){}

	override void semantic(Scope sc){ sc.error("feature "~to!string(typeid(this))~" not implemented",loc); mixin(ErrEplg); }

	// analysis is trapped because of circular await-relationship involving this node
	void noHope(Scope sc){}

	Type typeSemantic(Scope sc){
		Expression me=this;
		if(sstate != SemState.completed){ // TODO: is this ok?
			me.semantic(sc);
			mixin(Rewrite!q{me});
			if(auto ty=me.isType()) return ty;
			if(me is this) mixin(SemCheck);
			else mixin(SemProp!q{me});
		}
		// the empty tuple is an expression except if a type is requested
		if(auto et=me.isExpTuple()) if(!et.length) return et.type;
		sc.error(format("%s '%s' is used as a type",me.kind,me.toString()),loc);
		me.sstate = SemState.error;
		mixin(ErrEplg);
	}

	final void expSemantic(Scope sc){
		semantic(sc);
		auto f = this;
		mixin(Rewrite!q{f});
		void errorOut(){
			sc.error(format("%s '%s' is not an expression", f.kind, f.toString()), loc);
			rewrite = null;
			mixin(ErrEplg);
		}
		if(f.sstate == SemState.completed){
			if(f.isType()) return errorOut();
			else if(auto et=f.isTuple()){
				foreach(x; et) if(x.isType()) return errorOut();
			}
		}
	}

	final void weakenAccessCheck(AccessCheck check){
		if(check == AccessCheck.memberFuns){
			static struct WeakenCheckM{
				enum check = AccessCheck.memberFuns;
				void perform(Symbol self){
					self.accessCheck = min(self.accessCheck, check);
				}
				void perform(CurrentExp self){
					self.accessCheck = min(self.accessCheck, check);
				}
				void perform(CallExp self){
					if(auto fl=self.e.isFunctionLiteralExp())
						runAnalysis!WeakenCheckM(fl.bdy);
				}
				void perform(MixinExp self){
					self.accessCheck = min(self.accessCheck, check);
				}
			}
			runAnalysis!WeakenCheckM(this);
		}else{
			static struct WeakenCheck{
				immutable AccessCheck check;
				void perform(Symbol self){
					self.accessCheck = min(self.accessCheck, check);
				}
				void perform(CurrentExp self){
					self.accessCheck = min(self.accessCheck, check);
				}
				void perform(FunctionLiteralExp self){
					runAnalysis!WeakenCheck(self.bdy, check);
				}
				void perform(MixinExp self){
					self.accessCheck = min(self.accessCheck, check);
				}
			}
			runAnalysis!WeakenCheck(this,check);
		}
	}

	bool isConstant(){ return false; }
	bool isConstFoldable(){ return false; }

	bool isDirectlyAllocated(){ return false; }

	Expression clone(Scope sc, const ref Location loc)in{
		assert(sstate == SemState.completed);
	}body{
		Expression r;
		if(isConstFoldable()) r=cloneConstant();
		else r=ddup();
		r.loc = loc;
		return r;
	}

	private bool fdontConstFold = false; // mere optimization
	final void dontConstFold(){fdontConstFold = true;}
	final bool isAConstant(){return fdontConstFold;}
	final void constFold(Scope sc)in{
		assert(sstate == SemState.completed);
		assert(!rewrite);
	}body{
		if(!isConstFoldable() || fdontConstFold) return;
		//import std.stdio; wrietln("folding constant ", this);
		interpret(sc);
	}

	bool isLvalue(){return false;}

	final bool checkLvalue(Scope sc, ref Location l){
		if(isLvalue()) return true;
		sc.error(format("%s '%s' is not an lvalue",kind,toString()),l);
		return false;
	}

	bool checkMutate(Scope sc, ref Location l){
		if(checkLvalue(sc,l)){
			if(type.isMutable()) return true;
			else sc.error(format("%s '%s' of type '%s' is read-only",kind,loc.rep,type),l);
		}
		return false;
	}

	Dependent!bool implicitlyConvertsTo(Type rhs)in{
		assert(sstate == SemState.completed,toString()~" in state "~to!string(sstate));
	}body{
		if(auto t=type.implicitlyConvertsTo(rhs).prop) return t;
		auto l = type.getHeadUnqual().isIntegral(), r = rhs.getHeadUnqual().isIntegral();
		if(l && r){
			// note: r.getLongRange is always valid for basic types
			if(l.op == Tok!"long" || l.op == Tok!"ulong"){
				auto rng = getLongRange();
				return (r.getLongRange().contains(rng)
				        || r.flipSigned().getLongRange().contains(rng)).independent;
			}else{
				auto rng = getIntRange();
				return (r.getIntRange().contains(rng)
				        || r.flipSigned().getIntRange().contains(rng)).independent;
			}
		}
		return false.independent;
	}
	Expression implicitlyConvertTo(Type to)in{
		assert(to && to.sstate == SemState.completed);
	}body{
		if(type is to) return this;
		auto r = New!ImplicitCastExp(to,this);
		r.loc = loc;
		return r;
	}
	bool typeEquals(Type rhs)in{
		assert(sstate == SemState.completed, text(typeid(this)," ",this," ",sstate," ",loc));
	}body{
		return type.equals(rhs);
	}

	final bool finishDeduction(Scope sc)in{assert(!!sc);}body{
		static struct PropagateErrors{
			void perform(CallExp exp){
				// improve overload error messages
				// (don't show redundant deduction failure messages)
				// not required for correctness
				foreach(a;exp.args)
					if(auto ae = a.isAddressExp())
						if(ae.isUndeducedFunctionLiteral()){
							auto r=ae.e.isSymbol().meaning;
							mixin(SetErr!q{r});
						}
				///
			}
		}
		runAnalysis!PropagateErrors(this);

		static struct FinishDeduction{
			Scope sc;
			bool result = true;

			void perform(Symbol sym){
				if(sym.isFunctionLiteral)
					result &= runAnalysis!FinishDeduction(sym.meaning,sc).result;
			}

			void perform(FunctionDef fd){
				if(fd.sstate == SemState.error) return;
				size_t unres=0;
				foreach(x; fd.type.params)
					if(x.sstate!=SemState.error
				    && x.mustBeTypeDeduced())
						unres++;
				if(!unres) return;
				result = false;
				if(unres==1){
					foreach(x; fd.type.params){
						if(!x.mustBeTypeDeduced()) continue;
						sc.error(format("cannot deduce type for function literal parameter%s",
						                x.name?" '"~x.name.name~"'":""),x.loc);
						break;
					}
				}else sc.error("cannot deduce parameter types for function literal",
				               fd.type.params[0].loc.to(fd.type.params[$-1].loc));
				mixin(SetErr!q{fd.type});
				mixin(SetErr!q{fd});
				return;
			}
		}
		return runAnalysis!FinishDeduction(this,sc).result;
	}



	// careful: this has to be kept in sync with Type.mostGeneral
	final Dependent!Type typeMostGeneral(Expression rhs)in{
		assert(sstate == SemState.completed && sstate == rhs.sstate);
	}body{
		Type r   = null;
		mixin(ImplConvertsTo!q{bool l2r; this, rhs.type});
		mixin(ImplConvertsTo!q{bool r2l; rhs, this.type});

		if(l2r ^ r2l){
			r = r2l ? type : rhs.type;
			STC stc = this.type.getHeadSTC() & rhs.type.getHeadSTC();
			r.getHeadUnqual().applySTC(stc);
		}
		return r.independent;
	}
	final Dependent!Type typeCombine(Expression rhs)in{
		assert(sstate == SemState.completed && sstate == rhs.sstate);
	}body{
		if(auto r = typeMostGeneral(rhs).prop) return r;
		return type.combine(rhs.type);
	}


	Dependent!bool convertsTo(Type rhs)in{assert(sstate == SemState.completed);}body{
		if(auto t=implicitlyConvertsTo(rhs).prop) return t;
		if(auto t=type.convertsTo(rhs.getUnqual().getConst()).prop) return t;
		return false.independent;
	}


	final Expression convertTo(Type to)in{assert(type&&to);}body{
		if(type is to) return this;
		/+/ TODO: do we need this? Why? If needed, also consider the dependee !is null case
		auto iconvd = implicitlyConvertsTo(to);
		if(!iconvd.dependee&&iconvd.value) return implicitlyConvertTo(to);
		/// +/
		auto r = New!CastExp(STC.init,to,this);
		r.loc = loc;
		return r;
	}

	Dependent!Expression matchCallHelper(Scope sc, const ref Location loc, Type this_, Expression[] args, ref MatchContext context)in{
		assert(sstate == SemState.completed);
	}body{
		auto rd=type.getHeadUnqual().matchCallHelper(sc, loc, this_, args, context);
		if(rd.value) rd.value = this; // valid for dependee is null and dependee !is null
		return rd;
	}

	final Dependent!Expression matchCall(Scope sc, const ref Location loc, Expression[] args){
		MatchContext context;
		mixin(MatchCallHelper!q{auto r; this, sc, loc, null, args, context});
		if(!r){
			if(sc && finishDeduction(sc)) matchError(sc, loc, null, args);
			return null.independent!Expression;
		}
		if(r.sstate == SemState.completed) r=r.resolveInout(context.inoutRes);
		else assert(r.needRetry||r.sstate==SemState.error||cast(TemplateInstanceExp)r, text(r," ",r.sstate," ",r.needRetry));//||r.isSymbol()&&(r.isSymbol().isSymbolMatcher||r.isSymbol().isFunctionLiteral)||cast(TemplateInstanceExp)r,text(r," ",typeid(r),r.isSymbol()?" "~r.isSymbol().meaning.toString():""," ",args," ",r.sstate," ",r.needRetry));
		return r.independent;
	}

	Expression resolveInout(InoutRes res)in{
		assert(sstate == SemState.completed);
	}body{
		type = type.resolveInout(res);
		return this;
	}

	void matchError(Scope sc, Location loc, Type this_, Expression[] args){
		sc.error(format("%s '%s' of type '%s' is not callable",kind,toString(),type.toString()),loc);
	}

	/* members
	 */

	Scope getMemberScope()in{
		assert(sstate == SemState.completed);
	}body{
		return type.getMemberScope();
	}

	/* get an expression that can be used as 'this' reference.
	   this is useful for eg. e.bar!().foo, where e.bar!() is
	   the lhs expression for the member access, but only 'e'
	   will be used as 'this' reference.
	 */
	Expression extractThis(){ return this; }
	AccessCheck deferredAccessCheck(){ return AccessCheck.none; }

	IntRange getIntRange(){return type.getIntRange();}
	LongRange getLongRange(){return type.getLongRange();}

	// needed for template instantiation
	bool templateParameterEquals(Expression rhs)in{
		assert(sstate == SemState.completed,"not completed sstate "~toString());
		assert(rhs.sstate == SemState.completed,"rhs not completed sstate "~rhs.toString());
	}body{
		assert(0, "unsupported operation");
	}
	size_t templateParameterToHash(){
		assert(0, "unsupported operation");
	}
}


//pragma(msg, __traits(classInstanceSize,Expression)); // 0u. TODO: reduce and report

mixin template Semantic(T) if(is(T==LiteralExp)){

	static Expression factory(Variant value, Type type)in{assert(type.sstate == SemState.completed);}body{
		value=value.convertTo(type);
		auto r = New!LiteralExp(value);
		r.semantic(null);
		mixin(Rewrite!q{r});
		assert(r.type is type);
		r.dontConstFold();
		return r;
	}

	override void semantic(Scope sc){
		mixin(SemPrlg);
		type = value.getType();
		mixin(SemEplg);
	}

	override bool isConstant(){ return true; }
	override bool isConstFoldable(){ return true; }

	final bool isPolyString(){return lit.type == Tok!"``";}

	override bool typeEquals(Type rhs){
		if(super.typeEquals(rhs)) return true;
		if(!isPolyString()) return false;
		return rhs is Type.get!wstring()||rhs is Type.get!dstring();
	}

	override Dependent!bool implicitlyConvertsTo(Type rhs){
		if(auto t=super.implicitlyConvertsTo(rhs).prop) return t;
		if(type.getHeadUnqual().isSomeString())
			if(auto ptr = rhs.getHeadUnqual().isPointerTy()){
				return implicitlyConvertsTo(ptr.ty.getDynArr());
			}
		if(!isPolyString()) return false.independent;

		assert(Type.get!wstring().implicitlyConvertsTo(rhs).isIndependent &&
		       Type.get!dstring().implicitlyConvertsTo(rhs).isIndependent );

		return Type.get!wstring().implicitlyConvertsTo(rhs).or(
		       Type.get!dstring().implicitlyConvertsTo(rhs));
	}


	override IntRange getIntRange(){
		if(auto bt = type.getHeadUnqual().isIntegral()){
			auto v = value.get!ulong();
			bool s = bt.isSigned() || bt.bitSize()<32;
			return IntRange(cast(int)v,cast(int)v,s);
		}
		return super.getIntRange();
	}
	override LongRange getLongRange(){
		if(auto bt = type.getHeadUnqual().isIntegral()){
			auto v = value.get!ulong();
			bool s = bt.isSigned() || bt.bitSize()<64;
			return LongRange(v,v,s);
		}
		return super.getLongRange();
	}

	override bool templateParameterEquals(Expression rhs){
		if(!type.equals(rhs.type)) return false;
		return interpretV()==rhs.interpretV();
	}

	override size_t templateParameterToHash(){
		assert(!!type,text("no type! ",this));
		import hashtable;
		return FNV(type.toHash(), value.toHash());
	}
}

mixin template Semantic(T) if(is(T==ArrayLiteralExp)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{lit});
		if(!lit.length){type=Type.get!EmptyArray(); mixin(SemEplg);}
		auto ty=lit[0].type;
		foreach(i,x;lit[1..$]){
			mixin(Combine!q{Type newty; ty, x.type}); // TODO: keep state?
			if(newty) ty=newty;
			else{
				mixin(ImplConvertsTo!q{bool xtoty; x, ty}); // TODO: ditto?
				mixin(ImplConvertsTo!q{bool tytox; ty, x.type}); // TODO: ditto?
				if(!tytox){
					tytox = true;
					foreach(y;lit[0..i+1]){
						mixin(ImplConvertsTo!q{bool ytox; y, x.type});
						if(!(tytox &= ytox)) break;
					}
				}
				if(xtoty^tytox){
					ty = tytox ? x.type : ty;
					continue;
				}
				if((x.isAddressExp()||x.isArrayLiteralExp()) && x.type is Type.get!void())
					continue;
				sc.error(format("incompatible type '%s' in array of '%s'",x.type,ty),x.loc);
				mixin(ErrEplg);
			}
		}
		// TODO: is there a better solution than using 'void' as the type
		// for undeduced function literals?

		if(ty is Type.get!void())
		foreach(x; lit){
			if(x.isAddressExp()||x.isArrayLiteralExp())
				if(x.type is ty){
					type = ty;
					mixin(SemEplg);
				}
		}

		foreach(ref x; lit)  x=x.implicitlyConvertTo(ty);
		mixin(SemChldPar!q{lit});
		alias util.all all; // TODO: file bug
		assert(all!(_=>_.sstate == SemState.completed)(lit));
		type=ty.getDynArr();
		mixin(SemEplg);
	}

	override bool isConstant(){
		foreach(x; lit) if(!x.isConstant()) return false;
		return true;
	}
	override bool isConstFoldable(){
		foreach(x; lit) if(!x.isConstFoldable()) return false;
		return true;
	}

	override bool isDirectlyAllocated(){ return true; }

	override Dependent!bool implicitlyConvertsTo(Type rhs){
		if(auto t=super.implicitlyConvertsTo(rhs).prop) return t;
		if(rhs.getHeadUnqual() is Type.get!(void[])()) return true.independent;
		Type et = rhs.getElementType();
		if(auto arr = rhs.getHeadUnqual().isArrayTy())
			if(arr.length != lit.length) return false.independent;
		if(!et) return false.independent;
		foreach(x; lit){ // TODO: keep state somewhere? this can lead to quadratic performance
			mixin(ImplConvertsTo!q{bool xtoet; x, et});
			if(!xtoet) return false.independent;
		}
		return true.independent;
	}

	override bool templateParameterEquals(Expression rhs){
		if(!type.equals(rhs.type)) return false;
		return interpretV()==rhs.interpretV();
	}

	override size_t templateParameterToHash(){
		import hashtable;
		return FNVred(lit);
	}
}

mixin template Semantic(T) if(is(T _==PostfixExp!S,TokenType S)){
	static if(is(T _==PostfixExp!S,TokenType S)):
	static assert(S==Tok!"++" || S==Tok!"--");
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChldExp!q{e});
		if(e.checkMutate(sc,loc)){
			auto v = Type.get!void();
			auto ty = e.type.getHeadUnqual();
			if((ty.isBasicType() && e !is v)||ty.isPointerTy()){
				type = e.type;
				mixin(SemEplg);
			}
		}else mixin(ErrEplg);
		sc.error(format("type '%s' does not support postfix "~TokChars!op,e.type),loc);
		mixin(ErrEplg);
	}
}

mixin template Semantic(T) if(is(T==IndexExp)){
	DollarScope ascope;
	mixin DollarExp.DollarProviderImpl!e;

	override void semantic(Scope sc_){
		{alias sc_ sc;mixin(SemPrlg);}
		//mixin(SemChldPar!q{e});
		if(e.sstate != SemState.completed){
			alias sc_ sc;
			mixin(SemChldPar!q{e});
		}

		if(!ascope) ascope = New!DollarScope(sc_, this);
		alias ascope sc;

		if(e.isType()){
			auto r=typeSemantic(sc); // TODO: ok?
			mixin(SemCheck);
			assert(!!r);
			mixin(RewEplg!q{r});
		}else if(auto et=e.isExpTuple()){
			mixin(SemChldExp!q{a});
			if(a.length==0){
				e.loc=loc;
				mixin(RewEplg!q{e});
			}
			if(a.length>1){
				sc.error(format("can only use one index to index '%s'",e.type),a[1].loc.to(a[$-1].loc));
				mixin(ErrEplg);
			}
			a[0].prepareInterpret();
			mixin(SemChld!q{a});
			auto s_t = Type.get!Size_t();
			mixin(ImplConvertTo!q{a[0],s_t});
			mixin(IntChld!q{a[0]});
			auto n = a[0].interpretV().get!ulong();
			if(n>=et.length){
				sc.error(format("tuple index %s is out of bounds [0%s..%d%s)",a[0].toString(),Size_t.suffix,et.length,Size_t.suffix),a[0].loc);
				mixin(ErrEplg);
			}
			auto r=et.index(sc,loc,n);
			mixin(RewEplg!q{r});
		}else{
			mixin(SemChld!q{a});
			mixin(PropErr!q{e});
			auto ty = e.type.getHeadUnqual();
			bool isEmpty = false;
			if(auto dyn=ty.isDynArrTy()){
				type = dyn.ty;
			}else if(auto arr=ty.isArrayTy()){
				// TODO: sanity check against length
				type = arr.ty;
			}else if(auto ptr=ty.isPointerTy()){
				if(!a.length){
					sc.error("need bounds to slice pointer", loc);
					mixin(ErrEplg);
				}
				type = ptr.ty;
			}else if(ty is Type.get!EmptyArray()){
				type = Type.get!void();
				isEmpty = true;
			}else{ // TODO: operator overloading
				sc.error(format("'%s' is not indexable", e.type),loc);
				mixin(ErrEplg);
			} // it is a dynamic array, an array or pointer type
			if(!a.length) type = type.getDynArr();
			else{
				if(a.length>1){
					sc.error(format("can only use one index to index '%s'",e.type),a[0].loc.to(a[$-1].loc));
					mixin(ErrEplg);
				}
				auto s_t = Type.get!Size_t();
				mixin(ImplConvertTo!q{a[0],s_t});
				mixin(ConstFold!q{e});
				// TODO: length could be a maximum
				ulong length;
				if(auto le = e.isArrayLiteralExp())
					length = le.lit.length;
				else if(e.isConstant()){
					auto v = e.interpretV(); // TODO: this is inefficient
					length = v.length;
				}else if(!isEmpty) goto Lafter;
				//import std.stdio; wrietln("duh ",e,length);
				LongRange rng;
				if(s_t is Type.get!uint()){
					auto r = a[0].getIntRange();
					rng = LongRange(r.min, r.max,false);
				}else{
					assert(s_t is Type.get!ulong());
					rng = a[0].getLongRange();
				}
				if(!length||!rng.overlaps(LongRange(0,length-1,false))){
					mixin(ConstFold!q{a[0]});
					sc.error(format("array index %s is out of bounds [0%s..%d%s)",
					         a[0].toString(),Size_t.suffix,length,Size_t.suffix),a[0].loc);
					mixin(ErrEplg);
				}
			Lafter:;
			}
			if(!isConstFoldable()){
				mixin(ConstFold!q{e});
				foreach(ref x; a) mixin(ConstFold!q{x});
			}
			mixin(SemEplg);
		}
	}

	override bool isConstant(){
		if(!a.length) return e.isConstant();
		assert(a.length==1,to!string(this));
		return e.isConstant() && a[0].isConstant();
	}
	override bool isConstFoldable(){
		if(!a.length) return e.isConstFoldable();
		assert(a.length==1,to!string(this));
		return e.isConstFoldable() && a[0].isConstFoldable();
	}

	override Type typeSemantic(Scope sc_){
		//mixin(SemChld!q{e});
		{alias sc_ sc; mixin(SemChld!q{e});}

		auto tp = e.isTuple();

		Type ty;
		if(!tp || !a.length){
			alias sc_ sc;
			ty=e.typeSemantic(sc_);
			mixin(SemProp!q{e});
		}

		if(!a.length){
			mixin(NoRetry);
			if(tp) { e.loc=loc; return ty; }
			else   { return ty.getDynArr(); }
		}

		Scope sc;
		if(tp){
			if(!ascope) ascope = New!DollarScope(sc_,this);
			sc = ascope;
		}else sc = sc_;

		foreach(x;a) x.prepareInterpret();
		mixin(SemChldExp!q{a});

		if(a.length>1){
			if(tp) sc.error(format("can only use one index to index '%s'",e.type),a[0].loc.to(a[$-1].loc));
			else sc.error("can only specify one dimension for fixed-length array",a[0].loc.to(a[$-1].loc));
			mixin(ErrEplg);
		}
		assert(a.length==1);


		auto s_t=Type.get!Size_t();

		mixin(ImplConvertTo!q{a[0],s_t});

		mixin(IntChld!q{a[0]});

		mixin(NoRetry);

		ulong n = a[0].interpretV().get!ulong();
		if(tp){
			if(n>=tp.length){
				sc.error(format("tuple index %s is out of bounds [0%s..%d%s)",a[0].toString(),Size_t.suffix,tp.length,Size_t.suffix),a[0].loc);
				mixin(ErrEplg);
			}
			return tp.index(sc,loc,n).typeSemantic(sc);
		}
		// TODO: DMD considers 16777215 as the upper bound for static array size
		assert(!!ty);
		return ty.getArray(n);
	}

	override bool isLvalue(){
		return true;
	}

	override @property string kind(){ return e.kind; }

/+ // TODO (?)
	static string __dgliteralRng(){
		string r;
		foreach(x;["IntRange", "LongRange"]){
			r~=mixin(X!q{
				override @(x) get@(x)(){
					if(ty.isArrayTy()||ty.isDynArrTy()){

					}else return super.get@(x)(); // TODO: associative arrays
				}
			});
		}
		return r;
	}
	mixin(__dgliteralRng());
+/

}

mixin template Semantic(T) if(is(T==SliceExp)){

	DollarScope ascope;
	mixin DollarExp.DollarProviderImpl!e;

	override void semantic(Scope sc_){
		{alias sc_ sc; mixin(SemPrlg);}
		//mixin(SemChldPar!q{e});
		if(e.sstate != SemState.completed){
			alias sc_ sc;
			mixin(SemChldPar!q{e});
		}

		if(!ascope) ascope = New!DollarScope(sc_, this);

		// mixin(MaybeFold!q{e,l,r}); // TODO: this is better
		if(auto tp = e.isTuple()){
			auto r=sliceTuple(sc_,tp);
			if(r is this) return;
			mixin(RewEplg!q{r});
		}else{
			alias ascope sc;

			mixin(SemChldExpPar!q{e}); // does not use the scope anyway.

			mixin(SemChld!q{l,r});
			mixin(PropErr!q{e});
			auto ty = e.type.getHeadUnqual();
			bool isEmpty = false;
			if(auto dyn=ty.isDynArrTy()){
				type = dyn.ty;
			}else if(auto arr=ty.isArrayTy()){
				// TODO: sanity check against length
				type = arr.ty;
			}else if(auto ptr=ty.isPointerTy()){
				type = ptr.ty;
			}else if(ty is Type.get!EmptyArray()){
				type = Type.get!void();
				isEmpty = true;
			}else{ // TODO: operator overloading
				sc.error(format("'%s' is not sliceable",e.type),loc);
				mixin(ErrEplg);
			} // it is a dynamic array, an array or pointer type
			type = type.getDynArr();
			auto s_t = Type.get!Size_t();

			mixin(ImplConvertToPar!q{l,s_t});
			mixin(ImplConvertTo!q{r,s_t});
			mixin(PropErr!q{l});

			// TODO: remove code duplication between here and IndexExp.semantic
			// TODO: length could be a maximum
			ulong length;
			if(auto le = e.isArrayLiteralExp())
				length = le.lit.length;
			else if(e.isConstant()){
				auto v = e.interpretV(); // TODO: this is inefficient
				length = v.length;
			}else if(!isEmpty) goto Lafter;
			LongRange[2] rng;
			if(s_t is Type.get!uint()){
				auto r1 = l.getIntRange(), r2 = r.getIntRange();
				rng[0] = LongRange(r1.min, r1.max,false);
				rng[1] = LongRange(r2.min, r2.max,false);
			}else{
				assert(s_t is Type.get!ulong());
				rng[0] = l.getLongRange();
				rng[1] = r.getLongRange();
			}
			if(!rng[0].overlaps(LongRange(0,length,false))
			|| !rng[1].overlaps(LongRange(0,length,false))){
				mixin(ConstFold!q{l}); mixin(ConstFold!q{r});
				sc.error(format("slice indices [%s..%s] are out of bounds [0%s..%d%s]",l.toString(),r.toString(),Size_t.suffix,length,Size_t.suffix),l.loc.to(r.loc));
				mixin(ErrEplg);
			}
			if(s_t is Type.get!uint() && l.getIntRange().gr(r.getIntRange())
			|| s_t is Type.get!ulong() && l.getLongRange().gr(r.getLongRange())){
				sc.error("lower slice index exceeds upper slice index",l.loc.to(r.loc));
				mixin(ErrEplg);
			}
		Lafter:
			if(!isConstFoldable()){
				mixin(ConstFold!q{e});
				mixin(ConstFold!q{l});
				mixin(ConstFold!q{r});
			}
			mixin(SemEplg);
		}
	}
	override Type typeSemantic(Scope sc){
		e.typeSemantic(sc);
		mixin(SemProp!q{e});
		if(auto tp=e.isTuple()) return cast(TypeTuple)cast(void*)sliceTuple(sc, tp);
		return super.typeSemantic(sc);
	}
	override bool isConstant(){
		return e.isConstant() && l.isConstant() && r.isConstant();
	}
	override bool isConstFoldable(){
		return e.isConstFoldable() && l.isConstFoldable() && r.isConstFoldable();
	}

	override @property string kind(){ return e.kind; }

private:
	Expression sliceTuple(Scope sc_, Tuple tp){

		alias ascope sc;

		auto s_t = Type.get!Size_t();
		l.prepareInterpret();
		r.prepareInterpret();
		mixin(SemChldExp!q{l,r});
		mixin(ImplConvertToPar!q{l,s_t});
		mixin(ImplConvertTo!q{r,s_t});
		mixin(PropErr!q{l});
		// TODO: macrolize?
		l.interpret(sc);
		r.interpret(sc);
		mixin(SemProp!q{l,r});
		auto a = l.interpretV().get!ulong();
		auto b = r.interpretV().get!ulong();
		auto len = tp.length;
		if(a>len || b>len){
			sc.error(format("tuple slice indices [%s..%s] are out of bounds [0%s..%d%s]",l.toString(),r.toString(),Size_t.suffix,len,Size_t.suffix),l.loc.to(r.loc));
			mixin(ErrEplg);
		}
		if(a>b){
			sc.error("lower tuple slice index exceeds upper tuple slice index",l.loc.to(r.loc));
			mixin(ErrEplg);
		}

		auto r=tp.slice(sc,loc,a,b);
		r.semantic(sc);
		mixin(NoRetry);
		return r;
	}
}

mixin template Semantic(T) if(is(T==AssertExp)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{a});
		if(a.length<1){
			sc.error("missing arguments to assert", loc);
			mixin(ErrEplg);
		}else if(a.length>2){
			sc.error("too many arguments to assert", loc);
			mixin(ErrEplg);
		}
		a[0]=a[0].convertTo(Type.get!bool());
		// TODO: this is maybe not perfectly appropriate
		if(a.length>1 && a[1].type !is Type.get!string())
			a[1]=a[1].implicitlyConvertTo(Type.get!(const(char)[])());

		mixin(SemChld!q{a});
		type = Type.get!void();
		foreach(ref x;a) mixin(ConstFold!q{x});
		mixin(SemEplg);
	}
}

mixin template Semantic(T) if(is(T _==UnaryExp!S,TokenType S)){
	static if(is(T _==UnaryExp!S,TokenType S)):
	override void semantic(Scope sc){
		mixin(SemPrlg);
		static if(S==Tok!"&") e.willTakeAddress();
		mixin(SemChldExp!q{e});

		static if(S!=Tok!"&"&&S!=Tok!"!") auto ty=e.type.getHeadUnqual();
		static if(S==Tok!"!"){
			auto bl = Type.get!bool();
			mixin(ConvertTo!q{e,bl});
			type = bl;
			mixin(SemEplg);
		}else static if(S==Tok!"-" || S==Tok!"+" || S==Tok!"~"){
			auto v = Type.get!void();
			if(ty.isBasicType() && e !is v && ty !is Type.get!bool()){
				type = e.type;
				mixin(SemEplg);
			}
		}else static if(S==Tok!"++" || S==Tok!"--"){
			if(e.checkMutate(sc,loc)){
				auto v = Type.get!void();
				if(ty.isBasicType()&&e !is v&&ty !is Type.get!bool()||ty.isPointerTy()){
					type = e.type;
					mixin(SemEplg);
				}
			}else mixin(ErrEplg);
		}else static if(S==Tok!"*"){
			if(auto p=ty.isPointerTy()){
				type = p.ty;
				mixin(SemEplg);
			}else{
				sc.error(format("cannot dereference expression '%s' of non-pointer type '%s'",e.loc.rep,e.type),loc);
				mixin(ErrEplg);
			}
		}else static if(S==Tok!"&"){
			if(auto lv = e.isLvalue()){
				// TODO: this is a hack, find solution for taking address of
				// overloaded declaration

				FunctionDecl fd;
				auto fe = e.isFieldExp();
				if(auto s=fe?fe.e2:e.isSymbol()){
					if(auto ov=s.meaning.isOverloadSet()){
						if(ov.decls.length==1)
						if(auto fdo=ov.decls[0].isFunctionDecl()) fd = fdo;
					}else if(auto fdd=s.meaning.isFunctionDecl()) fd = fdd;
					if(fd){
						if(s.type is Type.get!void()) // need deduction first
							type = Type.get!void;
						else{
							if(auto fdef=fd.isFunctionDef()){
							if(fdef.deduceStatic){ // TODO: || deduceQualifiers
								s.makeStrong();
								mixin(SemChld!q{e});
							}}
							if(fd.stc&STCstatic) type=fd.type.getPointer();
							else type=fd.type.getDelegate();
							s.type=fd.type;
							s.meaning=fd;
						}
					}
				}
				if(!fd) type=e.type.getPointer();
				mixin(SemEplg);
			}else{
				sc.error(format("cannot take address of %s '%s'",e.kind,e.loc.rep),loc);
				mixin(ErrEplg);
			}
		}else static assert(0);
		// TODO: operator overloading
		// TODO: array ops
		static if(S!=Tok!"++" && S!=Tok!"--"){
			sc.error(format("invalid argument type '%s' to unary "~TokChars!S,e.type),loc);
		}else{
			sc.error(format("type '%s' does not support prefix "~TokChars!S,e.type),loc);
		}
		mixin(ErrEplg);
	}

	// TODO: constant addresses should be possible to be taken too
	static if(S==Tok!"+"||S==Tok!"-"||S==Tok!"~"||S==Tok!"!"){
		override bool isConstant(){ return e.isConstant(); }
		override bool isConstFoldable(){ return e.isConstFoldable(); }
	}
	static if(S==Tok!"&"){

	override bool isConstant(){
		return !!e.isSymbol(); // TODO: correct?
	}

	override Dependent!bool implicitlyConvertsTo(Type rhs){
		// function literals implicitly convert to both function and delegate
		if(auto sym = e.isSymbol()                      ){
		if(auto fd  = sym.meaning.isFunctionDef()       ){
			auto rhsu = rhs.getHeadUnqual();
			if(auto dg  = rhsu.isDelegateTy()){
				if(fd.deduceStatic){
					assert(sym.isStrong);
					return fd.type.getDelegate()
						.implicitlyConvertsTo(dg);
				}
			}else if(fd.canBeStatic)
				if(auto ptr = rhsu.isPointerTy()   ){
				if(auto ft  = ptr.ty.isFunctionTy()){
					return fd.type.getPointer()
						.implicitlyConvertsTo(rhsu);
				}
			}
		}}
		return super.implicitlyConvertsTo(rhs);
	}

	override Dependent!Expression matchCallHelper(Scope sc, const ref Location loc, Type this_, Expression[] args, ref MatchContext context){
		return e.matchCallHelper(sc, loc, this_, args, context);
	}

	// this is necessary to make template delegate literals work correctly
	// the scope of the symbol must be adjusted
	override Expression clone(Scope sc, const ref Location loc){
		auto r=New!(UnaryExp!(Tok!"&"))(e.clone(sc,loc));
		r.loc = loc;
		r.semantic(sc);
		return r;
	}


	final bool isUndeducedFunctionLiteral(){
		auto r=type is Type.get!void();
		assert(!r || e.isSymbol() && e.isSymbol().isFunctionLiteral);
		return r;
	}

	override bool templateParameterEquals(Expression rhs){
		if(this is rhs) return true;
		if(auto ae=rhs.isAddressExp())
		   return e.templateParameterEquals(ae.e);
		return false;
	}

	override size_t templateParameterToHash(){
		import hashtable;
		return FNV(e.templateParameterToHash());
	}

	}

	static if(S==Tok!"++"||S==Tok!"--"||S==Tok!"*")
		override bool isLvalue(){return true;}

	private static string __dgliteralRng(){
		string r;
		foreach(x;["IntRange","LongRange"]){
			r~=mixin(X!q{
				override @(x) get@(x)(){
					alias @(x) R;
					auto r = e.get@(x)();
					static if(S==Tok!"!"){
						bool t = r.min==0&&r.max==0;
						bool f = !r.contains(R(0,0,r.signed));
						return t ? R(1,1,true)
							 : f ? R(0,0,true)
							 :     R(0,1,true);
					}else static if(S==Tok!"+") return r;
					else static if(S==Tok!"-") return -r;
					else static if(S==Tok!"++"||S==Tok!"--"){
						r = mixin(`r`~TokChars!S[0]~`R(1,1,r.signed)`);
						if(auto ty = e.type.getHeadUnqual().isIntegral()){
							auto siz = ty.bitSize();
							static if(is(R==IntRange)){
								if(siz>=32) return r;
								r = r.narrow(ty.isSigned(),siz);
							}else{
								if(siz>=64) return r;
								auto nr = r.narrow(ty.isSigned(),siz);
								return R(nr.min,nr.max,nr.signed);
							}
						}
						return r;
					}else static if(S==Tok!"~") return ~r;
					return super.get@(x)();
				}
			});
		}
		return r;
	}
	mixin(__dgliteralRng());
}

mixin template Semantic(T) if(is(T==BinaryExp!(Tok!"."))){ }

class MatcherTy: Type{
	Type adapted;
	bool ambiguous;
	WhichTemplateParameter which;
	this(WhichTemplateParameter which)in{
		with(WhichTemplateParameter)
			assert(which == type || which == tuple);
	}body{
		this.which = which;
		sstate = SemState.completed;
	}

	override Dependent!void typeMatch(Type from){
		if(which==WhichTemplateParameter.tuple && !from.isTuple()) return indepvoid;

		if(!adapted) adapted=from;
		else{
			mixin(Unify!q{Type c; adapted, from}); // TODO: full unification
			if(c) adapted=c;
			else if(!adapted.equals(from)) ambiguous=true;
		}
		return indepvoid;
	}

	override string toString(){return "<<MT("~adapted.to!string()~")>>";}

	override bool hasPseudoTypes(){ return true; }

	mixin DownCastMethod;
	mixin DeepDup!MatcherTy;
}


class TemplateInstanceDecl: Declaration{
	TemplateDecl parent;    // template this instance was instantiated from

	Expression[] args;      // arguments as given by the instantiation site
	Expression[] resolved;  // arguments as given to the template body

	Match match = Match.exact; // match level

	Expression constraint;
	BlockDecl bdy;

	TemplateScope paramScope;

	final @property bool completedMatching(){ return matchState>=MatchState.completed; }
	final @property bool completedParameterResolution(){
		return matchState > MatchState.resolvedSemantic;
	}

	private{

		enum MatchState{
			start,              // start matching
			iftiStart,          // start matching in ifti mode
			iftiPrepare,
			iftiMatching,       // continue ifti matching
			resolvedSemantic,   // apply default args
			iftiResolvedSemantic,// apply default args and return to iftiMatch if necessary
			checkMatch,         // check if there is a match
			checkConstraint,    // check the constraint
			checkingConstraint, // checking in progress
			completed,          // matching succeeded
			analysis,           // analyzing template body
		}

		MatchState matchState = MatchState.start;
	}

	this(TemplateDecl parent, const ref Location loc, Expression[] args){
		super(parent.stc, parent.name);
		this.parent=parent;
		this.args=args;
		this.constraint = parent.constraint?parent.constraint.ddup():null;
		this.bdy=parent.bdy; // NOTE: bdy is the original template body at this point!

		this.loc = loc;

		scope_ = parent.scope_;
		sstate = SemState.begin;
	}

	this(TemplateDecl parent, const ref Location loc, Expression[] args, Expression[] iftiArgs){
		this(parent, loc, args);
		this.iftiArgs = iftiArgs;
		this.matchState = MatchState.iftiStart;
	}

	final void gag()in{
		assert(!paramScope && !iftiScope);
	}body{
		scope_ = New!GaggingRecordingScope(parent.scope_);
	}

	final void ungag()in{
		assert(isGagged,text("attempted to ungag ",this," which was not gagged"));
	}body{
		assert(!!cast(GaggingRecordingScope)scope_);
		(cast(GaggingRecordingScope)cast(void*)scope_).replay(parent.scope_);
		scope_ = parent.scope_;
		paramScope.parent = parent.scope_;

		Scheduler().add(this, scope_);
	}

	final @property bool isGagged(){ return scope_ !is parent.scope_; }

	final FunctionDecl iftiDecl()in{
		assert(finishedInstantiation());
	}body{
		return parent.iftiDecl()?bdy.decls[0].isFunctionDecl():null;
	}

	override void buildInterface(){
		if(sstate == SemState.completed || sstate == SemState.error || rewrite) return;
		bdy.buildInterface();
		mixin(SemProp!q{sc=bdy.scope_;bdy});
	}


	private void determineInstanceScope(Scope instantiationScope)in{
		assert(paramScope && paramScope.parent is paramScope.iparent);
	}body{
		Scope instanceScope = parent.scope_;

		size_t maxn = 0;
		foreach(i,x;args){
			if(i<parent.tuplepos && parent.params[i].which != WhichTemplateParameter.alias_)
				continue;
			Declaration decl = null;
			if(auto sym = x.isSymbol()) decl=sym.meaning;
			//else if(auto ty = x.isType()) // DMD 2.060 does not do this:
				// if(auto at = ty.isAggregateTy()) decl=at.decl;
			if(!decl) continue;
			assert(!!decl && decl.scope_,x.to!string);
			// TODO: find out if it is reasonable to make this assertion pass:
			// assert(decl.scope_.getDeclaration() || decl.stc & STCstatic, decl.toString());
			if(decl.stc & STCstatic || !decl.scope_.getDeclaration())
				continue;
			if(!instantiationScope.nestedIn(decl.scope_))
				continue;
			auto n = decl.scope_.getFrameNesting();
			if(n>=maxn){
				assert(n>maxn||instanceScope==scope_
				       ||instanceScope==decl.scope_);
				maxn=n;
				instanceScope = decl.scope_;
			}
		}
		if(!(parent.stc&STCstatic)){ // TODO: fix!
			for(auto d=instanceScope.getDeclaration();;){
				if(!d){instanceScope = parent.scope_; break;}
				if(d.scope_ !is parent.scope_) break;
				if(d.stc&STCstatic){instanceScope = parent.scope_; break;}
				d = d.scope_.getDeclaration();
			}
		}
		paramScope.iparent = instanceScope;
	}

	private void fillScopes()in{
		assert(scope_&&paramScope);
	}body{
		foreach(i,x;resolved){
			// TODO: don't leak references
			auto al = New!AliasDecl(STC.init, New!VarDecl(STC.init, x, parent.params[i].name, null));
			al.semantic(paramScope);
			mixin(PropErr!q{al});
			debug{
				mixin(Rewrite!q{al});
				assert(al.sstate == SemState.completed);
			}
		}
	}

	private bool checkResolvedValidity(){
		foreach(i,x; parent.params[0..min(parent.tuplepos,resolved.length)])
			if(resolved[i] && (resolved[i].sstate == SemState.error || !x.matches(resolved[i]).force)) return false;
		return true;
	}

	private bool startMatching(Scope sc_){
		auto tuplepos = parent.tuplepos;
		auto params   = parent.params;

		resolved = new Expression[params.length];
		
		// resolve non-tuple parameters
		if(args.length>tuplepos&&tuplepos==params.length) return false;
		resolved[0..min(tuplepos, args.length)] = args[0..min(tuplepos,$)];

		// TODO: does this work?
		if(!paramScope){
			paramScope = New!TemplateScope(scope_,scope_,this);
			determineInstanceScope(sc_);
		}

		// this always fills the first tuple parameter
		// other possible semantics would be to only fill the
		// first tuple parameter if it is the last template parameter
		// this would lead to uniform treatment of multiple tuple
		// parameters in a template parameter list, which is more pure,
		// but potentially less useful.
		if(tuplepos<params.length && args.length>tuplepos){
			Expression[] expr = args[tuplepos..$];
			Expression et = New!ExpTuple(paramScope.iparent,expr);
			et.semantic(scope_);
			mixin(Rewrite!q{et});
			assert(et.sstate == SemState.completed);
			resolved[tuplepos]=et;
		}

		if(!checkResolvedValidity) return false;

		if(matchState == MatchState.iftiStart) initializeIFTI();

		return true;
	}

	private{
		Expression[] iftiArgs;
		Parameter[] iftiEponymousParameters;
		MatcherTy[] matcherTypes;
		NestedScope iftiScope;
	}
	private void initializeIFTI(){
		// TODO: gc allocation
		auto fd = parent.iftiDecl();
		if(!fd){ // TODO: this is probably not required (and the test suite does not cover it)
			assert(matchState == MatchState.iftiStart);
			matchState = MatchState.start;
			return;
		}
		auto funparams = fd.type.params;
		iftiEponymousParameters = new Parameter[funparams.length];
		matcherTypes = new MatcherTy[parent.params.length];

		// function literal type deduction
		// TODO: can the efficiency be improved?
		iftiArgs = iftiArgs.dup;
		foreach(ref a;iftiArgs)
		if(auto ae = a.isAddressExp())
		if(ae.isUndeducedFunctionLiteral())
			a=a.ddup();
	}

	private void prepareIFTI(){
		// TODO: this is quite inefficient
		// TODO: use region allocator and release lots of memory at once
		// TODO: keep around iftiScope, and update it correctly
		auto fdecl = parent.iftiDecl();
		assert(!!fdecl);
		auto funparams = fdecl.type.params;

		// because of tuples, the array may change its size in one iteration
		iftiEponymousParameters=iftiEponymousParameters[0..funparams.length];
		iftiEponymousParameters.assumeSafeAppend(); // ok
		foreach(i,ref t;iftiEponymousParameters) t=funparams[i].ddup();

		iftiScope = New!NestedScope(scope_);

		foreach(i,p;parent.params){
			if(!resolved[i]){
				if(p.which == WhichTemplateParameter.type
				|| p.which == WhichTemplateParameter.tuple)
					matcherTypes[i]=New!MatcherTy(p.which);
				else continue;
			}
			auto al = New!AliasDecl(STC.init, New!VarDecl(STC.init, resolved[i]?resolved[i]:matcherTypes[i], parent.params[i].name,null));
			al.semantic(iftiScope);

			if(al.sstate == SemState.error) continue;
			debug{
				mixin(Rewrite!q{al});
				assert(al.sstate == SemState.completed);
			}
		}
		matchState = MatchState.iftiMatching;
	}

	private void matchIFTI(){
		if(matchState == MatchState.iftiPrepare) prepareIFTI();

		auto sc = iftiScope;

		foreach(ref x;iftiEponymousParameters){
			x.type = x.rtype.typeSemantic(iftiScope);
			mixin(PropRetry!q{x.rtype});
			if(!x.type) continue; // mixin(ErrEplg); // TODO: error message
			x.type = x.type.applySTC(x.stc);
		}

		mixin(SemChldPar!q{iftiEponymousParameters});
		iftiEponymousParameters = Tuple.expand(iftiScope, iftiEponymousParameters);

		foreach(ref x;iftiArgs) mixin(SemChld!q{x});

		bool resolvedSome = false;

		foreach(i,ref a;iftiArgs[0..min($,iftiEponymousParameters.length)])
		if(auto ae = a.isAddressExp())
		if(ae.isUndeducedFunctionLiteral()){
			if(!iftiEponymousParameters[i].type) continue;
			auto ft = iftiEponymousParameters[i].type.getHeadUnqual().getFunctionTy();

			if(!ft) continue;
			ft=ft.ddup(); // TODO: can we do without these allocations?
			ft.stripPseudoTypes();
			assert(!!cast(Symbol)ae.e);
			auto sym = cast(Symbol)cast(void*)ae.e;
			assert(!!cast(FunctionDef)sym.meaning);
			auto fd  = cast(FunctionDef)cast(void*)sym.meaning;
			auto reso = fd.type.resolve(ft);
			resolvedSome|=reso;
			if(reso){
				ae.sstate = sym.sstate = SemState.begin;
				// TODO: gag this?
				a.semantic(sc);
				mixin(PropRetry!q{a});
				// mixin(PropErr!q{a}); // TODO: get rid of this?
			}
		}
		// dw(iftiArgs," ",map!(_=>_.type)(iftiArgs));

		// if this behaviour should be changed, remember to edit
		// FunctionTy.typeMatch as well
		foreach(i,ref a;iftiEponymousParameters[0..min($,iftiArgs.length)]){
			if(!a.type) continue;
			auto mt = a.type.isMatcherTy();
			if(mt && mt.which==WhichTemplateParameter.tuple){
				if(i+1==iftiEponymousParameters.length){
					//TODO: gc allocation
					auto types = map!(_=>_.type.getHeadUnqual())(iftiArgs[i..$]).array();
					// mt.typeMatch(New!TypeTuple(types));
					mixin(TypeMatch!q{_; mt, New!TypeTuple(types)});
				}
				break;
			}else if(a.type.isTuple()) break;

			auto iftiType = iftiArgs[i].type.getHeadUnqual();

			if(iftiType is Type.get!void()){
				if(auto ae = iftiArgs[i].isAddressExp()){
					if(ae.isUndeducedFunctionLiteral()){
						auto sym = cast(Symbol)cast(void*)ae.e;
						assert(!!cast(FunctionDef)sym.meaning);
						auto fd  = cast(FunctionDef)cast(void*)sym.meaning;
						iftiType = fd.type;
					}
				}
			}

			//a.type.typeMatch(iftiType);
			mixin(TypeMatch!q{_; a.type, iftiType});
		}

		//dw(iftiEponymousParameters);
		//dw(matcherTypes);
		foreach(i,x; matcherTypes){
			if(!resolved[i] && x && x.adapted && !x.ambiguous){
				resolvedSome = true;
				resolved[i]=x.adapted;
			}
		}

		if(resolvedSome){
			matchState = MatchState.iftiPrepare;
			mixin(RetryEplg);
		}
		// foreach(i,t; parent.params)
	}

	private bool finishMatching(){

		auto tuplepos = parent.tuplepos;
		auto params = parent.params;

		foreach(i, p; params){
			if(!resolved[i]) continue;
			if(p.which!=WhichTemplateParameter.constant) continue;
			if(resolved[i].type.equals(p.type)) continue;
			// TODO: this 'force' is maybe dangerous
			match = min(match, resolved[i].type.constConvertsTo(p.type).force ?
			                                      Match.convConst       :
			                                      Match.convert         );
		}

		if(tuplepos < params.length && !resolved[tuplepos])
			resolved[tuplepos]=New!ExpTuple(paramScope.iparent,(Expression[]).init);

		alias util.any any;
		if(any!(_=>_ is null)(resolved)) return false;

		fillScopes();

		needRetry=false;
		return true;
	}

	final bool finishedInstantiation(){ return bdy !is parent.bdy; }

	void finishInstantiation(bool startAnalysis)in{
		assert(sstate != SemState.error);
		assert(!finishedInstantiation());
		assert(parent.sstate == SemState.completed);
		assert(!!paramScope);
	}body{
		auto bdyscope=New!NestedScope(paramScope);
		bdy = bdy.ddup();

		auto instanceScope = paramScope.iparent;
		bdy.stc|=parent.stc;
		if(instanceScope !is parent.scope_) bdy.stc&=~STCstatic;
		bdy.presemantic(bdyscope);
		assert(bdy.scope_ is bdyscope);
		auto decl=instanceScope.getDeclaration();
		if(decl) decl.nestedTemplateInstantiation(this); // TODO: correct?
		sstate = SemState.begin;
		if(startAnalysis) this.startAnalysis();
		else Scheduler().remove(this);
	}

	void startAnalysis()in{
		assert(finishedInstantiation);
	}body{
		matchState = MatchState.analysis;
		if(!isGagged) Scheduler().add(this, scope_);
	}

	private bool resolveDefault(Scope sc){
		bool resolvedSome = false;
		auto params = parent.params;
		// TODO: check whether the default argument matches
		foreach(i,ref r; resolved)
			if(!resolved[i]&&params[i].init){
				resolved[i]=params[i].init.ddup();
				resolvedSome = true;
			}
		foreach(r;resolved) if(r) r.prepareInterpret();
		foreach(ref r;resolved) if(r) mixin(SemChldPar!q{r});
		foreach(i,ref x;resolved){
			if(!x||x.sstate == SemState.error) continue;
			TemplateDecl.finishArgumentPreparation(sc, x);
			mixin(PropRetry!q{x});
			//if(!r||r.isSymbol()||r.isType()) continue;
			//mixin(IntChld!q{r});
		}
		return resolvedSome;
	}

	bool iftiAgain; // TODO: we don't want this in the instance!
	override void semantic(Scope sc_){
		if(sstate == SemState.error) return; // TODO: why needed?
		// assert(sstate != SemState.error); // would like to have this
		alias scope_ sc;
		needRetry=false;
		Ldecide:final switch(matchState) with(MatchState){
			case start, iftiStart:
				if(!startMatching(sc_))
					mixin(ErrEplg);
				if(matchState == start){
					matchState = resolvedSemantic; goto case resolvedSemantic;
				}else { matchState = iftiPrepare; goto case iftiPrepare; }

			case iftiPrepare, iftiMatching:
				matchIFTI();
				mixin(SemCheck);
				matchState = iftiResolvedSemantic;
				iftiAgain = false;
				goto case iftiResolvedSemantic;

			case resolvedSemantic, iftiResolvedSemantic:
				iftiAgain |=
					resolveDefault(matchState==iftiResolvedSemantic?iftiScope:scope_);
				mixin(SemCheck);
				assert(!needRetry);
				if(matchState == resolvedSemantic || !iftiAgain){
					matchState = checkMatch;
					goto case checkMatch;
				}else{
					matchState = iftiPrepare;
					goto case iftiPrepare;
				}

			case checkMatch:
				foreach(ref x;resolved){if(x) mixin(SemChldPar!q{x});}
				if(!checkResolvedValidity()||!finishMatching())
					mixin(ErrEplg);

				matchState = checkConstraint;

				auto r = parent.completeMatching(this, isGagged);
				if(r !is this) mixin(RewEplg!q{r});

				goto case checkConstraint;
			case checkConstraint:
				if(constraint){
					analyzeConstraint();
					mixin(SemCheck);
					if(!constraint.interpretV()){
						// TODO: show exact failing clause
						if(sc) sc.error("template constraint failed", loc);
						mixin(ErrEplg);
					}
				}

				matchState = completed;
				goto case completed;
			case checkingConstraint:
				if(sc) sc.error("recursive template expansion in template constraint", constraint.loc);
				mixin(ErrEplg);
				// give the instance exp a chance to finish the instantiation process
				case completed: Scheduler().remove(this); break;
				case analysis:
					assert(finishedInstantiation);
					instanceSemantic(sc_);
					break;
		}
	}

	private void instanceSemantic(Scope sc_)in{
		assert(finishedInstantiation);
	}body{
		// dw("ism ", this);
		{alias sc_ sc;mixin(SemPrlg);}
		assert(sstate == SemState.begin);
		sstate = SemState.started;
		scope(exit) if(sstate == SemState.started) sstate = SemState.begin;
		assert(!constraint||constraint.type is Type.get!bool());
		assert(!constraint||constraint.isConstant() && constraint.interpretV());
		assert(bdy !is parent.bdy);
		//mixin(SemChld!q{bdy});
		{
			auto sc = bdy.scope_;
			mixin(SemChld!q{bdy});
		}
		mixin(SemEplg);
	}


	private{
		Parameter[] eponymousFunctionParameters;
		Scope constraintScope;
	}

	private void initializeConstraintScope(){
		if(!constraintScope){
			constraintScope = paramScope.cloneNested(paramScope.iparent);
			if(parent.eponymousDecl) if(auto fd = parent.eponymousDecl.isFunctionDecl()){
				// TODO: gc allocation
				eponymousFunctionParameters = fd.type.params.dup;
				foreach(ref x; eponymousFunctionParameters)
					x=x.ddup;
			}
		}
	}

	private void analyzeConstraint(){
		alias constraintScope sc;
		mixin(PropErr!q{constraint});
		if(constraint.sstate == SemState.completed && constraint.isConstant())
			return;

		initializeConstraintScope();

		foreach(ref x; eponymousFunctionParameters){
			mixin(SemChldPar!q{x});
			if(x.sstate == SemState.error)
				mixin(SetErr!q{constraint});
		}
		mixin(PropErr!q{constraint});

		matchState = MatchState.checkingConstraint;
		scope(exit) matchState = MatchState.checkConstraint;

		constraint.prepareInterpret();
		constraint.prepareLazyConditionalSemantic();
		mixin(SemChldExp!q{constraint});
		mixin(ConvertTo!q{constraint,Type.get!bool()});
		mixin(IntChld!q{constraint});
	}


	/* template instances serve as containers for other declarations
	   they do not need to be checked for accessibility
	 */
	override bool needsAccessCheck(AccessCheck check){ return false; }

	override string kind(){return "template instance";}
	override string toString(){
		auto r = resolved;
		return name.toString()~"!("~join(map!(to!string)(r),",")~")";
	}

	mixin DownCastMethod;
	mixin Visitors;
}

interface Tuple{
	Expression index(Scope sc, const ref Location loc, ulong index)
		in{assert(index<length);}
	Expression slice(Scope sc, const ref Location loc, ulong a, ulong b)
		in{assert(a<=b && b<length);}

	@property ulong length();

	int opApply(scope int delegate(Expression) dg);


	static Expression[] expand(T...)(Expression[] a, ref T replicate){
		// TODO: this is very naive and inefficient
		Expression[] r;
		T rep;
		typeof(r.length) index = 0;
		foreach(i,x;a){
			if(!x) continue;
			if(auto tp=x.isTuple()){
				foreach(y; tp) y.loc=x.loc;
				if(auto et=x.isExpTuple()){
					et.accessCheckSymbols();
					r~=a[index..i]~et.exprs;
				}else if(auto tt=x.isTypeTuple())
					r~=a[index..i]~cast(Expression[])tt.types;
				foreach(j,ref rr;rep){
					rr~=replicate[j][index..i];
					foreach(k;0..tp.length) rr~=replicate[j][i];
				}
				index=i+1;
			}
		}
		if(index){
			foreach(j,ref rr;rep) rr~=replicate[j][index..$];
			foreach(j,rr;rep) replicate[j]=rr;// bug: simple assignment does not work
		}
		return index?r~=a[index..$]:a;
	}

	static VarDecl[] expand()(Scope sc, VarDecl[] a) in{ //templated as workaround
/+		alias util.all all;
		assert(all!(_=>!_.rtype&&!_.init||_.sstate == SemState.completed)(a));+/
	}body{
		// TODO: this is very naive and inefficient
		VarDecl[] r;
		typeof(r.length) index = 0;
		foreach(i,x;a){
			if(!x.type) continue;
			if(auto tp=x.type.isTypeTuple()){
				assert(x.tupleContext && x.tupleContext.tupleAlias);
				r~=a[index..i]~x.tupleContext.vds;
				index=i+1;
			}
		}
		return index?r~a[index..$]:a;
	}
	static Parameter[] expand()(Scope sc,Parameter[] a){ // ditto
		return cast(Parameter[])expand(sc,cast(VarDecl[])a);
	}

}

class ExpTuple: Expression, Tuple{
	/* indexing an expression tuple might create a symbol reference
	   therefore we need to remember the access check level.
	 */
	AccessCheck accessCheck = AccessCheck.all;

	protected this(){
		alias util.all all;
		assert(all!(_=>_.sstate==SemState.completed)(exprs));
	}

	this(Scope sc, Expression[] exprs)in{
		alias util.all all;
		assert(all!(_=>_.sstate==SemState.completed)(exprs));
	}body{
		// TODO: gc allocation
		this.exprs = new Expression[exprs.length];
		foreach(i, ref x; this.exprs) x=exprs[i].clone(sc, loc);
		exprs=Tuple.expand(exprs);
	}

	this(Scope sc, ulong len, Expression exp)in{
		assert(exp.sstate == SemState.completed);
		assert(len<=size_t.max);
	}body{
		// TODO: gc allocation
		exprs = new Expression[cast(size_t)len];
		foreach(ref x; exprs) x=exp.clone(sc,loc);
	}

	override Tuple isTuple(){return this;}

	void accessCheckSymbols(){
		foreach(r; exprs){
			if(auto s=r.isSymbol()){
				if(s.accessCheck<accessCheck){
					s.accessCheck = accessCheck;
					s.performAccessCheck();
				}
			}
		}
	}

	Expression index(Scope sc, const ref Location loc, ulong index){
		assert(index<length); // TODO: get rid of this when DMD is fixed
		assert(sstate == SemState.completed);
		auto r=exprs[cast(size_t)index].clone(sc,loc);

		if(auto s=r.isSymbol()){
			if(s.accessCheck<accessCheck){
				s.accessCheck = accessCheck;
				s.performAccessCheck();
			}
		}
		return r;
	}
	Expression slice(Scope sc, const ref Location loc, ulong a,ulong b)in{
		assert(a<=b && b<=length);
	}body{
		assert(sstate == SemState.completed);
		return New!ExpTuple(sc,exprs[cast(size_t)a..cast(size_t)b]);
	}
	@property ulong length(){ return exprs.length;}

	int opApply(scope int delegate(Expression) dg){
		foreach(x; exprs) if(auto r = dg(x)) return r;
		return 0;
	}

	override void semantic(Scope sc){
		mixin(SemPrlg);
		alias util.all all;
		// the empty tuple is an expression except if a type is requested
		if(exprs.length && all!(_=>cast(bool)_.isType())(exprs)){
			auto r=New!TypeTuple(cast(Type[])exprs);
			assert(r.sstate == SemState.completed);
			mixin(RewEplg!q{r});
		}
		// TODO: gc allocation
		Type[] tt = new Type[exprs.length];
		foreach(i,x;exprs){
			if(auto ty=x.isType()) tt[i]=ty;
			else tt[i]=x.type;
		}
		type = New!TypeTuple(tt);
		dontConstFold();
		mixin(SemEplg);
	}

	override ExpTuple clone(Scope sc, const ref Location loc){
		auto r = ddup();
		foreach(ref x; r.exprs) x = x.clone(sc,loc);
		r.loc = loc;
		r.sstate = SemState.begin;
		r.semantic(sc);
		return r;
	}


	override string toString(){return "("~join(map!(to!string)(exprs),",")~")";}
	override @property string kind(){return "sequence";}

	override bool isConstant(){
		alias util.all all;
		return all!(_=>_.isConstant())(exprs);
	}
	override bool isConstFoldable(){
		alias util.all all;
		return all!(_=>_.isConstFoldable())(exprs);
	}

	mixin TupleImplConvTo!exprs;

	mixin DownCastMethod;
	mixin Visitors;

	override bool templateParameterEquals(Expression rhs){
		alias util.all all;
		import std.range;
		if(auto et = rhs.isExpTuple()){
			if(et.length != length) return false;
			return all!(_=>_[0].templateParameterEquals(_[1]))(zip(exprs,et.exprs));
		}
		// this is not going to happen, since template parameters are only compared
		// if both match the instantiation => both are tuples or not tuples
		return false;
	}
	override size_t templateParameterToHash(){
		import hashtable;
		return FNVred(exprs);
	}

private:
	Expression[] exprs;
}

// TODO: inherit from comma expression as soon as tuple expansion works with it
class MultiReturnValueExp: Expression{
	CallExp call;
	Expression exp;
	this(CallExp call, Expression exp)in{
		assert(call.tmpVarDecl && call.tmpVarDecl.sstate == SemState.completed);
		assert(call.tmpVarDecl.tupleContext);
		alias util.all all;
		assert(all!(a=>a.sstate == SemState.completed)(call.tmpVarDecl.tupleContext.syms));
	}body{
		this.call = call;
		this.exp = exp;
		type = exp.type;
		sstate = SemState.completed;
	}

	override void semantic(Scope sc){
		mixin(SemPrlg);
		assert(0);
	}

	override MultiReturnValueExp clone(Scope sc, const ref Location loc){
		auto r=New!MultiReturnValueExp(call, exp.clone(sc,loc));
		r.loc = loc;
		r.semantic(sc);
		return r;
	}

	mixin DownCastMethod;
	mixin Visitors;
}
mixin template Semantic(T) if(is(T==MultiReturnValueExp)){}
ExpTuple makeMultiReturn(CallExp call)in{
	assert(call.sstate == SemState.completed);
	assert(call.tmpVarDecl && call.tmpVarDecl.sstate == SemState.completed);
	assert(call.tmpVarDecl.tupleContext);
	alias util.all all;
	assert(all!(a=>a.sstate == SemState.completed)(call.tmpVarDecl.tupleContext.syms));
}body{
	Expression r;
	if(call.tmpVarDecl.tupleContext.syms.length){
		r=call.tmpVarDecl.tupleContext.vds[0].init=
			New!MultiReturnValueExp(call, call.tmpVarDecl.tupleContext.syms[0]);
		return New!ExpTuple(call.tmpVarDecl.scope_, r~call.tmpVarDecl.tupleContext.syms[1..$]);
		// TODO: aliasing would be ok here
	}
	assert(0,"TODO: zero return values");
}

mixin template TupleImplConvTo(alias exprs){
	override Dependent!bool implicitlyConvertsTo(Type rhs){
		auto tt = rhs.isTypeTuple();
		if(!tt||tt.length!=length) return false.independent;
		Node[] dep;
		Scope idk = null;
		import std.range;
		foreach(x; zip(exprs, tt.types)){
			auto iconvd = x[0].implicitlyConvertsTo(x[1]);
			if(iconvd.dependee){
				assert(!idk || iconvd.dependee.scope_ is idk);
				idk = iconvd.dependee.scope_;
				dep ~= iconvd.dependee.node; // TODO: this is inefficient
				continue;
			}
			if(!iconvd.value) return false.independent;
		}
		if(idk) return multidep(dep, idk).dependent!bool;
		assert(!dep.length);
		return true.independent;
	}
}


class TypeTuple: Type, Tuple{
	this(Type[] types)in{
		alias util.all all;
		assert(all!(_=>_.sstate==SemState.completed)(types));
		assert(all!(_=>!_.isTuple())(types));
	}body{
		this.types = types;
		sstate = SemState.completed;
	}
	override void semantic(Scope sc){
		mixin(SemPrlg);
		assert(0);
	}

	override Tuple isTuple(){return this;}
	Expression index(Scope sc,const ref Location loc, ulong index){
		assert(index<length); // TODO: get rid of this when DMD is fixed
		assert(sstate == SemState.completed);
		return types[cast(size_t)index];
	}
	Expression slice(Scope sc,const ref Location loc, ulong a,ulong b)in{
		assert(a<=b && b<=length);
	}body{
		assert(sstate == SemState.completed);
		return New!TypeTuple(types[cast(size_t)a..cast(size_t)b]);
	}
	@property ulong length(){ return types.length;}

	// workaround for lacking delegate contravariance
	final override int opApply(scope int delegate(Expression) dg){
		return opApply(cast(int delegate(Type))dg);
	}
	final int opApply(scope int delegate(Type) dg){
		foreach(x; types) if(auto r = dg(x)) return r;
		return 0;
	}

	override string toString(){return "("~join(map!(to!string)(types),",")~")";}
	override @property string kind(){return "type sequence";}

	override bool equals(Type rhs){
		alias util.all all;
		import std.range;
		if(auto tt = rhs.isTypeTuple()){
			if(tt.length!=types.length) return false;
			return all!(a=>a[0].equals(a[1]))(zip(types, tt.types));
		}
		return false;
	}
	
	mixin TupleImplConvTo!types;

	mixin DownCastMethod;
	mixin Visitors;

	override bool templateParameterEquals(Expression rhs){
		alias util.all all;
		import std.range;
		if(auto tt = rhs.isTypeTuple()){
			if(tt.length!=types.length) return false;
			return all!(_=>_[0].templateParameterEquals(_[1]))(zip(types,tt.types));
		}
		return false;
	}

	override size_t templateParameterToHash(){
		import hashtable;
		return FNVred(types);
	}

private:
	Type[] types;
}


mixin template Semantic(T) if(is(T==TemplateParameter)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(rtype){
			type = rtype.typeSemantic(sc);
			mixin(SemProp!q{rtype});
			if(rspec){
				// TODO: ok?
				rspec.prepareInterpret();
				mixin(SemChldExp!q{rspec});
				mixin(FinishDeductionProp!q{rspec});

				mixin(ImplConvertTo!q{rspec, type});
				mixin(IntChld!q{rspec});
			}
			assert(!spec);
		}else if(rspec){
			// TODO: alias!!
			spec = rspec.typeSemantic(sc);
			mixin(SemProp!q{rspec});
		}
		mixin(SemEplg);
	}
	final Dependent!bool matches(Expression arg)in{
		assert(sstate == SemState.completed);
		assert(arg.sstate == SemState.completed);
		assert(which != WhichTemplateParameter.tuple);
	}body{
		final switch(which) with(WhichTemplateParameter){
			case alias_:
				// TODO: rspec!!
				return (arg.isSymbol()||arg.isType()||arg.isConstant()).independent;
			case constant:
				if(!arg.isConstant()) return false.independent;

				assert(!!this.type && this.type.sstate == SemState.completed);
				assert(!rspec || rspec.sstate == SemState.completed);

				mixin(ImplConvertsTo!q{bool iconv; arg, this.type});
				if(!iconv) return false.independent;
				// TODO: implicit conversion is wasteful on GC
				if(rspec){
					auto conv=arg.implicitlyConvertTo(this.type);
					conv.semantic(null);
					mixin(Rewrite!q{conv});
					// TODO: this loses the expression...
					if(conv.sstate!=SemState.completed)
						return Dependee(conv, null).dependent!bool;
					if(arg.interpretV()!=rspec.interpretV()) return false.independent;
				}
				return true.independent;
			case type, this_:
				if(!arg.isType) return false.independent;
				if(!spec) return true.independent;
				return arg.implicitlyConvertsTo(spec);
			case tuple:
				assert(0);
		}
	}

	invariant(){assert(sstate != SemState.completed || !rtype || !!type);}
}

mixin template Semantic(T) if(is(T==TemplateDecl)){
	/* position of the first tuple parameter, or params.length if there is none
	 */
	size_t tuplepos = -1;

	Declaration eponymousDecl;

	// TODO: how to deal with overloading?
	FunctionDecl iftiDecl(){
		//if(!eponymousDecl||bdy.decls.length!=1) return null;
		if(!eponymousDecl) return null;
		return eponymousDecl.isFunctionDecl();
	}

	Dependent!bool atLeastAsSpecialized(TemplateDecl rhs)in{
		assert(sstate == SemState.completed && sstate == rhs.sstate);
	}body{
		Dependee dependee;
		if(tuplepos != params.length){
			if(rhs.tuplepos == rhs.params.length)
				return false.independent; // no tuple param is more specialized
		}
		// TODO: there should be more rules
		
		foreach(i,p; params[0..min($, rhs.params.length)]){
			auto rp = rhs.params[i];
			with(WhichTemplateParameter)
			if(p.which == tuple && rp.which != tuple
			|| p.which == alias_ && rp.which != alias_)
				return false.independent;
			if(p.spec && rp.spec){
				// the answer 'false' might be determined from incomplete information
				auto rptopd=rp.spec.implicitlyConvertsTo(p.spec);
				auto ptorpd=p.spec.implicitlyConvertsTo(rp.spec);
				if(auto d=rptopd.dependee){dependee = d; continue;}
				if(auto d=ptorpd.dependee){dependee = d; continue;}
				if(rptopd.value&&!ptorpd.value)
					return false.independent;
			}
		}
		return Dependent!bool(dependee, true);
	}

	static void finishArgumentPreparation(Scope sc, ref Expression x){
		// TODO: fix code duplication!
		if(x.sstate != SemState.completed) return;
		if(x.isType()) return;
		if(auto ae=x.isAddressExp()) if(auto lit=ae.e.isSymbol()){
			// turn the function literal into a function declaration
			lit.isFunctionLiteral=false;
			if(auto fd = lit.meaning.isFunctionDecl())
				if(fd.type.hasUnresolvedParameters()){
					lit.sstate = SemState.begin;
					fd.sstate = SemState.pre;
					fd.scope_ = null;
					lit.meaning = fd.templatizeLiteral();
					lit.meaning.semantic(sc);
					mixin(Rewrite!q{lit.meaning});
					assert(lit.meaning.sstate == SemState.completed && !lit.meaning.needRetry);
					x = lit;
				}
			return;
		}
		if(x.isSymbol()||x.isType()) return;
		x.interpret(sc);
	}


	override void semantic(Scope sc){
		if(sstate == SemState.pre) presemantic(sc);
		mixin(SemPrlg);
		bdy.pickupSTC(stc);
		foreach(x; params) x.sstate = max(x.sstate,SemState.begin);
		mixin(SemChld!q{params});

		tuplepos=params.length;
		foreach_reverse(i,x; params)
			if(x.which == WhichTemplateParameter.tuple) tuplepos = i;

		// See if the eponymous declaration can be determined without analyzing
		// the template body. This is required for IFTI and template constraints.
		// TODO: deal with overloaded eponymous symbols
		foreach(x; bdy.decls){
			if(x.name && x.name.name is name.name) eponymousDecl = x;
			break;
		}

		sc.getModule().addTemplateDecl(this);
		mixin(SemEplg);
	}

	/* templates are always accessible, it is the contents of their instantiations
	   that might not be.
	 */
	override bool needsAccessCheck(AccessCheck check){ return false; }

/+ // TODO: where to put this?
	final static void verifyArgs(Expression[] args){
		alias util.all all;
		assert(all!(_=>_.sstate == SemState.completed &&(_.isType()||_.isConstant()||_.isSymbol())||_.isAddressExp()&&_.isAddressExp().e.isSymbol())(args),{
				string r;
				foreach(x;args){
					r~=text(x," ",x.sstate == SemState.completed," ",!!x.isType(),!!x.isConstant(),!!x.isSymbol(),'\n');
				}
				return r;
			}());
	}
+/
	private Declaration matchHelper(bool fullySpecified, T...)(Scope sc, const ref Location loc, T ts){
		alias ts[!fullySpecified] args; // respect this_
		assert(!!scope_);
		assert(sstate == SemState.completed);

		auto gagged = !sc||!sc.handler.showsEffect;

		static if(fullySpecified) if(auto r=store.lookup(args)){
			if(!gagged&&r.isGagged()) r.ungag();
			return r;
		}

		auto inst = New!TemplateInstanceDecl(this,loc,ts[!fullySpecified..$]);
		if(gagged) inst.gag();

		if(!inst.completedMatching){
			inst.semantic(sc);
			mixin(Rewrite!q{inst});
			if(inst.needRetry) return inst;
		}
		if(inst.sstate == SemState.error) return null; // TODO: remove
		return inst;
	}

	TemplateInstanceDecl completeMatching(TemplateInstanceDecl inst, bool gagged){
		if(auto exst = store.lookup(inst.resolved)) inst = exst;
		else store.add(inst);
		// dw("built ", inst);
		return inst;
	}

	override Declaration matchInstantiation(Scope sc, const ref Location loc, Expression[] args){
		auto r=matchHelper!true(sc, loc, args);
		// TODO: more explicit error message
		if(!r && sc) sc.error("instantiation does not match template declaration",loc);
		return r;
	}

	override Declaration matchIFTI(Scope sc, const ref Location loc, Type this_, Expression[] args, Expression[] funargs){
		if(!iftiDecl) return matchInstantiation(sc, loc, args);
		auto r=matchHelper!false(sc, loc, this_, args, funargs);
		// TODO: more explicit error message
		if(!r && sc) sc.error("could not match call to function template",loc);
		return r;
	}

	final override Dependent!Declaration matchCall(Scope sc, const ref Location loc, Type this_, Expression[] args, ref MatchContext context){
		assert(0);
	}


private:
	struct TemplateInstanceStore{
		import hashtable;
		static bool eq(Expression[] a,Expression[] b){
			if(a.length!=b.length) return false;
			foreach(i;0..a.length) if(!a[i].templateParameterEquals(b[i])) return false;
			return true;
		} // equality check
		static size_t h0(Expression[] a){ return FNVred(a); }      // hash

		private HashMap!(Expression[],TemplateInstanceDecl, eq, h0) instances;


		void add(TemplateInstanceDecl decl)in{
			assert(decl.completedParameterResolution);
		}body{
			foreach(x; decl.resolved)
				if(auto ty = x.isType())
					if(ty.hasPseudoTypes())
						return;

			instances[decl.resolved] = decl;
		}

		TemplateInstanceDecl lookup(Expression[] args){
			return instances.get(args,null);
		}
	}

	TemplateInstanceStore store;
	TemplateInstanceStore gaggedStore;
}



mixin template Semantic(T) if(is(T==TemplateInstanceExp)){
	override void semantic(Scope sc){
		mixin(SemPrlg);

		// eponymous template trick
		if(!!res){
			if(needIFTI) iftiResSemantic(sc);
			else instantiateResSemantic(sc);
			return;
		}

		mixin(RevEpoLkup!q{e});
		foreach(x; args){
			if(x.sstate != SemState.completed && !x.isFunctionLiteralExp()){
				x.prepareInterpret();
				x.weakenAccessCheck(AccessCheck.none);
			}
		}

		mixin(SemChld!q{e, args});

		Expression container = null;
		auto sym = e.isSymbol();
		if(!sym){
			if(auto fld = e.isFieldExp()){
				container = fld.e1;
				sym = fld.e2;
			}else{
				// TODO: this error message has a duplicate in Declaration.matchInstantiation
				sc.error(format("can only instantiate templates, not %s%ss",e.kind,e.kind[$-1]=='s'?"e":""),loc);
				mixin(ErrEplg);
			}
		}

		foreach(i,ref x; args){
			TemplateDecl.finishArgumentPreparation(sc, x);
			mixin(PropRetry!q{x});
		}

		mixin(SemChld!q{args});

		if(needIFTI) return IFTIsemantic(sc,container,sym);
		instantiateSemantic(sc,container,sym);
	}

	bool needIFTI = false;
	Expression[] iftiArgs;
	override void willCall() { needIFTI=true; }

	private void IFTIsemantic(Scope sc, Expression container, Symbol sym){
		mixin(SemChld!q{e,args});
		type = type.get!void();
		// the state will be reset in matchCallHelper
		if(!inst) mixin(SemEplg);
		finishSemantic(sc, container, sym);
	}

	override Dependent!Expression matchCallHelper(Scope sc, const ref Location loc, Type th_, Expression[] funargs, ref MatchContext context){
		assert(!th_);
		enum SemRet = q{ return this.independent!Expression; };
		assert(needIFTI);
		assert(sstate == SemState.completed);
		sstate = SemState.begin;
		iftiArgs = funargs;

		Expression container = null;
		Type this_ = null;
		auto sym = e.isSymbol();
		if(sym) this_ = sym.maybeThisContext();
		else{
			assert(!!cast(FieldExp)e);
			if(auto fld=cast(FieldExp)cast(void*)e){
				container = fld.e1;
				sym = fld.e2;
				if(auto tt=container.extractThis())	this_ = tt.type;
			}
		}

		inst = sym.meaning.matchIFTI(sc, loc, this_, args, funargs);
		if(!inst||inst.sstate==SemState.error) mixin(ErrEplg);

		if(!inst.isTemplateInstanceDecl
		|| !(cast(TemplateInstanceDecl)cast(void*)inst).completedMatching){
			mixin(SemChld!q{inst});
		}
		mixin(SemRet);
	}


	private void instantiateSemantic(Scope sc, Expression container, Symbol sym){
		if(!inst){
			inst = sym.meaning.matchInstantiation(sc, loc, args);
			if(!inst||inst.sstate==SemState.error) mixin(ErrEplg);
		}
		assert(!!inst);
		finishSemantic(sc, container, sym);
	}

	private void finishSemantic(Scope sc, Expression container, Symbol sym){
		if(!inst.isTemplateInstanceDecl
		|| !(cast(TemplateInstanceDecl)cast(void*)inst).completedMatching){
			mixin(PropErr!q{inst});
			mixin(SemChld!q{inst});
		}

		assert(!!cast(TemplateInstanceDecl)inst, text(typeid(this.inst)));
		auto inst = cast(TemplateInstanceDecl)cast(void*)inst; // update static type of inst
		auto decl = inst.parent;

		needRetry=false;
		foreach(i,x; decl.params[0..min($,args.length)]){
			mixin(Rewrite!q{args[i]});
			if(args[i].isType()) continue;
			if(x.which==WhichTemplateParameter.constant){
				mixin(ImplConvertTo!q{args[i],x.type});
			}else if(x.which==WhichTemplateParameter.tuple)
				break;
		}

		mixin(PropErr!q{args});
		// ! changing meaning of 'sym'
		auto acheck = sym.accessCheck;
		if(!inst.finishedInstantiation()) inst.finishInstantiation(true); // start analysis
		if(sc.handler.showsEffect&&inst.isGagged) inst.ungag();
		sym = New!Symbol(inst);
		sym.loc = loc;
		sym.accessCheck = acheck;

		if(container){
			auto res = New!(BinaryExp!(Tok!"."))(container, sym);
			res.loc = loc;
			res.accessCheck = acheck;
			this.res = res;
		}else res = sym;

		// for eponymous template trick: attempt lookup and don't perform trick if it fails
		eponymous=New!Identifier(decl.name.name);
		eponymous.loc=loc;
		eponymous.accessCheck = acheck;
		semantic(sc); // no indefinite recursion because 'res' is now set
	}

	private void instantiateResSemantic(Scope sc){
		{// TODO: this is kludgy
			auto tmpl = sc.getTemplateInstance();
			if(tmpl){
				if(tmpl.sstate == SemState.begin) tmpl.sstate = SemState.started;
				else tmpl = null;
			}
			scope(exit) if(tmpl) tmpl.sstate = SemState.begin;
			if(!inst.sstate == SemState.started) mixin(SemChld!q{res});
		}
		if(!eponymous.meaning && eponymous.sstate != SemState.failed
		&& eponymous.sstate != SemState.error){
			eponymous.recursiveLookup = false;
			//eponymous.lookup(res.getMemberScope());
			mixin(Lookup!q{_; eponymous, res.getMemberScope()});
		}
		if(auto nr=eponymous.needRetry) { needRetry = nr; return; }
		mixin(PropErr!q{eponymous});
		Identifier.tryAgain = true;
		if(eponymous.sstate == SemState.failed){
			needRetry=false;
			auto r = res;
			if(r.sstate!=SemState.completed&&r.sstate!=SemState.error)
				r.needRetry=true; // let the caller do the semantic analysis
			mixin(RewEplg!q{r});
		}
		Expression r=New!(BinaryExp!(Tok!"."))(res, eponymous);
		r.loc=loc;
		r.needRetry=true; // let the caller do the semantic analysis
		mixin(RewEplg!q{r});
	}

	private void iftiResSemantic(Scope sc){
		// TODO: fix this kludge
		instantiateResSemantic(sc);
		if(!rewrite) return;
		assert(!!cast(Expression)rewrite);
		auto tmp = rewrite.sstate!=SemState.completed?null.independent!Expression:
			(cast(Expression)cast(void*)rewrite).matchCall(sc, loc, iftiArgs);
		if(tmp.dependee||!tmp.value){
			static class MatchCallWhenReady: Expression{
				Expression exp;
				Expression[] iftiArgs;
				this(Expression e, const ref Location l, Expression[] ia){
					exp = e; loc = l; iftiArgs = ia;
				}
				void semantic(Scope sc){
					mixin(SemPrlg);
					mixin(SemChld!q{exp});
					mixin(MatchCall!q{auto r; exp, sc, loc, iftiArgs});
					if(!r) mixin(ErrEplg);
					mixin(RewEplg!q{r});
				}
				override string toString(){ return exp.toString(); }
			}
			auto r = New!MatchCallWhenReady(cast(Expression)cast(void*)rewrite, loc, iftiArgs);
			rewrite = null;
			r.semantic(sc);
			if(rewrite) return; // TODO: ok?
			mixin(RewEplg!q{r});
		}
		rewrite = tmp.value;
		if(!rewrite) mixin(ErrEplg);
	}

	override void noHope(Scope sc){
		if(res){
			auto unresolved = res.getMemberScope();
			if(!unresolved.inexistent(eponymous))
				mixin(ErrEplg);
		}else{
			mixin(RevEpoNoHope!q{e});
		}
	}

private:
	Expression res;
	Identifier eponymous;
	Declaration inst;
}

mixin template Semantic(T) if(is(T==ABinaryExp)){
}
mixin template Semantic(T) if(is(T _==BinaryExp!S,TokenType S) && !is(T==BinaryExp!(Tok!"."))){
	static if(is(T _==BinaryExp!S,TokenType S)):

	static if(S==Tok!"||"||S==Tok!"&&") bool lazyConditionalSemantic = false;

	override void semantic(Scope sc){
		mixin(SemPrlg);
		// TODO: can this be solved more elegantly?
		static if(S==Tok!"||"||S==Tok!"&&"){
			if(lazyConditionalSemantic){
				e1.prepareInterpret();
				mixin(SemChldExp!q{e1});
				auto bl = Type.get!bool();
				mixin(ConvertTo!q{e1,bl});
				mixin(IntChld!q{e1});
				if(cast(bool)e1.interpretV()^(S==Tok!"&&")) mixin(RewEplg!q{e1});
				else{
					mixin(SemChldExp!q{e2});
					auto vd = Type.get!void();
					if(e2.type.getHeadUnqual() is vd){
						type = vd;
					}else{
						mixin(ConvertTo!q{e2,bl});
						type = bl;
					}
					mixin(ConstFold!q{e2});
					mixin(SemEplg);
				}
			}
		}

		mixin(SemChldExp!q{e1,e2});
		// constant folding done by hijacking the SemEplg macro TODO: better options?
		auto c1 = e1.isConstFoldable(), c2 = e2.isConstFoldable();
		enum SemEplg = q{
			if(c1^c2){ // if both are constant, then the entire expression will be folded
				if(c1) mixin(ConstFold!q{e1});
				else mixin(ConstFold!q{e2});
			}
		}~SemEplg;
		static if(isAssignOp(S)){
			// TODO: properties, array ops \ ~=
			if(e1.checkMutate(sc,loc)){
				type = e1.type;
				static if(S==Tok!"~="){
					if(auto tt=type.isDynArrTy()){
						auto elt=tt.getElementType();
						mixin(ImplConvertsTo!q{auto e2toelt; e2, elt});
						if(e2toelt) e2=e2.implicitlyConvertTo(elt);
						else e2=e2.implicitlyConvertTo(type);
					}else{
						if(e1.finishDeduction(sc) && e2.finishDeduction(sc))
						// TODO: operator overloading
							sc.error(format("cannot append to expression of type '%s'", type),loc);
						mixin(ErrEplg);
					}
				}else static if(S==Tok!"+=" || S==Tok!"-="){
					if(auto tt=type.isPointerTy()){
						auto s_t = Type.get!Size_t();
						assert(tt.getSizeof() == s_t.getSizeof());
						e2=e2.implicitlyConvertTo(s_t);
					}else e2=e2.implicitlyConvertTo(type);
				}else e2=e2.implicitlyConvertTo(type);
				mixin(SemChld!q{e2});
				mixin(ConstFold!q{e2});
				/+if(e2.implicitlyConvertsTo(type)){
					...
				}else{
					sc.error(format("assigning to a '%s' from incompatible type '%s'",
					                e1.type.toString(), e2.type.toString()), loc);
					mixin(ErrEplg);
				}+/
				mixin(.SemEplg); // don't const fold lhs
			}else mixin(ErrEplg);
			//sc.error(format("expression '%s' is not assignable",e1.loc.rep),loc);
		}else static if(S==Tok!"in"||S==Tok!"!in"){
			type = Type.get!bool();
			super.semantic(sc);// TODO: implement
		}else static if(isRelationalOp(S)){
			Type ty = null;
			//bool conv1 = e2.implicitlyConvertsTo(e1.type);
			//bool conv2 = e1.implicitlyConvertsTo(e2.type);
			mixin(ImplConvertsTo!q{auto conv1; e2, e1.type});
			mixin(ImplConvertsTo!q{auto conv2; e1, e2.type});
			if(conv1 ^ conv2){
				if(conv1) ty = e1.type;
				else ty = e2.type;
			}else{
				mixin(TypeCombine!q{auto tt; e1,e2});
				if(tt) ty=tt;
			}
			if(ty){
				auto tyu=ty.getHeadUnqual();
				if(tyu.isBasicType() || tyu.isPointerTy() || tyu is Type.get!(typeof(null))() || tyu.getElementType()){
					mixin(ImplConvertToPar!q{e1,ty});
					mixin(ImplConvertTo!q{e2,ty});
					mixin(PropErr!q{e1});
					assert(e1.sstate == SemState.completed
					    && e2.sstate == SemState.completed);
					type = Type.get!bool();
					static if(S!=Tok!"=="&&S!=Tok!"!="&&S!=Tok!"is"&&S!=Tok!"!is"){
						if(ty.isComplex()){
							sc.error("cannot compare complex operands",loc);
							mixin(ErrEplg);
						}
					}
					if(auto el = tyu.getElementType()){
						// TODO: stub exp strategies are inefficient
						// TODO: DMD does not do this. report bug.
						Expression x=New!(BinaryExp!S)(New!StubExp(el),New!StubExp(el));
						x.loc = loc;
						mixin(SemChld!q{x});
					}
					mixin(SemEplg);
				}
			}
			// TODO: Associative arrays
			// TODO: operator overloading
		}else static if(isLogicalOp(S)){
			static assert(S==Tok!"&&"||S==Tok!"||");
			auto bl = Type.get!bool();
			e1=e1.convertTo(bl); // TODO: implicit explicit conversion
			// allow (bool) && (void), (bool) || (void)
			auto ty2 = e2.type.getHeadUnqual();
			if(ty2 !is Type.get!void()){
				e2=e2.convertTo(bl); // TODO: implicit explicit conversion
				ty2 = bl;
			}
			mixin(SemChld!q{e1,e2});
			type = ty2;
			mixin(SemEplg);
		}else static if(isShiftOp(S)||isArithmeticOp(S)||isBitwiseOp(S)){
			auto t1=e1.type.getHeadUnqual(), t2=e2.type.getHeadUnqual();
			auto bt1=t1.isBasicType(), bt2=t2.isBasicType();
			auto v = Type.get!void();
			static if(isShiftOp(S)){
				if(bt1 && bt2 && bt1 !is v && bt2 !is v){
					if(bt1.isIntegral()&&bt2.isIntegral()){
						bt1=bt1.intPromote();
						// correctly promote qualified types
						if(bt1 is t1) t1 = e1.type; else t1 = bt1;
						mixin(ImplConvertTo!q{e1,t1});
						assert(e1.sstate == SemState.completed);
						type = t1;
						int valid = true;
						bool narrow;
						if(bt1.bitSize()==32) narrow = true;
						else{narrow = false;assert(bt1.bitSize()==64);}
						if(bt2.bitSize()==32){
							auto r = e2.getIntRange();
							if(!r.overlaps(IntRange(0,narrow?31:63,r.signed))) valid = false;
						}else{
							assert(bt2.bitSize()==64);
							auto r = e2.getLongRange();
							if(!r.overlaps(LongRange(0,narrow?31:63,r.signed))) valid = false;
						}
						if(!valid){
							// TODO: display exact amount if it is known
							sc.error(format("shift amount is outside the range 0..%d",narrow?31:63),loc);
							mixin(ErrEplg);
						}
						mixin(SemEplg);
					}
				}
			}else static if(isArithmeticOp(S) || isBitwiseOp(S)){
				enum isBitwise = isBitwiseOp(S);
				if(bt1 && bt2 && bt1 !is v && bt2 !is v && (!isBitwise||bt1.isIntegral()&&bt2.isIntegral())){
					static if(isBitwise){auto bl=Type.get!bool();if(bt1 is bl && bt2 is bl) goto Ldontpromote;}
					bt1=bt1.intPromote(); bt2=bt2.intPromote();
					// correctly promote qualified types
					if(bt1 is t1) t1 = e1.type; else t1 = bt1;
					if(bt2 is t2) t2 = e2.type; else t2 = bt2;

					Ldontpromote:

					static if(S == Tok!"*" || S==Tok!"/" || S==Tok!"%"){
						bool f1 = bt1.isImaginary() && (bt2.isFloating() || bt2.isIntegral());
						bool f2 = bt2.isImaginary() && (bt1.isFloating() || bt1.isIntegral());
						if(f1) {
							if(bt2.isIntegral()){
								Type tt;
								if(bt1 == Type.get!ifloat()) tt = Type.get!float();
								else if(bt1 == Type.get!idouble) tt = Type.get!double();
								else tt = Type.get!real();
								mixin(ImplConvertTo!q{e2,tt});
							}
							type = S==Tok!"%"?e2.type.getHeadUnqual():bt1;
						}else if(f2) {
							if(bt1.isIntegral()){
								Type tt;
								if(bt2 == Type.get!ifloat()) tt = Type.get!float();
								else if(bt2 == Type.get!idouble) tt = Type.get!double();
								else tt = Type.get!real();
								mixin(ImplConvertTo!q{e1,tt});
								type = S==Tok!"%"?e2.type.getHeadUnqual():bt2;
							}
						}
						if(f1 || f2){
							sc.error("mixed real and imaginary operations not supported yet",loc);
							mixin(ErrEplg);
							// mixin(SemChld!q{e1,e2}~SemEplg);
						}
					}
					{mixin(Combine!q{auto ty; t1, t2});
					if(ty){
						auto conve2to = ty;
						static if(S == Tok!"%")
						if(auto bty = ty.isComplex()){
							if(bt2.isIntegral()){
								if(bty.op == Tok!"cfloat") conve2to=Type.get!float();
								else if(bty.op == Tok!"cdouble") conve2to=Type.get!double();
								else if(bty.op == Tok!"creal") conve2to=Type.get!real();
								else assert(0);
							}else if(bt2.isImaginary()) conve2to=e2.type;
							else{
								sc.error("cannot compute the remainder of complex number division",loc);
								mixin(ErrEplg);
							}
						}
						mixin(ImplConvertToPar!q{e1,ty});
						mixin(ImplConvertTo!q{e2,conve2to});
						mixin(PropErr!q{e1});
						assert(e1.sstate == SemState.completed
						    && e2.sstate == SemState.completed);
						static if(S == Tok!"/" || S==Tok!"%"){
							if(bt1.isIntegral() && bt2.isIntegral())
							if(e2.isConstant() && e2.interpretV() == Variant(0)){
								sc.error("divide by zero", loc);
								mixin(ErrEplg);
							}
						}
						type = ty;
						mixin(SemEplg);
					}}
				}else static if(S==Tok!"+"||S==Tok!"-"){ // pointer arithmetics
					if(bt2&&bt2.isIntegral() && t1.isPointerTy()){
						type = e1.type;
						mixin(SemEplg);
					}else static if(S==Tok!"+"){
						if(bt1&&bt1.isIntegral() && t2.isPointerTy()){
							type = e2.type;
							mixin(SemEplg);
						}
					}
				}
			}else static assert(0);
		}else static if(S==Tok!"~"){
			Type el1 = e1.type.getElementType(), el2 = e2.type.getElementType();
			bool f1 = !!el1, f2 = !!el2;

			bool e1toel2, e2toel1;
			if(f2) mixin(ImplConvertsTo!q{e1toel2; e1, el2});
			if(f1) mixin(ImplConvertsTo!q{e2toel1; e2, el1});
			if(f1 && f2){
				if(e1toel2){
					f1 = false;
					el1 = e1.type;
				}
				if(e2toel1){
					f2 = false;
					el2 = e2.type;
				}
			}

			// TODO: if arr1 is of type int[][], what is the meaning of arr1~[]?
			switch(f1<<1|f2){
				case 0b11: // both are arrays
					mixin(TypeMostGeneral!q{auto mg; e1,e2});
					if(mg){
						type = mg.getElementType();
						if(el1 !is el2) type = type.getHeadUnqual();
					}else{
						mixin(RefCombine!q{auto ty; el1, el2, 0});
						if(ty){
							if(el1 !is el2) type = ty.getHeadUnqual();
							else type = ty;
						}else{ // TODO: there might be a better place/approach for this logic
							auto l1 = e1.isLiteralExp(), l2 = e2.isLiteralExp();
							Type elo;
							if(l1 && l1.isPolyString()) elo = el2;
							else if(l2 && l2.isPolyString()) elo = el1;
							if(elo){
								auto elou = elo.getHeadUnqual();
								import std.typetuple;
								foreach(T; TypeTuple!(char,wchar,dchar)){
									if(elou is Type.get!T()){
										mixin(RefCombine!q{
											type;
											type.get!(immutable(T))(),
											elo,
											0
										});
										break;
									}
								}
							}
						}
						break;
					}
				case 0b10: // array ~ element
					if(e2toel1) type = el1;
					else{
						mixin(ImplConvertsTo!q{auto e2toe1; e2, e1.type});
						if(e2toe1){f2=true; type = el1;}
					}
					break;
				case 0b01: // element ~ array
					if(e1toel2) type = el2;
					else{
						mixin(ImplConvertsTo!q{auto e1toe2; e1, e2.type});
						if(e1toe2){f1=true; type = el2;}
					}
					break;
				default:  // both are elements
					break;
			}

			if(type){
				// TODO: unique data mustn't be const-qualified
				// TODO: except if the unqualified type has mutable indirections
				//auto stc = type.getHeadSTC();
				//if(stc&STCconst){
				//	stc&=~STCconst;
				//	// TODO: immutable~const should be immutable
				//	// TODO: except if the unqualified type has const indirections
				//	// if((el1.isImmutable() || el2.isImmutable())
				//	//   && el1 is el1.getConst() && el2 is el2.getConst())
				//	// 	stc|=STCimmutable;
				//	type = type.getHeadUnqual().applySTC(stc);
				//}
				if(!f1) e1=e1.implicitlyConvertTo(type);
				if(!f2) e2=e2.implicitlyConvertTo(type);

				type = type.getDynArr();

				if(f1) e1=e1.convertTo(type);
				if(f2) e2=e2.convertTo(type);
				mixin(SemChld!q{e1,e2});

				assert(e1.sstate == SemState.completed
				       && e2.sstate == SemState.completed);
				// structural const folding
				auto al1 = e1.isArrayLiteralExp(),
					al2 = e2.isArrayLiteralExp();
				if(f1 && f2){
					if(al1 && al2){
						al1.type = null;
						al1.sstate = SemState.begin;
						al1.lit ~= al2.lit;
						al1.loc = al1.loc.to(al2.loc);
						mixin(SemChld!q{e1});
						mixin(RewEplg!q{e1});
					}
				}else if(f1){
					assert(!f2);
					if(al1){
						al1.type = null;
						al1.sstate = SemState.begin;
						al1.lit ~= e2;
						al1.loc = al1.loc.to(e2.loc);
						mixin(SemChld!q{e1});
						mixin(RewEplg!q{e1});
					}
				}else if(f2){
					if(al2){
						al2.type = null;
						al2.sstate = SemState.begin;
						al2.lit = e1~al2.lit;
						al2.loc = e1.loc.to(al2.loc);
						mixin(SemChld!q{e2});
						mixin(RewEplg!q{e2});
					}
				}
				mixin(SemEplg);
			}
		}else static assert(S==Tok!",");
		static if(S==Tok!","){
			type=e2.type;
			mixin(SemEplg);
		}else{
			// TODO: operator overloading
			if(e1.finishDeduction(sc) && e2.finishDeduction(sc))
				sc.error(format("incompatible types '%s' and '%s' for binary "~TokChars!S,e1.type,e2.type),loc);
			mixin(ErrEplg);
		}
	}

	override bool isConstant(){
		static if(S==Tok!"is" || S==Tok!"!is") return false;
		else return e1.isConstant() && e2.isConstant();
	}
	override bool isConstFoldable(){
		static if(S==Tok!"is" || S==Tok!"!is") return false;
		else return e1.isConstFoldable() && e2.isConstFoldable();
	}

	static if(isAssignOp(S) && S!=Tok!"=")
		override bool isLvalue(){
			return true;
		}

	static if(S==Tok!"~"){ // '~' always reallocates, therefore conversion semantics are less strict
		override bool isDirectlyAllocated(){ return true; }
		override Dependent!bool implicitlyConvertsTo(Type rhs){
			if(auto t=super.implicitlyConvertsTo(rhs).prop) return t;
			// the type qualifiers of the head of the element type are unimportant.
			// example: if arr1, arr2 are of type int[], then arr1~arr2 implicitly converts to immutable(int)[]
			// example: if arr is of type int*[] then arr~arr implicitly converts to const(int)*[]
			Type ell = type.getElementType(), elr = rhs.getElementType();
			if(ell&&elr) return ell.getHeadUnqual().refConvertsTo(elr.getHeadUnqual(), 0);
			// if both operands implicitly convert to the result type, their concatenation does too.
			// example: [1,2,3]~[4,5,6] implicitly converts to short[]
			// example: 2 ~ [3,4,5] implicitly converts to short[]
			if(auto rel = rhs.getElementType()){
				auto el1 = e1.type.getElementType(), el2 = e2.type.getElementType();
				if(el1 && el1.equals(e2.type)){      // array ~ element
					auto b1=e1.implicitlyConvertsTo(rhs), b2=e2.implicitlyConvertsTo(rel);
					return b1.and(b2);
				}else if(el2 && el2.equals(e1.type)){ // element ~ array
					auto b1=e1.implicitlyConvertsTo(rel), b2=e2.implicitlyConvertsTo(rhs);
					return b1.and(b2);
				}
			}
			auto b1=e1.implicitlyConvertsTo(rhs), b2=e2.implicitlyConvertsTo(rhs);
			return b1.and(b2);
		}
	}

	private static string __dgliteralRng(){
		string r;
		foreach(x;["IntRange","LongRange"]){
			r~=mixin(X!q{
				override @(x) get@(x)(){
					static if(isArithmeticOp(S) || isShiftOp(S) || isBitwiseOp(S)){
						return mixin(`e1.get@(x)()`~TokChars!S~`e2.get@(x)()`);
					}else static if(S==Tok!"," || isAssignOp(S)){
						return e2.get@(x)();
					}else static if(S==Tok!"in"||S==Tok!"!in"){
						return super.get@(x)();
					}else static if(isRelationalOp(S)){
						static if(S==Tok!"is") enum S = Tok!"==";
						else static if(S==Tok!"!is") enum S = Tok!"!=";
						auto it = e1.type.getHeadUnqual().isIntegral();
						if(!it) return @(x)(0,1,true);
						// TODO: make more efficient
						LongRange r1, r2;
						if(it.bitSize()<=32){
							auto ir1 = e1.getIntRange();
							auto ir2 = e2.getIntRange();
							if(ir1.signed){
								assert(ir2.signed);
								r1 = LongRange(cast(int)ir1.min,cast(int)ir1.max,true);
								r2 = LongRange(cast(int)ir2.min,cast(int)ir2.max,true);
							}else{
								assert(!ir1.signed);
								r1 = LongRange(ir1.min,ir1.max,true);
								r2 = LongRange(ir2.min,ir2.max,true);
							}
						}else r1 = e1.getLongRange(), r2 = e2.getLongRange();

						if(r1.min==r1.max && r2.min==r2.max)
							return mixin(`r1.min `~TokChars!S~` r2.min`)?@(x)(1,1,true):@(x)(0,0,true);
						static if(S==Tok!"=="||S==Tok!"is"||S==Tok!"!<>"){
							return r1.overlaps(r2)?@(x)(0,1,true):@(x)(0,0,true);
						}else static if(S==Tok!"!="||S==Tok!"!is"||S==Tok!"<>"){
							return r1.overlaps(r2)?@(x)(0,1,true):@(x)(1,1,true);
						}else static if(S==Tok!"<"||S==Tok!"!>="){
							return r1.le(r2)  ? @(x)(1,1,true)
								 : r1.geq(r2) ? @(x)(0,0,true)
								 :              @(x)(0,1,true);
						}else static if(S==Tok!"<="||S==Tok!"!>"){
							return r1.leq(r2) ? @(x)(1,1,true)
								 : r1.gr(r2)  ? @(x)(0,0,true)
								 :              @(x)(0,1,true);
						}else static if(S==Tok!">"||S==Tok!"!<="){
							return r1.gr(r2)  ? @(x)(1,1,true)
								 : r1.leq(r2) ? @(x)(0,0,true)
								 :              @(x)(0,1,true);
						}else static if(S==Tok!">="||S==Tok!"!<"){
							return r1.geq(r2) ? @(x)(1,1,true)
								 : r1.le(r2)  ? @(x)(0,0,true)
								 :              @(x)(0,1,true);
						}else static if(S==Tok!"<>="||S==Tok!"!<>="){
							enum value = S==Tok!"<>=";
							return @(x)(value, value, true);
						}else static assert(0,TokChars!S);
					}else static if(isLogicalOp(S)){
						auto r1 = e1.get@(x)(), r2 = e2.get@(x)();
						bool f1=!r1.min&&!r1.max, f2=!r2.min&&!r2.max;
						bool t1=!r1.contains(@(x)(0,0,r1.signed));
						bool t2=!r2.contains(@(x)(0,0,r2.signed));
						static if(S==Tok!"||"){
							if(t1||t2) return @(x)(1,1,true);
							if(f1&&f2) return @(x)(0,0,true);
						}else static if(S==Tok!"&&"){
							if(t1&&t2) return @(x)(1,1,true);
							if(f1||f2) return @(x)(0,0,true);
						}else static assert(0);
						return @(x)(0,1,true);
					}else static if(S==Tok!"~"){
						return super.get@(x)();
					}else static assert(0);
				}
			});
		}
		return r;
	}
	mixin(__dgliteralRng());
}

template Semantic(T) if(is(T==TernaryExp)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e1});
		e1=e1.convertTo(Type.get!bool());
		mixin(SemChld!q{e1,e2,e3});
		auto vd = Type.get!void();
		if(e2.type.getHeadUnqual() is vd){
			mixin(ConvertTo!q{e3,vd}); // TODO: implicit explicit convertion
			type = vd;
		}else if(e3.type.getHeadUnqual() is vd){
			mixin(ConvertTo!q{e2,vd}); // TODO: implicit explicit conversion
			type = vd;
		}else{
			mixin(TypeCombine!q{type; e2, e3});
			if(!type){
				sc.error(format("incompatible types for ternary operator: '%s' and '%s'",e2.type,e3.type),loc);
				mixin(ErrEplg);
			}
			mixin(ImplConvertTo!q{e2,type});
			mixin(ImplConvertTo!q{e3,type});
		}
		if(!isConstFoldable()){
			mixin(ConstFold!q{e1});
			mixin(ConstFold!q{e2});
			mixin(ConstFold!q{e3});
		}
		mixin(SemEplg);
	}

	override bool isConstant(){
		return e1.isConstant() && e2.isConstant() && e3.isConstant();
	}
	override bool isConstFoldable(){
		return e1.isConstFoldable() && e2.isConstFoldable() && e3.isConstFoldable();
	}

	override bool isLvalue(){
		return e2.isLvalue() && e3.isLvalue();
	}

	override Dependent!bool implicitlyConvertsTo(Type rhs){
		if(auto t=super.implicitlyConvertsTo(rhs).prop) return t;
		auto b1=e2.implicitlyConvertsTo(rhs), b2 = e3.implicitlyConvertsTo(rhs);
		return b1.and(b2);
	}

	private static string __dgliteralRng(){
		string r;
		foreach(x;["IntRange","LongRange"]){
			r~=mixin(X!q{
				override @(x) get@(x)(){
					auto r1 = e1.get@(x)();
					bool t = !r1.contains(@(x)(0,0,true));
					bool f = !r1.min&&!r1.max;
					if(t) return e2.get@(x)();
					if(f) return e3.get@(x)();
					return e2.get@(x)().merge(e3.get@(x)());
				}
			});
		}
		return r;
	}

	mixin(__dgliteralRng());
}

mixin template Semantic(T) if(is(T==IsExp)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(!gscope) gscope = New!GaggingScope(sc);
		auto f = ty.typeSemantic(gscope);
		mixin(PropRetry!q{sc=gscope;ty});
		if(ty.sstate == SemState.error) goto no;

		assert(!!f);
		if(f.hasPseudoTypes()) mixin(ErrEplg);

		Token tok;
		switch(which){
			case WhichIsExp.type:
				goto yes;
			case WhichIsExp.isEqual, WhichIsExp.implicitlyConverts:
				if(tparams.length) goto default;
				if(tySpec){
					auto g = tySpec.typeSemantic(sc);
					mixin(SemProp!q{tySpec});

					assert(!!g);
					if(g.hasPseudoTypes()) mixin(ErrEplg);

					if(which == WhichIsExp.isEqual && f.equals(g)) goto yes;
					if(which == WhichIsExp.implicitlyConverts){
						mixin(ImplConvertsTo!q{bool iconv; f,g});
						if(iconv) goto yes;
					}
					goto no;
				}
			default: super.semantic(sc); return;
		}
	yes:
		tok = token!"true";
		goto ret;
	no:
		tok = token!"false";
		goto ret;
	ret:
		auto r = New!LiteralExp(tok);
		r.semantic(sc);
		r.loc = loc;
		mixin(RewEplg!q{r});
	}
private:
	GaggingScope gscope;
}

mixin template Semantic(T) if(is(T==VoidInitializerExp)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		type = Type.get!void();
		mixin(SemEplg);
	}
}


// abstracts a symbol. almost all circular dependency diagnostics are located here.
// CallExp is aware of the possibility of circular dependencies too, because it plays an
// important role in overloaded symbol resolution
// TemplateInstanceDecl catches circular dependencies in the template constraint.
// This is necessary because Symbol does not participate in the template instantiation
// process. This is a tradeoff.
// note: instances of this class have an identity independent from the referenced declaration

enum AccessCheck{
	uninitialized,
	none,
	memberFuns,
	all,
}
AccessCheck accessCheckCombine(AccessCheck a, AccessCheck b){ return max(a,b); }

class Symbol: Expression{ // semantic node
	Declaration meaning;
	protected this(){} // subclass can construct parent lazily

	bool isStrong;// is symbol dependent on semantic analysis of its meaning
	bool isFunctionLiteral; // does symbol own 'meaning'
	bool isSymbolMatcher;
	bool implicitCall = true;
	bool addressTaken = false;
	override void willTakeAddress(){
		addressTaken = true;
		implicitCall = false;
	}
	bool called;
	override void willCall(){
		called = true;
		implicitCall = false;
	}
	bool ignoreproperty = false;

	auto inoutRes = InoutRes.none; // TODO: is there a better way to do this?

	auto accessCheck = AccessCheck.all;
	this(Declaration m, bool strong=false, bool isfunlit=false)in{
		assert(!!m);
	}body{
		meaning = m;
		isStrong = strong;
		isFunctionLiteral = isfunlit;
	}
	void makeStrong(){
		if(!isStrong) sstate = SemState.begin;
		isStrong = true;
	}

	private enum CircErrMsg=q{if(circ){circErrMsg(); mixin(SemCheck);}};
	private void circErrMsg()in{assert(!!circ);}body{
		if(circ is this){
			Scope errsc = scope_;
			if(!errsc.handler.showsEffect()){
				foreach(x; clist) if(x.scope_.handler.showsEffect()){
					// NOTE: the test suite does not cover this case
					errsc = x.scope_;
					break;
				}else if(x.meaning.scope_&&x.meaning.scope_.handler.showsEffect()){
					errsc = x.meaning.scope_;
					break;
				}
			}
			errsc.error("circular dependencies are illegal",loc);
			circ = null;
			mixin(SetErr!q{});
			assert(0);
			foreach_reverse(x; clist[1..$]){
				// IFTI might spawn locationless identifiers
				if(x.loc.line) errsc.note("part of dependency cycle",x.loc);
				mixin(SetErr!q{x});
			}
			meaning.needRetry = meaning.sstate != SemState.error
				&& meaning.sstate != SemState.completed;
			clist=[];
		}else{
			needRetry = 2;
			clist~=this;
		}
	}

	static Symbol circ = null;
	private static Symbol[] clist = [];

	override Expression clone(Scope sc, const ref Location loc){
		Symbol r=ddup();
		r.sstate = SemState.begin;
		r.scope_ = null;
		r.loc = loc;
		r.semantic(sc);
		return r;
	}


	override void semantic(Scope sc){
		// dw("semantic: ",this," ",meaning.sstate," ", loc);
		debug scope(exit) assert((sstate != SemState.started||needRetry||rewrite) &&(sstate!=SemState.begin||needRetry||rewrite),toString()~" "~typeid(this.meaning).toString());
		debug scope(exit) assert(needRetry==2||!circ,toString()~" nR: "~to!string(needRetry)~" circ: "~to!string(circ));
		mixin(SemPrlg);
		if(!scope_) scope_=sc;
		assert(meaning && scope_);
		if(needRetry) sstate = SemState.begin;
		needRetry = false; // be reentrant

		if(sstate >= SemState.started){
			// template instances may depend circularly upon each other
			if(meaning.isTemplateInstanceDecl()&&meaning.sstate == SemState.started){
				sstate = SemState.begin;
				needRetry = true;
				return;
			}
			assert(!circ,toString());
			circ = this;
			sstate = SemState.error;
			needRetry = 2;
			clist~=this;
			return;
		}else sstate = SemState.started;

		enum MeaningSemantic = q{
			if(meaning.sstate != SemState.completed) meaning.semantic(meaning.scope_);
			mixin(Rewrite!q{meaning});
		};
		// resolve alias
		if(auto al=meaning.isAliasDecl()){
			mixin(MeaningSemantic);
			mixin(CircErrMsg);
			mixin(SemCheck);
			mixin(SemProp!q{sc=meaning.scope_;meaning});
			if(auto decl = al.aliasedDecl()) meaning = decl;
			else{
				// assert(!!al.aliasee.isType());
				sstate = SemState.begin;
				auto r=al.getAliasee(scope_, accessCheck, loc);
				mixin(RewEplg!q{r});
			}
		}

		alias util.any any;
		bool needParamDeduction = false;
		if(auto fd=meaning.isFunctionDecl()){
			needParamDeduction=any!(_=>_.mustBeTypeDeduced())(fd.type.params);
		}

		if(isSymbolMatcher){
			//assert(!!cast(SymbolMatcher)meaning,to!string(meaning));
			if(meaning.isSymbolMatcher()){
			meaning.semantic(scope_);
			mixin(CircErrMsg);
			if(meaning.rewrite)
				inoutRes = (cast(SymbolMatcher)cast(void*)meaning)
					.context.inoutRes;
				mixin(SemProp!q{sc=scope_;meaning});
			}
			isSymbolMatcher=false;
		}else if(isStrong){
			if(!needParamDeduction){
				// TODO: comprehensive treatment of error gagging
				if(isFunctionLiteral) meaning.semantic(scope_);
				else mixin(MeaningSemantic);
				mixin(CircErrMsg);
				mixin(SemProp!q{sc=scope_;meaning});
			}
		}

		// those are not virtual functions because of centralized symbol dependency handling
		// TODO: make specific parts virtual functions of the relevant classes instead

		if(auto vd=meaning.isVarDecl()){
			if(!vd.type || vd.stc & STCenum || (vd.init&&vd.stc&(STCimmutable|STCconst)&&vd.willInterpretInit())){
				mixin(MeaningSemantic);
				mixin(CircErrMsg);
				mixin(SemProp!q{sc=meaning.scope_;meaning});
			}
			assert(!!vd.type);

			mixin(VarDecl.SymbolResolve);
			// this symbol was obtained by simple identifier lookup
			// if it is directly inside of an aggregate, then the
			// current function's this pointer type must apply
			if(auto i=isIdentifier())
				if(i.recursiveLookup)
					if(auto decl=vd.scope_.getDeclaration())
						if(decl.isAggregateDecl())
							type = type.applyScopeSTC(sc);
			if(vd.stc&STCenum){
				if(vd.init){
					assert(vd.init.isConstFoldable());
					auto r=vd.init.cloneConstant();
					r.loc = loc;
					mixin(RewEplg!q{r});
				}else assert(meaning.sstate == SemState.error);
			}
		}else if(auto fd=meaning.isFunctionDecl()){
			if(!needParamDeduction){
				//if(fd.type.hasAutoReturn()){ // DMD 2.059 does this...
				if(fd.type.hasUnresolvedReturn()){
					needRetry = false;
					mixin(MeaningSemantic);
					mixin(CircErrMsg);
					mixin(SemProp!q{sc=meaning.scope_;meaning});
				}else fd.propagateSTC();
			}
			fd.type.semantic(meaning.scope_);
			assert(!fd.rewrite);
			if(needParamDeduction) type = Type.get!void();
			else type = fd.type;
		}else if(auto tm=meaning.isTemplateDecl()){
			if(called){
				auto s = New!Symbol(meaning);
				auto r = New!TemplateInstanceExp(s, (Expression[]).init);
				s.loc = r.loc = this.loc;
				s.accessCheck = accessCheck;
				r.willCall();
				r.semantic(sc);
				mixin(RewEplg!q{r});
			}
			type = Type.get!void();
		}else if(auto tm=meaning.isTemplateInstanceDecl()){
			// circular template instantiations are allowed
			// those just don't carry forward the information
			// whether the template compiled or not.
			// TODO:
			// dw(this," ",meaning.sstate);
			if(meaning.sstate != SemState.started){
				mixin(MeaningSemantic);
				mixin(CircErrMsg);
				if(meaning.sstate == SemState.error)
					sc.note("instantiated here",loc);
				mixin(SemProp!q{sc=meaning.scope_;meaning});
			}
			type=Type.get!void();
		}else if(auto ov=meaning.isOverloadSet()){
			foreach(ref x; ov.decls) if(auto fd = x.isFunctionDecl()){
				if(fd.type.hasUnresolvedReturn()){
					fd.semantic(fd.scope_);
					mixin(Rewrite!q{x});
					mixin(CircErrMsg);
					mixin(SemProp!q{sc=fd.scope_;x}); // TODO: depend just on type
				}else fd.propagateSTC();

				fd.analyzeType();
				mixin(Rewrite!q{fd.type});
				mixin(CircErrMsg);
				if(auto nr=fd.type.needRetry) {
					Scheduler().await(this, fd.type, fd.scope_);
					needRetry = nr; return;
				}
				mixin(PropErr!q{fd.type});
				assert(!fd.rewrite);
			}
			if(ov.count==1 && ov.decls.length){
				if(auto fd=ov.decls[0].isFunctionDecl()){
					meaning = fd;
					type = fd.type;
				}
			}else foreach(ref x;ov.tdecls){
				x.semantic(x.scope_);
				mixin(CircErrMsg);
				mixin(SemProp!q{sc=x.scope_;x});
			}

			if(!type) type=Type.get!void(); // TODO: fix
		}
		else if(typeid(this.meaning) is typeid(ErrorDecl)){mixin(ErrEplg);}
		else type=Type.get!void(); // same as DMD

		mixin(CircErrMsg);
		mixin(SemProp!q{type});
		assert(needParamDeduction||!meaning.isFunctionDecl()||(cast(FunctionTy)type).ret);

		if(auto at=meaning.isAggregateDecl()){
			auto r = at.getType();
			sstate = SemState.begin;
			mixin(RewEplg!q{r});
		}

		needRetry = false;
		performAccessCheck();
		mixin(SemCheck);

		if(inoutRes!=InoutRes.none){sstate=SemState.completed;resolveInout(inoutRes);}

		// TODO: integrate with templates, IFTI, UFCS and alias
		// uniform access principle
/+		Declaration implcalldecl = meaning.isFunctionDecl();
		if(!implcalldecl)if(auto ov=meaning.isOverloadSet())
			                 //if(ov.hasFunctions) // ?
				implcalldecl=meaning;
		if(implcalldecl){
			if(implicitCall || !ignoreproperty && meaning.stc&STCproperty){
				auto s = New!Symbol(meaning);
				s.loc = loc;
				s.ignoreproperty=true;
				auto r = New!CallExp(s,(Expression[]).init);
				r.loc=loc;
				r.semantic(sc);
				mixin(RewEplg!q{r});
			}
		}+/
		mixin(SemEplg);
	}

	void performAccessCheck() in{assert(meaning && scope_);}body{
		auto decl = scope_.getDeclaration();
		// it is necessary to perform the check in order to get
		// the correct type deduction, even if we are not interested
		// in the actual accessibility
		mixin(IsDeclAccessible!q{auto b; Declaration, decl, meaning});
		if(meaning.needsAccessCheck(accessCheck) && !b){
			// TODO: better error message?
			if(meaning.scope_.getDeclaration().isFunctionDef())
				scope_.error(format("cannot access the frame in which '%s' is stored", loc.rep),loc);
			else{
				// error message duplicated in FieldExp.semantic
				scope_.error(format("need 'this' to access %s '%s'",kind,loc.rep),loc);
			}
			scope_.note(format("%s was declared here",kind),meaning.loc);
			mixin(ErrEplg);
		}
	}

	override string toString(){
		auto tmpl=meaning.isTemplateInstanceDecl();
		if(!tmpl){
			if(auto nsts=cast(NestedScope)meaning.scope_)
			if(auto tmps=cast(TemplateScope)nsts.parent)
				tmpl=tmps.tmpl;
		}
		if(!meaning.name) return "(symbol)";
		if(tmpl && meaning.name.name==tmpl.name.name)
			return meaning.name.name~"!("~join(map!(to!string)(tmpl.args),",")~")";
		return meaning.name.toString();
	}
	override @property string kind(){return meaning.kind;}

	// TODO: maybe refactor
	override Scope getMemberScope(){
		if(auto tmpl=meaning.isTemplateInstanceDecl()) return tmpl.bdy.scope_;
		return super.getMemberScope();
	}

	Type thisType(){
		if(!(meaning.stc&STCstatic))
		if(auto decl=meaning.scope_.getDeclaration())
		if(auto aggr=decl.isAggregateDecl())
			return aggr.getType();
		return null;
	}

	////

	override Expression extractThis(){
		if(meaning.isTemplateInstanceDecl()) return null;
		return this;
	}

	final Type maybeThisContext(){
		// (similar code in semantic, TODO: can some of it be factored out?)
		if(auto i=isIdentifier())
			if(i.recursiveLookup)
				if(auto decl=meaning.scope_.getDeclaration())
					if(auto aggr=decl.isAggregateDecl())
						return aggr.getType().applyScopeSTC(scope_);
		return null;
	}

	override AccessCheck deferredAccessCheck(){
		if(!meaning.needsAccessCheck(accessCheck)) return AccessCheck.none;
		return super.deferredAccessCheck();
	}

	override bool isConstant(){
		assert(!!meaning,toString());
		//if(meaning.stc|STCstatic) return true;
		if(auto vd = meaning.isVarDecl())
			return vd.stc&STCenum
				|| vd.stc&(STCimmutable|STCconst)
				&& vd.init && vd.init.isConstant();

		return false;
	}

	override bool isConstFoldable(){
		if(auto vd = meaning.isVarDecl()) return !!(vd.stc&STCenum);
		return false;
	}

	// DMD 2.058/2.059 behave approximately like this:
	/+override bool typeEquals(Type rhs){
		if(meaning.stc&STCenum)
		if(auto vd = meaning.isVarDecl()) return vd.init.typeEquals(rhs);
		return super.typeEquals(rhs);
	}+/
	// override Type isType(){...} // TODO.
	override bool isLvalue(){
		if(!(meaning.stc&STCrvalue) && meaning.isVarDecl()) return true;
		   if(auto ov=meaning.isOverloadSet())
			   return !!ov.decls.length;
		   return !!meaning.isFunctionDecl();
	}

	override bool checkMutate(Scope sc, ref Location l){
		if(meaning.stc&STCproperty) return true;
		return super.checkMutate(sc, l);
	}


	override Dependent!Expression matchCallHelper(Scope sc, const ref Location loc, Type this_, Expression[] args, ref MatchContext context){
		if(!scope_) scope_=sc;
		assert(meaning && scope_);
		if(!this_) this_ = maybeThisContext();
		mixin(MatchCall!q{auto m; meaning, sc, loc, this_, args, context});
		if(m){
			// resolve the overload in place and then rely on
			// semantic to catch eventual circular dependencies:
			meaning = m;
			isSymbolMatcher=!!meaning.isSymbolMatcher();
			sstate = SemState.begin;
			type = null;
			Symbol.semantic(scope_);
			return this.independent!Expression;
		}
		return super.matchCallHelper(sc, loc, this_, args, context);
	}
	override void matchError(Scope sc, Location loc, Type this_, Expression[] args){
		if(!this_) this_ = maybeThisContext();
		if(meaning.isVarDecl()) return super.matchError(sc, loc, this_, args);
		meaning.matchError(sc,loc,this_,args);
	}


	import vrange;
	override IntRange getIntRange(){
		if(auto vd=meaning.isVarDecl()){
			if(vd.stc&STCenum || vd.stc&STCstatic&&vd.stc&STCimmutable)
				return vd.init.getIntRange();
		}
		return super.getIntRange();
	}
	override LongRange getLongRange(){
		if(auto vd=meaning.isVarDecl()){
			if(vd.stc&STCenum || vd.stc&STCstatic&&vd.stc&STCimmutable)
				return vd.init.getLongRange();
		}
		return super.getLongRange();
	}



	mixin DownCastMethod;
	//mixin Interpret!Symbol;
	mixin Visitors;

	Scope scope_;

	// TemplateDecl needs this.
	override bool templateParameterEquals(Expression rhs){
		if(auto sym = rhs.isSymbol()){
			auto decl = scope_.getDeclaration();
			auto sdecl = sym.scope_.getDeclaration();
			return meaning is sym.meaning &&
				Declaration.isDeclAccessible(decl, meaning).force ==
				Declaration.isDeclAccessible(sdecl, meaning).force;
				                  
		}
		// presumably this will never happen, as only parameters matching the
		// same template are tested
		return false;
	}

	override size_t templateParameterToHash(){
		import hashtable;
		return FNV(meaning.toHash());
	}
}

import visitors;

enum Match{
	none,
	convert,
	convConst,
	exact,
}
enum InoutRes{
	none,
	mutable,
	immutable_,
	const_,
	inout_,
	inoutConst, // inout(const(T))
}
// enum member functions would be nice
InoutRes mergeIR(InoutRes ir1, InoutRes ir2){
	if(ir1 == ir2) return ir1;
	if(ir1 == InoutRes.none) return ir2;
	if(ir2 == InoutRes.none) return ir1;
	return InoutRes.const_;
}
InoutRes irFromSTC(STC stc){
	if(stc&STCimmutable) return InoutRes.immutable_;
	else if(stc&STCconst){
		if(stc&STCinout) return InoutRes.inoutConst;
		else return InoutRes.const_;
	}else if(stc&STCinout) return InoutRes.inout_;
	else return InoutRes.mutable;
	
}
struct MatchContext{
	auto inoutRes = InoutRes.none;
	auto match = Match.exact;
}

// aware of circular dependencies
mixin template Semantic(T) if(is(T==CallExp)){

	override void noHope(Scope sc){
		mixin(RevEpoNoHope!q{e});
	}

	override void semantic(Scope sc){ // TODO: type checking
		// parameter passing
		mixin(SemPrlg);
		mixin(RevEpoLkup!q{e});
		e.willCall();
		mixin(SemChldPar!q{e});
		mixin(SemChldExp!q{args});
		mixin(PropErr!q{e});
		//dw(sstate," ",map!(a=>a.needRetry)(args),args);
		if(auto ty=e.isType())
		if(auto aggrty=ty.getUnqual().isAggregateTy())
		if(auto strd=aggrty.decl.isStructDecl()){
			// TODO: could re-use the callexp as the consCall field
			auto r = New!StructConsExp(ty, args);
			r.loc = loc;
			if(tmpVarDecl) r.initOfVar(tmpVarDecl);
			r.semantic(sc);
			mixin(RewEplg!q{r});
		}
		if(fun is null){
			mixin(MatchCall!q{fun; e, sc, loc, args});
			if(fun is null) mixin(ErrEplg);
		}

		mixin(SemChld!q{fun});
		mixin(SemProp!q{e}); // catch errors generated in matchCall TODO: still relevant?
		assert(fun && fun.type);
		auto tt = fun.type.getHeadUnqual().getFunctionTy();
		assert(!!tt);

		if(adapted is null)
		foreach(i,x; tt.params[0..args.length]){
			if(x.stc & STClazy){
				if(adapted is null) adapted = new Expression[args.length];
				else if(adapted[i]) continue;
				auto ft = New!FunctionTy(STC.init, args[i].type,cast(Parameter[])[],VarArgs.none);
				auto bs = New!BlockStm(cast(Statement[])[New!ReturnStm(args[i])]); // TODO: gc allocates []
				auto dg = New!FunctionLiteralExp(ft,bs,FunctionLiteralExp.Kind.delegate_);
				bs.loc = dg.loc = args[i].loc;
				adapted[i] = dg;
				// TODO: this is somewhat fragile
				static struct Reset{
					void perform(Symbol self){
						self.scope_=null;
						self.sstate=SemState.begin;
					}
					void perform(Node self){self.sstate = SemState.begin;}
				}
				runAnalysis!Reset(args[i]);
			}
		}

		mixin(SemChld!q{adapted});

		type = tt.ret;

		if(tt.params.length > args.length){
			// //  TODO: this allocates rather heavily
			// args ~= array(map!(_=>_.init.dup)(tt.params[args.length..$]);
			sc.error("default parameters not implemented yet",loc);
			mixin(ErrEplg);
		}
		foreach(i,x; tt.params[0..args.length]){
			auto pty = x.type;
			args[i]=args[i].implicitlyConvertTo(pty);
		}

		mixin(SemChld!q{args});
		mixin(ConstFold!q{e});
		foreach(ref x; args) mixin(ConstFold!q{x});

		// call expressions may create temporary variables
		if(!(tt.stc&STCbyref))
		if(auto aggrty=type.getHeadUnqual().isAggregateTy())
		if(aggrty.decl.isValueAggregateDecl()){
			needRetry = false;
			analyzeTemporary(sc, STC.init);
			mixin(SemCheck);
		}
		if(type.getHeadUnqual().isTypeTuple()){
			needRetry = false;
			analyzeTemporary(sc, tt.stc&STCbyref);
			mixin(SemCheck);
			if(tmpVarDecl.sstate == SemState.completed){
				auto r = makeMultiReturn(this);
				r.loc = loc;
				mixin(RewEplg!q{r});
			}// else VarDecl will do the honors
		}

		mixin(SemEplg);
	}

	override bool isLvalue(){ return !!(e.type.getHeadUnqual().getFunctionTy().stc & STCref); }

	Expression fun;
	Expression[] adapted;
}


// everything concerning error gagging is centralized here
import error;
class GaggingErrorHandler: ErrorHandler{

	static opCall(){static GaggingErrorHandler instance; return instance?instance:(instance=New!GaggingErrorHandler());}

	override void error(lazy string, Location){ nerrors++; }
	override void note(lazy string, Location){ /* do nothing */ }
	override void message(string msg){ /* do nothing */ }

	/* for errors that span gagging boundaries, this is important information
	 */
	override bool showsEffect(){ return false; }
}

class GaggingScope: NestedScope{

	this(Scope parent){super(parent);}

	override @property ErrorHandler handler(){return GaggingErrorHandler();}

	override bool insert(Declaration decl){
		// cannot insert into gagging scope
		// probably this will never happen
		return false;
	}

	override void error(lazy string, Location){ /* do nothing */ }
	override void note(lazy string, Location){ /* do nothing */ }

	// forward other members:
	override Dependent!Declaration lookup(Identifier ident, lazy Declaration alt){
		return parent.lookup(ident,alt);
	}
	override Dependent!Declaration lookupHere(Identifier ident, lazy Declaration alt){
		return parent.lookupHere(ident, alt);
	}

	override Dependent!Scope getUnresolved(Identifier ident){
		return parent.getUnresolved(ident);
	}

	override bool inexistent(Identifier ident){
		return parent.inexistent(ident);
	}

	override FunctionDef getFunction(){return parent.getFunction();}
}

class GaggingRecordingErrorHandler: GaggingErrorHandler{
		override void error(lazy string err, Location loc){
		nerrors++;
		records~=ErrorRecord(err,loc,RecordKind.error);
	}
	override void note(lazy string err, Location loc){
		records~=ErrorRecord(err,loc,RecordKind.note);
	}
	override void message(string err){
		records~=ErrorRecord(err,Location.init,RecordKind.message);
	}

	void replay(ErrorHandler h){
		foreach(r;records)
			(r.kind==RecordKind.message?h.message(r.err):
			 (r.kind==RecordKind.note?&h.note:&h.error)(r.err,r.loc));
	}

private:
	enum RecordKind{
		error,
		note,
		message
	}
	static struct ErrorRecord{
		string err;
		Location loc;
		RecordKind kind;
	}
	ErrorRecord[] records;
}

class GaggingRecordingScope: GaggingScope{
	private GaggingRecordingErrorHandler _handler;
	this(Scope parent){ _handler = New!GaggingRecordingErrorHandler(); super(parent); }
	override @property ErrorHandler handler(){ return _handler; }

	void replay(Scope sc){
		_handler.replay(sc.handler);
	}
}

mixin template Semantic(T) if(is(T==CastExp)){
	protected Dependent!bool checkConv(Scope sc){
		mixin(ConvertsTo!q{bool conv; e, type});
		if(conv) return true.independent;
		sc.error(format("cannot cast expression '%s' of type '%s' to '%s'",e.loc.rep,e.type,type),e.loc);
		//error(format("no viable conversion from type '%s' to '%s'",e.type,type),e.loc);
		return false.independent;
	}

	protected void displayFunctionLiteralConversionError(Scope sc){
		sc.error(format("cannot cast function literal to '%s'",type.toString()),loc);
	}


	//mixin(DownCastMethods!ImplicitCastExp);
	ImplicitCastExp isImplicitCastExp(){return null;}

	override void semantic(Scope sc){
		// TODO: sanity checks etc.
		mixin(SemPrlg);
		mixin(SemChldExp!q{e});

		// TODO: check if rewrite to implicit conversion required

		if(!ty) {
			// TODO: works differently for classes..?
			type = e.type.getHeadUnqual().applySTC(stc);
		}else{
			type=ty.typeSemantic(sc);
			mixin(SemProp!q{ty});
			type=type.applySTC(stc);
		}

		// implicitly typed delegate literals convert to both function and
		// delegate. furthermore, (implicit) casts can be used to determine
		// the argument types
		// this is done before the conversion sanity check in order to get
		// better error messages
		// TODO: this is heavy fp style. is there a better design?
		if(auto uexp = e.isAddressExp()            ){ // TODO: reduce the DMD bug
		if(auto sym = uexp.e.isSymbol()            ){
		if(auto fd  = sym.meaning.isFunctionDef()  ){
			if(sym.type is Type.get!void()){
				if(auto fty=type.getHeadUnqual().getFunctionTy()){
					// the scope in which the type is resolved might
					// be different from the initial scope:
					fd.scope_=sc; // eg. matching overloads
					fd.type.resolve(fty);
					uexp.sstate = sym.sstate = SemState.begin;
					mixin(SemChld!q{e});
				}else{
					displayFunctionLiteralConversionError(sc);
					mixin(SetErr!q{fd});
					mixin(ErrEplg);
				}
			}
			if(auto dg = type.getHeadUnqual().isDelegateTy()){
				if(fd.stc&STCstatic && fd.deduceStatic){
					assert(sym.isStrong && uexp.type.getFunctionTy());
					mixin(ImplConvertsTo!q{
						bool delegaterequested;
						uexp.type.getFunctionTy().getDelegate()
					  , dg
					});
					if(delegaterequested){
						fd.addContextPointer();
						uexp.sstate = sym.sstate = SemState.begin;
					}
				}
			}
		}}}
		mixin(SemChld!q{e});

		mixin CreateBinderForDependent!("CheckConv","checkConv");
		mixin(CheckConv!q{bool conversionLegal; this, sc});
		if(!conversionLegal) mixin(ErrEplg);


		auto el = type.getElementType();
		if(el && el.getHeadUnqual() !is Type.get!void()){
			if(auto al = e.isArrayLiteralExp()){
				al.sstate = SemState.begin;
				foreach(ref x; al.lit) x=x.convertTo(el);
				mixin(SemChld!q{e});
				if(e.type is type) mixin(RewEplg!q{e});
			}
		}
		if(auto te = e.isTernaryExp()){
			e.sstate = SemState.begin;
			te.e2=te.e2.convertTo(type);
			te.e3=te.e3.convertTo(type);
			mixin(SemChld!q{e});
			if(e.type is type) mixin(RewEplg!q{e});
		}
		mixin(SemEplg);
	}

	override bool isConstant(){
		if(sstate == SemState.error) return false;
		assert(sstate == SemState.completed);
		if(type.getHeadUnqual().isPointerTy()
		   || e.type.getHeadUnqual().isPointerTy()) return false; // TODO!
		auto iconvd=e.type.implicitlyConvertsTo(type);
		assert(!iconvd.dependee); // this fact has already been determined at this point.
		if(iconvd.value) return e.isConstant();
		if(type.getHeadUnqual().isPointerTy()) return false;
		if(type.getHeadUnqual() is Type.get!void()) return false;
		return e.isConstant();
	}
	override bool isConstFoldable(){
		if(sstate == SemState.error) return false;
		assert(sstate == SemState.completed);
		if(type.getHeadUnqual().isPointerTy()
		   || e.type.getHeadUnqual().isPointerTy()) return false; // TODO!
		auto iconvd=e.type.implicitlyConvertsTo(type);
		assert(!iconvd.dependee); // this fact has already been determined at this point.
		if(iconvd.value) return e.isConstFoldable();
		if(type.getHeadUnqual() is Type.get!void()) return false;
		return e.isConstFoldable();
	}

	override Dependent!bool implicitlyConvertsTo(Type rhs){
		if(auto t=super.implicitlyConvertsTo(rhs).prop)
			return t;//TODO: does this work out correctly?
		return e.implicitlyConvertsTo(rhs);
	}

	override Expression implicitlyConvertTo(Type rhs){
		if(!super.implicitlyConvertsTo(rhs).force){ // TODO: FIX!!!
			e=e.implicitlyConvertTo(rhs);
			return e;
		}else return super.implicitlyConvertTo(rhs);
	}


	private IntRange getBoolRange(BasicType ty){
		int osiz = ty.bitSize();
		bool t,f;
		if(osiz==32){
			auto r = e.getIntRange();
			f = r.min==0 && r.max==0;
			t = !r.contains(IntRange(0,0,r.signed));
		}else{
			auto r = e.getLongRange();
			f = r.min==0 && r.max==0;
			t = !r.contains(LongRange(0,0,r.signed));
		}
		return t ? IntRange(1,1,true)
		     : f ? IntRange(0,0,true)
		     :     IntRange(0,1,true);
	}

	override IntRange getIntRange(){
		auto ty = e.type.getHeadUnqual().isIntegral();
		auto nt = type.getHeadUnqual().isIntegral();
		if(!ty||!nt) return type.getIntRange();
		if(nt is Type.get!bool()) return getBoolRange(ty);
		int size=nt.bitSize();
		int osiz=ty.bitSize();
		bool signed=nt.isSigned();
		if(size<osiz){ // narrowing conversion
			if(osiz==64){
				auto r = e.getLongRange();
				return r.narrow(signed, size);
			}else{
				auto r = e.getIntRange();
				return r.narrow(signed, size);
			}
		}else{ // non-narrowing conversion
			assert(osiz<64);
			auto r=e.getIntRange();
			if(signed) r=r.toSigned();
			else r=r.toUnsigned();
			return r;
		}
	}
	override LongRange getLongRange(){
		auto ty = e.type.getHeadUnqual().isIntegral();
		auto nt = type.getHeadUnqual().isIntegral();
		if(!ty||!nt) return type.getLongRange();
		int size=nt.bitSize();
		int osiz=ty.bitSize();
		bool signed=nt.isSigned();
		LongRange r;
		if(osiz==64) r=e.getLongRange();
		else{
			assert(osiz<=32);
			auto or=e.getIntRange();
			ulong min, max;
			if(or.signed) min=cast(int)or.min, max=cast(int)or.max;
			else min = or.min, max = or.max;
			r=LongRange(min, max, true);
		}
		if(signed) r=r.toSigned();
		else r=r.toUnsigned();
		return r;
	}
}

class ImplicitCastExp: CastExp{ // semantic node
	this(Expression tt, Expression exp){super(STC.init, tt, exp);}

	protected override Dependent!bool checkConv(Scope sc){
		mixin(ImplConvertsTo!q{bool iconv; e, type});
		if(iconv) return true.independent;
		sc.error(format("cannot implicitly convert %s '%s' of type '%s' to '%s'",e.kind,e.loc.rep,e.type,type),e.loc); // TODO: replace toString with actual representation
		return false.independent;
	}

	protected override void displayFunctionLiteralConversionError(Scope sc){
		sc.error(format("cannot implicitly convert function literal to '%s'",type.toString()),loc);
	}


	mixin DownCastMethod;
/+
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e});
		auto tt=ty.semantic(sc);
		mixin(PropRetry!q{tt});
		type = tt.isType();
		assert(!!type); // if not a type the program is in error
		mixin(PropErr!q{type});
		if(e.implicitlyConvertsTo(type)){mixin(SemEplg);}
		sc.error(format("cannot implicitly convert expression '%s' of type '%s' to '%s'",e.loc.rep,e.type,type),e.loc); // TODO: replace toString with actual representation
		//error(format("no viable conversion from type '%s' to '%s'",e.type,type),e.loc);
		mixin(ErrEplg);
	}
+/

	override string toString(){return e.toString();}
}

class TmpVarDecl: VarDecl{
	override void presemantic(Scope sc){
		if(sstate != SemState.pre) return;
		scope_ = sc;
		sstate = SemState.begin;
	}
	this(STC stc, Expression rtype, Identifier name, Expression initializer){
		super(stc, rtype, name, initializer);
	}
	
	override TmpVarDecl newVarDecl(STC stc, Expression rtype, Identifier name, Expression init){
		return New!TmpVarDecl(stc,rtype,name,init);
	}

	mixin Visitors;
}
mixin template Semantic(T) if(is(T==TmpVarDecl)){ }


/+class TmpVarExp: Expression{
	VarDecl tempVarDecl;
	this(VarDecl tempVarDecl){ this.tempVarDecl = tempVarDecl; }
	void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{tempVarDecl});
		type = tempVarDecl.type;
		mixin(SemEplg);
	}
	override @property string kind(){ return tempVarDecl.init.kind; }
	override string toString(){ return tempVarDecl.init.toString(); }
}+/

class TemporaryExp: Expression{
	VarDecl tmpVarDecl;
	protected bool builtTmpVarDecl = false;

	override void initOfVar(VarDecl decl){
		assert(!tmpVarDecl||tmpVarDecl is decl);
		tmpVarDecl = decl;
	}

	final protected void analyzeTemporary(Scope sc, STC stc){
		if(!tmpVarDecl){
			tmpVarDecl = New!TmpVarDecl(stc,type,null,this);
			tmpVarDecl.loc = loc;
			tmpVarDecl.presemantic(sc);
			builtTmpVarDecl = true;
		}
		if(builtTmpVarDecl){
			sstate = SemState.completed;
			scope(success) sstate = tmpVarDecl.sstate;
			mixin(SemChld!q{tmpVarDecl});
		}
	}

	mixin DownCastMethod;
	mixin Visitors;
}
mixin template Semantic(T) if(is(T==TemporaryExp)){}

class StructConsExp: TemporaryExp{
	Expression[] args;

	Identifier constructor;
	CallExp consCall;

	bool contextIsNull = false;

	invariant(){ assert(cast(AggregateTy)(cast()type).getUnqual()&&cast(StructDecl)(cast(AggregateTy)(cast()type).getUnqual()).decl);}
	private @property StructDecl strd(){
		return cast(StructDecl)cast(void*)(cast(AggregateTy)cast(void*)type.getUnqual()).decl;
	}

	this(Type type, Expression[] args)in{
		auto strty = cast(AggregateTy)type.getUnqual();
		assert(strty&&cast(StructDecl)strty.decl);
	}body{ this.type=type; this.args=args; }

	override void semantic(Scope sc){
		assert(!!type);
		mixin(SemPrlg);
		mixin(SemChld!q{args});
		// TODO: static opCall
		mixin(ResolveConstructor);
		sstate = SemState.completed;
		needRetry = false;
		analyzeTemporary(sc, STC.init);
		mixin(SemCheck);
		mixin(SemEplg);
	}
	
	override @property string kind(){ return "struct literal"; }
	override string toString(){ return strd.name.toString()~"("~join(map!(to!string)(args),",")~")"; }

	mixin DownCastMethod;
	mixin Visitors;
}
mixin template Semantic(T) if(is(T==StructConsExp)){}

enum ResolveConstructor = q{
	static if(is(typeof(this)==NewExp)){
		alias a2 args;
		auto caggr = aggr.decl;
	}else auto caggr = strd;
	// TODO: struct default constructors

	mixin(IsDeclAccessible!q{bool b; Declaration, sc.getDeclaration, caggr});
	
	if(!b){
		// TODO: these errors must be delayed for struct fields
		auto parent=caggr.scope_.getDeclaration();
		assert(parent.isFunctionDecl()||
		       parent.isReferenceAggregateDecl()&&caggr.isClassDecl());
		static if(is(typeof(this)==NewExp)){
			if(parent.isFunctionDecl()){
				sc.error(format("cannot construct local %s '%s' outside of its frame", caggr.kind, caggr.name), loc);
			}else{
				sc.error(format("need 'this' pointer of type '%s' to construct nested class '%s'",parent.name, caggr.name), loc);
			}
			mixin(ErrEplg);
		}else{
			static assert(is(typeof(this)==StructConsExp));
			// TODO: new expression should do this as well
			contextIsNull = true;
		}
	}
	if(!caggr.isStructDecl()||args.length){ // implicit default constructor
		if(!constructor){
			constructor = New!Identifier("this");
			constructor.recursiveLookup = false;
		}
		if(!constructor.meaning){
			mixin(Lookup!q{_; constructor, caggr.asc});
			if(auto nr=constructor.needRetry) { needRetry = nr; return; }
		}
	}
	if(!constructor||constructor.sstate == SemState.failed){
		// no constructor for type
		// TODO: disabled default constructor
		if(args.length){
			sc.error("too many arguments to new expression (expected zero)",loc);
			mixin(ErrEplg);
		}
	}else{
		assert(constructor.meaning.isOverloadSet()&&
		       constructor.meaning.isOverloadSet().isConstructor() ||
		       constructor.meaning.isFunctionDecl()&&
		       constructor.meaning.isFunctionDecl().isConstructor());
		// nested classes cannot be built like this
		//if(caggr.isReferenceAggregateDecl())
		MatchContext context;
		mixin(SemChld!q{constructor});
		mixin(MatchCallHelper!q{auto r; constructor, sc, loc, type, args, context});
		if(!r){
			//sc.error("no matching constructor found", loc);
			constructor.matchError(sc,loc,type,args);
			mixin(ErrEplg);
		}
		if(!consCall){
			consCall = New!CallExp(constructor, args);
			consCall.fun = r;
			consCall.loc = loc;
		}
		mixin(SemChld!q{consCall});
		assert(constructor.meaning.isFunctionDecl()&&
		       constructor.meaning.isFunctionDecl().isConstructor());
		mixin(SemChld!q{constructor});
	}
};


mixin template Semantic(T) if(is(T==NewExp)){
	Identifier constructor;
	CallExp consCall;
	Scope scope_;
	
	override void semantic(Scope sc){
		mixin(SemPrlg);
		scope_ = sc;
		if(a1.length){
			sc.error("custom allocators are unsupported", a1[0].loc.to(a1[$-1].loc));
			mixin(ErrEplg);
		}
		// perform new T[i] => new T[](i) transformation
		if(auto ie=rty.isIndexExp()){
			if(ie.a.length>1){
				sc.error("dynamic arrays can only have one dimension", ie.a[0].loc.to(ie.a[$-1].loc));
				mixin(ErrEplg);
			}
			if(ie.a.length==1){
				if(a2.length>0){
					sc.error("no further arguments expected", a2[0].loc.to(a2[$-1].loc));
					mixin(ErrEplg);
				}
				swap(ie.a, a2);
			}
		}
		type = rty.typeSemantic(sc);
		mixin(SemChld!q{a2});
		mixin(SemProp!q{rty});
		auto tyu = type.getUnqual();
		if(auto da=tyu.isDynArrTy()){
			if(!a2.length){
				sc.error("expected array length argument", loc);
				mixin(ErrEplg);
			}
			auto d2=da;
			int actual = 1;
			foreach(x;1..a2.length){
				d2=d2.ty.isDynArrTy();
				assert(actual<int.max);
				actual++;
				if(!d2) break;
			}
			if(!d2){
				sc.error(format("too many arguments to new expression (expected at most %s)",toEngNum(actual)),loc);
				mixin(ErrEplg);
			}
		}else if(auto aggr=tyu.isAggregateTy()){
			if(!aggr.decl.isReferenceAggregateDecl())
				type = type.getPointer();
			if(auto iface=aggr.decl.isInterfaceDecl()){
				sc.error(format("cannot create instance of interface '%s'",iface.name), loc);
				mixin(ErrEplg);
			}
			mixin(ResolveConstructor);
		}else{
			if(a2.length>1){
				sc.error("too many arguments to new expression (expected at most one)",loc);
				mixin(ErrEplg);
			}
			if(a2.length) mixin(ImplConvertTo!q{a2[0], type});
			type = type.getPointer();
		}
		mixin(SemEplg);
	}

	override void noHope(Scope sc){
		if(constructor&&!type.isAggregateTy().decl.asc.inexistent(constructor))
			mixin(ErrEplg);
	}
	
	override bool isDirectlyAllocated(){ return true; }
}



mixin template Semantic(T) if(is(T==Identifier)){
	/* specifies whether or not to resume lookup recursively in
	   parent scopes if it fails in the initially given scope.
	 */
	bool recursiveLookup = true;

	override void semantic(Scope sc){
		if(!meaning) lookupSemantic(sc, sc);
		else super.semantic(sc);
	}

	final protected void lookupSemantic(Scope sc, Scope lkup)in{
		assert(!meaning);
	}body{
		mixin(SemPrlg);
		assert(sstate != SemState.failed);
		///lookup(lkup);
		mixin(Lookup!q{_;this,lkup});
		if(needRetry) return;
		if(sstate == SemState.failed){
			sc.error(format("undefined identifier '%s'",name), loc);
			mixin(ErrEplg);
		}
		super.semantic(sc);
	}

	/* looks up the given identifier in the scope given by the argument.

	   + if needRetry is set after the call, then the lookup should be retried later
	   + if sstate is SemState.failed after the call, then the lookup failed
	   + if the lookup succeeds, then 'meaning' will become initialized
	 */

	final Dependent!void lookup(Scope lkup)in{
		assert(!!lkup);
		assert(!meaning && sstate != SemState.error && sstate != SemState.failed, text(meaning," ",sstate));
	}out{
		if(!needRetry && sstate != SemState.error && sstate != SemState.failed)
			assert(meaning && meaning.scope_);
	}body{
		enum SemRet = q{ return indepvoid; };
		//needRetry = false; // TODO: why was this here?
		needRetry = true;
		if(allowDelay){
			sstate=SemState.begin; // reset

			//meaning=recursiveLookup?lkup.lookup(this, null):lkup.lookupHere(this, null);
			if(recursiveLookup) mixin(Lookup!q{meaning; lkup, this, null});
			else mixin(LookupHere!q{meaning; lkup, this, null});

			if(!meaning){
				if(unresolved){
					auto l = unresolved.potentialLookup(this);
					if(l.length){
						needRetry = true;
						unresolved = null;
						return multidep(cast(Node[])l).dependent!void;
					}
					if(!unresolved.inexistent(this)) mixin(ErrEplg);
					unresolved = null;
					tryAgain = true;
				}
				sstate = SemState.started;
				mixin(RetryBreakEplg);
			}else if(typeid(this.meaning) is typeid(DoesNotExistDecl)){
				meaning = null;
				needRetry=false;
				sstate = SemState.failed;
			}else{
				needRetry=false;
				tryAgain = true;
				unresolved = null;
				return indepvoid;
			}
		}else{
			if(sstate == SemState.started){
				needRetry = true;
				tryAgain = true;
				mixin(GetUnresolved!q{unresolved;lkup,this});
			}
			sstate = SemState.begin;
			mixin(RetryEplg);
		}
		unresolved = null;
		return indepvoid;
		// lkup.note(text("looked up ", this, " as ", meaning), loc);
	}

	/* performs reverse eponymous lookup for eponymous templates
	   eg. T foo(T)(T arg){return foo!T(arg);} and
	   eg. double foo(T)(T arg){return foo(2.0);} should compile
	 */

	final Expression reverseEponymousLookup(Scope sc)in{
		assert(!!meaning);
		assert(sstate != SemState.error);
		assert(recursiveLookup);
	}body{
		if(auto nest=cast(NestedScope)meaning.scope_){
			if(auto tmpl=cast(TemplateScope)nest.parent){
				if(tmpl.tmpl.name.name is name){
					auto parent = New!LookupIdentifier(name,tmpl.tmpl.scope_);
					parent.loc = loc;
					parent.recursiveLookup = false;
					return parent;
				}
			}
		}
		return this;
	}

	override void noHope(Scope sc){
		if(meaning) return;
		// TODO: there must be a better way to react when the scope is unavailable
		mixin(GetUnresolved!q{auto unresolved; sc, this});
		if(!unresolved.inexistent(this))
			mixin(ErrEplg);
	}

	static bool tryAgain = false;
	static bool allowDelay = false;
/+	static bool tryAgain(){return _tryAgain;}
	static void tryAgain(bool b){
		static int count=0;
		assert(!b||count++<100);
		import std.stdio; writeln(b);
		_tryAgain=b;
	}+/
private:
	Scope unresolved = null;
}

class LookupIdentifier: Identifier{
	Scope lkup;
	this(string name, Scope lkup){
		super(name);
		this.lkup = lkup;
	}

	override void semantic(Scope sc){
		if(!meaning) lookupSemantic(sc, lkup);
		else super.semantic(sc);
	}
	mixin DownCastMethod;
}

mixin template Semantic(T) if(is(T==ModuleIdentifier)){
	alias lkup mscope;
	override void semantic(Scope sc){
		assert(!!sc.getModule());
		if(!mscope) mscope = sc.getModule().sc;
		super.semantic(sc);
	}
}

abstract class CurrentExp: Expression{
	auto accessCheck = AccessCheck.all;
	Scope scope_;
	override void semantic(Scope sc){
		mixin(SemPrlg);
		scope_ = sc;
		auto aggr=sc.getAggregate();
		if(!aggr){
			sc.error(format("invalid use of '%s' outside of an aggregate declaration", toString()), loc);
			mixin(ErrEplg);
		}
		if(accessCheck!=AccessCheck.none)
		for(Declaration dl=sc.getDeclaration(); dl !is aggr; dl=dl.scope_.getDeclaration()){
			if(dl.stc&STCstatic){
				sc.error(format("invalid use of '%s' outside of a nonstatic member function", toString()), loc);
				mixin(ErrEplg);
			}
		}

		mixin CreateBinderForDependent!("DetermineType","determineType");
		mixin(DetermineType!q{type; this, sc, aggr});
		type = type.applyScopeSTC(sc);
		mixin(SemEplg);
	}

	override bool isLvalue(){
		assert(cast(AggregateTy)type.getHeadUnqual());
		return !!(cast(AggregateTy)type.getHeadUnqual()).decl.isValueAggregateDecl();
	}

	abstract Dependent!Type determineType(Scope sc, AggregateDecl d);
	override @property string kind(){ return "current object"; }

	mixin Visitors;
}
mixin template Semantic(T) if(is(T==CurrentExp)){}
mixin template Semantic(T) if(is(T==ThisExp)){
	protected override Dependent!Type determineType(Scope sc, AggregateDecl d){
		return d.getType().independent!Type;
	}
}
mixin template Semantic(T) if(is(T==SuperExp)){
	protected override Dependent!Type determineType(Scope sc, AggregateDecl d){
		auto raggr = d.isReferenceAggregateDecl();
		if(raggr){
			if(raggr.parents.length) raggr.findFirstNParents(1);
			if(raggr.parents.length){
				if(raggr.parents[0].needRetry)
					return Dependee(raggr.parents[0], raggr.scope_).dependent!Type;
				if(raggr.parents[0].sstate==SemState.error){
					mixin(SetErr!q{});
					return Dependee(this,null).dependent!Type;
				}
			}else goto Lerror;
			assert(raggr.parents[0].sstate == SemState.completed);
			assert(!!cast(AggregateTy)raggr.parents[0]);
			if(!(cast(AggregateTy)cast(void*)raggr.parents[0]).decl.isClassDecl())
				goto Lerror;
			return (cast(AggregateTy)cast(void*)raggr.parents[0]).decl.getType().independent!Type;
		}else goto Lerror;
	Lerror:
		// cast is workaround for bug in DMD
		sc.error(format("no super class for type '%s'",(cast(Type)d.getType()).toString()),loc);
		mixin(SetErr!q{});
		return Dependee(this,null).dependent!Type;
	}
}

mixin template Semantic(T) if(is(T==FieldExp)){

	Expression res;
	@property Expression member(){ return res ? res : e2; }

	AccessCheck accessCheck;
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e1});
		Type scopeThisType;
		auto msc = e1.getMemberScope();

		if(accessCheck == AccessCheck.init){
			accessCheck = e2.accessCheck;
			if(!e1.isType()) e2.accessCheck = e1.deferredAccessCheck();
		}

		if(e2.accessCheck!=AccessCheck.none) e2.loc=loc;

		if(!msc){
			if(auto ptr=e1.type.getHeadUnqual().isPointerTy())
				msc = ptr.ty.getMemberScope();
			if(!msc) goto Linexistent;
			e1 = New!(UnaryExp!(Tok!"*"))(e1);
			mixin(SemChld!q{e1});
		}

		auto this_ = e1.extractThis();

		if(!e2.meaning){
			if(auto ident = e2.isIdentifier()){
				e2.implicitCall = false;
				ident.recursiveLookup = false;
				//ident.lookup(msc);
				mixin(Lookup!q{_;ident,msc});
				if(ident.needRetry) { needRetry=true; return; }
				mixin(PropErr!q{ident});
				if(ident.sstate == SemState.failed) goto Linexistent;
			}
		}

		assert(!!e2.meaning);
		// TODO: find a better design here
		if(rewrite) return;
		e2.semantic(sc);
		res = e2;
		mixin(Rewrite!q{res});
		e2.rewrite = null;
		mixin(SemProp!q{e2});
		////
		if(auto sym = res.isSymbol()){
			e2=sym;
			type = e2.type;

			Type thisType=sym.thisType();
			bool needThis = !!thisType;
			if(needThis){
				if(this_ && sym.meaning.needsAccessCheck(AccessCheck.all))
				if(auto vd=sym.meaning.isVarDecl())
				if(vd.isField)
				{
					assert(!!this_.type.getUnqual().isAggregateTy());
					auto stc = this_.type.getHeadSTC();
					type=type.applySTC(stc);

					// delegates do not implicitly convert to const
					if(stc&STCconst && !e2.type.implicitlyConvertsTo(type).force){
						sc.error(format("cannot load field '%s' of type '%s' from const-qualified receiver",e2, e2.type), loc);
						mixin(ErrEplg);
					}
					e2.type = type;
				}

				if(sym.meaning.needsAccessCheck(accessCheck))
					return thisCheck(sc, this_, thisType);

			}
		}else if(this_){
			// TODO: integrate tuples with the rest of the code base
			if(res.isExpTuple()){
				type = res.type;
				mixin(SemEplg);
			}
			
			// type or enum on instance. ignore side effects of e1
			auto r=res;
			mixin(RewEplg!q{r});
			/*// TODO: do we rather want this:
			// enum reference. we need to evaluate 'this', but it
			// does not matter for the field expression
			//assert(e2.meaning.stc & STCenum);
			auto r=New!(BinaryExp!(Tok!","))(this_,res);
			r.loc=loc;
			r.semantic(sc);
			mixin(RewEplg!q{r});*/
		}
		if(!this_){
			// we do not have a 'this' pointer
			// and we do not need a 'this' pointer
			Expression r=res;
			mixin(RewEplg!q{r});
		}

		// we have a 'this' pointer that we don't need
		assert(!!type);
		mixin(SemEplg);

	Linexistent:

		if(isBuiltInField(sc,this_)) return;
		// TODO: UFCS

		TemplateInstanceDecl tmpl;
		if(auto fe=e1.isFieldExp()) if(auto t=fe.e2.meaning.isTemplateInstanceDecl()) tmpl=t;
		if(!tmpl)
		if(auto symb=e1.isSymbol())
		if(symb.meaning)if(auto t=symb.meaning.isTemplateInstanceDecl())
			tmpl=t;

		if(tmpl)
			sc.error(format("no member '%s' for %s '%s'",member.toString(),e1.kind,e1),loc);
		else
			sc.error(format("no member '%s' for type '%s'",member.toString(),e1.isType()?e1:e1.type),loc);
		mixin(ErrEplg);
	}

	void noHope(){
		if(auto i=e2.isIdentifier()){
			if(i.meaning) return;
			mixin(GetUnresolved!q{auto unresolved; e1.getMemberScope(), i});
			if(!unresolved.inexistent(i))
				mixin(ErrEplg);
		}
	}

	/* given that 'this' of type thisType is required, check if
	   this_ can be used as the 'this' pointer
	 */
	private void thisCheck(Scope sc,Expression this_, Type thisType){
		auto ttu = thisType.getUnqual();
		if(!this_){
			// statically bound calls to virtual member functions
			if(auto fd=sc.getFunction())
			if(auto decl=sc.getAggregate())
			if(fd.scope_.getDeclaration() is decl)
			if(auto raggr=decl.isReferenceAggregateDecl()){
				auto etu = cast(Type)raggr.getType(); // cast is workaround for DMD bug
				mixin(RefConvertsTo!q{bool conv; etu, ttu, 0});
				if(conv) goto Lok;
			}
			// member function templates
			if(auto sym=e1.isSymbol())
			if(sym.meaning.isTemplateInstanceDecl()){
				auto decl = sc.getDeclaration();
				mixin(IsDeclAccessible!q{bool acc; Declaration, decl, sym.meaning});
				if(acc) goto Lok;
			}
			// error message duplicated in Symbol.semantic
			sc.error(format("need 'this' to access %s '%s'",
			                e2.kind,e2.loc.rep),loc);

			mixin(ErrEplg);
		}
		assert(this_.sstate == SemState.completed);

		auto etu = this_.type.getUnqual();
		mixin(RefConvertsTo!q{bool conv; etu, ttu, 0});
		if(!conv){
			sc.error(format("need 'this' of type '%s' to access %s '%s'",
			                thisType.toString(),e2.kind,e2.loc.rep),loc);
			mixin(ErrEplg);
		}
		// successfully resolved non-tuple field expression that
		// requires 'this'
	Lok:mixin(SemEplg);
	}

	override Dependent!bool implicitlyConvertsTo(Type rhs){
		return member.implicitlyConvertsTo(rhs);
	}
	override bool isLvalue(){
		return member.isLvalue();
	}

	override Scope getMemberScope(){
		return member.getMemberScope();
	}
	override Expression extractThis(){
		if(isTuple()) return null;
		if(e2.meaning.isTemplateInstanceDecl()) return e1.extractThis();
		return this;
	}
	override AccessCheck deferredAccessCheck(){
		if(isTuple()) return AccessCheck.all;
		if(!e2.meaning.needsAccessCheck(accessCheck)) return accessCheck;
		return super.deferredAccessCheck();
	}

	override Dependent!Expression matchCallHelper(Scope sc, const ref Location loc, Type th_, Expression[] args, ref MatchContext context){
		assert(!th_);
		enum SemRet = q{ return this.independent!Expression; };
		if(member.isTuple()) return null.independent!Expression;
		Type this_ = null;
		// delegate and function pointer fields do not receive the implicit 'this'
		if(!e2.meaning.isVarDecl())
		if(auto tt=e1.extractThis())
			this_=tt.type;
		mixin(MatchCallHelper!q{auto exp; e2, sc, loc, this_, args, context});
		if(!exp) return null.independent!Expression;
		assert(!!cast(Symbol)exp);
		auto sym = cast(Symbol)cast(void*)exp;
		e2 = sym;
		sstate = SemState.begin;
		type = null;
		FieldExp.semantic(e2.scope_);
		Expression r = this;
		mixin(Rewrite!q{r});
		mixin(SemRet);
	}
	override void matchError(Scope sc, Location loc, Type th_, Expression[] args){
		assert(!th_);
		Type this_ = null;
		if(auto tt=e1.extractThis()) this_=tt.type;
		if(member.isTuple()) super.matchError(sc,loc,this_,args);
		return e2.matchError(sc,loc,this_,args);
	}

	import vrange;
	override IntRange getIntRange(){ return member.getIntRange(); }
	override LongRange getLongRange(){ return member.getLongRange(); }


	/* rewrites built-in fields and returns whether it was a built-in
	 */
	bool isBuiltInField(Scope sc,Expression this_)in{
		assert(!isTuple());
		assert(e1.sstate == SemState.completed);
		assert(!!cast(Identifier)e2);
	}body{
		auto name = (cast(Identifier)cast(void*)e2).name;
		auto ty = e1.isType();
		bool isType = true;
		if(ty is null){
			ty = e1.type;
			isType = false;
		}
		Expression r = null;
		if(auto elt = ty.getElementType()){
			if(!isType)	switch(name){
				case "ptr":
					r=New!PtrExp(e1);
					goto Lrewrite;
				case "length":
					r=New!LengthExp(e1);
					goto Lrewrite;
				default: break;
			}else switch(name){
				case "ptr":
					type = elt.getPointer();
					if(accessCheck == AccessCheck.all){
						thisCheck(sc, this_, ty);
						return true;
					}
					goto Lnorewrite;
				case "length":
					type = Type.get!Size_t();
					if(accessCheck == AccessCheck.all){
						thisCheck(sc, this_, ty);
						return true;
					}
					goto Lnorewrite;
				default: break;
			}
		}
		if(auto tp=e1.isTuple()){
			if(name=="length"){
				r=LiteralExp.factory(Variant(tp.length), Type.get!Size_t());
				goto Lrewrite;
			}
		}
		return false;
	Lrewrite:
		r.loc=loc;
		mixin(RewEplg!q{r});
	Lnorewrite:
		mixin(SemEplg);
	}
}

class PtrExp: Expression{
	Expression e;
	this(Expression e)in{
		assert(e.sstate == SemState.completed);
		assert(e.type.getElementType());
	}body{
		this.e=e;
		type=e.type.getElementType().getPointer();
		sstate = SemState.completed;
	}

	override string toString(){return e.toString()~".ptr";}
	override @property string kind(){return "array base pointer";}

	override void semantic(Scope sc){mixin(SemPrlg); assert(0);}

	mixin Visitors;
}

class LengthExp: Expression{
	Expression e;
	this(Expression e)in{
		assert(e.sstate == SemState.completed);
		assert(e.type.getElementType());
	}body{
		this.e=e;
		type=Type.get!Size_t();
		sstate = SemState.completed;
	}

	override bool checkMutate(Scope sc, ref Location l){
		return e.checkMutate(sc,l);
	}

	override string toString(){return e.toString()~".length";}
	override @property string kind(){return "array length";}

	override void semantic(Scope sc){mixin(SemPrlg); assert(0);}

	mixin Visitors;
}

mixin template Semantic(T) if(is(T==DollarExp)){
	Scope scope_;

	override void semantic(Scope sc){
		if(!meaning) meaning=sc.getDollar();
		if(!meaning){
			sc.error("'$' is undefined outside index or slice operators",loc);
			mixin(ErrEplg);
		}
		// Symbol.semantic(sc); // DMD BUG: DMD thinks this call is dynamically bound
		super.semantic(sc);
	}

	static VarDecl createDecl(Scope ascope, STC stc, Expression init)in{
		assert(!!ascope);
	}body{
		// TODO: the allocation of a new identifier is unnecessary
		auto dollar = new VarDecl(stc, Type.get!Size_t(),
		                     New!Identifier("__dollar"), init);
		dollar.sstate = SemState.begin; // do not add to scope
		dollar.scope_ = ascope;
		dollar.semantic(ascope);
		mixin(Rewrite!q{dollar});
		assert(dollar.sstate == SemState.completed);
		return dollar;
	}

	override bool isLvalue(){ return false; }

	override @property string kind(){ return "array length"; }
	override string toString(){ return "$"; }

	mixin template DollarProviderImpl(alias e){
		VarDecl dollar;

		// interface DollarProvider
		VarDecl getDollar(){
			if(!dollar){
				auto stc = STC.init;
				Expression init;
				if(auto tp=e.isTuple()){
					stc |= STCenum;
					init = LiteralExp.factory(Variant(tp.length), Type.get!Size_t());
				}

				// dollar variables at module scope are static
				if(!ascope.getDeclaration()) stc |= STCstatic;

				dollar = DollarExp.createDecl(ascope, stc, init);
			}
			return dollar;
		}
	}
}


mixin template Semantic(T) if(is(T==FunctionLiteralExp)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		auto dg=New!FunctionDef(STC.init,fty,New!Identifier(uniqueIdent("__dgliteral")),cast(BlockStm)null,cast(BlockStm)null,cast(Identifier)null,bdy, which==Kind.none);
		auto decl=sc.getDeclaration();
		if(which==Kind.function_ || !decl || decl.isAggregateDecl())
			dg.stc |= STCstatic;
		dg.sstate = SemState.begin;
		dg.scope_ = sc; // Symbol will use this scope to reason for analyzing DG
		Expression e=New!Symbol(dg, true, true);
		e.loc=dg.loc=loc;
		e = New!(UnaryExp!(Tok!"&"))(e);
		e.brackets++;
		e.loc=loc;
		e.semantic(sc);

		if(auto enc=sc.getDeclaration()) if(auto fd=enc.isFunctionDef()){
			fd.nestedFunctionLiteral(dg);
		}

		auto r = e;
		mixin(PropErr!q{r});
		mixin(RewEplg!q{r});
	}
}

mixin template Semantic(T) if(is(T==ConditionDeclExp)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(!decl) decl=New!VarDecl(stc,ty,name,init);
		mixin(SemChldPar!q{decl});
		if(!sym) sym = name;
		sym.semantic(sc);
		auto nsym = sym;
		mixin(Rewrite!q{nsym});
		assert(!!cast(Symbol)nsym);
		sym = cast(Symbol)cast(void*)nsym;
		mixin(SemProp!q{sym});
		type = sym.type;
		mixin(SemEplg);
	}
private:
	VarDecl decl;
	Symbol sym;
}

// types
mixin template Semantic(T) if(is(T==Type)){
	override void semantic(Scope sc) { }
	override Type typeSemantic(Scope sc) {
		semantic(sc);
		auto r=this;
		mixin(Rewrite!q{r});
		return r;
	}

	override Type clone(Scope,const ref Location) { return this; }

	final protected Type checkVarDeclError(Scope sc, VarDecl me)in{assert(sc);}body{
		if(me.name)
			sc.error(format("%s '%s' has invalid type '%s'", me.kind, me.name, this), me.loc);
		else
			sc.error(format("%s has invalid type '%s'", me.kind, this), me.loc);
		return New!ErrorTy();
	}
	Type checkVarDecl(Scope, VarDecl){return this;}

	Type getArray(long size){
		if(auto r=arrType.get(size,null)) return r;
		return arrType[size]=ArrayTy.create(this,size);
	}

	override Dependent!Expression matchCallHelper(Scope sc, const ref Location loc, Type this_, Expression[] args, ref MatchContext context){
		return null.independent!Expression;
	}
	override void matchError(Scope sc, Location loc, Type this_, Expression[] args){
		sc.error(format("%s '%s' is not callable",kind,toString()),loc);
	}



	private static auto __funcliteralTQ(){string r;
		foreach(x; typeQualifiers){ // getConst, getImmutable, getShared, getInout, getPointer, getDynArr. remember to keep getArray in sync.
			r ~= mixin(X!q{
				private Type @(x)Type;
				final Type get@(upperf(x))(){
					if(@(x)Type) return @(x)Type;
					return @(x)Type=get@(upperf(x))Impl();
				}
				protected Type get@(upperf(x))Impl(){return @(upperf(x))Ty.create(this);}
				Type getTail@(upperf(x))(){return this;}
				Type in@(upperf(x))Context(){return this;}
			});
		}
		foreach(x; ["pointer","dynArr"]){
			r ~= mixin(X!q{
				private Type @(x)Type;
				final Type get@(upperf(x))(){
					if(@(x)Type) return @(x)Type;
					return @(x)Type=@(upperf(x))Ty.create(this);
				}
			});
		}
		return r;
	}mixin(__funcliteralTQ());

	Type applySTC(STC stc){
		auto r = this;
		if(stc&STCimmutable)        r = r.getImmutable();
		if(stc&STCconst||stc&STCin) r = r.getConst();
		if(stc&STCinout)            r = r.getInout();
		if(stc&STCshared)           r = r.getShared();
		return r;
	}

	STC getHeadSTC(){ return STC.init;}

	final Type applyScopeSTC(Scope sc){
		auto aggr=sc.getAggregate();
		if(!aggr) return this;
		auto fl=sc.getDeclaration(), type = this;
		if(fl !is aggr)
		for(Declaration dl;;fl=dl){
		    dl=fl.scope_.getDeclaration();
		    if(dl is aggr) break;
	    }
		if(auto fd=fl.isFunctionDecl()){
			type = type.applySTC(fl.stc&STCtypeconstructor);
		}
		return type;
	}


	Type getHeadUnqual(){return this;} // is implemented as lazy field in the relevant classes
	Type getUnqual(){return this;}     // ditto

	Type getElementType(){return null;}

	bool isMutable(){return true;}

	/* this alias exists in order to be robust against language changes
	   involving an additional qualifier that can co-exist with immutable
	*/
	alias isImmutableTy isImmutable;
	// TODO: isConst, on by-need basis

	BasicType isIntegral(){return null;}
	BasicType isComplex(){return null;}

	final Type isSomeString(){
		return this is get!string() || this is get!wstring() || this is get!dstring() ? this : null;
	}

	final FunctionTy getFunctionTy(){ // TODO: could be a virtual function instead
		if(auto fty = isFunctionTy()) return fty;
		if(auto dgt = isDelegateTy()) return dgt.ft;
		if(auto fpt = isPointerTy())  return fpt.ty.isFunctionTy();
		return null;
	}


	/* used for matching inout. the formal parameter type is adapted
	   to match the actual argument as good as possible.
	 */
	Type adaptTo(Type from, ref InoutRes inoutRes){
		return this;
	}

	/* used for IFTI and template type parameter matching
	 */
	Dependent!void typeMatch(Type from){ return indepvoid; }
	bool hasPseudoTypes(){ return false; }

	override Type resolveInout(InoutRes inoutRes){
		return this;
	}

	/* important for is-expressions and parameter matching:
	   function, delegate and function pointer types cannot always
	   be kept unique, since they may include default parameters
	 */
	bool equals(Type rhs){
		return this is rhs;
	}

	override Dependent!bool convertsTo(Type rhs){
		return rhs.getHeadUnqual() is Type.get!void() ?true.independent:
			implicitlyConvertsTo(rhs.getUnqual().getConst());
	}

	override Dependent!bool implicitlyConvertsTo(Type rhs){
		return this.refConvertsTo(rhs.getHeadUnqual(),0);
	}


	final Dependent!bool constConvertsTo(Type rhs){
		return !this.getUnqual().equals(rhs.getUnqual()) ?false.independent:
			this.refConvertsTo(rhs,0);
	}


	// bool isSubtypeOf(Type rhs){...}

	/* stronger condition than subtype relationship.
	   a 'num'-times reference to a this must be a subtype of
	   a 'num'-times reference to an rhs.
	*/

	Dependent!bool refConvertsTo(Type rhs, int num){
		if(this is rhs) return true.independent;
		if(num < 2){
			if(auto d=rhs.isConstTy()) return refConvertsTo(d.ty.getTailConst(), 0);
		}
		return false.independent;
	}

	final protected Dependent!Type mostGeneral(Type rhs){
		if(rhs is this) return this.independent;
		Type r   = null;
		mixin(ImplConvertsTo!q{bool l2r; this, rhs});
		mixin(ImplConvertsTo!q{bool r2l; rhs, this});

		if(l2r ^ r2l){
			r = r2l ? this : rhs;
			STC stc = this.getHeadSTC() & rhs.getHeadSTC();
			r = r.getHeadUnqual().applySTC(stc);
		}
		return r.independent;
	}

	// TODO: similar code occurs in 3 places
	final protected Dependent!Type refMostGeneral(Type rhs, int num){
		if(rhs is this) return this.independent;
		Type r   = null;
		mixin(RefConvertsTo!q{bool l2r; this, rhs, num});
		mixin(RefConvertsTo!q{bool r2l; rhs, this, num});

		if(l2r ^ r2l){
			r = r2l ? this : rhs;
			if(!num){
				STC stc = this.getHeadSTC() & rhs.getHeadSTC();
				r = r.getHeadUnqual().applySTC(stc);
			}
		}
		return r.independent;
	}

	/* common type computation. roughly TDPL p60
	   note: most parts of the implementation are in subclasses
	*/

	Dependent!Type combine(Type rhs){
		if(auto r = mostGeneral(rhs).prop) return r;
		auto unqual = rhs.getHeadUnqual();
		if(unqual !is rhs) return unqual.combine(this);
		return null.independent!Type;
	}

	Dependent!Type refCombine(Type rhs, int num)in{assert(!!rhs);}body{
		if(auto d=rhs.isQualifiedTy()) return d.refCombine(this, num);
		if(auto r = refMostGeneral(rhs, num).prop) return r;
		if(num < 2){
			if(num) return getConst().refCombine(rhs.getConst(), 0);
			auto tconst = getTailConst();
			if(this !is tconst) return tconst.refCombine(rhs.getTailConst(), 0);
		}
		return null.independent!Type;
	}

	Dependent!Type unify(Type rhs){ return combine(rhs); }

	/* members
	 */

	override Scope getMemberScope(){
		return null;
	}

	override Expression extractThis(){ // would prefer using typeof(null)
		return null;
	}

	/* built-in properties
	 */
	ulong getSizeof(){
		assert(0, "no size yet for type "~to!string(this));
	}


	/* get the ranges associated with a type. expressions often
	   allow more specific statements about their range.
	*/
	override IntRange getIntRange(){return IntRange.full(true);}
	override LongRange getLongRange(){return LongRange.full(true);}

	// TemplateDecl needs this.
	override bool templateParameterEquals(Expression rhs){
		if(auto type = cast(Type)rhs) return equals(type);
		return false;
	}
	override size_t templateParameterToHash(){
		return toHash(); // TODO!: fix!
	}
}


mixin template Semantic(T) if(is(T==DelegateTy)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{ft});
		mixin(SemEplg);
	}

	override Dependent!Expression matchCallHelper(Scope sc, const ref Location loc, Type this_, Expression[] args, ref MatchContext context){
		auto rd=ft.matchCallHelper(sc, loc, this_, args, context);
		if(rd.value) rd.value = this; // valid for dependent is null and dependent !is null
		return rd;
	}

	override bool equals(Type rhs){
		if(auto dgt = rhs.isDelegateTy()) return ft.equals(dgt.ft);
		return false;
	}

	override Dependent!bool refConvertsTo(Type rhs, int num){
		if(auto dgt = rhs.isDelegateTy()) return ft.refConvertsTo(dgt.ft, num+1);
		return super.refConvertsTo(rhs,num);
	}

	override Dependent!Type combine(Type rhs){
		if(auto r = mostGeneral(rhs).prop) return r;
		auto unqual = rhs.getHeadUnqual();
		return unqual.refCombine(this,0);
	}

	// TODO: would like to have Dependent!DelegateTy here...
	override Dependent!Type refCombine(Type rhs, int num){
		if(auto dgt = rhs.isDelegateTy()){
			mixin(RefCombine!q{auto rcomb; ft, dgt.ft, num+1});
			assert(!rcomb||cast(FunctionTy)rcomb);
			if(auto r = cast(FunctionTy)cast(void*)rcomb)
				return r.getDelegate().independent!Type;
		}
		return null.independent!Type;
	}

	override Dependent!Type unify(Type rhs){
		if(auto rft=rhs.getFunctionTy()){
			mixin(Unify!q{auto unf; ft, rft});
			if(unf){
				assert(cast(FunctionTy)unf);
				return (cast(FunctionTy)cast(void*)unf).getDelegate().independent!Type;
			}
		}
		return null.independent!Type;
	}

	override DelegateTy resolveInout(InoutRes res){
		return ft.resolveInout(res).getDelegate();
	}

	override Dependent!void typeMatch(Type from){
		// function pointers might convert to a delegate
		// so matching should succeed
		// for robustness and convenience, this also accepts a normal
		// function type
		if(auto rft=from.getHeadUnqual().getFunctionTy()) ft.typeMatch(rft);
/+		if(auto ptr=from.isPointerTy())
			if(auto pft=ptr.ty.isFunctionTy())
				ft.typeMatch(pft);+/
		return indepvoid;
	}

	override bool hasPseudoTypes(){ return ft.hasPseudoTypes(); }

	private static string __dgliteralQual(){
		string r;
		foreach(x;["const","immutable","inout","shared"]){
			r~= mixin(X!q{
				override Type getTail@(upperf(x))(){
					return ft.addQualifiers(STC@(x)).getDelegate(); // TODO: cache?
				}
				override Type in@(upperf(x))Context(){
					return ft.in@(upperf(x))Context().getDelegate(); // TODO: cache?
				}
			});
		}
		return r;
	}
	mixin(__dgliteralQual());
}
mixin template Semantic(T) if(is(T==FunctionTy)){
	Scope scope_;

	void reset()in{
		assert(hasUnresolvedParameters());
	}body{
		sstate = SemState.begin;
		foreach(x;params) x.sstate = SemState.begin;
	}

	override void semantic(Scope sc){
		mixin(SemPrlg);
		assert(!!sc);
		scope_=sc;
		if(rret){
			ret = rret.typeSemantic(sc);
			mixin(PropRetry!q{rret});
		}
		if(ret) mixin(SemChldPar!q{ret});
		foreach(p; params){
			if(p.sstate==SemState.pre) p.sstate = SemState.begin; // never insert into scope
			if(!p.rtype && !p.init) continue; // parameter type needs to be deduced
			p.semantic(sc); // TODO: rewriting parameters ever needed?
			assert(!p.rewrite);
		}
		foreach(p;params){mixin(PropRetry!q{p});}
		if(rret) mixin(PropErr!q{rret});
		if(ret) mixin(PropErr!q{ret});
		mixin(PropErr!q{params});
		params = Tuple.expand(sc,params);
		mixin(SemEplg);
	}

	override Type checkVarDecl(Scope sc, VarDecl me){
		return checkVarDeclError(sc,me);
	}

	bool hasUnresolvedParameters(){
		foreach(x;params) if(x.mustBeTypeDeduced()) return true;
		return false;
	}

	bool resolve(FunctionTy rhs)in{
		assert(!!rhs);
	}body{
		bool r;
		if(!ret){ret = rhs.ret; r=!!ret;}
		foreach(i,p; params[0..min($,rhs.params.length)]){
			if(!p.type){
				auto ty=rhs.params[i].type;
				if(ty&&ty.getHeadUnqual()!is Type.get!void()){
					p.type=ty;
					r=true;
					p.semantic(scope_);
				}
			}
		}
		return r;
	}

	bool resolve(Expression[] args){
		bool r=false;
		foreach(i,p; params[0..min($,args.length)])
			if(!p.type){
				auto ty = args[i].type;
				if(ty&&ty.getHeadUnqual()!is Type.get!void()){
					p.type=ty;
					r=true;
					p.semantic(scope_);
				}
			}
		return r;
	}

	override FunctionTy resolveInout(InoutRes res){
		alias util.TypeTuple!(__traits(allMembers,InoutRes)) M;
		static assert(M[0]=="none");

		FunctionTy performResolution(){
			auto r=dup();
			r.params = r.params.dup;
			foreach(ref p;r.params){
				p=p.ddup();
				p.type = p.type.resolveInout(res);
				p.rtype=null;
				p.stc = STC.init;
			}
			foreach(x;M[1..$]) mixin("r.cache_inoutres_"~x)=r;
			r.ret = r.ret.resolveInout(res);
			return r;
		}

		final switch(res){
			foreach(x;M[1..$]){
				enum e = mixin("InoutRes."~x);
				enum i = "cache_inoutres_"~x;
				case e: if(mixin(i)) return mixin(i);
					return mixin(i)=performResolution();

			}
			case InoutRes.none:
				return this;
		}
	}

	override Dependent!void typeMatch(Type rhs){
		if(auto ft = rhs.isFunctionTy()){
			if(ret&&ft.ret){mixin(TypeMatch!q{_; ret, ft.ret});}//ret.typeMatch(ft.ret);
			foreach(i,p;params[0..min($,ft.params.length)]){
				auto mt = p.type ? p.type.isMatcherTy() : null;
				if(mt && mt.which==WhichTemplateParameter.tuple){
					//TODO: gc allocation
					alias util.all all;
					if(i+1==params.length&&all!(_=>_.type !is null)(ft.params[i..$])){
						auto types = map!(_=>_.type)(ft.params[i..$]).array();
						//mt.typeMatch(New!TypeTuple(types));
						mixin(TypeMatch!q{_; mt, New!TypeTuple(types)});
					}
					break;
				}

				if(p.type && ft.params[i].type)
					//p.type.typeMatch(ft.params[i].type);
					mixin(TypeMatch!q{_; p.type, ft.params[i].type});
			}
		}
		return indepvoid;
	}
	override bool hasPseudoTypes(){
		if(ret && ret.hasPseudoTypes()) return true;
		foreach(p;params)
			if(p.type && p.type.hasPseudoTypes())
				return true;
		return false;
	}

	final void stripPseudoTypes(){
		if(ret && ret.hasPseudoTypes()) ret = null;
		foreach(p;params)
			if(p.type && p.type.hasPseudoTypes())
				p.type = null;
	}

	override Dependent!Type unify(Type rhs){
		if(auto ft = rhs.isFunctionTy()){
			// TODO: unify STC
			if(vararg != ft.vararg ||
			   stc!=ft.stc||ft.params.length!=params.length) return Type.init.independent;
			Type r;
			auto p = new Parameter[params.length]; // TODO: avoid allocation
			if(!ret) r=ft.ret;
			else if(!ft.ret) r=ret;
			else mixin(Unify!q{r; ret, ft.ret});
			foreach(i,ref x;p){
				// TODO: unify STC
				x = New!Parameter(params[i].stc, null, null, null);
				if(!ft.params[i]||!params[i]||ft.params[i].stc!=params[i].stc)
					continue;
				Type tt;
				if(!params[i].type) tt = ft.params[i].type;
				else if(!ft.params[i].type) tt = params[i].type;
				else mixin(Unify!q{tt;params[i].type,ft.params[i].type});
				x.type = tt;
			}
			//if(ret == r && params == p) return this.independent!Type;
			auto res = New!FunctionTy(stc,r,p,vararg);
			do res.semantic(scope_); // TODO: not great
			while(!res.sstate == SemState.completed);
			return res.independent!Type;
		}else return rhs.unify(this);
	}

	override Dependent!Expression matchCallHelper(Scope sc, const ref Location loc, Type this_, Expression[] args, ref MatchContext context){
		alias util.any any; // TODO: file bug
		if(args.length > params.length ||
		   any!(_=>_.init is null)(params[args.length..params.length])){
				context.match=Match.none;
				return null.independent!Expression;
		}

		resolve(args);
		foreach(x;params)
			if(x.sstate == SemState.error||!x.type)
				return null.independent!Expression;

		immutable len = args.length;
		auto at = new Type[len]; // GC allocation, could be done on stack!
		// TODO: make behave like actual overloading
		// check compatibility of the 'this' pointer
		if(this_&&stc&STCinout) context.inoutRes = irFromSTC(this_.getHeadSTC());
		foreach(i,p; params[0..len]){
			if(!p.type) continue;
			at[i] = p.type.adaptTo(args[i].type, context.inoutRes);
		}
		if(this_){
			mixin(RefConvertsTo!q{
				auto compat;
				this_,
				this_.getHeadUnqual()
				.applySTC(stc&STCtypeconstructor)
				.resolveInout(context.inoutRes),
				0
			});
			if(!compat) return null.independent!Expression;
		}

		foreach(i,ref x;at) x = x.resolveInout(context.inoutRes);
		// the code that follows assumes the four matching level semantics
		static assert(Match.min == 0 && Match.max == Match.exact && Match.exact == 3);

		Match match = Match.exact;
		foreach(i,p; params[0..len]){
			if(!(p.stc & STCbyref)){
				if(args[i].typeEquals(at[i])) continue;
				mixin(ImplConvertsTo!q{bool iconv; args[i], at[i];});
				if(!iconv){
					match = Match.none;
					break;
				}else{
					mixin(ConstConvertsTo!q{bool cconv; args[i].type, at[i]});
					if(cconv){
						if(match == Match.exact) match = Match.convConst;
					}else match = Match.convert; // Note: Match.none breaks the loop
				}
			}else if(p.stc & STCref){
				mixin(RefConvertsTo!q{bool rconv;args[i].type,at[i],1});
				if(!rconv || !args[i].isLvalue()){
					match = Match.none;
					break;
				}
			}else{// if(params[i].stc & STCout){
				assert(p.stc & STCout);
				mixin(RefConvertsTo!q{bool rconv;at[i], args[i].type,1});
				if(!rconv || !args[i].isLvalue() || !args[i].type.isMutable()){
					match = Match.none;
					break;
				}
			}
		}
		context.match = match;
		return (match == Match.none ? null : this).independent!Expression;
	}

	final bool hasAutoReturn(){return rret is null;}
	final bool hasUnresolvedReturn(){return hasAutoReturn() && ret is null;}
	final void resolveReturn(Type to)in{
		assert(hasUnresolvedReturn());
		assert(!!to && to.sstate == SemState.completed);
	}body{
		ret = to;
	}

	override bool equals(Type rhs){
		return compareImpl(rhs);
	}

	private bool compareImpl(bool implconv=false)(Type rhs){
		// cannot access frame pointer to 'all'. TODO: file bug
		if(auto ft = rhs.isFunctionTy()){
			auto stc1 = stc, stc2 = ft.stc;
			static if(implconv){
				stc1 &= ~STCproperty, stc2 &= ~STCproperty; // STCproperty does not matter
				if(stc1 & STCsafe || stc1 & STCtrusted)
					stc1 &= ~STCsafe & ~STCtrusted, stc2 &= ~STCsafe & ~STCtrusted & ~STCsystem;
				// attributes that can be freely dropped:
				if(stc1 & STCpure) stc1 &= ~STCpure, stc2 &= ~STCpure;
				if(stc1 & STCnothrow) stc1 &= ~STCnothrow, stc2 &= ~STCnothrow;
				if(stc1 & STCconst) stc1 &= ~STCconst, stc2 &= ~STCconst;
				// immutable -> const is ok
				if(stc1 & STCimmutable && stc2 & STCconst)
					stc1 &= ~STCimmutable, stc2 &= ~STCconst;
				if(stc2 & STCdisable) stc1 &= ~STCdisable, stc2 &= ~STCdisable;
				// TODO: more implicit conversion rules
			}
			if(!((stc1==stc2 && (!ret||ret.equals(ft.ret)) &&
			     params.length == ft.params.length) &&
			     vararg == ft.vararg)) return false;
			//all!(_=>_[0].type.equals(_[1].type))(zip(params,ft.params)) &&
			foreach(i,x; params)
				if(x.type && !x.type.equals(ft.params[i].type)||
				   (x.stc&(STCbyref|STClazy))!=(ft.params[i].stc&(STCbyref|STClazy)))
					return false;
			return true;
		}else return false;
	}

	// TODO: rename and don't implement them
	override Dependent!bool refConvertsTo(Type rhs, int num){
		if(num<2) return compareImpl!true(rhs).independent;
		else return compareImpl!false(rhs).independent;
	}

	// TODO: would like to have Dependent!FunctionTy here...
	override Dependent!Type refCombine(Type rhs, int num){
		if(auto ft = rhs.isFunctionTy()){
			if(this.equals(rhs)) return this.independent!Type;
		}
		return null.independent!Type;
	}

	DelegateTy getDelegate()in{
		assert(sstate==SemState.completed);
	}body{
		if(dgtype) return dgtype;
		dgtype = New!DelegateTy(this);
		dgtype.semantic(scope_);
		mixin(Rewrite!q{dgtype});
		assert(dgtype.sstate == SemState.completed);
		return dgtype;
	}

	// function types are not mutable
	// and can be shared freely among threads
	override bool isMutable(){return false;}
	protected{
		override FunctionTy getConstImpl(){ return this; }
		override FunctionTy getImmutableImpl(){ return this; }
		override FunctionTy getSharedImpl()() { return this; }
		override FunctionTy getInoutImpl(){ return this; }
	}

	override FunctionTy inConstContext(){
		return removeQualifiers(STCconst);
	}
	override FunctionTy inImmutableContext(){
		return removeQualifiers(STCimmutable|STCconst|STCinout|STCshared);
	}
	override FunctionTy inSharedContext(){
		return removeQualifiers(STCshared);
	}
	override FunctionTy inInoutContext(){
		return removeQualifiers(STCinout);
	}

	// delegate types can be tail-qualified
	// DelegateTy is a client of this functionality

	final FunctionTy addQualifiers(STC qual){
		return modifyQualifiers!true(qual);
	}

	final FunctionTy removeQualifiers(STC qual){
		return modifyQualifiers!false(qual);
	}

	// TODO: does this duplicate all that is relevant?
	FunctionTy dup(){
		auto res=New!FunctionTy(stc,rret,params,vararg);
		res.ret = ret;
		res.sstate = sstate;
		return res;
	}

private:

	FunctionTy modifyQualifiers(bool add)(STC qual){
		static if(add){
			if((stc&qual) == qual) return this;
			auto diffq = stc&qual^qual;
		}else{
			if(!(stc&qual)) return this;
			auto diffq = stc&qual;
		}
		static if(add){
			if(stc&STCimmutable){
				diffq&=~(STCconst|STCinout|STCshared);
				if(!diffq) return this;
			}
		}
		diffq&=-diffq;
		switch(diffq){
			foreach(x; ToTuple!qualifiers){
				enum s=mixin("STC"~x);
				enum i="cache_"~x~(add?"":"_no");
				enum irev = i~".cache_"~x~(add?"_no":"");
				// alias ID!(mixin(i)) cache; // wut?
				case s:
					if(!mixin(i)){
						mixin(i) = dup();
						static if(add) mixin(i).stc|=s;
						else mixin(i).stc&=~s;
						mixin(irev)=this;
					}
					return mixin(i).modifyQualifiers!add(qual);
			}
			default: assert(0, STCtoString(diffq));
		}

	}

	DelegateTy dgtype;

	enum qualifiers = ["const","immutable","inout","nothrow","pure","shared",
	                   "safe","trusted","system"];
	static string __dgliteralgenCaches(){
		string r;
		foreach(x; qualifiers) r~="FunctionTy cache_"~x~", cache_"~x~"_no;\n";
		foreach(x; __traits(allMembers,InoutRes)[1..$])  r~="FunctionTy cache_inoutres_"~x~";";

		r~="public void clearCaches(){ dgtype=null;"; // TODO: these are not all caches!
		foreach(x; qualifiers) r~="cache_"~x~"=null;cache_"~x~"_no=null;";
		foreach(x; __traits(allMembers,InoutRes)[1..$]) r~="cache_inoutres_"~x~"=null;";
		r~="}";
		return r;
	}
	mixin(__dgliteralgenCaches);
}

mixin template Semantic(T) if(is(T==BasicType)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin({
			string r=`Type r;switch(op){`;
			foreach(x; basicTypes)
				r~=mixin(X!q{case Tok!"@(x)": r=Type.get!@(x)();break;});
			return r~`default: assert(0);}`;
		}());
		assert(r !is this);
		mixin(RewEplg!q{r});
	}

	override Type checkVarDecl(Scope sc, VarDecl me){
		if(op!=Tok!"void") return this;
		return checkVarDeclError(sc,me);
	}

	BasicType intPromote(){
		switch(op){
			case Tok!"bool":
			case Tok!"byte", Tok!"ubyte", Tok!"char":
			case Tok!"short", Tok!"ushort", Tok!"wchar":
				return Type.get!int();
			case Tok!"dchar":
				return Type.get!uint();
			default: return this;
		}
	}

	private static immutable int[] strength=
		[Tok!"bool":1,Tok!"char":2,Tok!"byte":2,Tok!"ubyte":2,Tok!"wchar":3,Tok!"short":3,Tok!"ushort":3,
		 Tok!"dchar":4,Tok!"int":4,Tok!"uint":4,Tok!"long":5,Tok!"ulong":5,Tok!"float":6,Tok!"double":6,Tok!"real":6,
		 Tok!"ifloat":-1,Tok!"idouble":-1,Tok!"ireal":-1,Tok!"cfloat":-2,Tok!"cdouble":-2,Tok!"creal":-2, Tok!"void":0];

	override BasicType isIntegral(){return strength[op]>0 && strength[op]<=5 ? this : null;}
	final BasicType isFloating(){return strength[op]==6 ? this : null;}
	override BasicType isComplex(){return strength[op]==-2 ? this : null;}
	final BasicType isImaginary(){return strength[op]==-1 ? this : null;}

	final BasicType flipSigned(){
		switch(op){
			case Tok!"byte": return Type.get!ubyte();
			case Tok!"ubyte": return Type.get!byte();
			case Tok!"short": return Type.get!ushort();
			case Tok!"ushort": return Type.get!short();
			case Tok!"int": return Type.get!uint();
			case Tok!"uint": return Type.get!int();
			case Tok!"long": return Type.get!ulong();
			case Tok!"ulong": return Type.get!long();
			case Tok!"char": return Type.get!byte();
			case Tok!"wchar": return Type.get!short();
			case Tok!"dchar": return Type.get!int();
			default: return this;
		}
	}

	final int bitSize(){
		return basicTypeBitSize(op);
	}
	final bool isSigned(){
		return basicTypeIsSigned(op);
	}

	override ulong getSizeof(){return basicTypeBitSize(op)>>3;}

	override Dependent!bool implicitlyConvertsTo(Type rhs){
		if(auto bt=rhs.getHeadUnqual().isBasicType()){ // transitive closure of TDPL p44
			if(op == Tok!"void") return (bt.op == Tok!"void").independent;
			if(strength[op]>=0 && strength[bt.op]>0)
				return (strength[op]<=strength[bt.op]).independent;
			if(strength[bt.op]==-2) return true.independent;
			// both must be imaginary:
			return (strength[op] == -1 && strength[bt.op] == -1).independent;
		}
		return false.independent;
	}

	override Dependent!bool convertsTo(Type rhs){
		if(auto t=super.convertsTo(rhs).prop) return t;
		// all basic types except void can be cast to each other
		if(auto bt=rhs.getUnqual().isBasicType())
			return (op != Tok!"void" || bt.op == Tok!"void").independent;
		return false.independent;
	}

	override Dependent!Type combine(Type rhs){
		if(this is rhs.getHeadUnqual()) return this.independent!Type;
		else if(rhs is Type.get!void()) return null.independent!Type;;
		if(auto bt=rhs.getHeadUnqual().isBasicType()){
			if(strength[op]>0&&strength[bt.op]>=0){
				if(strength[op]<4&&strength[bt.op]<4) return Type.get!int().independent!Type;
				if(strength[op]<strength[bt.op]) return bt.independent!Type;
				if(strength[op]>strength[bt.op]) return this.independent!Type;
			}else{
				if(strength[bt.op]==-2) return bt.complCombine(this).independent!Type;
				else if(strength[bt.op]==-1) return bt.imagCombine(this).independent!Type;
			}
			switch(strength[op]){
				case -2:
					return complCombine(bt).independent!Type;
				case -1: // imaginary types
					return imagCombine(bt).independent!Type;
				case 0:
					return null.independent!Type;
				case 4:
					return Type.get!uint().independent!Type;
				case 5:
					return Type.get!ulong().independent!Type;
				case 6:
					if(op==Tok!"float" && bt.op==Tok!"float") return this.independent!Type;
					else if(op!=Tok!"real" && bt.op!=Tok!"real") return Type.get!double().independent!Type;
					else return Type.get!real().independent!Type;
				default: assert(0);
			}
		}
		return super.combine(rhs);
	}

	// TODO: compress into a single template and two alias
	private BasicType imagCombine(BasicType bt)in{assert(strength[op]==-1);}body{
		if(strength[bt.op]==-1){
			if(op==Tok!"ifloat" && bt.op==Tok!"ifloat") return this;
			else if(op!=Tok!"ireal" && bt.op!=Tok!"ireal") return Type.get!idouble();
			else return Type.get!ireal();
		}
		// imaginary + complex
		if(strength[bt.op]==-2){
			if(op==Tok!"ifloat" && bt.op==Tok!"cfloat") return Type.get!cfloat();
			if(op!=Tok!"ireal" && bt.op!=Tok!"creal") return Type.get!cdouble();
			if(op==Tok!"ireal" || bt.op==Tok!"creal") return Type.get!creal();
		}
		// imaginary + 2's complement integer
		if(strength[bt.op]<6){
			if(op==Tok!"ifloat") return Type.get!cfloat();
			if(op==Tok!"idouble") return Type.get!cdouble();
			if(op==Tok!"ireal") return Type.get!creal();
		}
		// imaginary + 'real'
		if(op==Tok!"ifloat" && bt.op==Tok!"float") return Type.get!cfloat();
		if(op!=Tok!"ireal" && bt.op!=Tok!"real") return Type.get!cdouble();
		return Type.get!creal();
	}
	private BasicType complCombine(BasicType bt)in{assert(strength[op]==-2);}body{
		if(strength[bt.op]==-2){
			if(op==Tok!"cfloat" && bt.op==Tok!"cfloat") return this;
			else if(op!=Tok!"creal" && bt.op!=Tok!"creal") return Type.get!cdouble();
			else return Type.get!creal();
		}
		// complex + imaginary
		if(strength[bt.op]==-1){
			if(op==Tok!"cfloat" && bt.op==Tok!"ifloat") return Type.get!cfloat();
			if(op!=Tok!"creal" && bt.op!=Tok!"ireal") return Type.get!cdouble();
			if(op==Tok!"creal" || bt.op==Tok!"ireal") return Type.get!creal();
		}
		// complex + 2's complement integer
		if(strength[bt.op]<6){
			if(op==Tok!"cfloat") return Type.get!cfloat();
			if(op==Tok!"cdouble") return Type.get!cdouble();
			if(op==Tok!"creal") return Type.get!creal();
		}
		// complex + 'real'
		if(op==Tok!"cfloat" && bt.op==Tok!"float") return Type.get!cfloat();
		if(op!=Tok!"creal" && bt.op!=Tok!"real") return Type.get!cdouble();
		return Type.get!creal();
	}

	override IntRange getIntRange(){
		switch(op){
			mixin({
				string r;
				foreach(x;["dchar", "uint"])
					r~=mixin(X!q{case Tok!"@(x)": return IntRange(@(x).min,@(x).max,false);});
				foreach(x;["bool","byte","ubyte","char","short","ushort","wchar","int"])
					r~=mixin(X!q{case Tok!"@(x)": return IntRange(@(x).min,@(x).max,true);});
				return r;
			}());
			default: return super.getIntRange();
		}
	}
	override LongRange getLongRange(){
		switch(op){
			case Tok!"ulong": return LongRange(ulong.min,ulong.max,false);
			mixin({
				string r;
				foreach(x;["bool","byte","ubyte", "char","short","ushort","wchar","int","dchar","uint","long"])
					r~=mixin(X!q{case Tok!"@(x)": return LongRange(@(x).min,@(x).max,true);});
				return r;
			}());
			default: return super.getLongRange();
		}
	}

}


mixin template Semantic(T) if(is(T==ConstTy)||is(T==ImmutableTy)||is(T==SharedTy)||is(T==InoutTy)){

	private enum qual = T.stringof[0..$-2];

	/* directly create a semantically analyzed instance
	 */
	static Type create(Type next)in{
		assert(next.sstate == SemState.completed);
	}body{
		auto tt = mixin(`next.in`~qual~`Context()`);
		if(tt is next){
			assert(!mixin(`next.`~lowerf(qual)~`Type`));
			auto r = New!T(tt);
			r.ty = tt;
			r.sstate = SemState.completed;
			return r;
		}else return mixin(`tt.get`~qual)();
	}

	invariant(){assert(sstate < SemState.started || ty); mixin(_restOfInvariant);}
	Type ty; // the 'T' in 'qualified(T)', the "qualifyee"
	override void semantic(Scope sc){
		mixin(SemPrlg);
		ty=e.typeSemantic(sc);
		mixin(SemProp!q{e});
		Type r;
		static if(is(T==ConstTy)) r=ty.getConst();
		else static if(is(T==ImmutableTy)) r=ty.getImmutable();
		else static if(is(T==SharedTy)) r=ty.getShared();
		else static if(is(T==InoutTy)) r=ty.getInout();
		else static assert(0);

		sstate = SemState.begin;
		needRetry=false;
		r.semantic(sc);
		mixin(RewEplg!q{r});
	}

	static if(is(T==ConstTy)||is(T==ImmutableTy)||is(T==InoutTy))
		override bool isMutable(){return false;}
	else static if(is(T==SharedTy))
		override bool isMutable(){return ty.isMutable();}
	else static assert(0);


	/* some general notes:
	   the order of qualifiers is shared(inout(const(T))) or immutable(T) if
	   sstate == SemState.completed. 'create' and 'semantic' establish this dented invariant.
	   some of the code below relies on this order. it does not operate correctly on
	   incorrectly ordered input.
	 */
	private enum _restOfInvariant=q{ // TODO: fix this as soon as muliple invariants allowed
		import std.typetuple;
		alias TypeTuple!("ImmutableTy","SharedTy","InoutTy","ConstTy") Order;
		if(sstate == SemState.completed){
			foreach(x; Order){
				static if(!is(T==ImmutableTy)) if(x==T.stringof) break;
				assert(!mixin(`(cast()ty).is`~x)(), to!string(cast()ty));
			}
		}
	};

	static if(is(T==InoutTy)){
		override Type adaptTo(Type from, ref InoutRes res){
			if(auto imm = from.isImmutableTy()){
				res = mergeIR(res, InoutRes.immutable_);
			}else if(auto con = from.isConstTy()){
				assert(!con.ty.isInoutTy()); // normal form: inout(const(T))
				res = mergeIR(res, InoutRes.const_);
			}else if(auto sha = from.isSharedTy()){
				// information could be burried, eg shared(const(int))
				return adaptTo(sha.ty, res);
			}else if(auto ino = from.isInoutTy()){
				res = mergeIR(res, ino.ty.isConstTy() ?
				                   InoutRes.inoutConst :
				                   InoutRes.inout_);
			}else res = mergeIR(res, InoutRes.mutable);

			return ty.getTailInout().adaptTo(from.getHeadUnqual(), res).getInout();
		}
		override Type resolveInout(InoutRes res){
			assert(ty.resolveInout(res) is ty);
			final switch(res){
				case InoutRes.none, InoutRes.inout_:
					return this;
				case InoutRes.mutable:
					return ty;
				case InoutRes.immutable_:
					return ty.getImmutable();
				case InoutRes.const_:
					return ty.getConst();
				case InoutRes.inoutConst:
					return ty.getConst().getInout();
			}
		}
	}else{
		/* hand through adaptTo and resolveInout calls
		 */
		override Type adaptTo(Type from, ref InoutRes res){
			return mixin(`ty.getTail`~qual~`().adaptTo(from, res).get`~qual)();
		}
		override Type resolveInout(InoutRes res){
			return mixin(`ty.resolveInout(res).get`~qual)();
		}
	}

	override Dependent!void typeMatch(Type from){
		assert(!!from);
		static if(is(T==ConstTy)){
			if(auto imm = from.isImmutableTy()) from=imm.ty;
			else if(auto ccc = from.isConstTy()) from=ccc.ty;
			else if(auto ino = from.isInoutTy()) from=ino.ty;
		}else if(auto ccc = mixin(`from.is`~qual~`Ty()`)) from=ccc.ty;
		//mixin(`ty.getTail`~qual~`().typeMatch`)(from);
		mixin(TypeMatch!q{_;mixin(`ty.getTail`~qual~`()`), from});
		return indepvoid;
	}

	override bool hasPseudoTypes(){
		return ty.hasPseudoTypes();
	}

	override bool equals(Type rhs){
		if(auto d=mixin(`rhs.is`~T.stringof)()) return ty.equals(d.ty);
		return false;
	}

	override Dependent!bool implicitlyConvertsTo(Type rhs){
		// TODO: reference types, otherwise
		// getHeadUnqual never returns a qualified type ==> no recursion
		return getHeadUnqual().implicitlyConvertsTo(rhs.getHeadUnqual());
	}

	override Dependent!bool convertsTo(Type rhs){
		// TODO: reference types
		return getUnqual().convertsTo(rhs);
	}

	override Dependent!bool refConvertsTo(Type rhs, int num){
		// TODO: reference types
		if(this is rhs) return true.independent;
		if(auto d=mixin(`rhs.is`~T.stringof)()){
			static if(is(T==ConstTy) || is(T==ImmutableTy)){
				// const and immutable imply covariance
				return mixin(`ty.getTail`~qual)().refConvertsTo(mixin(`d.ty.getTail`~qual)(), 0);
			}else{
				// shared and inout do not imply covariance unless they are also const:
				auto nn = this is getConst() ? 0 : num;
				return mixin(`ty.getTail`~qual)().refConvertsTo(mixin(`d.ty.getTail`~qual)(),nn);
			}
		}
		static if(is(T==ImmutableTy)||is(T==InoutTy))if(num < 2){
			static if(is(T==ImmutableTy)){
				if(rhs is rhs.getConst()){
					// immutable(Sub)* implicitly converts to
					// [const|inout const|shared const|shared inout const](Super)*
					return ty.getTailImmutable().refConvertsTo(rhs.getHeadUnqual(), 0);
				}
			}else static if(is(T==InoutTy)){
				// inout(Sub)* implicitly converts to const(Super)*
				if(auto d=rhs.isConstTy()){
					return ty.inConstContext().getTailInout().refConvertsTo(d.ty.getTailConst(), 0);
				}
			}
		}
		return false.independent;
	}

	override Dependent!Type combine(Type rhs){
		// TODO: reference types
		if(this is rhs) return this.independent!Type;
		// special rules apply to basic types:
		if(rhs.isBasicType()) return getHeadUnqual().combine(rhs);
		if(auto r = mostGeneral(rhs).prop) return r;
		auto lhs = getHeadUnqual();
		rhs = rhs.getHeadUnqual();
		if(auto r = lhs.combine(rhs).prop) return r;
		return null.independent!Type;
	}

	override Dependent!Type refCombine(Type rhs, int num){
		// TODO: reference types
		if(auto r = refMostGeneral(rhs, num).prop) return r;
		if(num<2){
			static if(is(T==ConstTy)||is(T==ImmutableTy)){
				auto r = rhs.getConst();
				if(rhs is r) return null.independent!Type; // stop recursion
				return refCombine(r,num);
			}else{
				auto l=getConst(), r=rhs.getConst();
				if(this is l && rhs is r) return null.independent!Type; // stop recursion
				return l.refCombine(r,num);
			}
		}
		return null.independent!Type;
	}

	/* members
	 */

	override Scope getMemberScope(){ return getUnqual().getMemberScope(); }


	override ulong getSizeof(){return ty.getSizeof();}

	override IntRange getIntRange(){return ty.getIntRange();}
	override LongRange getLongRange(){return ty.getLongRange();}

	/* the following methods are overridden in order to keep the qualifier order straight
	 */

	override protected Type getConstImpl() {
		static if(is(T==ConstTy)||is(T==ImmutableTy)) return this;
		else static if(is(T==SharedTy)) return ty.getConst().getShared();
		else static if(is(T==InoutTy)) return ty.getConst().getInout();
		else static assert(0);
	}
	override protected Type getImmutableImpl(){
		static if(is(T==ImmutableTy)) return this;
		else return ty.getImmutable();
	}
	override protected Type getSharedImpl(){
		static if(is(T==ImmutableTy) || is(T==SharedTy)) return this;
		else return super.getSharedImpl();
	}

	static if(!is(T==ConstTy)){
		override protected Type getInoutImpl(){
			static if(is(T==InoutTy)||is(T==ImmutableTy)) return this;
			else static if(is(T==SharedTy)) return ty.getInout().getShared();
			else static assert(0);
		}
	}

	/* getHeadUnqual needs to tail-qualify the qualifyee
	 */
	override Type getHeadUnqual(){
		if(hunqualType) return hunqualType;
		return hunqualType=mixin(`ty.getHeadUnqual().getTail`~qual)();
	}

	override Type getUnqual(){
		if(unqualType) return unqualType;
		return unqualType=ty.getUnqual();
	}

	override Type getElementType(){ return getHeadUnqual().getElementType(); }

	override STC getHeadSTC(){
		return ty.getHeadSTC()|mixin("STC"~lowerf(qual));
	}


	/* tail-qualifying is done by tail-qualifying the qualifyee
	   and then head-qualifying back the result appropriately
	 */
	private static string __dgliteralTail(){ // TODO: maybe memoize this?
		string r;
		foreach(q;typeQualifiers){
			r~=mixin(X!q{
				override Type getTail@(upperf(q))(){
					return ty.getTail@(upperf(q))().get@(qual)();
				}
			});
		}
		return r;
	}
	mixin(__dgliteralTail());

	/* any part of the type may be transitively qualified by some
	   qualifier at most once. since immutable implies const (and
	   shared) and it is stronger than unqualified, immutable(inout(T-)-)
	   is simplified to immutable(T--)
	 */
	// TODO: analyze whether or not memoizing these is worthwhile
	override Type inConstContext(){
		static if(is(T==ConstTy)) return ty.inConstContext();
		else return mixin(`ty.inConstContext().get`~qual)();
	}
	override Type inImmutableContext(){
		return ty.inImmutableContext();
	}
	override Type inSharedContext(){
		static if(is(T==SharedTy)) return ty.inSharedContext();
		else return mixin(`ty.inSharedContext().get`~qual)();
	}
	override Type inInoutContext(){
		static if(is(T==InoutTy)) return ty.inInoutContext();
		else return mixin(`ty.inInoutContext().get`~qual)();
	}

private:
	Type hunqualType;
	Type unqualType;
}

/* helper for Semantic![PointerTy|DynArrTy|ArrayTy]
   creates the members getTail[Qualified] and in[Qualified]Context
   parameters:
     tail:    string evaluating to the tail of the type
     puthead: string evaluating to a member that puts the head back on the tail
 */
private mixin template GetTailOperations(string tail, string puthead){
	static string __dgliteralTailQualified(){// "delegate literals cannot be class members..."
		string r;
		foreach(q;typeQualifiers){
			r~=mixin(X!q{
				Type tail@(upperf(q))Type;
				override Type getTail@(upperf(q))(){
					if(tail@(upperf(q))Type) return tail@(upperf(q))Type;
					return tail@(upperf(q))Type=@(tail).get@(upperf(q))().@(puthead);
			    }
				override Type in@(upperf(q))Context(){ // TODO: analyze if memoizing worthwhile
					assert(@(tail)&&1);
					return @(tail).in@(upperf(q))Context().@(puthead);
				}
			});
		}
		return r;
	}
	mixin(__dgliteralTailQualified());
}

// TODO: make sure static arrays are treated like real value types
mixin template Semantic(T) if(is(T==PointerTy)||is(T==DynArrTy)||is(T==ArrayTy)){

	static if(is(T==ArrayTy)){
		static T create(Type next, long size)in{
			assert(next.sstate == SemState.completed);
		}body{
			auto r = New!T(next, size);
			r.ty = next;
			r.sstate = SemState.completed;
			return r;
		}
	}else{
		static T create(Type next)in{
			assert(next.sstate == SemState.completed);
		}body{
			auto r = New!T(next);
			r.ty = next;
			r.sstate = SemState.completed;
			return r;
		}
	}

	Type ty;
	override void semantic(Scope sc){
		mixin(SemPrlg);
		ty=e.typeSemantic(sc);
		mixin(SemProp!q{e});
		Type r;
		static if(is(T==ArrayTy)) r=ty.getArray(length);
		else r = mixin("ty.get"~T.stringof[0..$-2]~"()");

		mixin(RewEplg!q{r});
	}

	override Type adaptTo(Type from, ref InoutRes res){
		if(auto tt = mixin(`from.getHeadUnqual().is`~T.stringof)()){
			return mixin(`ty.adaptTo(tt.ty,res).`~puthead);
		}else return this;
	}
	override Type resolveInout(InoutRes res){
		return mixin(`ty.resolveInout(res).`~puthead);
	}

	override Dependent!void typeMatch(Type from){
		Type tt = from.getHeadUnqual().isPointerTy();
		// TODO: match static array dimension
		if(!tt) tt = from.getElementType();
		if(tt) mixin(TypeMatch!q{_; ty, tt});//ty.typeMatch(tt);
		return indepvoid;
	}
	override bool hasPseudoTypes(){
		return ty.hasPseudoTypes();
	}


	override bool equals(Type rhs){
		if(auto c=mixin(`rhs.is`~T.stringof)()){
			static if(is(T==ArrayTy)) if(c.length!=length) return false;
			return ty.equals(c.ty);
		}
		return false;
	}

	static if(is(T==ArrayTy)){
		override Dependent!bool implicitlyConvertsTo(Type rhs){
			if(auto t=super.implicitlyConvertsTo(rhs).prop) return t;
			return ty.getDynArr().implicitlyConvertsTo(rhs);
		}

	}

	override Dependent!bool convertsTo(Type rhs){
		if(auto t=super.convertsTo(rhs).prop) return t;
		rhs = rhs.getHeadUnqual();
		static if(is(T==PointerTy))
			return (rhs.isPointerTy() || rhs.isBasicType()).independent;
		else static if(is(T==DynArrTy))
			return (cast(bool)rhs.isDynArrTy()).independent;
		else return implicitlyConvertsTo(rhs);
	}

	// this adds one indirection for pointers and dynamic arrays
	override Dependent!bool refConvertsTo(Type rhs, int num){
		// dynamic and static arrays can implicitly convert to void[]
		static if(is(T==DynArrTy)||is(T==ArrayTy)){
			if(rhs.getUnqual() is Type.get!(void[])()){
				auto ell = getElementType(), elr = rhs.getElementType();
				auto stcr = elr.getHeadSTC(), stcl=getHeadSTC();
				if(auto t=ell.refConvertsTo(ell.getUnqual().applySTC(stcr),num+1).prop)
					return t;
			}
		}
		static if(is(T==ArrayTy))
			if(auto tt = rhs.isDynArrTy()){
				// intuition for num+1:
				// auto dynamic = fixedsize;
				// assert(dynamic.ptr is &fixedsize[0]);
				if(auto t=ty.refConvertsTo(tt.ty, num+1).prop)
					return t;
			}

		if(auto c=mixin(`rhs.is`~T.stringof)()){
			static if(is(T==ArrayTy))
				return c.length!=length?false.independent:ty.refConvertsTo(c.ty,num);
			else return ty.refConvertsTo(c.ty,num+1);
		}
		return super.refConvertsTo(rhs,num);
	}
	override Dependent!Type combine(Type rhs){
		if(auto r = mostGeneral(rhs).prop) return r;
		auto unqual = rhs.getHeadUnqual();
		return unqual.refCombine(this,0);
	}
	override Dependent!Type refCombine(Type rhs, int num){
		if(auto c=mixin(`rhs.is`~T.stringof)()){
			mixin(RefCombine!q{Type rcomb; ty, c.ty, num+!is(T==ArrayTy)});
			if(rcomb){
				static if(is(T==ArrayTy))
					if(c.length!=length)
						return rcomb.getDynArr().independent!Type;
				return mixin(`rcomb.`~puthead).independent!Type;
			}
		}
		return super.refCombine(rhs,num);
	}

	override Dependent!Type unify(Type rhs){
		if(auto c=mixin(`rhs.is`~T.stringof)()){
			static if(is(T==ArrayTy)) if(c.length!=length) return Type.init.independent;
			mixin(Unify!q{Type unf; ty, c.ty});
			if(unf) return mixin(`unf.`~puthead).independent!Type;
		}
		static if(is(T==PointerTy)){
			if(auto b = rhs.getFunctionTy()){
				auto a = getFunctionTy();
				if(!a) return null.independent!Type;
				mixin(Unify!q{Type c; a,b});
				if(c){
					assert(cast(FunctionTy)c);
					auto r = rhs.isDelegateTy() ? (cast(FunctionTy)cast(void*)c).getDelegate() : c.getPointer();
					return r.independent!Type;
				}
			}
		}
		return super.unify(rhs);
	}

	private enum puthead = "get"~(is(T==ArrayTy)?"Array(length)":typeof(this).stringof[0..$-2]~"()");
	mixin GetTailOperations!("ty", puthead);

	override Type getUnqual(){
		return mixin(`ty.getUnqual().`~puthead);
	}

	override ulong getSizeof(){
		// TODO: this is not true for all machines
		static if(is(T==PointerTy) || is(T==DynArrTy))
			auto s_ts = Type.get!Size_t().getSizeof();
		static if(is(T==PointerTy)) return s_ts;
		else static if(is(T==DynArrTy)) return s_ts * 2;
		else{
			static assert(is(T==ArrayTy));
			return length * ty.getSizeof();
		}
	}
	static if(is(T==PointerTy))
	override Dependent!Expression matchCallHelper(Scope sc, const ref Location loc, Type this_, Expression[] args, ref MatchContext context){
		if(auto ft=ty.getHeadUnqual().isFunctionTy()){
			auto rd=ft.matchCallHelper(sc, loc, this_, args, context);
			if(rd.value) rd.value = this; // valid for dependee is null and dependee !is null
			return rd;
		}
		return null.independent!Expression;
	}


	static if(is(T==ArrayTy) || is(T==DynArrTy)):
	override Type getElementType(){return ty;}
}

mixin template Semantic(T) if(is(T==NullPtrTy)){
	override Dependent!bool refConvertsTo(Type rhs, int num){
		if(!num && rhs.isPointerTy()) return true.independent;
		if(auto at=rhs.isAggregateTy())
			if(at.decl.isReferenceAggregateDecl())
				return true.independent;
		return super.refConvertsTo(rhs, num);
	}
	override Dependent!bool implicitlyConvertsTo(Type rhs){
		if(auto t=super.implicitlyConvertsTo(rhs).prop) return t;
		auto rhsu = rhs.getHeadUnqual();
		return (rhsu.isDynArrTy()
			|| rhsu is Type.get!EmptyArray()
			|| rhsu.isDelegateTy()).independent;
	}

	override ulong getSizeof(){
		// TODO: this is not true for all machines
		return Type.get!Size_t().getSizeof();
	}
}
mixin template Semantic(T) if(is(T==EmptyArrTy)){
	override Dependent!bool refConvertsTo(Type rhs, int num){
		if(!num){
			if(rhs.isDynArrTy()) return true.independent;
			if(auto arr = rhs.isArrayTy()) return (!arr.length).independent;
		}
		return super.refConvertsTo(rhs, num);
	}
	override Type getElementType(){
		assert(type is Type.get!void());
		return type;
	}

	override ulong getSizeof(){
		// TODO: this is not true for all machines
		return Type.get!Size_t().getSizeof() * 2;
	}
}


mixin template Semantic(T) if(is(T==TypeofExp)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(!f) f = e;
		f.weakenAccessCheck(AccessCheck.none);
		mixin(SemChld!q{f});
		mixin(FinishDeductionProp!q{f});
		//f = f.constFold(sc); // TODO: should this be done at all?
		if(f.isType()){
			sc.error(format("typeof argument '%s' is not an expression",e.loc.rep),e.loc);
			mixin(ErrEplg);
        }else e=f;

/+		if(!e.type){
			auto r=Type.get!void();
			mixin(RewEplg!q{r});
		}+/

		assert(!!f.type && f.type.sstate == SemState.completed,to!string(e)~" : "~to!string(f.type));

		auto r=f.type;
		mixin(RewEplg!q{r});
	}
private:
	Expression f; // semantically analyzed 'e', needed for nice error handling
}

mixin template Semantic(T) if(is(T==AggregateTy)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemEplg);
	}

	override Type checkVarDecl(Scope sc, VarDecl me){
		if(!decl.bdy){
			if(me.name)
				sc.error(format("%s '%s' has incomplete type '%s'", me.kind, me.name, this), me.loc);
			else
				sc.error(format("%s has incomplete type '%s'", me.kind, this), me.loc);
			return New!ErrorTy();
		}
		return this;
	}

	override AggregateScope getMemberScope(){
		return decl.asc;
	}

	override string toString(){
		TemplateInstanceDecl tmpl;
		if(auto nsts=cast(NestedScope)decl.scope_)
		if(auto tmps=cast(TemplateScope)nsts.parent)
			tmpl=tmps.tmpl;
		if(tmpl && decl.name.name is tmpl.name.name)
			return decl.name.name~"!("~join(map!(to!string)(tmpl.args),",")~")";
		return decl.name.name;
	}

	override Dependent!bool refConvertsTo(Type rhs, int num){
		if(this is rhs) return true.independent;
		if(!num){
			if(auto raggrd=decl.isReferenceAggregateDecl())
			if(auto at=rhs.isAggregateTy())
			if(auto atraggrd=at.decl.isReferenceAggregateDecl())
				return raggrd.isSubtypeOf(atraggrd);
		}
		return super.refConvertsTo(rhs, num);
	}

	override Dependent!Type combine(Type rhs){
		if(auto t=super.combine(rhs).prop) return t;
		return refCombine(rhs,0);
	}

	override Dependent!Type refCombine(Type rhs, int num){
		if(!num)
		if(auto cd1=decl.isClassDecl()){
			if(auto rat=rhs.isAggregateTy()){
				if(auto cd2=rat.decl.isClassDecl()){
					auto sup = cd1.commonSuperType(cd2);
					if(auto d=sup.dependee) return d.dependent!Type;
					if(sup.value) return sup.value.getType().independent!Type;
				}
			}
		}
		return super.refCombine(rhs,num);
	}
}


// statements

mixin template Semantic(T) if(is(T==Statement)){
	override void semantic(Scope sc){
		sc.error("feature not implemented",loc);
		sstate = SemState.error;
	}
}

mixin template Semantic(T) if(is(T==EmptyStm)){
	override void semantic(Scope sc){
		sstate = SemState.completed;
	}
}

mixin template Semantic(T) if(is(T==CompoundStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		//mixin(SemChld!q{s});
		size_t initial = current;
		foreach(i,ref x; s[initial..$]){
			mixin(SemChldPar!q{x});
			current = max(current, initial+1+i);
		}
		mixin(PropErr!q{s});
		mixin(SemEplg);
	}
	invariant(){assert(sstate!=SemState.completed || current == s.length);}
private:
	size_t current = 0; // points to the next child to be semantically analyzed
}

mixin template Semantic(T) if(is(T==BlockStm)){
	override void semantic(Scope sc){
		if(!mysc) mysc = New!BlockScope(sc);
		super.semantic(mysc);
	}
private:
	Scope mysc = null;
}

mixin template Semantic(T) if(is(T==LabeledStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(sstate == SemState.pre){ sc.insertLabel(this); sstate = SemState.begin; }
		mixin(SemChld!q{s});
		mixin(SemEplg);
	}
private:
	bool inserted = false;
}


mixin template Semantic(T) if(is(T==ExpressionStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChldExp!q{e});
		mixin(FinishDeductionProp!q{e});
		mixin(SemEplg);
	}
}

// TODO: those all should use implicit explicit conversion AST nodes
mixin template Semantic(T) if(is(T==IfStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(!tsc) tsc = New!BlockScope(sc);
		mixin(SemChldExpPar!q{sc=tsc;e});

		mixin(FinishDeduction!q{e});

		auto bl = Type.get!bool();
		if(e.sstate == SemState.completed){e=e.convertTo(bl); e.semantic(tsc);} // TODO: get rid of direct call
		if(e.sstate == SemState.completed) mixin(ConstFold!q{e});
		mixin(PropRetry!q{sc=tsc;e});

		mixin(SemChldPar!q{sc=tsc;s1});
		if(s2){
			if(!esc) esc = New!BlockScope(sc);
			mixin(SemChldPar!q{sc=esc;s2});
		}
		mixin(SemProp!q{sc=tsc;e});
		mixin(SemProp!q{sc=tsc;s1});
		mixin(SemEplg);
	}
private:
	BlockScope tsc, esc;
}


mixin template Semantic(T) if(is(T==BreakableStm)){ }
mixin template Semantic(T) if(is(T==LoopingStm)){ }

mixin template Semantic(T) if(is(T==WhileStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(!lsc){lsc = New!BlockScope(sc); lsc.setLoopingStm(this);}
		auto bl = Type.get!bool();
		mixin(SemChldExpPar!q{sc=lsc;e});
		mixin(FinishDeduction!q{e});
		if(e.sstate == SemState.completed){e=e.convertTo(bl);e.semantic(lsc);} // TODO: ditto
		if(e.sstate == SemState.completed) mixin(ConstFold!q{e});

		mixin(SemChld!q{sc=lsc;s});
		mixin(SemProp!q{sc=lsc;e});
		mixin(SemEplg);
	}
private:
	BlockScope lsc;
}

mixin template Semantic(T) if(is(T==DoStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(!lsc){lsc = New!BlockScope(sc); lsc.setLoopingStm(this);}
		auto bl = Type.get!bool();

		mixin(SemChldPar!q{sc=lsc;s});
		mixin(SemChldPar!q{e});// TODO: propose SemChld!q{sc=lsc;e}
		mixin(FinishDeduction!q{e});
		if(e.sstate == SemState.completed){e=e.convertTo(bl);e.semantic(lsc);} // TODO: get rid of direct call
		if(e.sstate == SemState.completed) mixin(ConstFold!q{sc=lsc;e});
		mixin(SemProp!q{sc=lsc;s});
		mixin(SemProp!q{e});
		mixin(SemEplg);
	}
private:
	BlockScope lsc;
}


mixin template Semantic(T) if(is(T==ForStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(!lscs1){lscs1 = New!BlockScope(sc);}
		if(s1) mixin(SemChldPar!q{sc=lscs1;s1});
		if(!lsc){ lsc = New!BlockScope(lscs1); lsc.setLoopingStm(this); }
		if(e1){
			mixin(SemChldExpPar!q{sc=lsc;e1});

			auto bl = Type.get!bool();
			mixin(FinishDeduction!q{e1});
			if(e1.sstate == SemState.completed){e1=e1.convertTo(bl);e1.semantic(lsc);}// TODO: ditto
			if(e1.sstate == SemState.completed) mixin(ConstFold!q{sc=lsc;e1});
			mixin(PropRetry!q{sc=lsc;e1});
		}
		if(e2){
			e2.semantic(lsc); // TODO: ditto
			if(e2.sstate == SemState.completed) mixin(ConstFold!q{sc=lsc;e2});
			mixin(PropRetry!q{sc=lsc;e2});
			mixin(FinishDeduction!q{e2});
		}
		mixin(SemChldPar!q{sc=lsc;s2});
		if(s1) mixin(PropErr!q{s1});
		if(e1) mixin(PropErr!q{e1});
		if(e2) mixin(PropErr!q{e2});
		mixin(PropErr!q{s2});
		mixin(SemEplg);
	}
private:
	BlockScope lscs1;
	BlockScope lsc;
}

mixin template Semantic(T) if(is(T==ForeachStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(!lsc){lsc = New!BlockScope(sc); lsc.setLoopingStm(this);}
		mixin(SemChld!q{aggregate});
		mixin(FinishDeductionProp!q{aggregate});
		auto ty = aggregate.type;
		// foreach over built-in arrays
		Type et = null;
		if(auto tt = ty.isArrayTy()) et = tt.ty;
		if(auto tt = ty.isDynArrTy()) et = tt.ty;
		if(et){
			if(vars.length>2){
				sc.error("at most two loop variables allowed for array foreach",
				         vars[0].loc.to(vars[$-1].loc));
				mixin(ErrEplg);
			}else{
				assert(vars.length);
				if(vars.length == 2 && !curparam){
					auto s_t = Type.get!Size_t();
					if(vars[0].rtype){
						vars[0].type = vars[0].rtype.typeSemantic(lsc);
						mixin(SemProp!q{sc=lsc;vars[0].rtype});
						if(!vars[0].type.equals(s_t)){ // TODO: This is a stub
							sc.error(format("invalid type '%s' for index variable '%s'", vars[0].rtype.loc.rep, vars[0].name.toString()), vars[0].rtype.loc);
							sstate = SemState.error;
						}
					}else vars[0].type = s_t;
					curparam++;
				}
				if(curparam < vars.length){
					if(vars[curparam].rtype){
						vars[curparam].type = vars[curparam].rtype.typeSemantic(lsc);
						mixin(SemProp!q{sc=lsc;vars[curparam].rtype});
						mixin(ImplConvertsTo!q{auto iconv; et, vars[curparam].type});
						if(!iconv){
							sc.error(format("cannot implicitly convert from element type '%s' to '%s'", et.toString(), vars[curparam].rtype.loc.rep),vars[curparam].rtype.loc);
							sstate = SemState.error;
						}
					}else vars[curparam].type = ty;
					curparam++;
				}
			}
		}
		// TODO: foreach over string types with automatic decoding
		// TODO: foreach over associative arrays
		// TODO: foreach over ranges
		// TODO: foreach with opApply
		// TODO: foreach over delegates
		// TODO: foreach over Tuples
		foreach(var; vars) var.semantic(lsc); // TODO: fix?
		//mixin(SemChld!q{scope=lsc, bdy}); // TODO: implement this
		bdy.semantic(lsc); // TODO: get rid of direct call
		mixin(SemProp!q{sc=lsc;bdy});
		mixin(PropErr!q{vars, aggregate});
		mixin(SemEplg);
	}

private:
	BlockScope lsc;
	size_t curparam=0;
}

mixin template Semantic(T) if(is(T==ReturnStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);

		if(e) mixin(SemChldExpPar!q{e});

		auto fun = sc.getFunction();
		assert(fun && fun.type,text(fun," ",fun?fun.type:null," ",sc," ",this));

		if(fun.type.hasUnresolvedReturn()){
			if(!e) fun.type.resolveReturn(Type.get!void());
			else if(e.sstate == SemState.completed && fun.sstate != SemState.error){
				fun.type.resolveReturn(e.type);
				mixin(RetryEplg);
			}else{
				fun.type.ret = New!ErrorTy();
				fun.type.sstate = SemState.error;
				fun.sstate = SemState.error;
				fun.needRetry = false;
				mixin(ErrEplg);
			}
		}else if(e){
			mixin(PropErr!q{e});
			if(fun.type.rret) mixin(PropErr!q{fun.type.rret});
			assert(!!fun.type.ret);
			mixin(PropErr!q{fun.type.ret});
			mixin(ImplConvertTo!q{e,fun.type.ret});
			// TODO: better error message if rvalue-ness is because of the implicit conv.
			if(fun.type.stc&STCref && !e.checkLvalue(sc,e.loc)) mixin(ErrEplg);
		}else if(fun.type.ret !is Type.get!void()){
			sc.error(format("non-void function '%s' should return a value",fun.name),loc);
			mixin(ErrEplg);
		}
		// TODO: auto ref
		isRefReturn = cast(bool)(fun.type.stc&STCref);
		if(isRefReturn && (assert(!!e),!e.checkLvalue(sc,e.loc))) mixin(ErrEplg);

		if(e&&!e.finishDeduction(sc)) mixin(ErrEplg);
		mixin(SemEplg);
	}

	bool isRefReturn;
}

mixin template Semantic(T) if(is(T==ContinueStm)||is(T==BreakStm)){
	private enum _which = is(T==ContinueStm)?"continue":"break";
	private enum _enc   = "loop"~(is(T==ContinueStm)?"":" or switch");
	private enum _name = is(T==ContinueStm)?"theLoop":"brokenOne";
	private enum _query = is(T==ContinueStm)?"LoopingStm":"BreakableStm";
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(!e){
			if(!mixin(_name)) mixin(_name) = mixin(`sc.get`~_query)();
			if(!mixin(_name)){
				sc.error("'"~_which~"' statement must be in "~_enc~" statement",loc);
				mixin(ErrEplg);
			}
		}else{
			if(!mixin(_name)){
				auto lstm = sc.lookupLabel(e);
				if(!lstm) goto Lerr;
				if(auto lp = mixin(`lstm.s.is`~_query)()) mixin(_name) = lp;
				else goto Lerr;
				if(!sc.isEnclosing(mixin(_name))) goto Lerr;
			}
		}
		mixin(SemEplg);
	Lerr:
		sc.error(format("enclosing label '%s' for "~_which~" statement not found",e.toString()),e.loc);
		mixin(ErrEplg);
	}
private:
	static if(is(T==ContinueStm)) LoopingStm theLoop;
	else static if(is(T==BreakStm)) BreakableStm brokenOne;
	else static assert(0);
}

mixin template Semantic(T) if(is(T==GotoStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		final switch(t) with(WhichGoto){
			case identifier:
				assert(cast(Identifier)e);
				sc.registerForLabel(this, cast(Identifier)cast(void*)e);
				break;
			case default_:
			case case_:
			case caseExp:
				super.semantic(sc); // TODO
		}
		mixin(SemEplg);
	}
	void resolveLabel(LabeledStm tgt)in{assert(t==WhichGoto.identifier);}body{
		target = tgt;
	}
private:
	LabeledStm target;
}


// declarations
mixin template Semantic(T) if(is(T==Declaration)){
	Scope scope_ = null;

	invariant(){assert(sstate != SemState.pre || !scope_, to!string(typeid(this)));}

	void pickupSTC(STC stc){
		this.stc|=stc;
	}

	void potentialInsert(Scope sc, Declaration decl){
		if(name) sc.potentialInsert(name, decl);
	}
	void potentialRemove(Scope sc, Declaration decl){
		if(name) sc.potentialRemove(name, decl);
	}


	// TODO: reduce DMD bug in presence of the out contract
	void presemantic(Scope sc){//out(result){
		//assert(result is this); // TODO: remove return type?
		//}body{ // insert into symbol table, but don't do the heavy processing yet
		if(sstate != SemState.pre) return;
		sstate = SemState.begin;
		if(!name){sc.error("feature "~to!string(typeid(this))~" not implemented",loc); sstate = SemState.error; return;} // TODO: obvious
		if(!sc.insert(this)){mixin(ErrEplg);}
	}

	void buildInterface(){ }

	override void semantic(Scope sc){
		if(sstate==SemState.pre) presemantic(sc);
		mixin(SemPrlg);
		mixin(SemEplg);
	}

	/* Returns true if the declaration has to be checked for accessibility at
	   the given access check level.
	 */
	bool needsAccessCheck(AccessCheck check)in{assert(check!=AccessCheck.init);}body{
		return !(stc&STCstatic) && check == AccessCheck.all;
	}

	Dependent!Declaration matchCall(Scope sc, const ref Location loc, Type this_, Expression[] args, ref MatchContext context){
		return null.independent!Declaration;
	}
	void matchError(Scope sc, Location loc, Type this_, Expression[] args){
		sc.error(format("%s '%s' is not callable",kind,name.toString()),loc);
	}

	Declaration matchInstantiation(Scope sc, const ref Location loc, Expression[] args){
		if(sc) sc.error(format("can only instantiate templates, not %s%ss",kind,kind[$-1]=='s'?"e":""),loc);
		return null;
	}

	Declaration matchIFTI(Scope sc, const ref Location loc, Type this_, Expression[] args, Expression[] funargs){
		if(sc) sc.error(format("%s '%s' is not a function template",kind, name.name),loc);
		return null;
	}

	// TODO: make OO instead of functional?
	static Dependent!bool isDeclAccessible(Declaration from, Declaration decl)in{
		assert(decl.sstate != SemState.pre);
	}body{
		// TODO: this check might be redundant
		if(decl.stc&STCstatic
		|| decl.stc&STCenum && decl.isVarDecl())
			return true.independent;

		// constructors have special lookup rules
		if(auto fd=decl.isFunctionDecl()){
			if(fd.isConstructor())
				return isDeclAccessible(from, fd.scope_.getDeclaration());
		}

		if(!decl.scope_){
			// parameters inside function types
			// do not have a scope
			assert(!!cast(Parameter)decl);
			return true.independent;
		}

		auto enc = decl.scope_.getDeclaration();
		if(!enc) return true.independent; // eg. delegate literals at module scope

		for(Declaration dl=from;;dl=dl.scope_.getDeclaration()){
			if(dl is null) return false.independent;
			if(dl is enc) return true.independent;
			if(auto raggr=dl.isReferenceAggregateDecl()){
				mixin(AggregateParentsInOrderTraversal!q{
					mixin(IsDeclAccessible!q{auto b; Declaration, parent, decl});
					if(b) return true.independent;
				});
			}
			if(from is enc) return (!from.isAggregateDecl()).independent;
			if(dl.stc & STCstatic) return false.independent;
			if(auto fn=dl.isFunctionDef()) fn.canBeStatic = false;
			// TODO: infer whether a template instantiation needs to be local or not
		}
		assert(0); // silence DMD. TODO: report bug
	}

	void nestedTemplateInstantiation(TemplateInstanceDecl decl){ assert(0,"TODO: nestedTemplateInstantiation for "~to!string(typeid(this))); }

	void nestedFunctionLiteral(FunctionDef def){ assert(0,"TODO: nestedDelegateLiteral for "~to!string(typeid(this))); }

	protected mixin template HandleNestedDeclarations(){
		override void nestedTemplateInstantiation(TemplateInstanceDecl decl){
			ndecls~=decl;
		}
		override void nestedFunctionLiteral(FunctionDef def){
			ndecls~=def;
		}
	private:
		Declaration[] ndecls;
	}

	int traverseInOrder(scope int delegate(Declaration) dg){ return dg(this); }

}

class TupleContext{
	VarDecl[] vds;
	Expression[] syms=null;
	AliasDecl tupleAlias=null;
}

mixin template Semantic(T) if(is(T==VarDecl)){
	Type type;

	TupleContext tupleContext;
	bool isField=false; // TODO: would rather not store these

	override void presemantic(Scope sc){
		if(sstate != SemState.pre) return;
		super.presemantic(sc);
		if(sstate == SemState.error) type = null; // TODO: why is this here?
		if(auto decl=sc.getDeclaration())
			if(auto aggr = decl.isAggregateDecl()){
				isField=true;
				aggr.layoutChanged();
			}
	}

	// used in Symbol to get the correct storage classes for the variable decl
	// TODO: this duplicates logic present in VarDecl.semantic
	enum SymbolResolve = q{
		vd.type.semantic(meaning.scope_);
		mixin(Rewrite!q{vd.type});
		type=vd.type;
		if(vd.type.sstate != SemState.error && vd.type.isTypeTuple()){
			mixin(MeaningSemantic); // TODO: does this generate invalid circ. dependencies?
			mixin(CircErrMsg);
			mixin(PropRetry!q{sc=meaning.scope_;meaning});
			if(meaning.sstate == SemState.completed){
				assert(!!vd.tupleContext && !!vd.tupleContext.tupleAlias);
				meaning = vd.tupleContext.tupleAlias;
				sstate = SemState.begin;
				semantic(sc);
				return;
			}
		}
		if(type.sstate == SemState.completed) type = type.applySTC(meaning.stc);
		else assert(type.needRetry||type.sstate == SemState.error);

		vd.stc|=type.getHeadSTC();
		// TODO: this is controversial, and should only be done for fields
		// if(vd.stc&(STCimmutable|STCconst) && vd.init) vd.stc|=STCstatic;
	};

	final bool willInterpretInit()in{assert(!!init);}body{
		return stc&(STCenum|STCstatic) || isField;
	}

	protected void defaultInit(){
		// convention: init is null means that the type should be zeroed out
		if(!init && type && type.sstate == SemState.completed){
			// default initializers
			if(auto aggr=type.getUnqual().isAggregateTy())
			if(auto strd=aggr.decl.isStructDecl()){
				init = New!StructConsExp(type,(Expression[]).init);
				init.loc = loc;
			}
		}

	}

	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(rtype){
			type=rtype.typeSemantic(sc);
			mixin(PropRetry!q{rtype});
		}

		if(!init) defaultInit();

		if(init){
			if(init.sstate!=SemState.completed){
				if(willInterpretInit()) init.prepareInterpret();
				init.initOfVar(this);
				mixin(SemChldExpPar!q{init});
			}
			// deduce type
			if(!type && init.sstate!=SemState.error) type=init.type;
		}else if(!rtype && !type){
			sc.error(format("initializer required for '%s' declaration",STCtoString(stc)),loc);
			mixin(ErrEplg);
		}
		if(sstate == SemState.pre && name){ // insert into scope
			presemantic(sc);
			mixin(SemCheck);
			sstate = SemState.begin;
		}

		if(!type||type.sstate==SemState.error||rtype&&rtype.sstate==SemState.error){
			type=null;
			mixin(ErrEplg);
		}

		assert(type.sstate == SemState.completed);

		if(auto tp = type.isTypeTuple()){
			alias tupleContext tc;
			auto len = tp.length;
			if(!tc) tc = New!TupleContext();
			ExpTuple et = null;
			TypeTuple tt = null;
			if(init){
				et=init.isExpTuple();
				if(!et) tt=init.type.isTypeTuple();
				if(et||tt){
					if(len!=(et?et.length:tt.length)){
						sc.error(format("tuple of %d elements cannot be assigned to tuple of %d elements",et.length,len),loc);
						mixin(ErrEplg);
					}
				}else{
					et = New!ExpTuple(sc, len, init);
					et.loc = init.loc;
					init = et;
					mixin(SemChldPar!q{init});
				}
				// better error message for type mismatch:
				if(!init.isVoidInitializerExp){
					mixin(ImplConvertsTo!q{bool iconv; init, type});
					if(!iconv) mixin(ImplConvertTo!q{init, type});
				}
				///
			}
			if(init) assert(tt || et && et.length==len && init.sstate == SemState.completed);
			// TODO: gc allocations
			if(!tc.vds){
				tc.vds = new VarDecl[cast(size_t)len];
				foreach(i, ref x;tc.vds){
					auto id  = name?New!Identifier("__tuple_"~name.name~"_"~to!string(i)):null;
					auto ini = init&&et?et.index(sc,init.loc,i):null;
					x = newVarDecl(stc, tp.index(sc,loc,i), id, ini);
					x.sstate = SemState.begin;
					x.loc = loc;
					x.scope_=scope_;
				}
			}
			mixin(SemChld!q{tc.vds});
			if(!tc.syms){
				tc.syms = new Expression[cast(size_t)len];
				foreach(i, ref x;tc.syms){
					auto sym = New!Symbol(tc.vds[i]);
					sym.accessCheck = AccessCheck.none;
					sym.loc = loc; // TODO: fix
					sym.scope_=scope_;
					x = sym;
				}
			}
			mixin(SemChld!q{tc.syms});
			if(!tc.tupleAlias){
				auto stpl = New!ExpTuple(sc,tc.syms); // TODO: can directly transfer ownership
				stpl.loc = loc;
				tc.tupleAlias = New!AliasDecl(STC.init, newVarDecl(STC.init, stpl, name, null));
				tc.tupleAlias.sstate = SemState.begin;
				tc.tupleAlias.loc = loc;
				tc.tupleAlias.scope_=scope_;
			}
			mixin(SemChld!q{tc.tupleAlias});
			assert(!tt||cast(CallExp)init);
			if(tt){
				sstate = SemState.completed;
				init = makeMultiReturn(cast(CallExp)cast(void*)init);
			}
			mixin(SemEplg); // Symbol will rewrite the meaning
		}

		{scope(exit) if(sstate==SemState.error) type=null;
			mixin(SemProp!q{type});
		}
		type = type.applySTC(stc);
		// add appropriate storage classes according to type
		stc |= type.getHeadSTC();
		// TODO: this is controversial, and should only be done for fields
		// if(stc&(STCimmutable|STCconst) && init) stc|=STCstatic;

		if(init){
			mixin(SemChld!q{init});
			/+if(!init.implicitlyConvertsTo(type)){
				sc.error(format("initializing '%s' from incompatible type '%s'",rtype.loc.rep,init.type.toString()),loc);
				mixin(ErrEplg);
			}+/
			if(willInterpretInit()){
				mixin(ImplConvertsTo!q{bool iconv;init, type});
				// type deduction should finish before interpretation
				if(!iconv) mixin(FinishDeductionProp!q{init});
				assert(init.sstate == SemState.completed, to!string(init));
				mixin(IntChld!q{init});
			}
			// order is significant: fully interpreted expressions might carry information
			// that allows more implicit conversions
			if(!init.isVoidInitializerExp()){
				mixin(ImplConvertTo!q{init,type});
			}
			if(!willInterpretInit()) mixin(FinishDeductionProp!q{init});
		}else if(stc&STCenum){
			sc.error("manifest constants must have initializers",loc);
			mixin(ErrEplg);
		}
		type = type.checkVarDecl(sc,this);
		mixin(SemProp!q{type});
		mixin(SemEplg);
	}

	override @property string kind(){
		return isField?"field":"variable";
	}

protected:
	VarDecl newVarDecl(STC stc, Expression rtype, Identifier name, Expression initializer){
		return New!VarDecl(stc,rtype,name,initializer);
	}
}

mixin template Semantic(T) if(is(T==Parameter)){
	override void presemantic(Scope sc){
		// NOTE: cannot rely on being in a function
		// parameters might be analyzed in the
		// template constraint scope as well
		if(!name.length) return;
		super.presemantic(sc);
	}

	final bool mustBeTypeDeduced(){
		return !type && !rtype && !init;
	}

	override void defaultInit(){} // parameters are not default-initialized

protected:
	override Parameter newVarDecl(STC stc, Expression rtype, Identifier name, Expression initializer){
		return New!Parameter(stc,rtype,name,initializer);
	}
}

mixin template Semantic(T) if(is(T==CArrayDecl)||is(T==CArrayParam)){

	override void semantic(Scope sc){
		while(postfix !is name){
			assert(!!cast(IndexExp)postfix, postfix.toString()~" "~name.toString());
			auto id = cast(IndexExp)cast(void*)postfix;
			postfix = id.e;
			id.e = rtype;
			rtype = id;
		}
		super.semantic(sc);
	}
}


mixin template Semantic(T) if(is(T==EmptyDecl)){
	override void presemantic(Scope sc){
		if(sstate != SemState.pre) return;
		sstate = SemState.begin;
		scope_ = sc;
	}
	override void semantic(Scope sc){
		mixin(SemEplg);
	}
}

mixin template Semantic(T) if(is(T==GenerativeDecl)){

}

mixin template Semantic(T) if(is(T==ConditionalDecl)){
	override void potentialInsert(Scope sc, Declaration decl){
		if(auto d = bdy.isDeclaration()) d.potentialInsert(sc, decl);
		if(els)if(auto d = els.isDeclaration()) d.potentialInsert(sc, decl);
	}
	override void potentialRemove(Scope sc, Declaration decl){
		if(auto d = bdy.isDeclaration()) d.potentialRemove(sc, decl);
		if(els)if(auto d = els.isDeclaration()) d.potentialRemove(sc, decl);
	}
}

mixin template Semantic(T) if(is(T==StaticIfDecl)){
	override void presemantic(Scope sc){
		if(sstate != SemState.pre) return;
		scope_=sc;
		sstate = SemState.begin;
		potentialInsert(sc, this);
	}

	private Statement evaluate(Scope sc){
		mixin(SemPrlg);
		scope(exit) if(!needRetry) potentialRemove(sc, this);
		cond.prepareInterpret();
		cond.prepareLazyConditionalSemantic();
		mixin(SemChld!q{cond});
		mixin(FinishDeductionProp!q{cond});

		mixin(ConvertTo!q{cond,Type.get!bool()});
		//cond = evaluateCondition(sc, cond);
		mixin(IntChld!q{cond});
		needRetry = false;
		if(cond.interpretV()){
			if(lazyDup) { lazyDup = false; bdy = bdy.ddup(); }
			if(auto d=bdy.isDeclaration()) d.pickupSTC(stc);
			if(auto decl = bdy.isDeclaration()) decl.presemantic(sc);
			return bdy;
		}else if(els){
			if(lazyDup) { lazyDup = false; els = els.ddup(); }
			if(auto d=els.isDeclaration()) d.pickupSTC(stc);
			if(auto decl = els.isDeclaration()) decl.presemantic(sc);
			return els;
		}else{
			lazyDup = false;
			mixin(SemEplg);
		}
	}

	override void buildInterface(){
		assert(!!scope_, text(this));
		auto r = evaluate(scope_).isDeclaration();
		if(r is this) return;
		assert(!!r);
		mixin(SemCheck);
		mixin(RewEplg!q{r});
	}

	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(sstate == SemState.pre) presemantic(sc);
		needRetry = false;
		auto res = evaluate(sc);
		if(res is this) return;
		assert(!!res);
		mixin(SemCheck);
		auto r=res;
		r.semantic(sc);
		mixin(RewEplg!q{r});
	}
private:
	bool lazyDup = false;
}


mixin template Semantic(T) if(is(T==StaticAssertDecl)){
	override void presemantic(Scope sc){
		if(sstate != SemState.pre) return;
		sstate = SemState.begin;
		scope_=sc;
	}
	override void semantic(Scope sc){
		mixin(SemPrlg);
		a[0].prepareInterpret();
		a[0].prepareLazyConditionalSemantic();
		if(a.length==2) a[1].prepareInterpret();

		mixin(SemChld!q{a});

		if(a.length<1){
			sc.error("missing arguments to static assert", loc);
			mixin(ErrEplg);
		}else if(a.length>2){
			sc.error("too many arguments to static assert", loc);
			mixin(ErrEplg);
		}

		mixin(SemChldExp!q{a[0]});

		foreach(x; a) mixin(FinishDeduction!q{x});
		mixin(PropErr!q{a});
		auto bl=Type.get!bool();
		mixin(ConvertTo!q{a[0],bl});
		mixin(IntChld!q{a[0]});

		if(!a[0].interpretV()){
			// work around finally block goto limitation...
			void printMessage(){
				sc.error(format("static assertion failure: '%s' is false",a[0].loc.rep), loc);
			}
			if(a.length == 1) printMessage();
			else try{
				mixin(SemChld!q{a[1]});
				if(!a[1].isType()){
					mixin(IntChld!q{a[1]});
					sc.error(a[1].interpretV().get!string(), loc);
				}else sc.error(a[1].toString(), loc);
			}finally if(sstate == SemState.error) printMessage();
			mixin(ErrEplg);
		}
		mixin(SemEplg);
	}
}

mixin template Semantic(T) if(is(T==AliasDecl)){
	override void semantic(Scope sc){
		if(sstate == SemState.pre) presemantic(sc);
		mixin(SemPrlg);
		if(!aliasee){
		if(auto vd = decl.isVarDecl()){
			if(vd.init){
				sc.error("alias declarations cannot have initializers",loc);
				mixin(ErrEplg);
			}
			aliasee = vd.rtype;
		}else if(auto fd = decl.isFunctionDecl()){
			aliasee = fd.type;
		}else assert(0);}

		aliasee.weakenAccessCheck(AccessCheck.none);
		mixin(SemChld!q{aliasee});
		mixin(FinishDeductionProp!q{aliasee}); // TODO: necessary?
		if(!aliasee.isSymbol() && !aliasee.isType() && !aliasee.isConstant() && !aliasee.isExpTuple()){
			auto ae = aliasee.isAddressExp();
			if(!ae||!ae.e.isSymbol()){
				sc.error("cannot alias an expression",loc);
				mixin(ErrEplg);
			}
		}
		mixin(SemEplg);
	}

	Declaration aliasedDecl()in{
		assert(sstate == SemState.completed);
	}body{
		if(auto sym = aliasee.isSymbol()){
			assert(!!sym.meaning);
			return sym.meaning;
		}
		return null;
	}

	Expression getAliasee(Scope sc, AccessCheck check, const ref Location loc)in{
		assert(sstate == SemState.completed);
		assert(!aliasee.isSymbol());
	}body{
		auto r=aliasee.clone(sc, loc);
		if(auto et=r.isExpTuple()) et.accessCheck=check;
		// templated delegate literal expressions
		if(auto add=r.isAddressExp()){
			if(auto sym=add.e.isSymbol())
				sym.accessCheck = check;
		}
		return r;
	}

private:
	Expression aliasee;
}


mixin template Semantic(T) if(is(T==BlockDecl)){
	override void potentialInsert(Scope sc, Declaration decl){
		foreach(x; decls) x.potentialInsert(sc, decl);
	}
	override void potentialRemove(Scope sc, Declaration decl){
		foreach(x; decls) x.potentialRemove(sc, decl);
	}

	override void presemantic(Scope sc){
		if(sstate!=SemState.pre) return;
		scope_ = sc;
		foreach(ref x; decls){
			x.pickupSTC(stc);
			x.presemantic(sc);
		}
		sstate = SemState.begin;
	}

	override void buildInterface(){
		foreach(ref x; decls){
			x.buildInterface();
			mixin(Rewrite!q{x});
			if(x.needRetry==2) mixin(PropRetry!q{sc=scope_;x});
		}
		foreach(x; decls) mixin(PropRetry!q{sc=scope_;x});
	}

	override void semantic(Scope sc){
		if(sstate == SemState.pre) presemantic(sc);
		mixin(SemPrlg);
		if(!addedToScheduler){
			foreach(x; decls)
				Scheduler().add(x, sc);
			addedToScheduler = true;
		}
		foreach(ref x; decls){
			x.semantic(sc);
			mixin(Rewrite!q{x});
		}
		foreach(x; decls) mixin(SemProp!q{x});

		//mixin(SemChld!q{decls});
		mixin(SemEplg);
	}

	override int traverseInOrder(scope int delegate(Declaration) dg){
		foreach(x; decls) if(auto r = x.traverseInOrder(dg)) return r;
		return 0;
	}

private:
	bool addedToScheduler = false;
}
mixin template Semantic(T) if(is(T==ReferenceAggregateDecl)){
	Expression[] rparents = null; // the expressions that the current parents originated from

	enum VtblState{
		fresh,
		inherited,
		overridden,
		needsOverride,
	}
	static struct VtblEntry{
		FunctionDecl fun;
		VtblState state;
	}
	struct Vtbl{
		VtblEntry[] vtbl;
		size_t[FunctionDecl] vtblIndex;
		@property size_t length(){ return vtbl.length; }
		Vtbl dup(){ return Vtbl(vtbl.dup, vtblIndex.dup); }
		void setInherited(){
			foreach(ref x;vtbl) x.state = VtblState.inherited;
		}
		void addFresh(FunctionDecl fun){
			vtblIndex[fun]=vtbl.length;
			vtbl~=VtblEntry(fun, VtblState.fresh);
		}
		void addOverride(FunctionDecl old, FunctionDecl fresh)in{
			assert(old in vtblIndex);
			auto oldSt = vtbl[vtblIndex[old]].state;
			assert(oldSt == VtblState.inherited || oldSt == VtblState.needsOverride);
		}body{
			size_t index = vtblIndex[old];
			vtblIndex.remove(old);
			vtblIndex[fresh]=index;
			vtbl[index]=VtblEntry(fresh, VtblState.overridden);
		}
		void needOverride(FunctionDecl old)in{
			if(old in vtblIndex){
				auto oldSt = vtbl[vtblIndex[old]].state;
				assert(oldSt == VtblState.inherited||oldSt == VtblState.needsOverride);
			}
		}body{
			if(old !in vtblIndex) return;
			static void doIt(ref VtblState st){ st = VtblState.needsOverride; }
			doIt(vtbl[vtblIndex[old]].state);
		}
		bool needsOverride(FunctionDecl fun){
			return fun in vtblIndex &&
				vtbl[vtblIndex[fun]].state == VtblState.needsOverride;
		}
		bool has(FunctionDecl fun){
			return !!(fun in vtblIndex);
		}
	}
	Vtbl vtbl;
	private Dependent!ClassDecl inheritVtbl(){
		ClassDecl parent;
		if(isClassDecl()){
			if(parents.length) findFirstNParents(1);
			if(parents.length){
				if(parents[0].needRetry||parents[0].sstate==SemState.error)
					return Dependee(parents[0], scope_).dependent!ClassDecl;
				if(rparents[0].sstate == SemState.error)
					return Dependee(rparents[0], scope_).dependent!ClassDecl;
				assert(parents[0].sstate==SemState.completed);
				assert(cast(AggregateTy)parents[0]&&cast(ReferenceAggregateDecl)(cast(AggregateTy)parents[0]).decl);
				auto parentc = cast(ReferenceAggregateDecl)cast(void*)(cast(AggregateTy)cast(void*)parents[0]).decl;
				if(auto cdecl=parentc.isClassDecl()){
					parent = cdecl;
					if(parent.needRetry||parent.sstate==SemState.error)
						return Dependee(parent, parent.scope_).dependent!ClassDecl;
					if(!vtbl.length){
						vtbl=parent.vtbl.dup;
						vtbl.setInherited();
					}
				}
			}
		}
		return parent.independent;
	}

	final ClassDecl parentClass(){
		if(!parents.length||!parents[0]||parents[0].sstate!=SemState.completed) return null;
		assert(!!cast(AggregateTy)parents[0]);
		return (cast(AggregateTy)cast(void*)parents[0]).decl.isClassDecl();
	}

	private mixin CreateBinderForDependent!("InheritVtbl","inheritVtbl");
	private Dependent!void addToVtbl(FunctionDecl decl){
		// inherit vtbl (need to wait until parent is finished with semantic)
		mixin(InheritVtbl!q{ClassDecl parent; this});
		OverloadSet set;
		if(!parent) goto Lfresh;
		auto ovscd = parent.asc.lookupHere(decl.name, null);
		assert(!ovscd.dependee);
		auto ovsc = ovscd.value;
		if(!ovsc||typeid(ovsc) is typeid(DoesNotExistDecl)) goto Lfresh;

		set = ovsc.isOverloadSet();
		if(!set) goto Lfresh;


		// need to provide new/aliased versions for ALL overloads
		if(!(decl.stc&STCnonvirtualprotection))
		foreach(x; set.decls){
			if(x.stc&STCstatic) continue;
			auto fun = x.isFunctionDecl();
			if(vtbl.needsOverride(fun)) break; // already performed operation for this set
			if(!fun) continue;
			vtbl.needOverride(fun);
		}

		if(decl.stc & STCoverride){
			mixin(DetermineOverride!q{auto ovr; set, decl});
			if(ovr){
				if(!vtbl.has(ovr)){
					decl.scope_.error("multiple overrides of the same function",decl.loc);
					mixin(SetErr!q{decl});
					return Dependee(ErrorDecl(), null).dependent!void;
				}
				vtbl.addOverride(ovr, decl);
				return indepvoid;
			}
		}
	Lfresh:
		if(!set && decl.stc & STCoverride){
			// this error message is duplicated in OverloadSet.determineOverride
			decl.scope_.error(format("method '%s' does not override anything", decl.name), decl.loc);
				mixin(SetErr!q{decl});
			return Dependee(ErrorDecl(), null).dependent!void;
		}
		if(!(decl.stc&STCnonvirtual)) vtbl.addFresh(decl);
		return indepvoid;
	}

	// invariant(){ foreach(x;parents) assert(x !is null); }

	final override void findParents(){
		findFirstNParents(parents.length);
	}
	private size_t knownParents = 0;
	invariant(){ assert(knownParents<=parents.length); }
	private void updateKnownParents(){
		foreach(x; parents[knownParents..$]){
			if((x.sstate != SemState.completed||x.needRetry) && x.sstate != SemState.error)
				break;
			knownParents++;
		}
	}
	// scopes need access to this. (maybe those should be moved here instead)
	public final void findFirstNParents(size_t n)in{assert(n<=parents.length);}body{
		if(n<=knownParents) return;
		alias scope_ sc;
		if(!rparents) rparents = parents.map!(a=>a.ddup).array; // uncontrolled gc allocation
		foreach(i,ref x; parents[knownParents..n]){
			auto ty=x.typeSemantic(sc);
			mixin(Rewrite!q{x});
			if(x.sstate == SemState.error) continue;
			if(ty){
				void check(Type ty){
					auto agg = ty.isAggregateTy();
					if(!agg && ty.sstate == SemState.completed ||
					   agg&&!agg.decl.isReferenceAggregateDecl()){
						sc.error("base specifier must name a class or interface",
						         rparents[knownParents+i].loc);
						x = New!ErrorTy();
					}
				}
				if(auto tpl=ty.isTypeTuple()) foreach(Type y;tpl) check(y);
				else check(ty);
			}
		}
		parents = Tuple.expand(parents, rparents);
		updateKnownParents(); // valid because only prior unknown parents can cause expansion
		assert(parents.length==rparents.length,text(parents," ",rparents));
	}

	final override Expression unresolvedParent()out(x){
		assert(!x||x.needRetry);
	}body{
		updateKnownParents();
		if(knownParents == parents.length) return null;
		return parents[knownParents];
/+		foreach(x;parents) if(x.needRetry) return x;
		return null;+/
	}

	/* Check validity of parents
	 - Detect circular inheritance
	 - Constrain max. number of base classes
	 - It is possible that circular template instance dependencies have prevented
	   the analysis to propagate errors in a template instance to the instantiation
	   expression located in a parent list. This function validates all error-free
	   parent locations by analyzing the expression they originated from again. At this
	   point, all the circular template instance dependencies have been resolved and
	   the result can be trusted.
	   TODOs:
	    * avoid duplicate CTFE-invocation for eg. the class C: D!(foo()) case
	 */

	final override void finishInheritance(){
		mixin CreateBinderForDependent!("CheckCircularInheritance", "checkCircularInheritance");
		mixin(CheckCircularInheritance!q{_;this});
		mixin(InheritVtbl!q{ClassDecl _; this});
		if(!parents.length) goto Lvtbl;
		assert(parents[0].sstate==SemState.error||!!cast(AggregateTy)parents[0]);
		bool hasExplicitBaseClass = false;
		if(parents[0].sstate != SemState.error){
			mixin(SemChld!q{sc=scope_;rparents[0]});
			hasExplicitBaseClass = !!(cast(AggregateTy)cast(void*)parents[0]).decl.isClassDecl();
		}else rparents[0].sstate = SemState.error;

		foreach(i, x;parents[1..$]){
			if(x.sstate == SemState.error){rparents[i].sstate=SemState.error; continue;}
			assert(x.sstate == SemState.completed);
			assert(!!cast(AggregateTy)x);
			if((cast(AggregateTy)cast(void*)x).decl.isClassDecl()){
				scope_.error(hasExplicitBaseClass         ?
				             "only one base class allowed":
				             "base class must appear first in the super type list",
				             rparents[1+i].loc,
				             );
				mixin(SetErr!q{rparents[1+i]});
			}
			mixin(SemChldPar!q{sc=scope_;rparents[1+i]});
		}
		bool[FunctionDecl] hiders;
	Lvtbl:
		enum SemRet = q{ return; };
		foreach(decl; &bdy.traverseInOrder){
			if(auto fd = decl.isFunctionDecl()){
				if(vtbl.has(fd)) continue;
				mixin CreateBinderForDependent!("AddToVtbl","addToVtbl");
				mixin(AddToVtbl!(q{_;this,fd},false));
			}
		}
		foreach(x; vtbl.vtbl){
			if(x.state == VtblState.needsOverride){
				auto ovscd = asc.lookupHere(x.fun.name, null);
				assert(!ovscd.dependee);
				auto ovsc = ovscd.value;
				assert(!!ovsc && typeid(ovsc) !is typeid(DoesNotExistDecl));
				auto ovs = ovsc.isOverloadSet();
				assert(!!ovs);
				FunctionDecl fun;
				foreach(y; ovs.decls){
					if(y.stc & (STCnonvirtualprotection|STCstatic))
						continue;
					if(auto fd=y.isFunctionDecl()){
						// if(!vtbl.has(fd)) continue;
						fun = fd;
						break;
					}
				}
				assert(!!fun);
				if(fun in hiders) continue;
				hiders[fun] = true;
				// TODO: investigate the issue further and give more helpful error message
				string hint = fun.stc & STCoverride ?
					" (either override all overloads or alias missing ones into the child class scope)":
					" (did you forget to specify 'override'?)";

				string kind = fun.stc & STCoverride ?" override":"";

				scope_.error(format("method%s '%s' illegally shadows a method in the parent class%s", kind, fun.name, hint),fun.loc);
				mixin(SetErr!q{fun});
			}
		}
		foreach(decl; &bdy.traverseInOrder) mixin(PropErr!q{decl});
		mixin(PropErr!q{rparents});
	}

	// TODO: make resolution faster (?)
	final Dependent!bool isSubtypeOf(ReferenceAggregateDecl rhs) in{
		assert(rhs!is null);
	}body{
		auto stack=SupertypeStack.init, dummy = false;
		return isSubtypeOfImpl(rhs, stack, dummy);
	}
	final Dependent!void checkCircularInheritance(){
		auto stack=SupertypeStack.init, dummy = false;
		if(auto d=isSubtypeOfImpl(null, stack, dummy).dependee) return d.dependent!void;
		return indepvoid;
	}
	private final Dependent!bool isSubtypeOfImpl(ReferenceAggregateDecl rhs, ref SupertypeStack stack, out bool failed){
		if(this is rhs) return true.independent;
		if(stack.has(this)){ failed=true; return false.independent; }
		stack.insert(this); scope(exit) stack.remove(this);
		findParents();
		foreach(i,ref x;parents){
			if(rparents[i].sstate == SemState.error) continue;
			ReferenceAggregateDecl rad;
			if(x.sstate == SemState.completed){
				assert(!!cast(AggregateTy)x&&cast(ReferenceAggregateDecl)(cast(AggregateTy)x).decl,text(typeid(x)," ",x.sstate));
				rad =
					cast(ReferenceAggregateDecl)cast(void*)
					(cast(AggregateTy)cast(void*)x)
					.decl;
			}else if(auto fe=x.isFieldExp()){
				//hack: peek into ongoing template instantiations
				if(fe.e2.meaning)
				if(auto rd = fe.e2.meaning.isReferenceAggregateDecl())
					rad = rd;
				if(!rad) continue;
			}else continue;
			assert(!!rad);
			auto t=rad.isSubtypeOfImpl(rhs,stack,failed).prop;
			if(failed){
				scope_.error("circular inheritance",rparents[i].loc);
				stack.showCycle(rad, scope_);
				mixin(SetErr!q{rparents[i]});
				failed = false;
				continue;
			}
			if(t) return t;
		}
		// TODO: template instances should wake up their dependees when meanings become clear
		if(auto x=unresolvedParent()) return multidep(cast(Node[])parents, scope_).dependent!bool;
		return false.independent;
	}

protected:
	// faster for super type stacks smaller than 17 elements.
	// this is usually the case
	struct SupertypeStack{
		void insert(ReferenceAggregateDecl decl){
			if(num<16) initial[num++]=decl;
			else overrun[decl]=num++;
		}
		void remove(ReferenceAggregateDecl decl){
			if(num<=16){
				assert(num&&initial[num-1]==decl);
				initial[--num]=null;
			}else{
				--num;
				assert(overrun[decl]==num);
				overrun.remove(decl);
			}
		}
		bool has(ReferenceAggregateDecl decl){
			foreach(x;initial[0..min(num,$)]) if(x is decl) return true;
			if(overrun !is null) return overrun.get(decl,-1)!=-1;
			return false;
		}
		void showCycle(ReferenceAggregateDecl start, Scope sc)in{
			assert(has(start));
		}body {
			// TODO: uncontrolled allocations
			auto arr = initial[0..min(num,$)].dup;
			auto k = overrun.keys, v = overrun.values;
			//import std.algorithm;
			sort!"a[1]<b[1]"(zip(k,v));
			arr~=k;
			arr=arr.find(start);
			foreach(x;retro(zip(arr,arr[0..$-1]))){
				alias util.all all;
				assert(all!(a=>cast(AggregateTy)a)(x[1].parents));
				auto rparent = zip(x[1].parents,x[1].rparents)
					.find!((a,b)=>(cast(AggregateTy)cast(void*)a[0]).decl is b)(x[0])
					.front[1];
				mixin(SetErr!q{rparent});
				sc.note("part of inheritance cycle",rparent.loc);
			}
		}
	private:
		ReferenceAggregateDecl[16] initial = null;
		size_t num = 0;
		size_t[ReferenceAggregateDecl] overrun;
	}
}

mixin template Semantic(T) if(is(T==ClassDecl)){

	// TODO: O(n+m*log n) least common ancestor possible?
	final Dependent!ClassDecl commonSuperType(ClassDecl rhs){
		SupertypeStack s1, s2;
		return commonSuperTypeImpl(rhs,s1,s2);
	}

	// braindead implementation
	final Dependent!ClassDecl commonSuperTypeImpl(ClassDecl rhs, ref SupertypeStack s1, ref SupertypeStack s2){
		if(this is rhs) return this.independent;
		if(s1.has(rhs)) return rhs.independent;
		if(s2.has(this)) return this.independent;
		if(!parents.length&&!rhs.parents.length) return null.independent!ClassDecl;
		if(parents.length) findFirstNParents(1);
		if(rhs.parents.length) rhs.findFirstNParents(1);

		if(parents.length&&
		   (parents[0].needRetry||parents[0].sstate == SemState.error))
			return Dependee(parents[0], scope_).dependent!ClassDecl;

		if(rhs.parents.length&&
		   (rhs.parents[0].needRetry||rhs.parents[0].sstate == SemState.error))
			return Dependee(rhs.parents[0], scope_).dependent!ClassDecl;

		assert((!parents.length||cast(AggregateTy)parents[0])&&
		       (!rhs.parents.length||cast(AggregateTy)rhs.parents[0]));

		auto c1 = !parents.length?this:
			(cast(AggregateTy)cast(void*)parents[0]).decl.isClassDecl();
		auto c2 = !rhs.parents.length?rhs:
			(cast(AggregateTy)cast(void*)rhs.parents[0]).decl.isClassDecl();

		if(!c1||!c2) return null.independent!ClassDecl;
		s1.insert(this); s2.insert(rhs);
		return c1.commonSuperTypeImpl(c2,s1,s2);
	}

}
mixin template Semantic(T) if(is(T==InterfaceDecl)){}
mixin template Semantic(T) if(is(T==ValueAggregateDecl)){}
mixin template Semantic(T) if(is(T==StructDecl)){}
mixin template Semantic(T) if(is(T==UnionDecl)){}


mixin template Semantic(T) if(is(T==AggregateDecl)){
	/* overridden in ReferenceAggregateDecl */
	protected void findParents(){ }
	protected Expression unresolvedParent(){ return null; }
	protected void finishInheritance()in{assert(!unresolvedParent());}body{ }

	override void presemantic(Scope sc){
		if(sstate != SemState.pre) return;
		if(auto aggr=sc.getAggregate())
			if(aggr.isValueAggregateDecl()||isValueAggregateDecl())
				stc|=STCstatic;

		super.presemantic(sc);

		scope_ = sc;
		// this is not a factory method because of a DMD bug.
		if(!asc) asc = isReferenceAggregateDecl()?
			         New!InheritScope(cast(ReferenceAggregateDecl)cast(void*)this) :
			         New!AggregateScope(this);

		if(bdy) bdy.presemantic(asc);
	}

	override void buildInterface(){
		if(sstate == SemState.completed || sstate == SemState.error || rewrite) return;
		if(bdy){
			bdy.buildInterface();
			mixin(PropRetry!q{sc=asc;bdy});
		}
		findParents();
		if(auto exp=unresolvedParent()) mixin(PropRetry!q{sc=scope_;exp});
		finishInheritance();
		mixin(SemCheck);
	}

	override void semantic(Scope sc){
		if(sstate == SemState.pre) presemantic(sc);
		mixin(SemPrlg);
		if(bdy) mixin(SemChld!q{sc=asc;bdy});
		findParents();
		if(auto exp=unresolvedParent()){mixin(PropRetry!q{exp});}
		needRetry=false;
		finishInheritance();
		mixin(SemCheck);
		mixin(SemEplg);
	}

	AggregateTy getType(){
		if(type) return type;
		return type=New!AggregateTy(this);
	}
	AggregateScope asc;

	mixin HandleNestedDeclarations;

	/* Called in presemantic of fields. This allows multiple different interpretations
	   of the same aggregate type during different CTFE executions, while the layout
	   can still be cached.
	 */

	void layoutChanged(){
		updateVersion();
		layoutKnown = false;
	}

	bool isLayoutKnown(){
		return layoutKnown;
	}

private:
	AggregateTy type;
	bool layoutKnown = false;
}

mixin template Semantic(T) if(is(T==Declarators)){
	override void presemantic(Scope sc){
		if(sstate!=SemState.pre) return;
		scope_=sc;
		foreach(ref x; decls) x.presemantic(sc);
		sstate=SemState.begin;
	}
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{decls});
		mixin(SemEplg);
	}

	override int traverseInOrder(scope int delegate(Declaration) dg){
		foreach(x; decls) if(auto r=x.traverseInOrder(dg)) return r;
		return 0;
	}
}

abstract class OverloadableDecl: Declaration{ // semantic node
	this(STC stc,Identifier name){super(stc,name);}
	override OverloadableDecl isOverloadableDecl(){return this;}
}

class OverloadSet: Declaration{ // purely semantic node

	debug private bool _matchedOne = false; // TODO: remove

	this(OverloadableDecl[] args...)in{
		assert(args.length);
		foreach(d; args) assert(!!d.scope_);
	}body{
		super(STC.init,args[0].name);
		foreach(d;args) add(d);
		sstate = SemState.begin; // do not insert into scope
	}
	this(Identifier name){super(STC.init,name);}
	void add(OverloadableDecl decl)in{
		assert(!decls.length||decls[0].name.name is decl.name.name);
		assert(!tdecls.length||tdecls[0].name.name is decl.name.name);
		debug assert(!_matchedOne, "TODO!"); // TODO:
	}body{
		if(auto td=decl.isTemplateDecl()) tdecls~=td;
		else decls~=decl;
	}

	/* accessibility of overloads is checked after they have been resolved
	 */
	override bool needsAccessCheck(AccessCheck check){ return false; }

	override string toString(){ return join(map!(to!string)(decls~cast(OverloadableDecl[])tdecls),"\n");}
	override OverloadSet isOverloadSet(){return this;}

	final bool isConstructor(){
		foreach(x;decls)
			if(auto fd=x.isFunctionDecl())
				return fd.isConstructor();
		foreach(x;tdecls)
			if(auto ep = x.iftiDecl())
				return ep.isConstructor();
		return false;
	}

	private static struct Matched{ // local structs cannot be qualified yet
		MatchContext context;      // TODO: move into matchCall
		FunctionDecl decl;
	}

	private mixin CreateBinderForDependent!("CanOverride","canOverride");
	// TODO: make this a public member function of function decl instead
	private static Dependent!bool canOverride(FunctionDecl fd, FunctionDecl fun){
		alias util.all all;
		import std.range;
		if(fd.stc & STCnonvirtual) return false.independent;
		// STC parent may be freely introduced, but will be here to stay
		bool mayOverride(STC parent, STC child){
			return !(fd.type.stc&parent) || fun.type.stc&child;
		}
		auto helper = Type.get!void.getPointer();
		if(fun.type.params.length == fd.type.params.length &&
		   !((fun.type.stc^fd.type.stc)&STCinvariantunderoverride) &&
		   // reuse the type system for determining valid type constructor overrides
		   // TODO: put these in the same implementation as the implicit conversion rules
		   // for function pointers and delegates ?
		   helper.applySTC(fd.type.stc&STCtypeconstructor)
		   .refConvertsTo(helper.applySTC(fun.type.stc&STCtypeconstructor), 0)
		   .force &&
		   mayOverride(STCsafe, STCsafe|STCtrusted) &&
		   mayOverride(STCpure, STCpure) &&
		   mayOverride(STCnothrow, STCnothrow) &&
		   mayOverride(STCdisable, STCdisable) &&
		   
			   // STCdeprecated ?
		   
		   all!(a=>a[0].type.equals(a[1].type) &&
		        !((a[0].stc^a[1].stc)&STCmattersforparamoverride))
		   (zip(fun.type.params, fd.type.params))
		){
			// TODO: resolve inout according to STC of parent
			//mixin(RefConvertsTo!q{bool rconv; fun.type.ret, fd.type.ret, 0});
			return fun.type.ret.refConvertsTo(fd.type.ret,0);
		}
		return false.independent;
	}

	/* find a function decl that may override fun, or return null
	 */
	Dependent!FunctionDecl findOverrider(FunctionDecl fun){
		// TODO: multi-dep
		// TODO: both const and non-const may override non-const
		// TODO: in this case, the non-const overload is to be preferred!
		foreach(ref decl; decls){
			auto fd = decl.isFunctionDecl();
			if(!fd) continue;
			mixin(CanOverride!q{auto co; OverloadSet, fun, fd});
			if(co) return fd.independent;
		}
		return null.independent!FunctionDecl;
	}

	/* find the function decl that fun overrides, or display an error and return null
	 */
	Dependent!FunctionDecl determineOverride(FunctionDecl fun){
		size_t num = 0;
		foreach(ref decl; decls){
			decl.semantic(decl.scope_);
			mixin(Rewrite!q{decl});
			auto fd=decl.isFunctionDecl();
			if(!fd) continue;
			if(fd.needRetry||fd.sstate == SemState.error)
				return Dependee(fd,fd.scope_).dependent!FunctionDecl;// TODO: depend just on type
			mixin(CanOverride!q{auto covr; OverloadSet, fd, fun});
			if(covr) swap(decl, decls[num++]);
		}

		//dw((cast(FunctionDecl)decls[0]).type.params.map!(a=>a.type)[0].equals(fun.type.params.map!(a=>a.type)[0]));
		if(!num){
			// this error message is duplicated in OverloadSet.determineOverride
			fun.scope_.error(format("method '%s' does not override anything", fun.name), fun.loc);
		}else{
			if(fun.type.stc&STCconst)
				thisSTCIsBetter!"a.type.stc"(cast(FunctionDecl[])decls, STCconst, num);
			if(num == 1) return (cast(FunctionDecl)cast(void*)decls[0]).independent;
			fun.scope_.error("method override is ambiguous", fun.loc);
			foreach(i;0..num) fun.scope_.note("candidate overridden function", decls[i].loc);
		}
		mixin(SetErr!q{fun});
		return null.independent!FunctionDecl;
	}

	private final void thisSTCIsBetter(alias str, R)(R stcr, STC stc, ref size_t num){
		auto s(ElementType!R a){ return mixin(str); }
		alias util.any any;
		bool found = false;
		foreach(x; stcr[0..num]) if((s(x)&stc)==stc){found=true; break; }
		if(!found) return;
		//if(any!((a)=>!!(s(a)&stc))(stcr)){
		for(size_t i=0;i<num;i++)
			if((s(stcr[i])&stc)!=stc)
				swap(stcr[i], stcr[--num]);
			//}
	}

	override Dependent!Declaration matchCall(Scope sc, const ref Location loc, Type this_, Expression[] args, ref MatchContext context){
		debug _matchedOne = true;

		if(!tdecls.length){
			if(decls.length == 1) return decls[0].matchCall(sc, loc, this_, args, context);
		}else return New!FunctionOverloadMatcher(this, loc, this_, args).independent!Declaration;

		auto matches = new Matched[decls.length]; // pointless GC allocation
		foreach(i,decl; decls){
			if(decl.sstate == SemState.error){
				auto fd=decl.isFunctionDecl();
				if(!fd||fd.type.sstate == SemState.error)
					return Dependee(decl,decl.scope_).dependent!Declaration;
			}
			mixin(MatchCall!q{auto matched; decls[i], null, loc, this_, args, matches[i].context});
			assert(!matched||cast(FunctionDecl)matched);
			matches[i].decl = cast(FunctionDecl)cast(void*)matched;
		}

		// TODO: some work is lost if this kicks in. significant?
		mixin(DetermineMostSpecialized!q{FunctionDecl r; this, matches, this_, context});

		if(!r) foreach(a;args)
		if(auto ae = a.isAddressExp())
		if(ae.isUndeducedFunctionLiteral()){
			return New!FunctionOverloadMatcher(this, loc, this_, args).independent!Declaration;
		}
		return r.independent!Declaration;
	}

	final Dependent!FunctionDecl determineMostSpecialized(Matched[] matches, Type this_, out MatchContext context)in{
		alias util.all all;
		//assert(all!(_=>!_.decl||_.decl.sstate!=SemState.error)(matches));
		assert(matches.length<cast(size_t)-1);
	}body{
		cand = altCand = null;
		foreach(ref m; matches) if(m.decl is null) m.context.match = Match.none;

		auto best = reduce!max(Match.none, map!(_=>_.context.match)(matches));
		if(best == Match.none){
			context.match = Match.none;
			return FunctionDecl.init.independent;
		}
		//TODO: the following line causes an ICE, reduce.
		//auto bestMatches = matches.partition!(_=>_.context.match!=best)();
		//auto numBest = bestMatches.length;
		size_t numBest = 0;
		for(size_t i=0;i<matches.length;i++){
			if(matches[i].context.match==best)
				swap(matches[numBest++], matches[i]);
		}
		if(this_){
			STC hstc = this_.getHeadSTC();
			if(hstc&STCconst) thisSTCIsBetter!"a.decl.stc"(matches, STCconst, numBest);
			if(hstc&STCinout) thisSTCIsBetter!"a.decl.stc"(matches, STCinout, numBest);
			if(hstc&STCimmutable){
				thisSTCIsBetter!"a.decl.stc"(matches, STCimmutable, numBest);
				thisSTCIsBetter!"a.decl.stc"(matches, STCconst|STCinout, numBest);
			}
		}
		assert(numBest);
		if(numBest == 1){
			context = matches[0].context;
			return matches[0].decl.independent;
		}
		auto bestMatches = matches[0..numBest];
		// find the most specialized match
		size_t candidate = 0;
		foreach(i, match; bestMatches[1..$]){
			// if there is a declaration that is at least as specialized
			// then it cannot be the unique best match
			//if(match.decl.atLeastAsSpecialized(bestMatches[candidate].decl))
			mixin(AtLeastAsSpecialized!q{bool alas; match.decl, bestMatches[candidate].decl});
			if(alas) candidate = i+1;
		}
		swap(bestMatches[0], bestMatches[candidate]);
		
		scope(exit){
			context = bestMatches[0].context;
			cand = bestMatches[0].decl;
		}

		foreach(i, match; bestMatches[1..$]){
			//if(!cand.atLeastAsSpecialized(match.decl)
			//|| match.decl.atLeastAsSpecialized(bestMatches[0].decl)){
			mixin(AtLeastAsSpecialized!q{bool alas1; bestMatches[0].decl, match.decl});
			mixin(AtLeastAsSpecialized!q{bool alas2; match.decl, bestMatches[0].decl});
			if(alas1){
				// inout functions are less specialized
				if(bestMatches[0].context.inoutRes==InoutRes.none&&match.context.inoutRes!=InoutRes.none)
					continue;
				if(alas2 && bestMatches[0].context.inoutRes!=InoutRes.none&&match.context.inoutRes==InoutRes.none){
					swap(bestMatches[0], bestMatches[i+1]);
					continue;
				}
				// matching static the right way is better
				if(!(bestMatches[0].decl.stc&STCstatic) != !this_ && !(match.decl.stc&STCstatic) == !this_)
					continue;
				if(!(bestMatches[0].decl.stc&STCstatic) == !this_ && !(match.decl.stc&STCstatic) != !this_){
					swap(bestMatches[0], bestMatches[i+1]);
					continue;					
				}
			}
			if(!alas1||alas2){
				// at least two identically good matches
				altCand = match.decl;
				return FunctionDecl.init.independent;
			}
		}
		return bestMatches[0].decl.independent;
	}

	static Dependent!void eliminateLessSpecializedTemplateMatches(Matched[] tmatches){
		foreach(ref m; tmatches) if(m.decl is null) m.context.match = Match.none;
		auto best = reduce!max(Match.none, map!(_=>_.context.match)(tmatches));

		if(best == Match.none) return indepvoid;

		TemplateDecl cand = null;
		size_t cpos;
		foreach(i,c; tmatches){
			if(c.context.match!=best) continue;
			cand = c.decl.extractTemplateInstance().parent;
			cpos = i;
			break;
		}
		if(!cand) return indepvoid;
		foreach(i,c; tmatches[cpos+1..$]){
			if(c.context.match!=best) continue;
			auto altCand = c.decl.extractTemplateInstance().parent;
			//if(altCand.atLeastAsSpecialized(cand)) { cand = altCand; }
			mixin(AtLeastAsSpecialized!q{bool alas; altCand, cand});
			if(alas) { cand = altCand; }
		}
		foreach(ref c; tmatches){
			if(c.context.match!=best) continue;
			auto altCand = c.decl.extractTemplateInstance().parent;
			// if(!altCand.atLeastAsSpecialized(cand)) { c.decl = null; }
			mixin(AtLeastAsSpecialized!q{bool alas; altCand, cand});
			if(!alas) { c.decl = null; }
		}
		return indepvoid;
	}

	static Dependent!void eliminateLessSpecializedTemplateInstances(TemplateInstanceDecl[] insts){
		auto best = reduce!max(Match.none, map!(_=>_?_.match:Match.none)(insts));

		if(best == Match.none) return indepvoid;

		TemplateDecl cand = null;
		size_t cpos;
		foreach(i,ref c; insts){
			if(!c) continue;
			if(c.match!=best) { c=null; continue; }
			cand = c.parent;
			cpos = i;
			break;
		}
		if(!cand) return indepvoid;
		foreach(i,c; insts[cpos+1..$]){
			if(!c) continue;
			if(c.match!=best) { c=null; continue; }
			auto altCand = c.parent;
			// if(altCand.atLeastAsSpecialized(cand)) { cand = altCand; }
			mixin(AtLeastAsSpecialized!q{bool alas; altCand, cand});
			if(alas) { cand = altCand; }
		}
		foreach(ref c; insts){
			if(!c) continue;
			if(c.match!=best) { c=null; continue; }
			auto altCand = c.parent;
			// if(!altCand.atLeastAsSpecialized(cand)) { c = null; }
			mixin(AtLeastAsSpecialized!q{bool alas; altCand, cand});
			if(!alas) { c = null; }
		}
		return indepvoid;
	}


	private FunctionDecl cand; // TODO: somewhat fragile, maybe better to just recompute
	private FunctionDecl altCand;
	final override void matchError(Scope sc, Location loc, Type this_, Expression[] args){
		if(count == 1) return (decls.length?decls[0]:tdecls[0]).matchError(sc,loc,this_,args);
		if(altCand is null){
			sc.error(format("no matching function for call to '%s(%s)'",name,join(map!"a.type.toString()"(args),",")), loc);
			foreach(decl; decls){
				if(auto fdef = decl.isFunctionDecl())
					if(fdef.type.sstate == SemState.error) continue;
				sc.note(format("candidate %s not viable", decl.kind), decl.loc); // TODO: say why
			}
		}else{
			assert(cand !is altCand);
			// TODO: list all of the most specialized functions
			sc.error(format("call to '%s' is ambiguous",name), loc);
			sc.note("candidate function",cand.loc);
			sc.note("candidate function",altCand.loc);
		}
	}

	override Declaration matchInstantiation(Scope sc, const ref Location loc, Expression[] args){
		if(tdecls.length==0) return null; // TODO: error message
		if(tdecls.length==1) return tdecls[0].matchInstantiation(sc, loc, args);
		return New!TemplateOverloadMatcher(this, loc, args);
	}

	final void instantiationError(Scope sc, const ref Location loc, TemplateInstanceDecl[] insts, Expression[] args){
		size_t c=0;
		foreach(x;insts) if(x) c++;
		assert(c!=1);
		if(!c){
			sc.error(format("no matching template for instantiation '%s!(%s)'",name,join(map!"a.toString()"(args),",")),loc);
			foreach(i, tdecl; tdecls){
				if(tdecl.sstate == SemState.error) continue;
				sc.note("candidate template not viable", tdecl.loc); // TODO: say why
			}
		}else{
			sc.error(format("instantiation of template '%s' is ambiguous", name), loc);
			foreach(i, tdecl; tdecls){
				if(!insts[i]||tdecl.sstate == SemState.error) continue;
				sc.note("candidate template",tdecl.loc);
			}
		}
	}

	override Declaration matchIFTI(Scope sc, const ref Location loc, Type this_, Expression[] args, Expression[] funargs){
		if(tdecls.length==1) return tdecls[0].matchIFTI(sc, loc, this_, args, funargs);
		return New!FunctionOverloadMatcher(this, loc, this_, args, funargs);
	}

	override @property string kind(){
		if(count==1) return decls.length?decls[0].kind:tdecls[0].kind;
		return "overload set";
	}

	public final @property size_t count(){ return decls.length + tdecls.length; }

// private: // TODO: introduce again
	OverloadableDecl[] decls;
	TemplateDecl[] tdecls;
}

// TODO: should those be nested classes of OverloadSet? Silly indentation...
abstract class SymbolMatcher: Declaration{
	OverloadSet set;
	Expression[] args;
	MatchContext context; // will be picked up by Symbol

	this(OverloadSet set, const ref Location loc, Expression[] args){
		super(set.stc,set.name);
		this.set=set;
		this.args=args;
		this.loc=loc;
	}

	mixin DownCastMethod;
}

class TemplateOverloadMatcher: SymbolMatcher{
	Declaration[] insts;
	this(OverloadSet set, const ref Location loc, Expression[] args){
		super(set, loc, args);
		// TODO: gc allocation
		insts = new Declaration[](set.tdecls.length);
		foreach(i, ref x; insts) x=set.tdecls[i].matchInstantiation(null, loc, args);
		mixin(RetryEplg);
	}
	override void semantic(Scope sc_){
		{alias sc_ sc;mixin(SemPrlg);}
		foreach(ref x; insts){
			if(!x) continue;
			{Scope sc=null;mixin(SemChldPar!q{x});}
			assert(!!cast(TemplateInstanceDecl)x);
			if(x.sstate == SemState.error) x = null;
			assert(!x||(cast(TemplateInstanceDecl)x).completedMatching);
		}
		OverloadSet.eliminateLessSpecializedTemplateInstances(cast(TemplateInstanceDecl[])insts);
		size_t c = 0;
		foreach(x; insts) if(x) c++;
		if(c==1) foreach(r; insts) if(r) mixin(RewEplg!q{r});
		if(sc_) set.instantiationError(sc_, loc, cast(TemplateInstanceDecl[])insts, args);
		mixin(ErrEplg);
	}
}


/* This class matches function calls of the form fun( ), (first constructor)
   in which case it resolves into a function declaration upon success.
   (this implements the matchCall return value interface.)

   as well as function calls of the form fun!( )( ), in which case it resolves
   into the template declaration upon success.
   (this implements the matchIFTI return value interface.)

   It makes sense to use the same implementation for those two operations,
   because they need to exhibit very similar behaviour.
 */

class FunctionOverloadMatcher: SymbolMatcher{

	Type this_;

	UnaryExp!(Tok!"&")[][] literals;
	Declaration[] iftis;
	// match the eponymous declaration
	// if it was not determined by IFTI.
	Expression[] eponymous;

	size_t[] positions;
	GaggingScope gscope;


	this(OverloadSet set, const ref Location loc, Type this_, Expression[] args)in{
		assert(set.decls.length>1||set.tdecls.length>0);
	}body{
		this.this_=this_;
		super(set, loc, args);
		// TODO: GC allocations
		iftis = new Declaration[](set.tdecls.length);
		foreach(i, ref x; iftis) x=set.tdecls[i].matchIFTI(null, loc, this_, templArgs, args);

		size_t numfunclit;
		foreach(a;args)
			if(auto ae = a.isAddressExp())
				if(ae.isUndeducedFunctionLiteral())
					numfunclit++;
		literals = new UnaryExp!(Tok!"&")[][](set.decls.length+1, numfunclit);
		positions = new size_t[numfunclit];

		size_t i=0;
		foreach(pos,a;args){
			if(auto ae = a.isAddressExp()){
				if(ae.isUndeducedFunctionLiteral()){
					// (not very cache friendly for huge number of function literal args
					// but that is not a case worth optimizing for)
					foreach(j;0..set.decls.length)
						literals[j][i] = ae.ddup();
					literals[$-1][i] = ae;
					positions[i]=pos;
					i++;
				}
			}
		}
		mixin(RetryEplg);
	}

	bool matchATemplate = false;
	Expression[] templArgs = [];

	this(OverloadSet set, const ref Location loc, Type this_, Expression[] templArgs, Expression[] args){
		matchATemplate = true;
		this.templArgs = templArgs;
		this(set, loc, this_, args);
	}

	TemplateInstanceDecl waitFor = null;
	FunctionDecl rewriteIfOk = null;

	override void semantic(Scope sc_){
		{alias sc_ sc;mixin(SemPrlg);}
		if(waitFor){
			alias sc_ sc;
			if(waitFor.sstate != SemState.started){
				mixin(SemChld!q{sc=waitFor.scope_;waitFor});
			}
			assert(!!rewriteIfOk);
			auto r=rewriteIfOk;
			mixin(RewEplg!q{r});
		}

		if(!gscope) gscope = New!GaggingScope(sc_);

		assert(iftis.length == set.tdecls.length);
		foreach(i, ref x; iftis){
			if(!x) continue;
			if(eponymous.length && eponymous[i]) continue;

			if(!x.isTemplateInstanceDecl()
			|| !(cast(TemplateInstanceDecl)cast(void*)x).completedMatching){
				x.semantic(null);
				mixin(PropRetry!q{sc=sc_;x});
				if(x.sstate == SemState.error) continue;
			}

			assert(!!cast(TemplateInstanceDecl)x);
			auto inst = cast(TemplateInstanceDecl)cast(void*)x;
			assert(!!inst.completedMatching);
			if(!inst.finishedInstantiation()) inst.finishInstantiation(false);

			auto fd = inst.iftiDecl();
			if(!fd){
				// if(!matchATemplate) continue; // TODO: do we want this?
				if(inst.sstate != SemState.completed && inst.sstate != SemState.started){
					if(inst.isGagged()) inst.ungag();
					inst.startAnalysis();
					x.semantic(sc_);
				}
				mixin(SemProp!q{sc=sc_;x}); // TODO: show where the problem happened
				fd = inst.iftiDecl();
				if(!fd){
					// TODO: gc allocation
					if(!eponymous.length) eponymous = new Expression[](iftis.length);
					// this creates identifiers without location, as we don't want those
					// to show up in circular dependency traces
					// TODO: accessCheck?
					eponymous[i]=New!(BinaryExp!(Tok!"."))(New!Symbol(x), New!Identifier(x.name.name));
					continue;
				}
			}
			assert(!!fd);

			fd.analyzeType();
			//mixin(PropRetry!q{fd.type});
			if(auto nr=fd.type.needRetry) { needRetry = nr; return; }
		}

		// resolve the eponymous declarations that are not determined by IFTI.
		foreach(ref x; eponymous) if(x){
				x.semantic(gscope);
				// mixin(PropRetry!q{sc=gscope;x});
				mixin(SemProp!q{sc=gscope;x});
				auto sym = x.isSymbol();
				if(!sym || !sym.meaning.isFunctionDecl()){
					//x=x.matchCall(null, loc, args);
					{alias sc_ sc; mixin(MatchCall!q{x; x, null, loc, args});}
					if(!x) continue;
					mixin(PropRetry!q{sc=null;x});
				}
			}

		debug set._matchedOne = true;
		OverloadSet.Matched[] matches, tmatches;
		if(!matchATemplate){
			//matches = determineFunctionMatches(); // pointless GC allocation
			alias sc_ sc; mixin(DetermineFunctionMatches!q{matches; this});
			foreach(l1;literals[0..$-1]) foreach(ref l2;l1){mixin(SemChldPar!q{sc=gscope;l2});}
		}

		MatchContext tcontext;
		//tmatches=determineTemplateMatches();
		{alias sc_ sc;mixin(DetermineTemplateMatches!q{tmatches; this});}

		// TODO: error handling
		FunctionDecl t,r;
		//auto t=set.determineMostSpecialized(tmatches, tcontext);
		{alias sc_ sc;mixin(DetermineMostSpecialized!q{t; set, tmatches, this_, tcontext});}
		auto cand = set.cand, altCand = set.altCand;
		//auto r=set.determineMostSpecialized(matches, context);
		{alias sc_ sc;mixin(DetermineMostSpecialized!q{r; set, matches, this_, context});}

		TemplateInstanceDecl inst;

		if(tcontext.match>context.match && t){
			r=t;
			context = tcontext;
			inst = r.extractTemplateInstance();
			if(sc_&&inst.isGagged){
				inst.ungag();
				inst.startAnalysis();
			}

			if(matchATemplate){mixin(RewEplg!q{inst});}
		}
		// TODO: could re-use the function literal arguments of the most specialized function
		if(!r){
			if(!set.cand && !set.altCand || tcontext.match>context.match)
				set.cand = cand, set.altCand = altCand;
			// TODO: more adequate error message in the matchATemplate case
			if(sc_) set.matchError(sc_, loc, this_, args);
			mixin(ErrEplg);
		}else{
			if(inst&&inst.sstate != SemState.completed){
				waitFor = inst;
				rewriteIfOk = r;
			}else mixin(RewEplg!q{r});
		}
	}
private:
	mixin CreateBinderForDependent!("DetermineFunctionMatches","determineFunctionMatches");
	mixin CreateBinderForDependent!("DetermineTemplateMatches","determineTemplateMatches");
	Dependent!(OverloadSet.Matched[]) determineFunctionMatches(){
		enum SemRet = q{ return (OverloadSet.Matched[]).init.independent; };
		auto matches = new set.Matched[set.decls.length];   // pointless GC allocations
	    trymatch: foreach(i,decl; set.decls){
			if(decl.sstate == SemState.error){
				auto fd=decl.isFunctionDecl();
				if(!fd||fd.type.sstate == SemState.error)
					mixin(ErrEplg);
			}
			adjustArgs(args, i);
			foreach(a; args) if(a.sstate == SemState.error) continue trymatch;
			//auto matched=set.decls[i].matchCall(null, loc, args, matches[i].context);
			mixin(MatchCall!q{auto matched; set.decls[i], null, loc, this_, args, matches[i].context});
			assert(!matched||cast(FunctionDecl)matched);
			matches[i].decl = cast(FunctionDecl)cast(void*)matched;
			if(matches[i].decl){
				convertLiterals(gscope, args, matches[i].decl);
				if(hasErrors(args)) matches[i].decl=null;
			}
		}
		restoreArgs(args);
		return matches.independent;
	}

	Dependent!(OverloadSet.Matched[]) determineTemplateMatches()in{
		assert(set.tdecls.length == iftis.length);
	}body{
		MatchContext tcontext;
		auto tmatches = new set.Matched[set.tdecls.length]; // pointless GC allocation
		foreach(i,x; iftis){
			if(!x||x.sstate == SemState.error) continue;
			assert(!!cast(TemplateInstanceDecl)x);
			auto inst = cast(TemplateInstanceDecl)cast(void*)x;
			auto fd = inst.iftiDecl();

			if(!fd){
				if(eponymous.length<=i || !eponymous[i]) continue;
				assert(eponymous[i].sstate == SemState.completed && cast(Symbol)eponymous[i]);
				auto sym = (cast(Symbol)cast(void*)eponymous[i]);
				fd = sym.meaning.isFunctionDecl();
			}else{
				if(fd.type.sstate == SemState.error) continue;
				//fd=fd.matchCall(null, loc, args, tcontext);
				mixin(MatchCall!q{auto tmp; fd, null, loc, this_, args, tcontext});
				assert(!tmp||cast(FunctionDecl)tmp);
				fd = cast(FunctionDecl)cast(void*)tmp;
			}
			if(!fd) continue;
			assert(fd.type.sstate == SemState.completed, text(fd.type.sstate));

			tmatches[i].decl = fd;
			tmatches[i].context = tcontext;
		}
		OverloadSet.eliminateLessSpecializedTemplateMatches(tmatches);
		return tmatches.independent;
	}

	void adjustArgs(Expression[] args, size_t j){
		foreach(k,i;positions) args[i] = literals[j][k];
	}
	void restoreArgs(Expression[] args){
		adjustArgs(args, literals.length-1);
	}
	bool hasErrors(Expression[] args){
		foreach(i;positions) if(args[i].sstate == SemState.error) return true;
		return false;
	}
	void convertLiterals(Scope sc, Expression[] args, FunctionDecl decl){
		foreach(i;positions){
			if(args[i].sstate == SemState.error) continue;
			if(auto ae=args[i].isAddressExp()){
				if(ae.isUndeducedFunctionLiteral()){
					if(decl.type.params[i].type){
						args[i] = args[i].implicitlyConvertTo(decl.type.params[i].type);
						args[i].semantic(sc);
						mixin(Rewrite!q{args[i]});
						mixin(FinishDeduction!q{args[i]});
						auto meaning=args[i];
					}
				}
			}
		}
	}
}




mixin template Semantic(T) if(is(T==FunctionDecl)){

	final bool isConstructor(){
		return name.name == "this";
	}

	/* this is general enough to be in Declaration,
	   but it is at the moment not needed for anything
	   else than function declarations. therefore it
	   is declared here in order not to clutter the vtables
	 */
	TemplateInstanceDecl extractTemplateInstance(){
		assert(!!cast(NestedScope)scope_);
		assert(!!cast(TemplateScope)(cast(NestedScope)scope_).parent);
		auto tsc = cast(TemplateScope)cast(void*)(cast(NestedScope)cast(void*)scope_).parent;
		assert(!!tsc.tmpl);
		return tsc.tmpl;
	}


	final public void propagateSTC(){
		// TODO: constructors shouldn't pick up some of those
		// TODO: what to do about @property?
		enum mask = function{
			STC r;
			// TODO: ToTuple is a workaround, is there a bug here?
			foreach(x;ToTuple!(functionSTC~attributeSTC))
				static if(x!="@disable") r|=mixin("STC"~x);
			return r;
		}();
		type.stc|=mask&stc;
	}

	void analyzeType(){ type.semantic(scope_); }

	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(sstate == SemState.pre) presemantic(sc);
		propagateSTC();
		if(type.hasAutoReturn()){
			sc.error("function body required for return type inference",loc);
			mixin(ErrEplg);
		}
		mixin(SemChld!q{type});
		mixin(SemEplg);
	}
	private bool isMemberFunction(){
		if(!isConstructor()){
			if(auto decl=scope_.getDeclaration()) return !!decl.isAggregateDecl();
		}else{
			// constructors are logically members of the enclosing scope
			auto decl=scope_.getDeclaration();
			if(!decl||!decl.isAggregateDecl()) return false;
			if(auto decl2=decl.scope_.getDeclaration)
				return !!decl2.isAggregateDecl();
		}
		return false;
	}
	override bool needsAccessCheck(AccessCheck check){
		if(check==AccessCheck.memberFuns) return isMemberFunction();
		return super.needsAccessCheck(check);
	}

	// TODO: would like Dependent!FunctionDecl for return type
	override Dependent!Declaration matchCall(Scope sc, const ref Location loc, Type this_, Expression[] args, ref MatchContext context){
		enum SemRet = q{ return this.independent!Declaration; };
		// semantically analyze the type if necessary
		type.semantic(scope_); // TODO: get rid of direct call
		//mixin(SemProp!q{type});
		if(auto nr=type.needRetry) { needRetry = nr; mixin(SemRet); }
		mixin(PropErr!q{type});
		mixin(MatchCallHelper!q{auto r; type, sc, loc, this_, args, context});
		return (r ? this : Declaration.init).independent;
	}

	Dependent!bool atLeastAsSpecialized(FunctionDecl rhs)in{
		assert(type.sstate == SemState.completed, text(type.sstate," ",type.needRetry));
		assert(rhs.type.sstate == SemState.completed, text(rhs.type.sstate," ",rhs.type.needRetry));
	}body{
		MatchContext dummy;
		// GC allocations, unneeded
		// TODO: allocate this on the stack
		auto pt = new Expression[](type.params.length);
		foreach(i,x; type.params) pt[i] = new StubExp(x.type,!!(x.stc&STCbyref));
		auto aggr = scope_.getAggregate();
		auto this_ = aggr ? aggr.getType().applySTC(stc) : null;

		// TODO: reduce DMD bug
		/+auto pt = array(map!(function Expression (_)=>
		                     new StubExp(_.type,!!(_.stc&STCbyref)))(type.params));+/

		mixin(MatchCall!q{auto rr; rhs, null, loc, this_, pt, dummy});
		assert(!rr||cast(FunctionDecl)rr);
		auto r=cast(FunctionDecl)cast(void*)rr;
		assert(!r||r.type.sstate == SemState.completed);
		// prefer function definitions to their own forward declarations
		if(r && !isFunctionDef() && rhs.isFunctionDef() && type.equals(rhs.type)
		   && stc == rhs.stc && scope_ is rhs.scope_) // TODO: consider linkage
			return false.independent;
		return (cast(bool)r).independent;
	}

	override void matchError(Scope sc, Location loc, Type this_, Expression[] args){
		alias util.any any; // TODO: file bug
		if(args.length > type.params.length
		|| any!(_=>_.init is null)(type.params[args.length..type.params.length])){
			sc.error(format("too %s arguments to %s '%s'",args.length<type.params.length?"few":"many", kind, signatureString()[0..$-1]),loc);
			sc.note("declared here",this.loc);
			return;
		}
		int num=0;
		InoutRes inoutRes;
		if(this_&&stc&STCinout) inoutRes = irFromSTC(this_.getHeadSTC());

		auto at = new Type[args.length];
		foreach(i,p; type.params){
			at[i] = p.type.adaptTo(args[i].type, inoutRes);
		}
		foreach(ref x;at) x = x.resolveInout(inoutRes);
		
		auto compatd=!this_?true.independent:
			this_.refConvertsTo(
			    this_.getHeadUnqual()
			    .applySTC(type.stc&STCtypeconstructor)
			    .resolveInout(inoutRes),
			    0
			);
		if(!compatd.dependee&&!compatd.value) num++;

		foreach(i,p; type.params){
			auto iconvd = args[i].implicitlyConvertsTo(at[i]);
			if(!iconvd.dependee && !iconvd.value) num++;
		}
		if(num>1){
			sc.error(format("incompatible argument types (%s)%s to %s '%s'", join(map!"a.type.toString()"(args),","),this_?STCtoString(this_.getHeadSTC()):"",kind,signatureString()[0..$-1]),loc);
			sc.note("declared here",this.loc);
		}else{
			if(!compatd.value){
				auto hstc = this_.getHeadSTC();
				auto fstc = type.stc&STCtypeconstructor;
				// TODO: this allocates
				if(isConstructor){
					auto hstcstr=hstc?"'"~STCtoString(hstc)~"'-qualified":"unqualified";
					auto fstcstr=fstc?"'"~STCtoString(fstc)~"'-qualified":"unqualified";
					auto n1 = hstcstr[0]=='u'||hstcstr[1].among('a','e','i','o','u')?"n":"";
					auto n2 = fstcstr[0]=='u'||fstcstr[1].among('a','e','i','o','u')?"n":"";
					
					sc.error(format("cannot construct a%s %s object using a%s %s constructor",n1,hstcstr,n2,fstcstr), loc);
				}else{
					auto hstcstr=hstc?"qualified '"~STCtoString(hstc)~"'":"unqualified";
					auto fstcstr=fstc?"'"~STCtoString(fstc)~"'":"unqualified";

					sc.error(format("'this' reference is %s, but %s is required", hstcstr, fstcstr), loc);
				}
					
			}
			foreach(i,p; type.params){
				void displayNote(){
					if(p.name) sc.note(format("while matching function parameter '%s'",p.name),p.loc);
					else sc.note("while matching function parameter",p.loc);
				}
				if(!(p.stc & STCbyref)){
					auto iconvd = args[i].implicitlyConvertsTo(at[i]);
					if(!iconvd.dependee && !iconvd.value){
						if(args[i].sstate == SemState.error) continue;
						// trigger consistent error message
						args[i].implicitlyConvertTo(at[i]).semantic(sc);
						displayNote();
						break;
					}
				}else if(p.stc&STCref){

					if(!args[i].checkLvalue(sc, args[i].loc)){
						displayNote();
						break;
					}
					auto irconvd = args[i].type.refConvertsTo(p.type,1);
					if(!irconvd.dependee && !irconvd.value){
						sc.error(format("incompatible argument type '%s' for 'ref' parameter of type '%s'",args[i].type.toString(),p.type.toString()),args[i].loc);
						displayNote();
						break;
					}
				}else{// if(p.stc&STCout){
					assert(p.stc&STCout);
					if(!args[i].checkMutate(sc, args[i].loc)){
						displayNote();
						break;
					}
					auto irconvd = p.type.refConvertsTo(args[i].type,1);
					if(!irconvd.dependee && !irconvd.value){
						sc.error(format("incompatible argument type '%s' for 'out' parameter of type '%s'", args[i].type, p.type),args[i].loc);
						displayNote();
						break;
					}
				}
			}
			
		}
	}


	final TemplateDecl templatizeLiteral()in{
		assert(sstate == SemState.pre);
		size_t nump = 0;
		assert(type.hasUnresolvedParameters());
	}body{
		type.reset();

		size_t nump = 0;
		foreach(x;type.params) if(x.mustBeTypeDeduced()) nump++;
		// TODO: gc allocations
		TemplateParameter[] tparams = new TemplateParameter[nump];
		immutable static string namebase = "__T";
		size_t j=-1;
		// TODO: can the scope be kept clean by using some tricks?
		foreach(i,ref x; tparams){
			while(!type.params[++j].mustBeTypeDeduced()) {}
			string name = namebase~to!string(i+1);
			auto which = WhichTemplateParameter.type;
			x = New!TemplateParameter(which, Expression.init,
			                          New!Identifier(name),
			                          Expression.init, Expression.init);

			type.params[j].rtype = New!Identifier(name);
		}

		auto tmplname = name.name;

		// TODO: GC allocation
		name.name~="Impl";

		auto uexp   = New!(UnaryExp!(Tok!"&"))(New!Identifier(name.name));
		uexp.brackets++;

		auto alias_ = New!AliasDecl(STC.init, New!VarDecl(STC.init,uexp,New!Identifier(tmplname),Expression.init));

		static class FunclitTemplateDecl: TemplateDecl{
			this(STC stc, Identifier name, TemplateParameter[] prm, BlockDecl b){
				super(false,stc,name,prm,Expression.init,b);
			}
			// OO FTW!
			override FunctionDecl iftiDecl(){
				assert(!!cast(FunctionDecl)bdy.decls[0]);
				return cast(FunctionDecl)cast(void*)bdy.decls[0];
			}
		}

		auto t=New!FunclitTemplateDecl(stc&STCstatic, New!Identifier(tmplname), tparams,
		                        New!BlockDecl(STC.init,[cast(Declaration)this,alias_]));

		t.loc = loc;
		return t;
	}
}

mixin template Semantic(T) if(is(T==FunctionDef)){

	override void analyzeType(){
		assert(!!scope_);
		if(!fsc){
			fsc = New!FunctionScope(scope_, this);
			foreach(p; type.params){
				if(p.sstate == SemState.pre) p.sstate = SemState.begin;
				if(p.name) if(!fsc.insert(p)) p.sstate = SemState.error;
			}
		}

		foreach(x; type.params){
			x.semantic(fsc);
			assert(!x.rewrite);
			if(auto nr=x.needRetry){
				Scheduler().await(this, x, fsc);
				type.needRetry = nr; return;
			}
		}
		type.semantic(scope_);
		if(type.needRetry) Scheduler().await(this, type, scope_);
	}

	override void semantic(Scope sc){
		mixin(SemPrlg);
		propagateSTC();
		if(sstate == SemState.pre){
			presemantic(sc); // add self to parent scope
			if(sstate == SemState.error) needRetry=false;
		}
		assert(sstate == SemState.begin || sstate == SemState.started);
		bool reset = sstate == SemState.begin;
		sstate = SemState.started;
		scope(exit) if(reset&&sstate == SemState.started) sstate = SemState.begin;
		analyzeType();
		if(auto nr=type.needRetry) { needRetry = nr; return; }
		mixin(PropErr!q{type});

		if(type.sstate == SemState.error) sstate = SemState.error, needRetry=false;

		mixin(SemChldPar!q{sc=fsc; bdy});

		if(type.hasUnresolvedReturn()){
			type.resolveReturn(Type.get!void());
		}
		foreach(gto;&fsc.unresolvedLabels){
			assert(cast(Identifier)gto.e);
			if(auto lbl = fsc.lookupLabel(cast(Identifier)cast(void*)gto.e))
				gto.resolveLabel(lbl);
			else{
				sc.error(format("use of undeclared label '%s'",gto.e.toString()), gto.e.loc);
				sstate = SemState.error;
			}
		}

		mixin(PropErr!q{});
		mixin(PropErr!q{type, bdy});
		if(deduceStatic && canBeStatic) stc |= STCstatic;
		mixin(SemEplg);
	}

	mixin HandleNestedDeclarations;

	/* specifies whether or not to deduce the 'static' qualifier
	   this is equivalent to the assertion that the function definition
	   is given as a function literal.
	 */

	bool deduceStatic;
	bool canBeStatic = true;

	final void addContextPointer() in{
		assert(sstate == SemState.completed);
		assert(deduceStatic);
		assert(stc&STCstatic);
	}body{
		assert(canBeStatic);
		stc&=~STCstatic;
		canBeStatic=false;
	}
private:
	FunctionScope fsc;
}

mixin template Semantic(T) if(is(T==PragmaDecl)){
	override void presemantic(Scope sc){
		if(sstate != SemState.pre) return;
		if(auto b=bdy.isDeclaration()) b.presemantic(sc);
		sstate = SemState.begin;
	}
	int c;
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(args.length<1){sc.error("missing arguments to pragma",loc); mixin(ErrEplg);}
		if(auto id=args[0].isIdentifier()){
			bool intprt = true;
			switch(id.name){
				case "__p":
					intprt = false;
					goto case;
				case "msg":
					if(args.length<2){if(bdy)mixin(SemChld!q{bdy}); mixin(SemEplg);}
					//foreach(ref x; args[1..$]) x = x.semantic(sc);
					//mixin(SemChldPar!q{args[1..$]});
					auto a = args[1..$];
					foreach(x; a) x.prepareInterpret();
					foreach(ref x;a){
						mixin(SemChldPar!q{x});
						mixin(FinishDeduction!q{x});
					}
					mixin(PropErr!q{a});
					foreach(ref x; a)
						if(!x.isType() && !x.isExpTuple() && intprt){
							mixin(IntChld!q{x});
						}

					// TODO: this should use the scope's error handler for output
					import std.stdio;
					// if(!sc.handler.showsEffect) stderr.write("(gagged:) ");
					foreach(x; a)
						if(!x.isType() && !x.isExpTuple() && intprt)
							sc.handler.message(x.interpretV().get!string());
						else sc.handler.message(x.toString());
					sc.handler.message("\n");
					if(bdy) mixin(SemChld!q{bdy});
					mixin(SemEplg);
				default: break;

				// some vendor specific pragmas
				case "__range":
					if(args.length!=2) break;
					mixin(SemChld!q{args[1]});
					mixin(PropErr!q{args[1]});
					sstate = args[1].sstate;
					if(sstate == SemState.completed){
						import std.stdio;
						auto ty=args[1].type.getHeadUnqual().isIntegral();
						if(ty&&ty.bitSize()<=32) stderr.writeln(args[1].getIntRange());
						else stderr.writeln(args[1].getLongRange());
					}
					mixin(SemEplg);
			}
		}
		sc.error(format("unrecognized pragma '%s'",args[0].loc.rep),args[0].loc); // TODO: option to ignore
		mixin(SemChld!q{bdy});
		mixin(ErrEplg);
	}
}

// string mixins

mixin template Semantic(T) if(is(T==MixinExp)||is(T==MixinStm)||is(T==MixinDecl)){
	static if(is(T==MixinExp)) alias Expression R; // workaround
	else static if(is(T==MixinStm)) alias Statement R;
	else static if(is(T==MixinDecl)) alias Declaration R;
	static if(is(T==MixinDecl)){
		override void presemantic(Scope sc){
			if(sstate != SemState.pre) return;
			scope_ = sc;
			sstate = SemState.begin;
			sc.insertMixin(this);
		}
		Declaration mixedin;
		override void buildInterface(){
			mixedin=evaluate(scope_);
			mixin(SemCheck);
			auto r=mixedin;
			r.presemantic(scope_);
			r.buildInterface();
			mixin(RewEplg!q{r});
		}
	}else static if(is(T==MixinExp)){
		AccessCheck accessCheck = accessCheck.all;
	}
	private R evaluate(Scope sc){
		mixin(SemPrlg);
		a[0].prepareInterpret();
		mixin(SemChld!q{a});

		if(a.length<1){
			sc.error("missing arguments to string mixin", loc);
			mixin(ErrEplg);
		}else if(a.length>2){
			sc.error("too many arguments to string mixin", loc);
			mixin(ErrEplg);
		}

		mixin(FinishDeductionProp!q{a[0]});
		int which;
		Type[3] types = [Type.get!(const(char)[])(),
		                 Type.get!(const(wchar)[])(),
		                 Type.get!(const(dchar)[])()];
		foreach(i,t;types) if(!which){
			mixin(ImplConvertsTo!q{bool icd; a[0], t});
			if(icd) which=cast(int)i+1;
		}
		if(!which){
			sc.error("expected string argument to string mixin", a[0].loc);
			mixin(ErrEplg);
		}
		foreach(i,t; types) if(i+1==which){
			mixin(ImplConvertTo!q{a[0],t});
			a[0]=a[0].convertTo(t.getImmutable());
			mixin(SemChld!q{a[0]});
		}
		assert(a[0].sstate == SemState.completed);

		mixin(IntChld!q{a[0]});
		auto str = a[0].interpretV().get!string();
		//str~=(is(T==MixinStm)&&str[$-1]!=';'?";":"")~"\0\0\0\0";
		str~="\0\0\0\0";
		Source src = New!Source(format("<mixin@%s:%d>",loc.source.name,loc.line), str); // TODO: column?
		import parser;
		//auto handler = sc.handler;
/+		auto handler = New!StringMixinErrorHandler();
		auto ohan = sc.handler;
		sc.handler = handler;+/

		auto nerrors = sc.handler.nerrors;

		static if(is(T==MixinExp)){
			auto r=parseExpression(src,sc.handler);
			r.weakenAccessCheck(accessCheck);
		}else static if(is(T==MixinStm)) auto r=New!CompoundStm(parseStatements(src,sc.handler)); // TODO: use CompoundStm instead
		else static if(is(T==MixinDecl)) auto r=New!BlockDecl(STC.init,parseDeclDefs(src,sc.handler));
		else static assert(0);

		if(sc.handler.nerrors != nerrors) mixin(ErrEplg);

		else static if(is(T==MixinDecl)) r.pickupSTC(stc);
		r.semantic(sc);
		//ohan.note("mixed in here", loc);
		// TODO: do we want something like this?
/+		sc.handler = ohan;
		if(handler.errors.length){
			sc.error("mixed in code contained errors",loc);
			foreach(x; handler.errors) sc.handler.playErrorRecord(x);
			mixin(ErrEplg);
		}+/
		mixin(Rewrite!q{r});
		needRetry = false;
		return r;
	}

	override void semantic(Scope sc){
		auto r=evaluate(sc);
		mixin(SemCheck);
		static if(is(T==MixinDecl)) sc.removeMixin(this);
		mixin(RewEplg!q{r});
	}
}
/+
// TODO: do we want something like this?
class StringMixinErrorHandler: ErrorHandler{
	ErrorRecord[] errors;
	override void error(lazy string err, Location loc){
		errors~=ErrorRecord(err,loc);
	}
	override void note(lazy string err, Location loc){
		errors~=ErrorRecord(err,loc,true);
	}
}+/
