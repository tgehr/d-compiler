// Written in the D programming language
// Author: Timon Gehr
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.array, std.conv, std.algorithm, std.range, std.string;

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
	static if(is(typeof(this):typeof(return))) return this;
	else static if(is(typeof(return)==class)) return null;
	else static if(is(typeof(return)==bool)) return true;
	else return;
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
			debug{
				auto rw=@(s).rewrite;
				assert(!!cast(typeof(@(s)))@(s).rewrite, text("rewrite from ",typeid(typeof(@(s)))," to ",typeid(rw)));
			}
			assert(@(s)!is @(s).rewrite, "non-terminating rewrite! "~.to!string(@(s)));
			//assert(!!cast(typeof(@(s)))@(s).rewrite,"cannot store "~.to!string(typeid(@(s).rewrite))~" into reference of type "~.to!string(typeid(typeof(@(s)))));
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
				// auto xxx = @(sp[1]);dw("propagated error from ", typeid(xxx)," ",@(sp[1])," to ",this);
				@(ErrEplg)
			}
		}else foreach(x;@(sp[1])) mixin(PropErr!q{x});
	}):mixin(X!q{if(sstate==SemState.error){@(NoRetry)mixin(SemRet);}});
}
template PropErr(string s) if(s.canFind(",")){ alias MultiArgument!(.PropErr,s) PropErr; }

template PropRetryNoRew(string s) if(!s.canFind(",")){
	enum sp = splitScope(s);
	enum PropRetryNoRew=mixin(X!q{
		static assert(!is(typeof(_nR)));
		if(auto _nR=@(sp[1]).needRetry){
			assert(_nR!=2 || sstate != SemState.error,text("error in cdep from ",@(sp[1])," to ",toString()));
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
					foreach(ref x;@(t)) mixin(_SemChldImpl!("x","@(op)","@(sc)"));
					static if(is(typeof(@(t)): Expression[]) && (!is(typeof(this)==TemplateInstanceExp)||"@(t)"!="args")){
						pragma(msg, typeof(this)," @(t)");
						@(t)=mixin(`Tuple.expand(@(sc),AccessCheck.all,@(t),@(t~"Leftover"))`);
						if(mixin(`@(t~"Leftover")`)){
							mixin(_SemChldImpl!("@(t)Leftover","@(op)","@(sc)"));
						}
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

template CreateBinderForDependent(string name, string fun=lowerf(name)){
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
				`~(propErr?`assert(!_@(name)_`~varn~`.dependee,text("illegal dependee ",_@(name)_`~varn~`.dependee.node," ",_@(name)_`~varn~`.dependee.node.sstate));`:``)~`
				static if(!is(typeof(_@(name)_`~varn~`)==Dependent!void))`~var~`=_@(name)_`~varn~`.value;
			`;
		}

	}));
}
mixin CreateBinderForDependent!("ImplConvertsTo","implicitlyConvertsTo");
mixin CreateBinderForDependent!("RefConvertsTo");
mixin CreateBinderForDependent!("ConstConvertsTo");
mixin CreateBinderForDependent!("ConvertsTo");
mixin CreateBinderForDependent!("TypeMostGeneral");
mixin CreateBinderForDependent!("TypeCombine");
mixin CreateBinderForDependent!("Combine");
mixin CreateBinderForDependent!("Unify");
mixin CreateBinderForDependent!("TypeMatch");
mixin CreateBinderForDependent!("RefCombine");
mixin CreateBinderForDependent!("MatchCall");
mixin CreateBinderForDependent!("MatchCallHelper");
mixin CreateBinderForDependent!("AtLeastAsSpecialized");
mixin CreateBinderForDependent!("DetermineMostSpecialized");
mixin CreateBinderForDependent!("Lookup");
mixin CreateBinderForDependent!("LookupHere");
mixin CreateBinderForDependent!("GetUnresolved");
mixin CreateBinderForDependent!("GetUnresolvedHere");
mixin CreateBinderForDependent!("IsDeclAccessible");
mixin CreateBinderForDependent!("DetermineOverride");
mixin CreateBinderForDependent!("FindOverrider");
mixin CreateBinderForDependent!("LookupSealedOverloadSet");
mixin CreateBinderForDependent!("LookupSealedOverloadSetWithRetry");
mixin CreateBinderForDependent!("EliminateLessSpecializedTemplateMatches");

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
					mixin(Lookup!q{_; ident, sc, sc});
					if(auto nr=ident.needRetry) { needRetry = nr; return; }
				}
				if(ident.sstate == SemState.failed){
					// show lookup error
					ident.sstate = SemState.begin;
					mixin(SemChldPar!q{@(e)});
				}

				if(ident.sstate != SemState.error && ident.meaning){
					// constructor calls are not subject to reverse eponymous lookup
					// reverse eponymous lookup is also not performed for reference
					// aggregate declarations. This behaviour is copied from DMD.
					static if(is(typeof(this)==CallExp))
						if(ident.meaning.isAggregateDecl())
							goto Lnorevepolkup;
					@(e) = ident.reverseEponymousLookup(sc);
				Lnorevepolkup:;
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
enum SemPrlgDontSchedule=q{
	if(sstate == SemState.error||sstate == SemState.completed||rewrite){mixin(SemRet);}
	//dw(cccc++); if(!champ||cccc>champ.cccc) champ=this;
	//dw(champ);
	/+debug scope(failure){
		if(loc.line) write("here! ",loc," ",typeid(this));
		else write("here! ",toString()," ",typeid(this));
		static if(is(typeof(meaning))) write(" meaning: ",meaning," ",typeid(this.meaning)," ",meaning.sstate);
		writeln();
	}+/
};
enum SemPrlg=SemPrlgDontSchedule~q{
	Scheduler().add(this,sc);
};
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
	// dw(this," ",__LINE__);
	mixin(NoRetry);
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
	/+Node _rewrite;
	@property Node rewrite(){ return _rewrite; }
	@property Node rewrite(Node n){
		if(!_rewrite) assert(!!n);
		dw("old: ",_rewrite);
		dw("new: ",n);
		return _rewrite=n;
	}+/
	SemState sstate = SemState.begin;
	ubyte needRetry = false; // needRetry == 2: unwind stack for circular dep handling
	/+ubyte _needRetry = false;
	@property ubyte needRetry(){ return _needRetry; }
	@property void needRetry(ubyte val){
		assert(val!=1||sstate!=SemState.error);
		assert(!val || sstate != SemState.completed || isExpression()&&isExpression().isConstant(),val.to!string);
		_needRetry=val;
	}+/

	invariant(){
		//assert(sstate!=SemState.error||needRetry!=1, "needRetry and error "~to!string(loc)~" "~to!string(typeid(this))~(cast(Identifier)this?" "~(cast(Identifier)this).name:"")~" Identifier.tryAgain: "~to!string(Identifier.tryAgain)~" needRetry: "~to!string(needRetry)); // !!!!?
	}

	void semantic(Scope sc)in{assert(sstate>=SemState.begin);}body{
		mixin(SemPrlg);
		sc.error("feature not implemented",loc);
		mixin(ErrEplg);
	}

	// analysis is trapped because of circular await-relationship involving this node
	void noHope(Scope sc){}
}

// error nodes (TODO: file bug against covariance error)

mixin template Semantic(T) if(is(T==ErrorDecl)||is(T==ErrorExp)||is(T==ErrorStm)||is(T==ErrorTy)){
	override void semantic(Scope sc){ }
	static if(is(T:Declaration))
	override void presemantic(Scope sc){assert(0);}
}

enum InContext:ubyte{
	none,
	addressTaken,
	called,
	instantiated,
	passedToTemplateAndOrAliased,
	fieldExp,
}

// expressions
mixin template Semantic(T) if(is(T==Expression)){
	Type type;
	invariant(){
		assert(sstate != SemState.completed || type && type.sstate == SemState.completed,text(typeid(this)," ",loc));
	}

	// run before semantic if the expression occurs in a specified context
	void isInContext(InContext inContext){ }
	// TODO: those are not strictly necessary:
	final void willTakeAddress(){ isInContext(InContext.addressTaken); }
	final void willCall(){ isInContext(InContext.called); }
	final void willInstantiate(){ isInContext(InContext.instantiated); }
	final void willPassToTemplateAndOrAlias(){ isInContext(InContext.passedToTemplateAndOrAliased); }
	final void willAlias(){ willPassToTemplateAndOrAlias(); }
	final void willPassToTemplate(){ willPassToTemplateAndOrAlias(); }

	protected mixin template ContextSensitive(){
		enum isContextSensitive = true;
		static assert(!is(typeof(super.inContext)), "already context-sensitive");
		auto inContext = InContext.none;
		override void isInContext(InContext inContext){
			assert(this.inContext.among(InContext.none, inContext), text(this," ",this.inContext," ",inContext));
			this.inContext=inContext;
		}
		final void transferContext(Expression r){
			final switch(inContext) with(InContext){
				case none: break;
				case addressTaken: r.willTakeAddress(); break;
				case called: r.willCall(); break;
				case instantiated: r.willInstantiate(); break;
				case passedToTemplateAndOrAliased: r.willPassToTemplateAndOrAlias(); break;
				case fieldExp: if(auto sym=isSymbol()) sym.inContext=InContext.fieldExp; break;
			}
		}
	}

	void initOfVar(VarDecl decl){}

	override void semantic(Scope sc){
		mixin(SemPrlg);
		sc.error("feature "~to!string(typeid(this))~" not implemented",loc);
		mixin(ErrEplg);
	}

	Type typeSemantic(Scope sc){
		// dw(this," ",sstate," ",typeid(this));
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
		if(auto sym=me.isSymbol()) if(auto ov=sym.meaning.isCrossScopeOverloadSet()){
			ov.reportConflict(sc,loc);
			goto Lerr;
		}
		sc.error(format("%s '%s' is used as a type",me.kind,me.toString()),loc);
		me.sstate = SemState.error;
		Lerr:mixin(ErrEplg);
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
		static struct WeakenCheck{
			immutable AccessCheck check;
			void perform(Symbol self){
				self.accessCheck = min(self.accessCheck, check);
			}
			void perform(CurrentExp self){
				self.accessCheck = min(self.accessCheck, check);
			}
			void perform(MixinExp self){
				self.accessCheck = min(self.accessCheck, check);
			}
		}
		runAnalysis!WeakenCheck(this,check);
	}

	final void restoreAccessCheck(Scope sc, AccessCheck check){
		// TODO: _perform_ access check
		static struct RestoreCheck{
			immutable AccessCheck check;
			bool r=false;
			enum b=q{
				if(self.accessCheck<check) r=true;
				self.accessCheck = check;
			};
			void perform(Symbol self){ mixin(b); }
			void perform(CurrentExp self){ mixin(b); }
			void perform(MixinExp self){ mixin(b); }
		}
		if(runAnalysis!RestoreCheck(this,check).r){
			static struct Reset{
				void perform(Expression e){ if(!e.isType()) e.sstate = SemState.begin; }
			}
			runAnalysis!Reset(this);
			semantic(sc);
		}
	}

	final void checkAccess(Scope sc,AccessCheck accessCheck){
		if(accessCheck==AccessCheck.none) return;
		if(auto s=AliasDecl.getAliasBase(this)){
			if(s.accessCheck<accessCheck){
				s.accessCheck = accessCheck;
				static struct ResetSstate{
					void perform(Expression e){
						if(e.sstate==SemState.error) return;
						e.sstate = SemState.begin;
						assert(!e.rewrite);
					}
				}
				runAnalysis!ResetSstate(this);
				semantic(sc);
			}
		}
	}


	bool isConstant(){ return false; }
	bool isConstFoldable(){ return false; }

	bool isUnique(){ return false; }

	Expression clone(Scope sc, InContext inContext, AccessCheck accessCheck, const ref Location loc)in{
		assert(sstate == SemState.completed);
	}body{
		Expression r;
		if(isConstFoldable()) r=cloneConstant();
		else r=ddup();
		r.loc = loc;
		r.isInContext(inContext);
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
		// import std.stdio; writeln("folding constant ", this);
		interpret(sc);
	}

	bool isLvalue(){return false;}

	final bool checkLvalue(Scope sc, ref Location l){
		if(isLvalue()) return true;
		sc.error(format("%s '%s' is not an lvalue",kind,toString()),l);
		return false;
	}

	final bool canMutate(){
		return isLvalue() && type.isMutable();
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
		if(l && r && l.bitSize()<128 && r.bitSize()<128){ // TODO: VRP for cent and ucent
			// note: r.getLongRange is always valid for other basic types
			if(l.op == Tok!"long" || l.op == Tok!"ulong"){
				return r.getLongRange().contains(getLongRange()).independent;
			}else{
				return r.getIntRange().contains(getIntRange()).independent;
			}
		}
		return false.independent;
	}
	Expression implicitlyConvertTo(Type to)in{
		assert(to && to.sstate == SemState.completed);
	}body{
		if(type.equals(to)) return this;
		auto r = New!ImplicitCastExp(to,this);
		r.loc = loc;
		return r;
	}
	bool typeEquals(Type rhs)in{
		assert(sstate == SemState.completed, text(typeid(this)," ",this," ",sstate," ",loc));
	}body{
		return type.equals(rhs);
	}

	final bool finishDeduction(Scope sc)in{assert(!!sc,text(this));}body{
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
				if(sym.meaning)
				if(auto cso=sym.meaning.isCrossScopeOverloadSet()){
					cso.reportConflict(sc,sym.loc);
					mixin(SetErr!q{sym});
				}
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
		Type r = null;
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

	final Dependent!Expression matchCall(Scope sc, const ref Location loc, Expression[] args)in{
		assert(sstate == SemState.completed);
	}body{
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
	bool tmplArgEquals(Expression rhs)in{
		assert(sstate == SemState.completed,"not completed sstate "~toString());
		assert(rhs.sstate == SemState.completed,"rhs not completed sstate "~rhs.toString());
	}body{
		assert(0, "unsupported operation");
	}
	size_t tmplArgToHash(){
		// default implementation provided
		// in order to support arbitrary expressions
		// as tuple variable initializers
		// TODO: this is hacky
		return 0;
	}
}


//pragma(msg, __traits(classInstanceSize,Expression)); // 0u. TODO: reduce and report

mixin template Semantic(T) if(is(T==LiteralExp)){

	static Expression factory(Variant value)in{
		assert(!!value.getType());
	}body{
		auto vtype=value.getType();
		if(auto tt=vtype.isTypeTuple()){
			auto vals=value.getTuple();
			auto exprs=new Expression[](vals.length);
			foreach(i,v;vals){
				exprs[i]=factory(v);
				assert(exprs[i].sstate==SemState.completed &&
				       exprs[i].type==tt.allIndices()[i]);
			}
			return New!ExpTuple(exprs.captureTemplArgs, vtype);
		}
		auto r = New!LiteralExp(value);
		r.semantic(null);
		mixin(Rewrite!q{r});
		assert(r.type is vtype);
		r.dontConstFold();
		return r;
	}

	static Expression polyStringFactory(string value){
		Expression r = factory(Variant(value, Type.get!string()));
		assert(cast(LiteralExp)r);
		(cast(LiteralExp)cast(void*)r).lit.type = Tok!"``";
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
		if(isPolyString()){
			assert(Type.get!wstring().implicitlyConvertsTo(rhs).isIndependent &&
			       Type.get!dstring().implicitlyConvertsTo(rhs).isIndependent );

			return Type.get!wstring().implicitlyConvertsTo(rhs).or(
				Type.get!dstring().implicitlyConvertsTo(rhs));
		}


		return false.independent;
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

	override bool tmplArgEquals(Expression rhs){
		if(!type.equals(rhs.type)) return false;
		if(!rhs.isConstant()) return false;
		return interpretV()==rhs.interpretV();
	}

	override size_t tmplArgToHash(){
		assert(!!type,text("no type! ",this));
		import hashtable;
		return FNV(type.toHash(), value.toHash());
	}
}

mixin template Semantic(T) if(is(T==ArrayLiteralExp)){
	Expression litLeftover=null;
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{lit});
		if(!lit.length){type=Type.get!EmptyArray(); mixin(SemEplg);}
		auto ty=lit[0].type;
		if(!type) foreach(i,x;lit[1..$]){
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
			mixin(Combine!q{Type newty; ty, x.type}); // TODO: keep state?
			if(newty){
				ty=newty;
				continue;
			}
			if((x.isAddressExp()||x.isArrayLiteralExp()) && x.type is Type.get!void())
				continue;
			sc.error(format("incompatible type '%s' in array of '%s'",x.type,ty),x.loc);
			mixin(ErrEplg);
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
		if(type){ ty=type.getElementType(); assert(!!ty); }
		if(ty.getHeadUnqual() !is Type.get!void())
			foreach(ref x; lit)  x=x.implicitlyConvertTo(ty);
		mixin(SemChldPar!q{lit});
		alias util.all all; // TODO: file bug
		assert(all!(_=>_.sstate == SemState.completed)(lit));
		type=ty.getDynArr();
		mixin(SemEplg);
	}

	override bool isUnique(){ return true; } // TODO: analyze what's contained within

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

	override bool tmplArgEquals(Expression rhs){
		if(!type.equals(rhs.type)) return false;
		return interpretV()==rhs.interpretV();
	}

	override size_t tmplArgToHash(){
		import hashtable;
		return FNVred(lit);
	}
}

mixin template Semantic(T) if(is(T _==PostfixExp!S,TokenType S)){
	static if(is(T _==PostfixExp!S,TokenType S)):
	static assert(S==Tok!"++" || S==Tok!"--");
	///
	mixin OpOverloadMembers;
	TmpVarExp tmp1,tmp2;
	///
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
		if(!tmp1){
			assert(!tmp2);
			tmp1=New!TmpVarExp(e);
			tmp1.loc=loc;
			tmp1.semantic(sc);
			assert(!!tmp1.sym);
			tmp2=New!TmpVarExp(tmp1.sym);
			tmp2.loc=loc;
			tmp2.initTmpVarDecl(sc,true);
			tmp2.semantic(sc);
			assert(!!tmp2.sym);
		}
		mixin(OpOverload!("opUnary",q{[LiteralExp.polyStringFactory(TokChars!S)]},
		q{(Expression[]).init},"tmp1.sym","sc",q{
			auto tmpe=New!(BinaryExp!(Tok!","))(tmp1,tmp2);
			tmpe.loc=loc;
			r=New!(BinaryExp!(Tok!","))(tmpe,r);
			r.loc=loc;
			r=New!(BinaryExp!(Tok!","))(r,tmp2.sym);
			r.loc=loc;
		}));
		sc.error(format("type '%s' does not support postfix "~TokChars!op,e.type),loc);
		mixin(ErrEplg);
	}
}

mixin template OpOverloadMembers(){ // TODO: this bloats the AST, find a better way?
	Expression opoverload=null;
	Expression oofun=null;
	GaggingScope oosc=null;
}

template BuildOpOver(string opover,string e, string name, string tmargs){
	enum BuildOpOver = mixin(X!q{
		if(!@(opover)){
			auto id=New!Identifier("@(name)");
			id.loc=loc;
			@(opover)=New!(BinaryExp!(Tok!"."))(@(e),id);
			@(opover).loc=loc;
			@({
				if(tmargs.length) return mixin(X!q{
					@(opover)=New!TemplateInstanceExp(@(opover),@(tmargs));
					@(opover).loc=loc;
				});
				return "";
			}());
		}

	});
}

template OpOverload(string name, string tmargs="", string args="", string e="e", string sc="sc", string post=""){
	enum OpOverload = mixin(X!q{
		@(BuildOpOver!("opoverload",e,name,tmargs));
		if(!oosc) oosc=New!GaggingScope(@(sc));
		opoverload.willCall();
		mixin(SemChldPar!q{sc=oosc;opoverload});
		auto args = @(args);
		if(!oofun&&opoverload.sstate==SemState.completed){
			mixin(MatchCall!q{oofun; opoverload, @(sc), loc, args});
			if(!oofun) mixin(SetErr!q{opoverload});
		}
		if(oofun){
			mixin(SemChldPar!q{sc=oosc;oofun});
			oosc=null;
			Expression r=New!CallExp(oofun,args);
			r.loc=loc;
			@(post)
			r.semantic(sc);
			mixin(RewEplg!q{r});
		}
	});
}

mixin template Semantic(T) if(is(T==IndexExp)){
	Expression aLeftover=null;
	DollarScope ascope;
	mixin DollarExp.DollarProviderImpl!e;
	mixin ContextSensitive;

	mixin OpOverloadMembers;

	override void semantic(Scope sc_){
		{alias sc_ sc;mixin(SemPrlg);}
		{alias sc_ sc;mixin(SemChldPar!q{e});}

		if(!ascope) ascope = New!DollarScope(sc_, this);
		alias ascope sc;
		if(e.isType()){
			auto r=typeSemantic(sc); // TODO: ok?
			mixin(SemCheck);
			assert(!!r);
			mixin(RewEplg!q{r});
		}else if(e.isExpTuple()||e.sstate == SemState.completed && e.type.isTypeTuple()){
			mixin(SemChldExp!q{a});
			mixin(PropErr!q{e});
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
			bool checkn(size_t len){
				if(n<len) return true;
				sc.error(format("tuple index %s is out of bounds [0%s..%d%s)",a[0].toString(),Size_t.suffix,len,Size_t.suffix),a[0].loc);
				return false;
			}
			Expression r;
			if(auto et=e.isExpTuple()){
				if(!checkn(et.length)) mixin(ErrEplg);
				r=et.index(sc,inContext,loc,n);
			}else if(auto c=e.isCommaExp()){
				bool err=false;
				Expression go(CommaExp c){
					Expression rhs;
					if(auto cc=c.e2.isCommaExp()) rhs=go(cc);
					else{
						auto et=c.e2.isExpTuple();
						assert(!!et);
						if(!checkn(et.length)){ err=true; return c; }
						rhs=et.index(sc,inContext,loc,n);
					}
					auto r=New!(BinaryExp!(Tok!","))(c.e1, rhs);
					r.brackets++;
					r.loc=c.loc;
					return r;
				}
				r=go(c);
				if(err) mixin(ErrEplg);
			}else assert(0,text(e," ",e.loc));
			r.semantic(sc);
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
			}else{
				mixin(OpOverload!("opIndex","","a","e","sc_"));
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
				{
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
			return tp.index(sc,inContext,loc,n).typeSemantic(sc);
		}
		// TODO: DMD considers 16777215 as the upper bound for static array size
		assert(!!ty);
		return ty.getArray(n);
	}

	override bool isLvalue(){
		return !!a.length; // slice expression is no lvalue
	}

	override @property string kind(){ return a.length?"index expression":"slice"; }

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
	mixin OpOverloadMembers;

	override void semantic(Scope sc_){
		{alias sc_ sc; mixin(SemPrlg);}
		//mixin(SemChldPar!q{e});
		if(e.sstate != SemState.completed){
			alias sc_ sc;
			mixin(SemChldPar!q{e});
		}
		mixin(Rewrite!q{e});

		if(!ascope) ascope = New!DollarScope(sc_, this);

		// mixin(MaybeFold!q{e,l,r}); // TODO: this is better
		if(e.isTuple()||e.type&&e.type.isTuple()){
			Expression r=null;
			if(auto tp = e.isTuple()){
				r=sliceTuple(sc_,tp);
			}else if(auto c=e.isCommaExp()){
				Expression go(CommaExp c){
					Expression rhs;
					if(auto cc=c.e2.isCommaExp()){
						rhs=go(cc);
					}else{
						auto tp=c.e2.isTuple();
						assert(!!tp);
						rhs=sliceTuple(sc_,tp);
					}
					if(!rhs) return null;
					auto r=New!(BinaryExp!(Tok!","))(c.e1, rhs);
					r.brackets++;
					r.loc=c.loc;
					return r;
				}
				r=go(c);
			}else assert(0);
			if(!r) return;
			r.semantic(sc_);
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
			}else{
				// TODO: this gc allocates
				mixin(OpOverload!("opSlice","",q{[l,r]},"e","sc_"));
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
			{
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

	override void isInContext(InContext ctx){
		with(InContext)
			if(ctx.among(passedToTemplateAndOrAliased, fieldExp))
				e.isInContext(ctx);
	}

	override @property string kind(){ return e.kind; }

private:
	Expression sliceTuple(Scope sc_, Tuple tp){
		enum SemRet = q{ return null; };
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

		auto r=tp.slice(loc,a,b);
		r.semantic(sc);
		mixin(NoRetry);
		return r;
	}
}

mixin template Semantic(T) if(is(T==ImportExp)){
	Expression aLeftover=null;
	override void semantic(Scope sc){
		mixin(SemPrlg);
		foreach(x;a) x.prepareInterpret();
		mixin(SemChld!q{a});
		if(a.length<1){
			sc.error("missing file name for import expression", loc);
			mixin(ErrEplg);
		}else if(a.length>1){
			sc.error("too many arguments for import expression", loc);
			mixin(ErrEplg);
		}
		mixin(FinishDeductionProp!q{a[0]});
		// TODO: this code is identical for MixinExp
		int which;
		Type[3] types = [Type.get!(const(char)[])(),
		                 Type.get!(const(wchar)[])(),
		                 Type.get!(const(dchar)[])()];
		foreach(i,t;types) if(!which){
			mixin(ImplConvertsTo!q{bool icd; a[0], t});
			if(icd) which=cast(int)i+1;
		}
		if(!which){
			sc.error("expected string argument for import expression", a[0].loc);
			mixin(ErrEplg);
		}
		foreach(i,t; types) if(i+1==which)
			mixin(ImplConvertTo!q{a[0],t});
		assert(a[0].sstate == SemState.completed);

		a[0].interpret(sc);
		if(aLeftover) aLeftover.interpret(sc);
		mixin(SemProp!q{a[0]});
		if(aLeftover) mixin(SemProp!q{aLeftover});
		auto file = a[0].interpretV().convertTo(Type.get!string()).get!string();
		auto cm = sc.getModule();
		auto repo = cm.repository;
		string error=null;
		auto str=repo.readFile(file,error);
		if(error){
			sc.error(error,a[0].loc);
			mixin(ErrEplg);
		}
		auto r=LiteralExp.polyStringFactory(str);
		r.loc=loc;
		mixin(RewEplg!q{r});
	}
 }

mixin template Semantic(T) if(is(T==AssertExp)){
	Expression aLeftover=null;
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
	static if(overloadableUnary.canFind(TokChars!S)) mixin OpOverloadMembers;
	static if(is(T _==UnaryExp!S,TokenType S)):

	override void semantic(Scope sc){
		mixin(SemPrlg);
		static if(S==Tok!"&"){
			auto sym = e.isSymbol();
			if(!sym||sym.inContext==InContext.none)
				e.willTakeAddress();
		}
		mixin(SemChldExp!q{e});

		static if(S!=Tok!"&"&&S!=Tok!"!"){
			auto ty=e.type.getHeadUnqual();
			// integral promote enum types to unqualified base
			if(auto et=ty.isEnumTy()){
				mixin(GetEnumBase!q{ty;et.decl});
				ty=ty.getHeadUnqual();
			}
		}
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
			if(e.canMutate()){
				auto v = Type.get!void();
				if(ty.isBasicType()&&e !is v&&ty !is Type.get!bool()||ty.isPointerTy()){
					type = e.type;
					mixin(SemEplg);
				}
			}
		}else static if(S==Tok!"*"){
			if(auto p=ty.isPointerTy()){
				type = p.ty;
				mixin(SemEplg);
			}
		}else static if(S==Tok!"&"){
			if(e.type.isTuple()){
				// TODO: propose element-wise semantics
				sc.error("cannot take address of sequence", loc);
				mixin(ErrEplg);
			}if(auto lv = e.isLvalue()){
				// TODO: this is a hack, find solution for taking address of
				// overloaded declaration

				FunctionDecl fd=null;
				auto fe = e.isFieldExp();
				if(auto s=fe?fe.e2:e.isSymbol()){
					fd=tryGetFunctionDecl(s);
					if(fd){
						if(s.type is Type.get!void()) // need deduction first
							type = Type.get!void;
						else{
							if(auto fdef=fd.isFunctionDef()){
							if(!fdef.finishedInference()){
								needRetry=true;
								Scheduler().await(this,fdef,fdef.scope_);
								return;
							}}
							// resolve inout and check this pointer compatibility
							InoutRes inoutRes;
							if(fe)if(auto this_ = fe.e1.extractThis()){
								if(fd.stc&STCinout) inoutRes = irFromSTC(this_.type.getHeadSTC());
								if(inoutRes==InoutRes.immutable_)
									inoutRes=InoutRes.inoutConst;

								if(fd.needsAccessCheck(fe.accessCheck)){
									mixin(RefConvertsTo!q{
										auto compat;
										this_.type,
										this_.type.getHeadUnqual()
										.applySTC(fd.stc&STCtypeconstructor)
										.resolveInout(inoutRes),
										0
									});
									if(!compat){
										FunctionDecl.incompatibleThisError(sc,e.loc,this_.type.getHeadSTC(),fd.stc&STCtypeconstructor, fd);
										mixin(ErrEplg);
									}
								}
							}

							s.type=fd.type;
							s.meaning=fd;
							auto res=fd.type.resolveInout(inoutRes);
							if(fd.stc&STCstatic) type=res.getPointer();
							else type=res.getDelegate();
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
		static if(overloadableUnary.canFind(TokChars!S)){
			// TODO: this gc allocates
			mixin(OpOverload!("opUnary",q{
				[LiteralExp.polyStringFactory(TokChars!S)]
			},q{(Expression[]).init}));
		}
		// TODO: array ops
		static if(S==Tok!"*"){
			sc.error(format("cannot dereference expression '%s' of non-pointer type '%s'",e.loc.rep,e.type),loc);
		}else static if(S==Tok!"++" || S==Tok!"--"){
			if(e.checkMutate(sc,loc)) // TODO: it would be better to first check if the type is fully off
				sc.error(format("type '%s' does not support prefix "~TokChars!S,e.type),loc);
		}else{
			sc.error(format("invalid argument type '%s' to unary "~TokChars!S,e.type),loc);
		}
		mixin(ErrEplg);
	}

	// TODO: constant addresses should be possible to be taken too
	static if(S==Tok!"+"||S==Tok!"-"||S==Tok!"~"||S==Tok!"!"){
		override bool isConstant(){ return e.isConstant(); }
		override bool isConstFoldable(){ return e.isConstFoldable(); }
	}
	static if(S==Tok!"&"){

	override void noHope(Scope sc){
		auto fe = e.isFieldExp();
		if(auto s=fe?fe.e2:e.isSymbol()){
			auto fd=tryGetFunctionDecl(s);
			if(auto fdef=fd.isFunctionDef()){
				if(!fdef.finishedInference())
					fdef.cancelInference();
			}
		}
	}

	private static FunctionDecl tryGetFunctionDecl(Symbol s){
		FunctionDecl fd=null;
		if(auto ov=s.meaning.isOverloadSet()){
			if(ov.decls.length==1)
				if(auto fdo=ov.decls[0].isFunctionDecl()) fd = fdo;
		}else if(auto fdd=s.meaning.isFunctionDecl()) fd = fdd;
		return fd;
	}

	override void isInContext(InContext inContext){
		if(inContext == InContext.passedToTemplateAndOrAliased){
			if(auto sym=e.isSymbol())
				sym.accessCheck=AccessCheck.none;
		}else if(inContext == InContext.fieldExp){
			if(auto sym=e.isSymbol())
				sym.inContext=InContext.fieldExp;
		}
	}

	override bool isConstant(){
		return !!e.isSymbol(); // TODO: correct?
	}

	override Dependent!bool implicitlyConvertsTo(Type rhs){
		// function literals implicitly convert to both function and delegate
		if(auto sym = e.isSymbol()                      ){
		if(auto fd  = sym.meaning.isFunctionDef()       ){
			auto rhsu = rhs.getHeadUnqual();
			if(auto dg  = rhsu.isDelegateTy()){
				if(fd.inferStatic){
					assert(sym.isStrong);
					return fd.type.addQualifiers(STCimmutable).getDelegate()
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
	override void matchError(Scope sc, Location loc, Type this_, Expression[] args){
		e.matchError(sc,loc,this_,args);
	}

	// this is necessary to make template delegate literals work correctly
	// the scope of the symbol must be adjusted
	override Expression clone(Scope sc, InContext inContext, AccessCheck accessCheck, const ref Location loc){
		auto ctx=InContext.addressTaken;
		if(inContext==inContext.fieldExp) ctx=inContext;
		auto r=New!(UnaryExp!(Tok!"&"))(e.clone(sc,ctx,accessCheck,loc));
		r.loc = loc;
		r.semantic(sc);
		return r;
	}


	final bool isUndeducedFunctionLiteral(){
		auto r=type is Type.get!void();
		assert(!r || e.isSymbol() && e.isSymbol().isFunctionLiteral);
		return r;
	}

	override bool tmplArgEquals(Expression rhs){
		if(this is rhs) return true;
		if(auto ae=rhs.isAddressExp())
		   return e.tmplArgEquals(ae.e);
		return false;
	}

	override size_t tmplArgToHash(){
		import hashtable;
		return FNV(e.tmplArgToHash());
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
			else{
				// if unification fails, ignore 'void'
				// this eg. helps when one argument is an empty array
				// void foo(T)(T[] a, T[] b); foo([],[1,2,3])
				auto v = Type.get!void();
				if(adapted==v) adapted=from;
				else if(from!=v) ambiguous=true;
			}
		}
		return indepvoid;
	}

	override string toString(){return "<<MT("~adapted.to!string()~")>>";}

	override bool hasPseudoTypes(){ return true; }

	mixin DownCastMethod;
	mixin Visitors;
}
mixin template Semantic(T) if(is(T==MatcherTy)){}


struct TemplArgsWithTypes{
	TemplArgs args;
	TypeTemplArgs argTypes;
}

class TemplateInstanceDecl: Declaration{
	TemplateDecl parent;      // template this instance was instantiated from

	Expression instantiation; // an expression that is responsible for analysis
	                          // of this instance. (either a symbol or a instantiation)

	TemplArgs args;         // arguments as given by the instantiation site
	TypeTemplArgs argTypes; // types of the template arguments
	TemplArgs resolved;     // arguments as given to the template body

	Match match = Match.exact; // match level.

	Expression constraint;
	BlockDecl bdy;

	TemplateScope paramScope;
	Scope parentScope;

	bool isMixin = false;

	final @property bool completedMatching(){ return matchState>=MatchState.completed; }
	final @property bool hasFailedToMatch(){ return matchState==MatchState.failed; }
	final @property bool completedParameterResolution(){
		return matchState > MatchState.resolvedSemantic;
	}

	private{

		enum MatchState{
			start,               // start matching
			iftiStart,           // start matching in ifti mode
			iftiPrepare,
			iftiMatching,        // continue ifti matching
			resolvedSemantic,    // apply default args
			iftiResolvedSemantic,// apply default args and return to iftiMatch if necessary
			checkMatch,          // check if there is a match
			checkConstraint,     // check the constraint
			checkingConstraint,  // checking in progress
			completed,           // matching succeeded
			failed,              // matching failed
			analysis,            // analyzing template body
		}

		MatchState matchState = MatchState.start;
	}

	this(TemplateDecl parent, const ref Location loc, Expression expr, TemplArgsWithTypes args)in{
		assert(expr.isSymbol() || expr.isTemplateInstanceExp());
		assert(parent && parent.scope_);
	}body{
		super(parent.stc, parent.name);
		this.parent=parent;
		this.args=args.args;
		this.argTypes=args.argTypes;
		this.constraint = parent.constraint?parent.constraint.ddup():null;
		this.bdy=parent.bdy; // NOTE: bdy is the original template body at this point!

		this.loc = loc;

		if(!this.instantiation)
			this.instantiation = expr; // TODO: need to handle FieldExp?

		scope_ = parentScope = parent.scope_;
		sstate = SemState.begin;
	}

	this(TemplateDecl parent, const ref Location loc, Expression func, TemplArgsWithTypes args, Expression[] iftiArgs)in{
		assert(func.isSymbol() || func.isTemplateInstanceExp());
	}body{
		this(parent, loc, func, args);
		this.origIftiArgs = iftiArgs;
		this.matchState = MatchState.iftiStart;
	}

	final void gag()in{
		assert(!paramScope && !iftiScope);
	}body{
		scope_ = New!GaggingRecordingScope(parentScope);
	}

	final void ungag()in{
		assert(isGagged,text("attempted to ungag ",this," which was not gagged"));
	}body{
		assert(!!cast(GaggingRecordingScope)scope_);
		(cast(GaggingRecordingScope)cast(void*)scope_).replay(parentScope);
		scope_ = parentScope;
		paramScope.parent = parentScope;

		Scheduler().add(this, scope_);
	}

	void initializeMixin(Scope sc)in{assert(!isGagged);}body{
		isMixin=true;
		scope_ = parentScope = sc;
	}

	final @property bool isGagged(){ return scope_ !is parentScope; }

	final FunctionDecl iftiDecl()in{
		assert(finishedInstantiation());
	}body{
		return parent.iftiDecl()?bdy.decls[0].isFunctionDecl():null;
	}

	private bool determineInstanceScope()in{
		assert(paramScope && paramScope.parent is paramScope.iparent);
	}body{
		Scope instanceScope = parentScope;
		bool removeStatic = false;

		int maxn = parentScope.getFrameNesting();
		foreach(i,x;args){
			Declaration decl = null;
			if(auto addr=x.isAddressExp()) x=addr.e; // delegate literals
			if(auto sym = AliasDecl.getAliasBase(x)) decl=sym.meaning;
			else if(auto ty = x.isType()) // DMD 2.060 does not do this:
				if(auto at = ty.isAggregateTy()) decl=at.decl;
			if(!decl) continue;
			assert(!!decl && decl.scope_,x.to!string);
			// TODO: find out if it is reasonable to make this assertion pass:
			// assert(decl.scope_.getDeclaration() || decl.stc & STCstatic, decl.toString());
			if(decl.stc & STCstatic || !decl.scope_.getDeclaration())
				continue;
			auto n = decl.scope_.getFrameNesting();
			if(n>=maxn){
				maxn=n;
				if(instanceScope !is parentScope && !decl.scope_.isNestedIn(instanceScope)){
					instanceScope = parentScope;
					removeStatic=false;
					break; // TODO: fix!
				}
				instanceScope = decl.scope_;
				removeStatic=true;
			}
		}
		paramScope.iparent = instanceScope;
		return removeStatic;
	}

	private void fillScopes()in{
		assert(scope_&&paramScope);
	}body{
		foreach(i,x;resolved){
			// TODO: don't leak references
			/+if(parent.params[i].which!=WhichTemplateParameter.alias_)
				x.checkAccess(paramScope,AccessCheck.all);+/
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

	private bool checkIftiArgsValidity(){
		foreach(x;iftiArgs) if(x.sstate==SemState.error) return false;
		return true;
	}

	private bool startMatching(Scope sc_){
		auto tuplepos = parent.tuplepos;
		auto params   = parent.params;

		resolved = (new Expression[params.length]).captureTemplArgs;

		// resolve non-tuple parameters
		if(args.length>tuplepos&&tuplepos==params.length) return false;
		resolved[0..min(tuplepos, args.length)] = args[0..min(tuplepos,args.length)]; // TODO: dollar

		// TODO: does this work?
		if(!paramScope){
			paramScope = New!TemplateScope(scope_,scope_,this);
		}

		// this always fills the first tuple parameter
		// other possible semantics would be to only fill the
		// first tuple parameter if it is the last template parameter
		// this would lead to uniform treatment of multiple tuple
		// parameters in a template parameter list, which is more pure,
		// but potentially less useful.
		if(tuplepos<params.length && args.length>tuplepos){
			auto expr = args[tuplepos..args.length]; // TODO: dollar
			Expression et = New!ExpTuple(expr,New!TypeTuple(argTypes[tuplepos..args.length]));
			et.semantic(scope_);
			mixin(Rewrite!q{et});
			assert(et.sstate == SemState.completed);
			resolved[tuplepos]=et;
		}

		assert({ foreach(x;resolved)
				if(x&&x.sstate!=SemState.completed) return false;
			return true; }());
		if(!checkResolvedValidity()) return false;
		if(matchState == MatchState.iftiStart) initializeIFTI();
		return true;
	}

	private{
		Expression[] origIftiArgs;
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
		iftiArgs = origIftiArgs.dup;
		foreach(i,ref a;iftiArgs)
		if(auto ae = origIftiArgs[i].isAddressExp())
		if(ae.isUndeducedFunctionLiteral())
			a=ae.ddup();
	}

	private void prepareIFTI(){
		// TODO: this is quite inefficient
		// TODO: use region allocator and release lots of memory at once
		// TODO: keep around iftiScope, and update it correctly
		auto fdecl = parent.iftiDecl();
		assert(!!fdecl);
		auto funparams = fdecl.type.params;

		// because of tuples, the array may change its size in one iteration
		iftiEponymousParameters.length=funparams.length;
		iftiEponymousParameters.assumeSafeAppend(); // ok
		foreach(i,ref t;iftiEponymousParameters) t=funparams[i].ddup();

		iftiScope = New!NestedScope(New!GaggingScope(scope_));

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
			if(!x.type) continue;
			x.type = x.type.applySTC(x.stc);
		}

		mixin(SemChldPar!q{iftiEponymousParameters});
		iftiEponymousParameters = Tuple.expandVars(iftiScope, iftiEponymousParameters);

		foreach(i,a;iftiArgs[0..min($,iftiEponymousParameters.length)])
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
			if(fd.type.resolve(ft)){
				fd.rescope(New!GaggingScope(fd.scope_)); // TODO: allocation
				ae.sstate=sym.sstate=SemState.begin;
			}
		}

		bool resolvedSome = false;
		scope(exit)if(resolvedSome){
			foreach(i,ref a;iftiArgs)
				if(auto ae = origIftiArgs[i].isAddressExp())
					if(ae.isUndeducedFunctionLiteral())
						a=ae.ddup();
		}
		foreach(ref x;iftiArgs) mixin(SemChldPar!q{x});
		// dw(iftiArgs," ",map!(_=>_.type)(iftiArgs));

		// if this behaviour should be changed, remember to edit
		// FunctionTy.typeMatch as well
		//foreach(i,ref a;iftiEponymousParameters[0..min($,iftiArgs.length)]){
		auto numt = iftiEponymousParameters.count!((a){
				if(!a.type||!a.type.sstate==SemState.completed)
					return false;
				auto mt=a.type.getHeadUnqual().isMatcherTy();
				return mt && mt.which==WhichTemplateParameter.tuple;
			});
		for(size_t i=0,j=0;i<iftiEponymousParameters.length&&j<=iftiArgs.length;){
			auto a=iftiEponymousParameters[i];
			if(!a.type||a.type.sstate!=SemState.completed) break;
			auto mt = a.type.getHeadUnqual().isMatcherTy();
			if(mt && mt.which==WhichTemplateParameter.tuple){
				auto num=min(iftiArgs.length-j,
				             numt+iftiArgs.length-iftiEponymousParameters.length);
				if(numt+iftiArgs.length<iftiEponymousParameters.length) num=0;
				// TODO: the following is somewhat ad-hoc.
				// the reason it is here is because we cannot create a parameter of type
				// Seq!void
				alias util.any any;
				if(any!(a=>!a.type||a.type.sstate!=SemState.completed||
				        a.type is Type.get!void())(iftiArgs[j..j+num])) break;
				//TODO: gc allocation
				auto types = map!(_=>_.type.getHeadUnqual())(iftiArgs[j..j+num]).toTemplArgs;
				// mt.typeMatch(New!TypeTuple(types));
				// TODO: this might be expensive:
				mixin(TypeMatch!q{_; mt, New!TypeTuple(types)});
				i++;
				j+=num;
				continue;
			}else if(a.type.isTuple()) break;
			if(j==iftiArgs.length) break;

			auto iftiType = iftiArgs[j].type.getHeadUnqual();

			if(iftiType is Type.get!void()){
				if(auto ae = iftiArgs[j].isAddressExp()){
					if(ae.isUndeducedFunctionLiteral()){
						if(!a.type.isMatcherTy()){
							auto sym = cast(Symbol)cast(void*)ae.e;
							assert(!!cast(FunctionDef)sym.meaning);
							auto fd  = cast(FunctionDef)cast(void*)sym.meaning;
							iftiType = fd.type;
						}else{ i++; j++; continue; }
					}
				}
			}

			//a.type.typeMatch(iftiType);
			mixin(TypeMatch!q{_; a.type, iftiType});
			i++,j++;
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
			resolved[tuplepos]=New!ExpTuple((Expression[]).init);

		// strip default arguments from function types
		foreach(i;0..params.length){
			if(auto cur=resolved[i].maybe!(a=>a.isType())){
				auto ncur=cur.stripDefaultArguments();
				if(cur !is ncur) resolved[i]=ncur;
			}
		}
		
		alias util.any any;
		if(any!(_=>_ is null)(resolved)) return false;

		fillScopes();

		needRetry=false;
		return true;
	}

	final bool finishedInstantiation(){ return bdy !is parent.bdy; }

	void finishInstantiation(bool startAnalysis)in{
		assert(sstate != SemState.error);
		assert(!hasFailedToMatch());
		assert(!finishedInstantiation());
		assert(parent.sstate == SemState.completed);
		assert(!!paramScope);
	}body{
		auto r = parent.getUniqueInstantiation(this);
		if(r !is this){
			if(!r.finishedInstantiation) r.finishInstantiation(startAnalysis);
			else if(startAnalysis) r.startAnalysis();
			mixin(RewEplg!q{r});
		}
		match=Match.exact; // everything within resolved has been converted accordingly

		auto bdyscope=New!NestedScope(paramScope);
		bdy = bdy.ddup();

		bdy.stc|=parent.stc;
		if(!isMixin){
			if(determineInstanceScope()){
				bdy.stc&=~STCstatic;
				foreach(decl;&bdy.traverseInOrder){
					decl.stc&=~STCstatic;
					if(auto fd=decl.isFunctionDef())
						fd.inferStatic=true; // TODO: also infer this for other declarations
				}
			}
		}else bdy.stc&=~STCstatic;
		auto instanceScope = paramScope.iparent;
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
		if(matchState==MatchState.analysis) return;
		matchState = MatchState.analysis;
		if(!isGagged) Scheduler().add(this, scope_);
	}

	private bool resolveDefault(Scope sc){
		bool resolvedSome = false;
		auto params = parent.params;
		// TODO: check whether the default argument matches
		enum SemRet = q{ return true; }; // TODO: get rid of this again
		foreach(i,ref r; resolved.unsafeByRef)
			if(!r&&params[i].init_){
				r=params[i].init_.ddup();
				resolvedSome = true;
			}
		foreach(r;resolved) if(r) r.prepareInterpret();
		foreach(ref r;resolved.unsafeByRef()) if(r) mixin(SemChldPar!q{r});
		foreach(i,ref x;resolved.unsafeByRef()){
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
		enum fail = q{ sstate=SemState.completed; matchState = failed; goto case failed; };
		// assert(sstate != SemState.error); // would like to have this
		alias scope_ sc;
		needRetry=false;
		Ldecide:final switch(matchState) with(MatchState){
			case start, iftiStart:
				if(!startMatching(sc_))
					mixin(fail);
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
				if(matchState == iftiResolvedSemantic && !iftiAgain)
					if(!checkIftiArgsValidity())
						mixin(fail);
				if(matchState == resolvedSemantic || !iftiAgain){
					matchState = checkMatch;
					goto case checkMatch;
				}else{
					matchState = iftiPrepare;
					goto case iftiPrepare;
				}

			case checkMatch:
				foreach(ref x;resolved.unsafeByRef()){if(x) mixin(SemChld!q{x});}
				if(!checkResolvedValidity()||!finishMatching())
					mixin(fail);

				// do implicit conversions
				foreach(i; 0..resolved.length){
					auto x = resolved[i];
					scope(exit) resolved[i]=x;

					auto p = parent.params[i];
					mixin(Rewrite!q{x});
					if(x.isType()) continue;
					if(p.which==WhichTemplateParameter.constant){
						mixin(ImplConvertTo!q{x,p.type});
						x.semantic(sc);
						x.interpret(sc);
						mixin(Rewrite!q{x});
						mixin(PropErr!q{x});
						assert(x.sstate == SemState.completed);
					}else if(p.which==WhichTemplateParameter.tuple)
						break;
				}

				matchState = checkConstraint;
				goto case checkConstraint;
			case checkConstraint:
				auto uniq=parent.getUniqueInstantiation(this);
				if(uniq is this){
					if(constraint){
						analyzeConstraint();
						mixin(SemCheck);
						if(!constraint.interpretV()){
							mixin(fail);
						}
					}
				}else{
					if(!uniq.completedMatching) mixin(SemChld!q{uniq});
					assert(uniq.completedMatching);
					if(uniq.matchState == failed){ matchState=failed; goto case failed; }
				}

				matchState = completed;
				goto case completed;
			case checkingConstraint:
				if(sc) sc.error("recursive template expansion in template constraint", constraint.loc);
				mixin(ErrEplg);
				// give the instance exp a chance to finish the instantiation process
			case completed,failed: Scheduler().remove(this); break;
			case analysis:
				assert(finishedInstantiation);
				instanceSemantic(sc_);
				break;
		}
	}

	void emitError(Scope sc)in{assert(hasFailedToMatch());}body{
		if(!sc||!sc.handler.showsEffect) return;
		if(constraint&&constraint.sstate==SemState.completed&&
		   constraint.isConstant()&&!constraint.interpretV()){
			//TODO: show exact failing clause
			sc.error("template constraint failed", loc);
		}else{
			// TODO: more explicit error message
			sc.error("instantiation does not match template declaration",loc);
		}
	}

	private void instanceSemantic(Scope sc_)in{
		assert(finishedInstantiation);
	}body{
		{alias sc_ sc;mixin(SemPrlg);}
		assert(sstate == SemState.begin);
		sstate = SemState.started;
		scope(exit) if(sstate == SemState.started) sstate = SemState.begin;
		assert(!constraint||constraint.type is Type.get!bool());
		assert(!constraint||constraint.isConstant() && constraint.interpretV());
		assert(bdy !is parent.bdy);

		scope(exit) if(sstate == SemState.error)
            sc_.note("instantiated here",instantiation.loc);// TODO: improve

		{alias sc_ sc;mixin(SemChld!q{sc=bdy.scope_;bdy});}
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

import rope_;
interface Tuple{
	Expression index(Scope sc, InContext inContext, const ref Location loc, ulong index)
		in{assert(index<length);}
	Expression slice(const ref Location loc, ulong a, ulong b)
		in{assert(a<=b && b<length);}

	@property size_t length();

	int opApply(scope int delegate(Expression) dg);

	static T expand(T,S...)(Scope sc,AccessCheck accessCheck,T a, ref Expression leftover, ref S replicate)if(is(T _:X[],X)||is(T _:Rope!(X,TemplArgInfo),X)){
		T r;
		S rep;
		Expression oldLeftover=leftover;
		leftover=null;
		static if(is(T _:X[],X))enum isarray=true;else enum isarray=false; // TODO: fix this ASAP
		typeof(r.length) index = 0;
		foreach(i,x;a){
			if(!x) continue;
			if(x.isTuple()||x.type&&x.type.isTuple()){
				size_t len;
				void spliceExpTuple(ExpTuple et){
					static if(isarray){
						auto exprs=et.exprs.array;
						foreach(ref exp;exprs){
							exp=exp.clone(sc,InContext.none,accessCheck,et.loc);
							exp.checkAccess(sc, accessCheck);
						}
						static if(!rep.length){
							if(exprs.length&&leftover){
								auto ne=New!(BinaryExp!(Tok!","))(leftover, exprs[0]);
								ne.loc=ne.e1.loc.to(ne.e2.loc);
								ne.semantic(sc);
								exprs[0]=ne;
								leftover=null;
							}
						}
					}else{
						auto exprs=et.exprs;
						assert(accessCheck==AccessCheck.none);
					}
					r~=a[index..i]~exprs;
				}
				if(auto et=x.isExpTuple()){
					len=et.length;
					spliceExpTuple(et);
				}else if(auto tt=x.isTypeTuple()){
					len=tt.length;
					static if(isarray) T tts=tt.types.generalize!Expression.array;
					else T tts=tt.types.generalize!Expression;
					r~=a[index..i]~tts; // TODO: ok?
				}else static if(isarray&&!rep.length){
					if(auto ce=x.isCommaExp()){
						ExpTuple et;
						auto commaLeft=splitCommaExp(ce,et);
						if(!leftover) leftover=commaLeft;
						else{
							auto nl=New!(BinaryExp!(Tok!","))(leftover, commaLeft);
							nl.loc=nl.e1.loc.to(nl.e2.loc);
							leftover=nl;
						}
						spliceExpTuple(et);
					}else assert(0);
				}else assert(0);
				foreach(j,ref rr;rep){
					rr~=replicate[j][index..i];
					foreach(k;0..len) rr~=replicate[j][i];
				}
				index=i+1;
			}
		}
		if(index){
			foreach(j,ref rr;rep) rr~=replicate[j][index..$];
			foreach(j,rr;rep) replicate[j]=rr;// bug: simple assignment does not work
		}
		if(oldLeftover){
			if(leftover){
				auto nl=New!(BinaryExp!(Tok!","))(leftover, oldLeftover);
				nl.loc=nl.e1.loc.to(nl.e2.loc);
				leftover=nl;
			}else leftover=oldLeftover;
		}
		return index?r~=a[index..a.length]:a; // TODO: dollar
	}
	static Expression splitCommaExp(CommaExp ce, ref ExpTuple et){
		Expression go(CommaExp e){
			if(auto ce=e.e2.isCommaExp()){
				auto r=New!(BinaryExp!(Tok!","))(e.e1, go(ce));
				r.loc=r.e1.loc.to(r.e2.loc);
				return r;
			}
			et=e.e2.isExpTuple();
			assert(!!et);
			return e.e1;
		}
		return go(ce);
	}

	static VarDecl[] expandVars(Scope sc, VarDecl[] a) in{
/+		alias util.all all;
		assert(all!(_=>!_.rtype&&!_.init_||_.sstate.among(SemState.completed,SemState.error))(a));+/
	}body{
		// TODO: this is very naive and inefficient
		VarDecl[] r;
		typeof(r.length) index = 0;
		foreach(i,x;a){
			if(!x.type||x.sstate==SemState.error) continue;
			if(auto tp=x.type.isTypeTuple()){
				assert(x.tupleContext && x.tupleContext.tupleAlias);
				r~=a[index..i]~x.tupleContext.vds;
				index=i+1;
			}
		}
		return index?r~a[index..$]:a;
	}
	static Parameter[] expandVars(Scope sc,Parameter[] a){ // ditto
		return cast(Parameter[])expandVars(sc,cast(VarDecl[])a);
	}

	enum toStringInitial="(";
	enum toStringFinal=")";
	enum toStringEmpty=toStringInitial~toStringFinal;
}

class ExpTuple: Expression, Tuple{
	/* indexing an expression tuple might create a symbol reference
	   therefore we need to remember the access check level.
	 */
	AccessCheck accessCheck = AccessCheck.all;

	this(Expression[] exprs){ this(exprs.captureTemplArgs); }
	this(TemplArgs exprs)in{
		alias util.all all;
	}body{
		// TODO: gc allocation
		this.exprs = exprs;
	}

	this(size_t len, Expression exp)in{
		assert(exp.sstate == SemState.completed);
		assert(len<=size_t.max);
	}body{
		auto exprsa = new Expression[cast(size_t)len];
		foreach(ref x;exprsa) x=exp;
		exprs = exprsa.captureTemplArgs;
	}

	/+private+/ this(TemplArgs exprs, Type type){// TODO: report DMD bug
		this.exprs=exprs;
		this.type=type;
		semantic(null);
	}

	override Tuple isTuple(){return this;}

	Expression index(Scope sc, InContext inContext, const ref Location loc, ulong index){
		assert(index<length); // TODO: get rid of this when DMD is fixed
		assert(sstate == SemState.completed);
		return indexImpl(sc,inContext,loc,exprs[cast(size_t)index]);
	}

	final allIndices(Scope sc, InContext inContext, const ref Location loc){
		static struct AllIndices{
			private{
				Scope sc;
				InContext inContext;
				Location loc;
				ExpTuple tp;
			}
			int opApply(scope int delegate(Expression) dg){
				foreach(exp;this.tp.exprs)
					if(auto r=dg(tp.indexImpl(sc,inContext,loc,exp)))
						return r;
				return 0;
			}
		}
		return AllIndices(sc,inContext,loc,this);
	}

	private Expression indexImpl(Scope sc, InContext inContext, const ref Location loc, Expression exp){
		auto r=exp.clone(sc,inContext,accessCheck,loc);
		r.checkAccess(sc, accessCheck);
		return r;
	}
	Expression slice(const ref Location loc, ulong a,ulong b)in{
		assert(a<=b && b<=length);
	}body{
		assert(sstate == SemState.completed);
		assert(cast(TypeTuple)type);
		auto types = (cast(TypeTuple)cast(void*)type).types;
		return New!ExpTuple(exprs[cast(size_t)a..cast(size_t)b],New!TypeTuple(types[cast(size_t)a..cast(size_t)b]));
	}
	@property size_t length(){ return exprs.length;}

	int opApply(scope int delegate(Expression) dg){
		foreach(x; exprs) if(auto r = dg(x)) return r;
		return 0;
	}

	override void semantic(Scope sc){
		mixin(SemPrlg);
		alias util.all all;

		mixin(SemChld!q{exprs.unsafeByRef});
		Expression dummyLeftover=null;
		exprs=Tuple.expand(sc, AccessCheck.none, exprs, dummyLeftover);
		assert(!dummyLeftover);

		// the empty tuple is an expression except if a type is requested
		if(exprs.length && exprs.value.typeOnly){
			auto r=New!TypeTuple(cast(TypeTemplArgs)exprs); // TODO: ok?
			assert(r.sstate == SemState.completed);
			mixin(RewEplg!q{r});
		}
		// auto tt = exprs.map!(x=>x.isType() ? assert(cast(Type)x), cast(Type)cast(void*)x : x.type).rope; // TODO: report DMD bug
		if(!type){
			auto tta = new Type[exprs.length];
			foreach(i,ref x;tta){
				if(auto ty=exprs[i].isType()) x = ty;
				else x = exprs[i].type;
			}
			auto tt = tta.captureTemplArgs;
			type = New!TypeTuple(tt);
		}
		dontConstFold();
		mixin(SemEplg);
	}

	override ExpTuple clone(Scope sc, InContext inContext, AccessCheck accessCheck, const ref Location loc){
		// auto r = New!ExpTuple(sc, exprs.map!(x => x.clone(sc,InContext.passedToTemplateAndOrAliased,loc)).rope, type); // TODO: report DMD bug
		/+auto exprsa = new Expression[exprs.length];
		foreach(i,ref x;exprsa) x = exprs[i].clone(sc,InContext.passedToTemplateAndOrAliased,loc);
		auto r = New!ExpTuple(sc, exprsa.ropeCapture, type);+/

		auto r = New!ExpTuple(exprs, type);
		r.accessCheck = accessCheck;
		r.loc = loc;
		return r;
	}


	override string toString(){return toStringInitial~join(map!(to!string)(exprs),",")~toStringFinal;}
	override @property string kind(){return "sequence";}

	override bool isConstant(){ return exprs.value.isConstant; }
	override bool isConstFoldable(){ return exprs.value.isConstFoldable; }

	override bool isLvalue(){ return exprs.value.isLvalue; }

	mixin TupleImplConvTo!exprs;

	mixin DownCastMethod;
	mixin Visitors;

	override bool tmplArgEquals(Expression rhs){
		alias util.all all;
		import std.range;
		if(auto et = rhs.isExpTuple()){
			if(et.length != length) return false;
			return all!(_=>_[0].tmplArgEquals(_[1]))(zip(exprs,et.exprs));
		}
		// this is not going to happen, since template parameters are only compared
		// if both match the instantiation => both are tuples or not tuples
		return false;
	}
	override size_t tmplArgToHash(){
		import hashtable : toHash;
		return toHash(exprs.value.hash);
	}

private:
	TemplArgs exprs;
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
	this(TypeTemplArgs types)in{
		alias util.all all;
		// assert(all!(_=>_.sstate==SemState.completed)(types));
		// assert(all!(_=>!_.isTuple())(types));
	}body{
		this.types = types;
		sstate = SemState.completed;
	}
	override void semantic(Scope sc){
		mixin(SemPrlg);
		assert(0);
	}

	override Tuple isTuple(){return this;}
	Expression index(Scope sc, InContext inContext, const ref Location loc, ulong index){
		assert(index<length); // TODO: get rid of this when DMD is fixed
		assert(sstate == SemState.completed);
		return types[cast(size_t)index];
	}

	final allIndices(){ return types; }
	Expression slice(const ref Location loc, ulong a,ulong b)in{
		assert(a<=b && b<=length);
	}body{
		assert(sstate == SemState.completed);
		return New!TypeTuple(types[cast(size_t)a..cast(size_t)b]);
	}
	@property size_t length(){ return types.length;}

	// workaround for lacking delegate contravariance
	final override int opApply(scope int delegate(Expression) dg){
		return opApply(cast(int delegate(Type))dg);
	}
	final int opApply(scope int delegate(Type) dg){
		foreach(x; types) if(auto r = dg(x)) return r;
		return 0;
	}

	override string toString(){return toStringInitial~join(map!(to!string)(types),",")~toStringFinal;}
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

	// TODO: optimize this:
	override Dependent!Type combine(Type rhs){
		if(auto tpl=rhs.isTypeTuple()){
			if(equals(rhs)) return this.independent!Type;
			if(tpl.length!=length) return null.independent!Type;
			auto ts = new Type[types.length]; // TODO: allocation (eg. prune allocation when combination yields)
			foreach(i;0..types.length){
				mixin(Combine!q{auto r; types[i], tpl.types[i]});
				ts[i]=r;
			}
			return New!TypeTuple(ts.captureTemplArgs).independent!Type;
		}
		return null.independent!Type;
	}

	mixin DownCastMethod;
	mixin Visitors;

	override bool tmplArgEquals(Expression rhs){
		alias util.all all;
		import std.range;
		if(auto tt = rhs.isTypeTuple()){
			if(tt.length!=types.length) return false;
			return all!(_=>_[0].tmplArgEquals(_[1]))(zip(types,tt.types));
		}
		return false;
	}

	override size_t tmplArgToHash(){
		import hashtable : toHash;
		return toHash(types.value.hash);
	}

	static TypeTemplArgs expand(R)(R tts)if(isInputRange!R&&is(ElementType!R==Type)){
		TypeTemplArgs r;
		foreach(x;tts){
			if(auto ty=x.isTypeTuple()) r~=ty.types;
			else r~=x;
		}
		return r;
	}

	override protected Type getArray(ulong size){
		assert(0,text("cannot create array of ",this));
	}
	private static funcliteralTQ(){string r;
		// TODO: make those more efficient for very long tuples.
		// TODO: replace funcliteralTQ by delegate literal once possible.
		foreach(x; typeQualifiers){ // getConst, getImmutable, getShared, getInout.
			auto impl(string s){
				return `New!TypeTuple(types.map!(t=>t.`~s~`()).array.captureTemplArgs)`;
			}
			r ~= mixin(X!q{
				protected override Type get@(upperf(x))Impl(){
					return @(impl(`get`~upperf(x)));
				}
				override Type getTail@(upperf(x))(){
					return @(impl(`getTail`~upperf(x)));
				}
				override Type in@(upperf(x))Context(){return @(impl(`in`~upperf(x)~`Context`));}
			});
		}
		return r;
	}
	mixin(funcliteralTQ);
private:
	TypeTemplArgs types;
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
				return (AliasDecl.getAliasBase(arg)||arg.isType()||arg.isConstant()).independent;
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
			if(auto fd = lit.meaning.isFunctionDecl()){
				if(fd.type.hasUnresolvedParameters()){
					lit.sstate = SemState.begin;
					fd.sstate = SemState.pre;
					fd.scope_ = null;
					lit.meaning = fd.templatizeLiteral(sc,lit.loc);
					lit.inContext = InContext.none;
					lit.meaning.semantic(sc);
					mixin(Rewrite!q{lit.meaning});
					assert(lit.meaning.sstate == SemState.completed && !lit.meaning.needRetry);
					x = lit;
				}
				return;
			}
		}
		if(x.isType()||AliasDecl.getAliasBase(x)) return;
		x.interpret(sc);
	}


	override void semantic(Scope sc){
		if(sstate == SemState.pre) presemantic(sc);
		mixin(SemPrlg);
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
	private Declaration matchHelper(bool isIFTI, T...)(Scope sc, const ref Location loc, bool gagged, bool isMixin, T ts){
		static if(isIFTI) assert(!isMixin);
		alias ts[isIFTI+1] args; // respect this_
		assert(!!scope_);
		assert(sstate == SemState.completed);

		// shortcut, could also be left out
		static if(!isIFTI) if(!isMixin) if(auto r=store.lookup(args.args)){
			if(r.finishedInstantiation()){
				if(!gagged&&r.isGagged()) r.ungag();
				return r;
			}
		}

		auto inst = New!TemplateInstanceDecl(this,loc,ts[isIFTI..$]);
		if(isMixin) inst.initializeMixin(sc);
		if(gagged) inst.gag();

		if(!inst.completedMatching){
			inst.semantic(sc);
			mixin(Rewrite!q{inst});
		}
		return inst;
	}

	TemplateInstanceDecl getUniqueInstantiation(TemplateInstanceDecl inst){
		if(!inst.isMixin){
			if(auto exst = store.lookup(inst.resolved)) inst = exst;
			else store.add(inst);
		}
		// dw("built ", inst);
		return inst;
	}

	override Declaration matchInstantiation(Scope sc, const ref Location loc, bool gagged, bool isMixin, Expression expr, TemplArgsWithTypes args){
		auto r=matchHelper!false(sc, loc, !sc||!sc.handler.showsEffect||gagged, isMixin, expr, args);
		return r;
	}

	override Declaration matchIFTI(Scope sc, const ref Location loc, Type this_, Expression func, TemplArgsWithTypes args, Expression[] funargs){
		if(!iftiDecl) return matchInstantiation(sc, loc, !sc||!sc.handler.showsEffect, false, func, args);
		auto gagged=!sc||!sc.handler.showsEffect; // TODO: get rid of !sc
		auto r=matchHelper!true(sc, loc, gagged, false, this_, func, args, funargs);
		// TODO: more explicit error message
		if(!r && !gagged) sc.error("could not match call to function template",loc);
		return r;
	}

	final override Dependent!Declaration matchCall(Scope sc, const ref Location loc, Type this_, Expression func, Expression[] args, ref MatchContext context){
		assert(0);
	}

	void forallInstances(scope void delegate(TemplateInstanceDecl) dg){
		foreach(k,v;store.instances) dg(v);
	}


private:
	struct TemplateInstanceStore{
		import hashtable;
		static bool eq(TemplArgs a,TemplArgs b){
			if(a.length!=b.length) return false;
			foreach(i;0..a.length) if(!a[i].tmplArgEquals(b[i])) return false;
			return true;
		} // equality check
		static size_t h0(TemplArgs a){ return a.tmplArgToHash(); }      // hash

		private HashMap!(TemplArgs,TemplateInstanceDecl, eq, h0) instances;


		void add(TemplateInstanceDecl decl)in{
			assert(decl.completedParameterResolution);
		}body{
			foreach(x; decl.resolved)
				if(auto ty = x.isType())
					if(ty.hasPseudoTypes())
						return;

			instances[decl.resolved] = decl;
		}

		TemplateInstanceDecl lookup(TemplArgs args){
			return instances.get(args,null);
		}
	}

	TemplateInstanceStore store;
}


mixin template Semantic(T) if(is(T==TemplateMixinDecl)){
	// TODO: peek into ongoing instantiation for more precision?
	override void potentialInsert(Scope sc, Declaration dependee){
		sc.potentialInsertArbitrary(dependee,this);
	}
	override void potentialRemove(Scope sc, Declaration dependee){
		sc.potentialRemoveArbitrary(dependee,this);
	}

	override void presemantic(Scope sc){
		if(sstate != SemState.pre) return;
		TemplateInstanceExp tie;
		if(auto ti=inst.isTemplateInstanceExp()) tie = ti;
		else{
			tie = New!TemplateInstanceExp(inst,(Expression[]).init);
			tie.loc = inst.loc;
			inst = tie;
		}
		tie.isMixin = true;
		tie.willAlias();
		tie.matchingOnly();
		scope_ = sc;
		sstate = SemState.begin;
		potentialInsert(sc, this);
	}

	NamespaceDecl nspace = null;

	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(sstate == SemState.pre) presemantic(sc);
		scope(exit) if(!needRetry) potentialRemove(sc, this);
		mixin(SemChld!q{inst});
		assert(cast(Symbol)inst,text(inst," ",inst.sstate," ",typeid(this.inst)));
		auto sym=cast(Symbol)cast(void*)inst;
		assert(cast(TemplateInstanceDecl)sym.meaning);
		auto meaning=cast(TemplateInstanceDecl)cast(void*)sym.meaning;
		meaning.bdy.pickupSTC(stc);
		meaning.startAnalysis();
		auto instsc=meaning.bdy.scope_;
		if(!sc.addImport(instsc,ImportKind.mixin_)) mixin(ErrEplg);
		potentialRemove(sc, this);
		sym.makeStrong();
		mixin(SemChld!q{inst});
		if(name&&!nspace) nspace = New!NamespaceDecl(instsc,name);
		if(nspace) mixin(SemChld!q{nspace});
		mixin(SemEplg);
	}

	override int traverseInOrder(scope int delegate(Declaration) dg){
		if(auto r=dg(this)) return r;
		if(auto sym=inst.isSymbol())
		if(sym.meaning)
		if(auto meaning=sym.meaning.isTemplateInstanceDecl())
			return meaning.bdy.traverseInOrder(dg);
		return 0;
	}
}

class NamespaceDecl: Declaration{
	Scope sc;
	this(Scope sc,Identifier name){ super(STC.init,name); this.sc=sc; }

	override string toString(){ return name.toString(); }
	override @property string kind(){ return "name space"; }

	mixin Visitors;
	mixin DownCastMethod;
}
mixin template Semantic(T) if(is(T==NamespaceDecl)){}

mixin template Semantic(T) if(is(T==TemplateInstanceExp)){
	TemplArgs analyzedArgs;
	TypeTemplArgs argTypes;

	@property bool analyzedArgsInitialized(){
		return analyzedArgs.length||!args.length;
	}
	bool isMixin = false;

	override void semantic(Scope sc){
		mixin(SemPrlg);
		// eponymous template trick
		if(!!res){
			if(inContext==InContext.called) iftiResSemantic(sc);
			else instantiateResSemantic(sc);
			return;
		}
		mixin(RevEpoLkup!q{e});
		foreach(x; args){
			x.willPassToTemplate();
			if(x.sstate != SemState.completed && !x.isFunctionLiteralExp())
				x.prepareInterpret();
			x.weakenAccessCheck(AccessCheck.none);
		}
		e.willInstantiate();
		mixin(SemChld!q{e});
		if(auto r=e.isUFCSCallExp()){
			if(auto sym=r.e.isSymbol()) sym.inContext=InContext.none; // clear context
			auto tmpl = New!TemplateInstanceExp(r.e,args);
			tmpl.loc = loc;
			tmpl.willCall();
			r.instantiate(tmpl, inContext==InContext.called);
			r.semantic(sc);
			mixin(RewEplg!q{r});
		}
		mixin(SemChld!q{args});
		alias util.any any;

		Expression container = null;
		auto sym = e.isSymbol();
		AccessCheck accessCheck;
		if(!sym){
			if(auto fld = e.isFieldExp()){
				container = fld.e1;
				sym = fld.e2;
				accessCheck = fld.accessCheck;
			}else{
				// TODO: this error message has a duplicate in Declaration.matchInstantiation
				sc.error(format("can only instantiate templates, not %s%ss",e.kind,e.kind[$-1]=='s'?"e":""),loc);
				mixin(ErrEplg);
			}
		}else accessCheck=sym.accessCheck;

		foreach(i,ref x; args){
			TemplateDecl.finishArgumentPreparation(sc, x);
			mixin(PropRetry!q{x});
		}
		mixin(SemChld!q{args});

		if(!analyzedArgsInitialized){
			analyzedArgs = args.captureTemplArgs();
			Expression dummyLeftover=null;
			analyzedArgs = Tuple.expand(sc,AccessCheck.none,analyzedArgs,dummyLeftover);
			assert(!dummyLeftover);
			argTypes = TypeTuple.expand(args.map!((a){
				// TODO: this is hacky (the type passed is irrelevant), better approaches?
				if(auto tt=a.isTypeTuple()) return tt;
				return a.type;
			}));
		}
		mixin(SemProp!q{sym.meaning});

		if(inContext==InContext.called) return IFTIsemantic(sc,container,sym,accessCheck);
		instantiateSemantic(sc,container,sym,accessCheck);
	}

	Expression[] iftiArgs;
	mixin ContextSensitive;

	private void IFTIsemantic(Scope sc, Expression container, Symbol sym, AccessCheck accessCheck){
		mixin(SemChld!q{e,args});
		type = type.get!void();
		// the state will be reset in matchCallHelper
		if(!inst) mixin(SemEplg);
		finishSemantic(sc, container, sym, accessCheck);
	}

	override Dependent!Expression matchCallHelper(Scope sc, const ref Location loc, Type th_, Expression[] funargs, ref MatchContext context){
		assert(!th_);
		enum SemRet = q{ return this.independent!Expression; };
		assert(inContext==InContext.called);
		assert(sstate == SemState.completed || sstate == SemState.begin);
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
		inst = sym.meaning.matchIFTI(sc, loc, this_, this, TemplArgsWithTypes(analyzedArgs,argTypes), funargs);
		if(!inst||inst.sstate==SemState.error) mixin(ErrEplg);

		if(!inst.isTemplateInstanceDecl
		|| !(cast(TemplateInstanceDecl)cast(void*)inst).completedMatching){
			mixin(SemChld!q{inst});
		}
		if(sc) semantic(sc);
		else needRetry = true;
		mixin(SemRet);
	}


	private void instantiateSemantic(Scope sc, Expression container, Symbol sym, AccessCheck accessCheck){
		if(!inst){
			inst = sym.meaning.matchInstantiation(sc, loc, false, isMixin, this, TemplArgsWithTypes(analyzedArgs,argTypes));
			if(!inst||inst.sstate==SemState.error) mixin(ErrEplg);
		}
		assert(!!inst);
		finishSemantic(sc, container, sym, accessCheck);
	}

	private void finishSemantic(Scope sc, Expression container, Symbol sym, AccessCheck accessCheck){
		if(!inst.isTemplateInstanceDecl
		|| !(cast(TemplateInstanceDecl)cast(void*)inst).completedMatching){
			mixin(PropErr!q{inst});
			mixin(SemChld!q{inst});
		}

		if(auto symm=inst.isSymbolMatcher()){
			assert(symm.hasFailedToMatch());
			symm.emitError(sc);
			mixin(ErrEplg);
		}

		assert(!!cast(TemplateInstanceDecl)inst, text(typeid(this.inst)));
		auto inst = cast(TemplateInstanceDecl)cast(void*)inst; // update static type of inst

		if(inst.hasFailedToMatch()){
			inst.emitError(sc);
			mixin(ErrEplg);
		}

		auto decl = inst.parent;

		if(!isMixin && decl.isMixin){
			sc.error("cannot instantiate a mixin template regularly", loc);
			sc.note("declared here", decl.loc);
			mixin(ErrEplg);
		}

		needRetry=false;

		// ! changing meaning of 'sym'
		if(!inst.finishedInstantiation()){
			inst.finishInstantiation(!matchOnly); // start analysis?
			mixin(Rewrite!q{inst});
		}
		if(sc.handler.showsEffect&&inst.isGagged) inst.ungag();
		sym = New!Symbol(inst);
		sym.loc = loc;
		sym.accessCheck = accessCheck;
		if(matchOnly) sym.makeWeak(); // do not propagate errors
		transferContext(sym);
		if(inst.instantiation is this)
			inst.instantiation = sym; // transfer ownership

		if(container && !isMixin){
			auto res = New!(BinaryExp!(Tok!"."))(container, sym);
			res.loc = loc;
			this.res = res;
		}else res = sym;

		if(!isMixin){
			// for eponymous template trick: attempt lookup and don't perform trick if it fails
			eponymous=New!Identifier(decl.name.name);
			eponymous.loc=loc;
			eponymous.accessCheck=accessCheck;
		}
		semantic(sc); // no indefinite recursion because 'res' is now set
	}

	private void instantiateResSemantic(Scope sc){
		if(eponymous){
			if(!eponymous.meaning && eponymous.sstate != SemState.failed
			   && eponymous.sstate != SemState.error){
				eponymous.recursiveLookup = false;
				mixin(Lookup!q{_; eponymous, sc, res.getMemberScope()});
			}
			if(auto nr=eponymous.needRetry) { needRetry = nr; return; }
			mixin(PropErr!q{eponymous});
		}
		if(!eponymous||eponymous.sstate == SemState.failed){
			needRetry=false;
			auto r = res;
			if(r.sstate!=SemState.completed&&r.sstate!=SemState.error)
				r.needRetry=true; // let the caller do the semantic analysis
			mixin(RewEplg!q{r});
		}
		Expression r=New!(BinaryExp!(Tok!"."))(res, eponymous);
		r.loc=loc;
		r.needRetry=true; // let the caller do the semantic analysis
		transferContext(r);
		mixin(RewEplg!q{r});
	}

	private void iftiResSemantic(Scope sc){
		// TODO: fix this kludge
		instantiateResSemantic(sc);
		if(!rewrite) return;
		assert(!!cast(Expression)rewrite);
		if((cast(Expression)cast(void*)rewrite).isType()) return;
		auto tmp = rewrite.sstate!=SemState.completed?null.independent!Expression:
			(cast(Expression)cast(void*)rewrite).matchCall(sc, loc, iftiArgs);
		if(tmp.dependee||!tmp.value){
			static class MatchCallWhenReady: Expression{
				Expression exp;
				Expression[] iftiArgs;
				this(Expression e, const ref Location l, Expression[] ia){
					exp = e; loc = l; iftiArgs = ia;
				}
				override void semantic(Scope sc){
					mixin(SemPrlg);
					mixin(SemChld!q{exp});
					Expression r;
					auto f=exp;
					if(exp.isType()) r=exp;
					else{
						mixin(MatchCall!q{r; exp, sc, loc, iftiArgs});
						if(!r) mixin(ErrEplg);
					}
					if(rewrite) return; // TODO: ok?
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
			if(unresolved&&!unresolved.inexistent(sc,eponymous))
				mixin(ErrEplg);
		}else{
			mixin(RevEpoNoHope!q{e});
		}
	}

	public final void matchingOnly(){
		matchOnly = true;
	}

private:
	Expression res;
	Identifier eponymous;
	Declaration inst;

	bool matchOnly = false;
}

mixin template Semantic(T) if(is(T==ABinaryExp)){
}
mixin template Semantic(T) if(is(T _==BinaryExp!S,TokenType S) && !is(T==BinaryExp!(Tok!"."))){
	static if(is(T _==BinaryExp!S,TokenType S)):

	static if(overloadableBinary.canFind(TokChars!S) || TokChars!S[$-1]=='=' &&
	          overloadableBinary.canFind(TokChars!S[0..$-1])||S==Tok!"=="||S==Tok!"!="){
		mixin OpOverloadMembers;
		static if(overloadableBinary.canFind(TokChars!S)){
			Expression opoverloadR;
			Expression oofunR;
		}
	}
	static if(S==Tok!"!in"){
		Expression opin;
	}

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
			if((e1.canMutate()||e1.isLengthExp())&&(S==Tok!"="||!e1.type.isTypeTuple())){
				type = e1.type;
				static if(S==Tok!"~="){
					if(auto tt=type.isDynArrTy()){
						auto elt=tt.getElementType();
						mixin(ImplConvertsTo!q{auto e2toelt; e2, elt});
						if(e2toelt) e2=e2.implicitlyConvertTo(elt);
						else e2=e2.implicitlyConvertTo(type);
					}else goto Lnomatch;
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
				static if(S==Tok!"="){
					if(e1.type.isTypeTuple()){
						auto r=New!TupleAssignExp(e1,e2);
						r.brackets=brackets; // (for formatting)
						r.loc=loc;
						r.semantic(sc);
						mixin(RewEplg!q{r});
					}
				}
				mixin(.SemEplg); // don't const fold lhs
			}else{
			Lnomatch:
				// TODO: opAssign
				static if(overloadableBinary.canFind(TokChars!S[0..$-1])&&TokChars!S[$-1]=='='){
					mixin(OpOverload!("opOpAssign",q{
								[LiteralExp.polyStringFactory(TokChars!S[0..$-1])]
									},"[e2]","e1"));
				}
				if(!e1.checkMutate(sc,loc)) mixin(ErrEplg);
				if(e1.finishDeduction(sc) && e2.finishDeduction(sc)){
					static if(S==Tok!"~="){
						// TODO: allocation
						sc.error(format("cannot append to expression of type '%s'", type),loc);
					}else{
						sc.error(format("cannot use expression of type '%s' in the left hand side of '"~TokChars!S~"'",e1.type),loc);
					}
				}
				mixin(ErrEplg);
			}
		//sc.error(format("expression '%s' is not assignable",e1.loc.rep),loc);
		}else static if(S==Tok!"in"){
			// TODO
		}else static if(S==Tok!"!in"){
			if(!opin){
				opin = New!(BinaryExp!(Tok!"in"))(e1,e2);
				opin.loc=loc;
			}
			mixin(SemChld!q{opin});
			auto bl = Type.get!bool();
			mixin(ConvertsTo!q{bool conv; opin, bl});
			if(conv){
				auto r = New!(UnaryExp!(Tok!"!"))(opin);
				r.loc=loc;
				r.semantic(sc);
				mixin(RewEplg!q{r});
			}
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
				// promote comparison method of the enum base type
				if(auto et=tyu.isEnumTy()){
					mixin(GetEnumBase!q{tyu;et.decl});
					tyu=tyu.getHeadUnqual();
				}
				mixin(ImplConvertToPar!q{e1,ty});
				mixin(ImplConvertTo!q{e2,ty});
				// TODO: figure out exact spec for is and !is
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
			// integral promote enum types to unqualified base
			if(auto et1=t1.isEnumTy()){
				mixin(GetEnumBase!q{t1;et1.decl});
				t1=t1.getHeadUnqual();
			}
			if(auto et2=t2.isEnumTy()){
				mixin(GetEnumBase!q{t2;et2.decl});
				t2=t2.getHeadUnqual();
			}

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
							if(e2.isConstant() && e2.interpretV() == Variant(0,e2.type)){
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
					}else{
						mixin(RefCombine!q{auto ty; el1, el2, 0});
						if(ty) type = ty;
						else{ // TODO: there might be a better place/approach for this logic
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

				if(f1&&!e1.type.getUnqual().equals(type.getUnqual()))
				   e1=e1.implicitlyConvertTo(type);
				if(f2&&!e2.type.getUnqual().equals(type.getUnqual()))
				   e2=e2.implicitlyConvertTo(type);
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
			if(!e1.finishDeduction(sc) || !e2.finishDeduction(sc)) goto Lerr;
			{
			// operator overloading with opBinary and opBinaryRight
			static if(overloadableBinary.canFind(TokChars!S)){
				mixin(BuildOpOver!("opoverloadR","e2","opBinaryRight",
				      q{[LiteralExp.polyStringFactory(TokChars!S)]}));
				mixin(BuildOpOver!("opoverload","e1","opBinary",
				      q{[LiteralExp.polyStringFactory(TokChars!S)]}));
				if(!oosc) oosc=New!GaggingScope(sc);

				opoverloadR.willCall();
				opoverload.willCall();
				if(auto ti=opoverloadR.isTemplateInstanceExp()) ti.matchingOnly();
				if(auto ti=opoverload.isTemplateInstanceExp()) ti.matchingOnly();

				mixin(SemChldPar!q{sc=oosc;opoverloadR});
				mixin(SemChldPar!q{sc=oosc;opoverload});

				if(!oofun&&opoverload.sstate==SemState.completed){
					bool other = opoverloadR.sstate==SemState.completed;
					if(opoverload.isUFCSCallExp()) other = true;
					auto oofund=opoverload.matchCall(other?oosc:sc, loc, [e2]);
					if(oofund.dependee.node){
						mixin(PropRetry!q{oofund.dependee.node});
						if(!other) mixin(PropErr!q{oofund.dependee.node});
					}
					oofun=oofund.value;
					if(!oofun) mixin(SetErr!q{opoverload});
				}
				if(oofun) mixin(SemChldPar!q{sc=oosc;oofun});

				if(!oofunR&&opoverloadR.sstate==SemState.completed){
					auto oofunRd=opoverloadR.matchCall(oosc, loc, [e1]);
					if(oofunRd.dependee.node){
						mixin(PropRetry!q{oofunRd.dependee.node});
					}
					oofunR=oofunRd.value;
					if(!oofunR) mixin(SetErr!q{opoverloadR});
				}
				if(oofunR) mixin(SemChldPar!q{sc=oosc;oofunR});

				MatchContext context, contextR;
				Expression r;

				if(oofunR && oofunR.sstate == SemState.completed)
					oofunR.matchCallHelper(oosc, loc, null, [e1], contextR).force;
				else contextR.match=Match.none;
				if(oofun && oofun.sstate == SemState.completed)
					oofun.matchCallHelper(oosc, loc, null, [e1], context).force;
				else context.match=Match.none;
				if(contextR.match!=context.match){
					if(contextR.match>context.match){
						opoverloadR=null;
						mixin(BuildOpOver!("opoverloadR","e2","opBinaryRight",
						      q{[LiteralExp.polyStringFactory(TokChars!S)]}));
						auto tmpe=New!TmpVarExp(e1);
						tmpe.loc=loc;
						tmpe.semantic(sc);
						assert(!!tmpe.sym);
						auto c=New!CallExp(opoverloadR,[tmpe.sym]);
						r=New!(BinaryExp!(Tok!","))(tmpe,c);
						r.loc=c.loc=loc;
					}else{
						r=New!CallExp(oofun,[e2]);
						r.loc=loc;
					}
				}else if(context.match!=Match.none){
					// TODO: consider specialization
					sc.error(format(mixin(X!"Both '%s.opBinary!\"@(TokChars!S)\"(%s)' and '%s.opBinaryRight!\"@(TokChars!S)\"(%s)' are equally well matching operator overloads"),e1.loc.rep,e2.loc.rep,e2.loc.rep,e1.loc.rep),loc);
					mixin(ErrEplg);
				}
				oosc=null;
				if(r){r.semantic(sc);mixin(RewEplg!q{r});}
			}
			static if(S==Tok!"in"){
				type = Type.get!bool();
				super.semantic(sc);// TODO: implement
			}
			sc.error(format("incompatible types '%s' and '%s' for binary "~TokChars!S,e1.type,e2.type),loc);
			}
		Lerr:mixin(ErrEplg);
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

	static if(S==Tok!","){
		override void isInContext(InContext inContext){
			e2.isInContext(inContext);
		}
		override bool isLvalue(){
			return e2.isLvalue();
		}
	}

	static if(isAssignOp(S))
		override bool isLvalue(){
			return true;
		}

	static if(S==Tok!"~"){ // '~' always reallocates, therefore conversion semantics are less strict
		override bool isUnique(){ return true; }
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
					}else static if(S==Tok!"<>="||S==Tok!"!<>="){
						enum value = S==Tok!"<>=";
						return @(x)(value, value, true);
					}else static if(isRelationalOp(S)){
						static if(S==Tok!"is") enum S = Tok!"==";
						else static if(S==Tok!"!is") enum S = Tok!"!=";
						else enum S = toIntegerRelationalOp(S);
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

class TupleAssignExp: TemporaryExp{
	ExpTuple e1, e2;
	Expression commaLeft1,commaLeft2;
	Expression[] assignments;
	Expression lowered;
	this(Expression e1, Expression e2)in{
		assert(e1&&e1.sstate==SemState.completed);
		assert(e2&&e2.sstate==SemState.completed);
		assert(e1.type.equals(e2.type));
		assert(e1.isLvalue());
		assert(e1.type.isTypeTuple());
	}body{
		if(auto ce1=e1.isCommaExp()) commaLeft1=ExpTuple.splitCommaExp(ce1,this.e1);
		else this.e1=e1.isExpTuple();
		if(auto ce2=e2.isCommaExp()) commaLeft2=ExpTuple.splitCommaExp(ce2,this.e2);
		else this.e2=e2.isExpTuple();
		assert(this.e1&&this.e2);
	}
	override void semantic(Scope sc){
		mixin(SemPrlg);
		type=e1.type;
		assert(e1.length == e2.length);
		if(commaLeft1){ commaLeft1.semantic(sc); assert(commaLeft1.sstate==SemState.completed); }
		if(commaLeft2){ commaLeft2.semantic(sc); assert(commaLeft2.sstate==SemState.completed); }
		if(assignments.length!=e1.length){
			// TODO: InContext.assigned
			assignments=new Expression[](e1.length);
			foreach(i,ref assgn;assignments){
				assgn=New!(BinaryExp!(Tok!"="))(e1.index(sc,InContext.none,e1.loc,i),e2.index(sc,InContext.none,e2.loc,i));
				assgn.loc=loc;
			}
		}
		foreach(ref assgn;assignments) mixin(SemChld!q{assgn});
		if(!lowered){
			Expression vars=null;
			auto symbols=new Expression[](e1.length); // TODO: allocation
			foreach(i;0..e1.length){
				auto tmpe=New!TmpVarExp(assignments[i]);
				tmpe.loc=loc;
				tmpe.semantic(sc);
				if(vars){
					auto r=New!(BinaryExp!(Tok!","))(vars,tmpe);
					r.loc=vars.loc;
					vars=r;
				}else vars=tmpe;
				symbols[i]=tmpe.sym;
			}
			lowered=New!(BinaryExp!(Tok!","))(vars,New!ExpTuple(symbols));
			lowered.loc=loc;
			if(commaLeft2){
				lowered=New!(BinaryExp!(Tok!","))(commaLeft2,lowered);
				lowered.loc=loc;
			}
			if(commaLeft1){
				lowered=New!(BinaryExp!(Tok!","))(commaLeft1,lowered);
				lowered.loc=loc;
			}
		}
		mixin(SemChld!q{lowered});
		mixin(NoRetry);
		sstate=SemState.completed;
		createTemporary(sc);
	}

	override string toString(){ return _brk(e1.toString()~"="~e2.toString()); }

	mixin Visitors;
}
mixin template Semantic(T) if(is(T==TupleAssignExp)){}

template Semantic(T) if(is(T==TernaryExp)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e1});
		e1=e1.convertTo(Type.get!bool());
		mixin(SemChld!q{e1,e2,e3});
		auto vd = Type.get!void();
		mixin(TypeCombine!q{type; e2, e3});
		if(!type){
			if(e2.type.getHeadUnqual() is vd){
				mixin(ConvertTo!q{e3,vd}); // TODO: implicit explicit conversion
				type = vd;
			}else if(e3.type.getHeadUnqual() is vd){
				mixin(ConvertTo!q{e2,vd}); // TODO: implicit explicit conversion
				type = vd;
			}else{

				sc.error(format("incompatible types for ternary operator: '%s' and '%s'",e2.type,e3.type),loc);
				mixin(ErrEplg);
			}
		}
		mixin(ImplConvertTo!q{e2,type});
		mixin(ImplConvertTo!q{e3,type});
		if(!isConstFoldable()){
			mixin(ConstFold!q{e1});
			mixin(ConstFold!q{e2});
			mixin(ConstFold!q{e3});
		}
		mixin(NoRetry);
		sstate=SemState.completed;
		if(!tmpVarDecl) if(type.isTypeTuple()) createTemporary(sc);
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

	override void isInContext(InContext inContext){
		e2.isInContext(inContext);
		e3.isInContext(inContext);
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
		Token tok;
		if(ty.sstate == SemState.error) goto no;

		assert(!!f);
		if(f.hasPseudoTypes()) mixin(ErrEplg);

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
		if(rewrite) return;
		auto r = New!LiteralExp(tok);
		r.loc = loc;
		r.semantic(sc);
		mixin(RewEplg!q{r});
	}
private:
	GaggingScope gscope;
}

mixin template Semantic(T) if(is(T==TypeidExp)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e});
		sc.error("feature TypeidExp not implemented",loc);
		mixin(ErrEplg);
		//mixin(SemEplg);
	}
}

mixin template Semantic(T) if(is(T==VoidInitializerExp)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		type = Type.get!void();
		mixin(SemEplg);
	}
}

mixin template Semantic(T) if(is(T==ArrayInitAssocExp)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		sc.error("unimplemented feature ArrayInitAssocExp",loc);
		mixin(ErrEplg);
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
	ctfe,
	all,
}
AccessCheck accessCheckCombine(AccessCheck a, AccessCheck b){ return max(a,b); }

class Symbol: Expression{
	Declaration meaning;
	protected this(){} // subclass can construct parent lazily

	// TODO: compress all these bools into a bitfield
	bool isStrong;// is symbol dependent on semantic analysis of its meaning
	bool isWeak;
	bool isFunctionLiteral; // does symbol own 'meaning'
	bool isSymbolMatcher;
	bool errorOnMatchingFailure = true;
	mixin ContextSensitive;
	private bool _ignoreProperty = false;
	@property bool ignoreProperty(){
		return _ignoreProperty||inContext==InContext.instantiated||inContext==InContext.passedToTemplateAndOrAliased;
	}
	@property void ignoreProperty(bool b)in{
		assert(inContext!=InContext.instantiated||b);
	}body{
		_ignoreProperty = b;
	}

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
	void makeWeak(){
		isWeak = true;
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
			// make emmitted circular dependency errors deterministic
			// (this is not strictly necessary, but it simplifies regression testing.)
			if(errsc.handler){
				auto first = iota(0,clist.length).reduce!((a,b)=>clist[a].sourcePriority<clist[b].sourcePriority?a:b);
				clist = chain(clist[first..$],clist[0..first]).array;
			}
			////

			errsc.error("circular dependencies are illegal",clist[0].loc);
			circ = null;
			mixin(SetErr!q{});
			foreach_reverse(x; clist[1..$]){
				// IFTI might spawn location-free identifiers
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


	override Expression clone(Scope sc, InContext inContext, AccessCheck accessCheck, const ref Location loc){
		auto r=ddup();
		r.scope_ = null;
		r.sstate = SemState.begin;
		r.loc = loc;
		r.inContext = inContext;
		r.accessCheck = accessCheck;
		r.semantic(sc);
		return r;
	}


	override void semantic(Scope sc){
		// dw("semantic: ",this," ",meaning.sstate," ", loc," ",cast(void*)meaning," ",meaning.loc," ",typeid(this.meaning));
		debug scope(exit) assert(sstate != SemState.started||needRetry||rewrite,toString()~" "~typeid(this.meaning).toString());
		debug scope(exit) assert(needRetry==2||!circ,toString()~" nR: "~to!string(needRetry)~" circ: "~to!string(circ));
		mixin(SemPrlgDontSchedule);
		// if(inContext != InContext.fieldExp) Scheduler().add(this,sc);
		if(!scope_) scope_=sc;
		assert(meaning && scope_);
		if(needRetry) sstate = SemState.begin;
		needRetry = false; // be reentrant

		if(sstate >= SemState.started){
			// template instances may depend circularly upon each other
			if(meaning.isTemplateInstanceDecl()){
				if(meaning.sstate == SemState.started){
					sstate = SemState.begin;
					needRetry = true;
					return;
				}
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
			if(auto decl = al.simpleAliasedDecl()) meaning = decl;
			else{
				// assert(!!al.aliasee.isType());
				sstate = SemState.begin;
				auto r=al.getAliasee(scope_, accessCheck, inContext, loc);
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
				if(auto sym=meaning.isSymbolMatcher()){
					assert(sym.hasFailedToMatch());
					if(errorOnMatchingFailure) sym.emitError(scope_);
					mixin(ErrEplg);
				}
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
			if(vd.stc & STCenum || (vd.init_&&vd.stc&(STCimmutable|STCconst)&&vd.willInterpretInit())){
				mixin(MeaningSemantic);
				mixin(CircErrMsg);
				mixin(SemProp!q{sc=meaning.scope_;meaning});
			}else if(!vd.type){
				mixin(MeaningSemantic);
				mixin(CircErrMsg);
				if(!vd.type) mixin(PropRetry!q{sc=meaning.scope_;meaning});
				if(!vd.type) mixin(PropErr!q{sc=meaning.scope_;meaning});
			}
			assert(!!vd.type);
			mixin(VarDecl.SymbolResolve);
			// this symbol is free-standing
			// if it is directly inside of an aggregate, then the
			// current function's this pointer type must apply
			if(inContext!=InContext.fieldExp)
				if(vd.scope_ && // (eg. delegate types do not have this)
				   !(vd.stc&(STCstatic|STCenum)))
				if(auto decl=vd.scope_.getDeclaration())
				if(decl.isAggregateDecl())
					type = type.applyScopeSTC(sc);
			if(vd.stc&STCenum){
				if(vd.init_){
					auto r=vd.init_.cloneConstant();
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
			if(inContext==InContext.called){
				auto s = New!Symbol(meaning);
				auto r = New!TemplateInstanceExp(s, (Expression[]).init);
				s.loc = r.loc = loc;
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
			if(tm.sstate != SemState.started){
				mixin(MeaningSemantic);
				mixin(CircErrMsg);
				if(!isWeak) mixin(SemProp!q{sc=meaning.scope_;meaning});
			}
			type=Type.get!void();
		}else if(auto ov=meaning.isOverloadSet()){
			foreach(ref x; ov.decls) if(auto fd = x.isFunctionDecl()){
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
			if(ov.count==1 && ov.decls.length){ // TODO: why does this not bypass sealing?
				if(auto fd=ov.decls[0].isFunctionDecl()){
					meaning = fd;
					needRetry = 1;
					return semantic(sc);
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

		if(auto et=meaning.isEnumDecl()){
			auto r = et.getType();
			sstate = SemState.begin;
			mixin(RewEplg!q{r});
		}

		needRetry = false;
		if(inContext!=InContext.fieldExp &&
		   (!isFunctionLiteral ||
		    type !is Type.get!void() &&
		    !meaning.isFunctionDef().canBeStatic)) // TODO: coerce?
		{
			performAccessCheck();
			mixin(SemCheck);
		}

		if(inoutRes!=InoutRes.none){sstate=SemState.completed;resolveInout(inoutRes);}

		if(isImplicitlyCalled()&&inContext!=InContext.fieldExp){
			auto s = New!Symbol(meaning);
			s.loc = loc;
			s.accessCheck = accessCheck;
			s.ignoreProperty = true;
			auto args = Seq!(s,(Expression[]).init);
			auto r = meaning.stc&STCproperty?New!PropertyCallExp(args):New!CallExp(args);
			r.loc = loc;
			r.semantic(sc);
			mixin(RewEplg!q{r});
		}
		// TODO: simple pointer-chain expression alias?
		if(!inContext.among(InContext.fieldExp,InContext.passedToTemplateAndOrAliased) &&
		   thisType() && maybeThisContext() &&
		   !meaning.isFunctionDecl().maybe!(a=>a.isConstructor()) &&
		   !meaning.isOverloadSet().maybe!(a=>a.isConstructor())
		){
			auto t = New!ThisExp();
			t.loc = loc;
			auto s = New!Symbol(meaning);
			s.loc = loc;
			s.accessCheck = accessCheck;
			s.ignoreProperty = ignoreProperty;
			auto r = New!(BinaryExp!(Tok!"."))(t,s);
			r.loc = loc;
			transferContext(r);
			r.semantic(sc);
			mixin(RewEplg!q{r});
		}
		mixin(SemEplg);
	}

	final bool isImplicitlyCalled(){
		return isImplicitlyCalled(inContext);
	}

	final bool isImplicitlyCalled(InContext inContext){
		Declaration implcalldecl = meaning.isFunctionDecl();
		if(!implcalldecl)
			if(auto ov=meaning.isOverloadSet())
				if(ov.hasFunctions())
					implcalldecl=meaning;
		bool implicitCall;
		switch(inContext) with(InContext){
			case called, addressTaken, instantiated, passedToTemplateAndOrAliased, fieldExp:
				implicitCall=false; break;
			default: implicitCall=true;
		}
		return implcalldecl && (implicitCall || !ignoreProperty && meaning.stc&STCproperty);
	}

	string accessError(){
		// TODO: better error message?
		if(meaning.scope_.getDeclaration().isFunctionDef())
			return format("cannot access the frame in which '%s' is stored", loc.rep);
		else{
			// error message duplicated in FieldExp.semantic
			return format("need 'this' to access %s '%s'",kind,loc.rep);
		}
	}

	void performAccessCheck() in{assert(meaning && scope_);}body{
		auto decl = scope_.getDeclaration();
		// it is necessary to perform the check in order to get
		// the correct type deduction, even if we are not interested
		// in the actual accessibility
		if(meaning.needsAccessCheck(accessCheck)){
			mixin(IsDeclAccessible!q{auto b; Declaration, decl, meaning});
			if(!b){
				scope_.error(accessError(), loc);
				scope_.note(format("%s was declared here",kind),meaning.loc);
				mixin(ErrEplg);
			}
		}
	}

	invariant(){ assert(!meaning||meaning.name !is this, text(typeid(this.meaning)," ",meaning.loc)); }
	override string toString(){
		auto tmpl=meaning.isTemplateInstanceDecl();
		if(!tmpl){
			if(auto nsts=cast(NestedScope)meaning.scope_)
			if(auto tmps=cast(TemplateScope)nsts.parent)
				tmpl=tmps.tmpl;
		}
		if(!meaning.name) return "(symbol)";
		// TODO: properly display alias delegate literal symbols
		if(tmpl && meaning.name.name==tmpl.name.name)
			return meaning.name.name~"!("~join(map!(to!string)(tmpl.args),",")~")";
		return meaning.name.toString();
	}
	override @property string kind(){return meaning.kind;}

	// TODO: maybe refactor
	override Scope getMemberScope(){
		if(auto tmpl=meaning.isTemplateInstanceDecl()) return tmpl.bdy.scope_;
		if(auto nspace=meaning.isNamespaceDecl()) return nspace.sc;
		return super.getMemberScope();
	}

	Type thisType(){
		if(!(meaning.stc&STCstatic)||meaning.isOverloadSet())
		if(meaning.scope_) // eg. parameters inside function types
		if(auto decl=meaning.scope_.getDeclaration())
		if(auto aggr=decl.isAggregateDecl())
			return aggr.getType();
		return null;
	}

	////

	override Expression extractThis(){
		if(meaning.isTemplateInstanceDecl()||meaning.isNamespaceDecl())
			return null;
		return this;
	}

	final Type maybeThisContext(){
		// (similar code in semantic, TODO: can some of it be factored out?)
		if(inContext==InContext.fieldExp) return null;
		Declaration mfun=null;
		for(auto decl=scope_.getDeclaration();
		    decl&&!decl.isAggregateDecl();
		    decl=decl.scope_.getDeclaration())
		{
			if(decl.stc&STCstatic) return null;
			mfun=decl;
		}
		if(!mfun||!mfun.isFunctionDecl()) return null;
		if(auto aggr=scope_.getAggregate())
			return aggr.getType().applyScopeSTC(scope_);
		return null;
	}

	override AccessCheck deferredAccessCheck(){
		if(meaning.isTemplateInstanceDecl()||meaning.isNamespaceDecl())
			return accessCheck;
		return super.deferredAccessCheck();
	}

	override bool isConstant(){
		assert(!!meaning,toString());
		//if(meaning.stc|STCstatic) return true;
		if(auto vd = meaning.isVarDecl())
			return vd.stc&STCenum
				|| vd.stc&(STCimmutable|STCconst)
				&& vd.init_ && vd.init_.isConstant();
		if(auto vd = meaning.isFunctionDecl()) return true;
		return false;
	}

	override bool isConstFoldable(){
		if(auto vd = meaning.isVarDecl()) return !!(vd.stc&STCenum);
		return false;
	}

	// DMD 2.058/2.059 behave approximately like this:
	/+override bool typeEquals(Type rhs){
		if(meaning.stc&STCenum)
		if(auto vd = meaning.isVarDecl()) return vd.init_.typeEquals(rhs);
		return super.typeEquals(rhs);
	}+/
	// override Type isType(){...} // TODO.
	override bool isLvalue(){
		if(meaning.isTmpVarDecl()) return !!(meaning.stc&STCref);
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
		if(meaning.isVarDecl()) return super.matchCallHelper(sc, loc, this_, args, context);
		if(!this_) this_ = maybeThisContext();
		mixin(MatchCall!q{auto m; meaning, sc, loc, this_, this, args, context});
		if(m){
			mixin(Rewrite!q{m});
			// resolve the overload in place and then rely on
			// semantic to catch eventual circular dependencies:
			meaning = m;
			isSymbolMatcher=!!meaning.isSymbolMatcher();
			sstate = SemState.begin;
			type = null;
			Symbol.semantic(scope_);
			assert(!rewrite||cast(Expression)rewrite);
			return (cast(Expression)cast(void*)(rewrite?rewrite:this)).independent;
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
				return vd.init_.getIntRange();
		}
		return super.getIntRange();
	}
	override LongRange getLongRange(){
		if(auto vd=meaning.isVarDecl()){
			if(vd.stc&STCenum || vd.stc&STCstatic&&vd.stc&STCimmutable)
				return vd.init_.getLongRange();
		}
		return super.getLongRange();
	}



	mixin DownCastMethod;
	//mixin Interpret!Symbol;
	mixin Visitors;

	Scope scope_;

	// TemplateDecl needs this.
	override bool tmplArgEquals(Expression rhs){
		if(auto sym = rhs.isSymbol()){
			auto decl = scope_.getDeclaration();
			auto sdecl = sym.scope_.getDeclaration();
			return meaning is sym.meaning &&
				Declaration.isDeclAccessible(decl, meaning).force ==
				Declaration.isDeclAccessible(sdecl, meaning).force;

		}
		return false;
	}

	override size_t tmplArgToHash(){
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
	with(InoutRes){
		if(ir1 == ir2 || ir2 == none) return ir1;
		if(ir1 == none) return ir2;
		if(ir1.among(inout_,const_,inoutConst) &&
		   ir2.among(inout_,const_,inoutConst))
			return InoutRes.inoutConst;
		return InoutRes.const_;
	}
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

class UFCSCallExp: CallExp{
	mixin DownCastMethod;
	mixin Visitors;
}
mixin template Semantic(T) if(is(T==UFCSCallExp)){
	this(Expression exp, Expression this_, bool incomplete)in{
		assert(exp.isSymbol() || exp.isType());
		assert(exp.sstate == SemState.completed);
	}body{
		super(exp, [this_]);
		this.incomplete = incomplete;
	}
	bool incomplete;
	final void moreArgs(Expression[] margs)in{
		assert(incomplete);
	}body{
		args~=margs;
		incomplete = false;
		sstate = SemState.begin;
	}
	final void instantiate(TemplateInstanceExp e, bool stillIncomplete)in{
		assert(incomplete);
		//assert(e.sstate == SemState.completed && e.inContext == InContext.called);
	}body{
		e.loc=this.e.loc.to(e.loc);
		this.e=e;
		incomplete=stillIncomplete;
		if(!incomplete) sstate = SemState.begin;
	}
	override void semantic(Scope sc){
		if(incomplete){
			type = Type.get!void();
			mixin(SemEplg);
		}
		super.semantic(sc);
	}
	override @property string kind(){ return "UFCS function call"; }
	override string toString(){
		// assert(e.toString().startsWith(".")); // TODO: fix ('this' rewrite might kill this)
		return args[0].toString()~e.toString()~"("~join(map!(to!string)(args[1..$]),",")~")";
	}

	override Dependent!Expression matchCallHelper(Scope sc, const ref Location loc, Type this_, Expression[] args, ref MatchContext context){
		if(!incomplete) return super.matchCallHelper(sc,loc,this_,args,context);
		// TODO: this allocates
		//if(e.sstate != SemState.completed) return this.independent!Expression; // TODO: this is a hack
		auto nargs=this.args~args;
		e.semantic(sc);
		if(e.needRetry||e.sstate==SemState.error)
			return Dependee(e,null).dependent!Expression;
		mixin(MatchCallHelper!q{auto m; e,sc,loc,this_,nargs,context});
		if(!m) return null.independent!Expression;
		if(m.sstate == SemState.completed)
			return this.independent!Expression;
		static class MatchCallWhenReady: Expression{
			Expression exp;
			Expression[] nargs;
			this(Expression e, const ref Location l, Expression[] nargs){
				exp = e; loc = l; this.nargs=nargs;
			}
			override void semantic(Scope sc){
				mixin(SemPrlg);
				mixin(SemChld!q{exp});
				Expression r;
				auto f=exp;
				if(exp.isType()) r=exp;
				else{
					mixin(MatchCall!q{r; exp, sc, loc, nargs});
					if(!r) mixin(ErrEplg);
				}
				if(rewrite) return; // TODO: ok?
				r = New!UFCSCallExp(r,nargs[0],true);
				r.loc = loc;
				r.semantic(sc);
				mixin(RewEplg!q{r});
			}
			override string toString(){ return exp.toString(); }
		}
		auto r = New!MatchCallWhenReady(m, loc, nargs);
		r.semantic(sc);
		return r.independent!Expression;
	}
}

// aware of circular dependencies
mixin template Semantic(T) if(is(T==CallExp)){
	Expression argsLeftover=null;

	override void noHope(Scope sc){
		mixin(RevEpoNoHope!q{e});
	}

	// This is somewhat hacky
	private void constructorRewrite(Scope sc){
		if(auto ty=e.isType())
		if(auto aggrty=ty.getUnqual().isAggregateTy())
		if(auto strd=aggrty.decl.isStructDecl()){
			// TODO: could re-use the callexp as the consCall field
			auto r = New!StructConsExp(ty, args);
			r.argsLeftover=argsLeftover;
			r.loc = loc;
			if(tmpVarDecl) r.initOfVar(tmpVarDecl);
			r.semantic(sc);
			mixin(RewEplg!q{r});
		}
	}
	private enum ConstructorRewrite = q{ constructorRewrite(sc); if(rewrite) return; };

	override void semantic(Scope sc){ // TODO: type checking
		// parameter passing
		mixin(SemPrlg);
		mixin(RevEpoLkup!q{e});
		e.willCall();
		mixin(SemChldPar!q{e});
		mixin(SemChldExp!q{args});
		mixin(PropErr!q{e});
		// eg. 1.foo(2), will be rewritten to .foo(1)(2)
		// this completes the rewrite to .foo(1,2)
		if(auto r=e.isUFCSCallExp()){
			if(r.incomplete){
				r.moreArgs(args);
				r.loc=loc;
				r.semantic(sc);
				mixin(RewEplg!q{r});
			}
		}

		mixin(ConstructorRewrite);

		if(fun is null){
			mixin(MatchCall!q{fun; e, sc, loc, args});
			// TODO: opCall
			if(fun is null) mixin(ErrEplg);
		}
		mixin(SemChld!q{fun});
		mixin(SemProp!q{e}); // catch errors generated in matchCall TODO: still relevant?

		mixin(ConstructorRewrite);

		//dw(sstate," ",map!(a=>a.needRetry)(args),args);
		assert(fun && fun.type);
		auto tt = fun.type.getHeadUnqual().getFunctionTy();
		if(!tt){
			// fun was rewritten (eg. @property call, class template)
			// TODO: opCall
			mixin(MatchCall!q{fun; fun, sc, loc, args});
			assert(fun is null);
			mixin(ErrEplg);
		}

		// TODO: this might be somewhat fragile; make 'reset'
		// a member function and implement manually where needed
		static struct Reset{
			void perform(Symbol self){
				self.scope_=null;
				self.sstate=SemState.begin;
			}
			void perform(Node self){
				if(auto e=self.isExpression())
					if(e.isType()) return;
				self.sstate=SemState.begin;
			}
		}
		if(adapted is null)
		foreach(i,x; tt.params[0..args.length]){
			if(x.stc & STClazy){
				if(adapted is null) adapted = new Expression[args.length];
				else if(adapted[i]) continue;
				auto vt=Type.get!void();
				if(x.type.getHeadUnqual() is vt){
					auto narg=New!CastExp(STC.init,vt,args[i]);
					narg.loc=args[i].loc;
					args[i]=narg;
				}
				auto ft = New!FunctionTy(STC.init,args[i].type,cast(Parameter[])[],VarArgs.none);
				auto bs = New!BlockStm(cast(Statement[])[New!ReturnStm(args[i])]); // TODO: gc allocates []
				auto dg = New!FunctionLiteralExp(ft,bs,FunctionLiteralExp.Kind.delegate_);
				bs.loc = dg.loc = args[i].loc;
				adapted[i] = dg;
				runAnalysis!Reset(args[i]);
			}
		}

		foreach(ref x;adapted) if(x) mixin(SemChld!q{x});

		type = tt.ret;

		if(tt.params.length > args.length){
			// default arguments
			import util: all;
			assert(all!(a=>a.init_ !is null)(tt.params[args.length..$]));
			// TODO: this allocates rather heavily
			args~=map!(a=>a.init_.ddup)(tt.params[args.length..$]).array;
			foreach(ref arg;args) runAnalysis!Reset(arg);
			// TODO: replace 'this'-expressions suitably
		}
		foreach(i,x; tt.params[0..args.length]){
			auto pty = x.type;
			args[i]=args[i].implicitlyConvertTo(pty);
		}
		mixin(SemChld!q{args});
		mixin(ConstFold!q{e});
		foreach(ref x; args) mixin(ConstFold!q{x});

		// call expressions may create temporary variables
		mixin(NoRetry);
		sstate=SemState.completed;
		if(!tmpVarDecl){
			if(!(tt.stc&STCbyref))
				if(auto aggrty=type.getHeadUnqual().isAggregateTy())
					if(aggrty.decl.isValueAggregateDecl()) return createTemporary(sc);
			if(type.getHeadUnqual().isTypeTuple()) return createTemporary(sc);
		}

		// mixin(SemEplg); // not necessary, since NoRetry called above
	}

	override bool isLvalue(){
		assert(!!fun.type.getHeadUnqual().getFunctionTy());
		return !!(fun.type.getHeadUnqual().getFunctionTy().stc & STCref);
	}

	override @property string kind(){ return "function call result"; }

	Expression fun;
	Expression[] adapted;
}

class PropertyCallExp: CallExp{
	this(Expression exp, Expression[] args){ super(exp,args); }
	override string toString(){ return _brk(!args.length?e.toString():e.toString()~(args.length==1?args[0].toString():"Seq!("~join(map!(to!string)(args),",")~")")); }
	override @property string kind(){ return "@property call"; }
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
	protected override Dependent!Declaration lookupImpl(Scope view, Identifier ident){
		return parent.lookupImpl(view, ident);
	}
	protected override Dependent!Declaration lookupHereImpl(Scope view, Identifier ident, bool ignoreImports){
		return parent.lookupHereImpl(view, ident, ignoreImports);
	}

	protected override Dependent!IncompleteScope getUnresolvedImpl(Scope view, Identifier ident, bool onlyMixins, bool noHope=false){
		return parent.getUnresolvedImpl(view, ident, onlyMixins, noHope);
	}

	protected override bool inexistentImpl(Scope view, Identifier ident){
		return parent.inexistentImpl(view, ident);
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
		// TODO: this requires some code duplication in ImplicitCastExp. Better solutions?
		mixin(ConvertsTo!q{bool conv; e, type});
		if(!conv){
			auto oe=e;
			relaxCastedExpression();
			if(oe !is e){
				mixin(ConvertsTo!q{auto cc; e, type});
				conv=cc;
			}
		}
		if(conv) return true.independent;
		sc.error(format("cannot cast expression '%s' of type '%s' to '%s'",e.loc.rep,e.type,type),e.loc);
		//error(format("no viable conversion from type '%s' to '%s'",e.type,type),e.loc);
		return false.independent;
	}

	final protected void relaxCastedExpression(){
		if(e.type.isSomeString()) return;
		if(auto el=e.type.getElementType())
			if(auto lit=e.isLiteralExp())
				e=lit.toArrayLiteral();
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
					fd.rescope(sc); // eg. matching overloads
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
				if(fd.stc&STCstatic && fd.inferStatic){
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

		mixin CreateBinderForDependent!("CheckConv");
		mixin(CheckConv!q{bool conversionLegal; this, sc});
		if(!conversionLegal) mixin(ErrEplg);

		auto el = type.getElementType();
		if(el && el.getHeadUnqual() !is Type.get!void()){
			if(auto al = e.isArrayLiteralExp()){
				al.sstate = SemState.begin;
				al.type = null;
				foreach(ref x; al.lit) x=x.convertTo(el);
				mixin(SemChld!q{e});
				if(e.type !is type && e.type.getElementType() is type.getElementType()){
					e.type = type;
				}
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

class ImplicitCastExp: CastExp{
	this(Expression tt, Expression exp){super(STC.init, tt, exp);}

	protected override Dependent!bool checkConv(Scope sc){
		mixin(ImplConvertsTo!q{bool iconv; e, type});
		if(!iconv){
			auto oe=e;
			relaxCastedExpression();
			if(oe !is e){
				mixin(ImplConvertsTo!q{auto cc; e, type});
				iconv=cc;
			}
		}
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
	override string kind(){return e.toString();}
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

	override void handleRef(Scope sc){ return actuallyHandleRef(sc); }

	override TmpVarDecl newVarDecl(STC stc, Expression rtype, Identifier name, Expression init_){
		return New!TmpVarDecl(stc,rtype,name,init_);
	}

	mixin DownCastMethod;
	mixin Visitors;
}
mixin template Semantic(T) if(is(T==TmpVarDecl)){ }


class TmpVarExp: Expression{
	Expression e;
	TmpVarDecl tmpVarDecl;
	Expression sym;
	this(Expression e)in{assert(e&&e.sstate==SemState.completed);}body{ this.e=e; }
	void initTmpVarDecl(Scope sc,bool forceRvalue)in{assert(!tmpVarDecl);}body{
		assert(e&&!sym);
		tmpVarDecl = New!TmpVarDecl(!forceRvalue&&e.isLvalue()?STCref:STC.init,null,null,e);
		tmpVarDecl.presemantic(sc);
		sym = New!Symbol(tmpVarDecl);
		sym.loc = loc;
		e = null;
	}
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(!tmpVarDecl) initTmpVarDecl(sc,false);
		mixin(SemChld!q{tmpVarDecl, sym});
		type = Type.get!void();
		mixin(SemEplg);
	}
	override @property string kind(){ return tmpVarDecl.init_.kind; }
	override string toString(){ return tmpVarDecl.init_.toString(); }

	mixin DownCastMethod;
	mixin Visitors;
}
mixin template Semantic(T) if(is(T==TmpVarExp)){ }

abstract class TemporaryExp: Expression{
	VarDecl tmpVarDecl;
	//protected bool builtTmpVarDecl = false;

	override void initOfVar(VarDecl decl){
		assert(!tmpVarDecl||tmpVarDecl is decl);
		if(!(decl.stc&STCenum)) tmpVarDecl = decl;
	}
	void createTemporary(Scope sc)in{assert(sstate==SemState.completed);}body{
		auto tmpe=New!TmpVarExp(sdup());
		tmpe.loc=loc;
		tmpe.semantic(sc);
		auto r=New!(BinaryExp!(Tok!","))(tmpe,tmpe.sym);
		r.loc=loc;
		r.semantic(sc);
		mixin(RewEplg!q{r});
	}

	mixin DownCastMethod;
	mixin Visitors;
}
mixin template Semantic(T) if(is(T==TemporaryExp)){}

class StructConsExp: TemporaryExp{
	Expression[] args;
	Expression argsLeftover;

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
		//analyzeTemporary(sc, STC.init);
		if(!tmpVarDecl){
			auto ne=New!StructConsExp(type, args);
			ne.argsLeftover=argsLeftover;
			ne.loc=loc;
			createTemporary(sc);
		}
		mixin(SemCheck);
		mixin(SemEplg);
	}

	override @property string kind(){ return "struct literal"; }
	override string toString(){
		return strd.name.toString()~"("~join(map!(to!string)(args),",")~leftoverToString(args,argsLeftover)~")";
	}


	mixin DownCastMethod;
	mixin Visitors;
}
mixin template Semantic(T) if(is(T==StructConsExp)){}

enum ResolveConstructor = q{
	static if(is(typeof(this)==NewExp)){
		alias a2 args;
		auto caggr = aggr.decl;
		alias a2Leftover argsLeftover;
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
			constructor.willCall();
		}
		if(!constructor.meaning){
			mixin(Lookup!q{_; constructor, sc, caggr.asc});
			if(auto nr=constructor.needRetry) { needRetry = nr; return; }
		}
	}
	if(!constructor||constructor.sstate == SemState.failed){
		// no constructor for type
		// TODO: disabled default constructor
		// TODO: default constructor. (remember to make sure that invisible constructors are respected for the decision whether to create default constructors for structs)
		if(args.length){
			sc.error("too many arguments to "~kind~" (expected zero)",loc);
			mixin(ErrEplg);
		}
	}else{
		// nested classes cannot be built like this
		//if(caggr.isReferenceAggregateDecl())
		MatchContext context;
		mixin(SemChld!q{constructor});
		mixin(MatchCallHelper!q{auto r; constructor, sc, loc, type, args, context});
		// TODO: assert that we have actually found a constructor
		if(!r){
			//sc.error("no matching constructor found", loc);
			constructor.matchError(sc,loc,type,args);
			mixin(ErrEplg);
		}
		if(!consCall){
			consCall = New!CallExp(constructor, args);
			consCall.argsLeftover = argsLeftover;
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

	Expression a2Leftover;

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
			int actual = 0;
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
				sc.error(format("cannot create instance of interface '%s'",iface.name),loc);
				mixin(ErrEplg);
			}else if(!aggr.decl.bdy){
				sc.error(format("cannot create instance of incomplete %s '%s'",aggr.decl.kind,aggr.decl.name),loc);
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
		if(constructor&&!type.isAggregateTy().decl.asc.inexistent(sc,constructor))
			mixin(ErrEplg);
	}

	override bool isUnique(){ return true; } // TODO: need to ensure strong purity of constructor!
}



mixin template Semantic(T) if(is(T==Identifier)){
	/* specifies whether or not to resume lookup recursively in
	   parent scopes if it fails in the initially given scope.
	 */
	bool recursiveLookup = true;

	/* specifies whether this identifier should ignore imported scopes other
	   than template mixins.
	 */
	bool onlyMixins = false; // TODO: merge those two bools into one bit field

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
		mixin(Lookup!q{_;this,sc,lkup});
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

	final Dependent!void lookup(Scope sc, Scope lkup)in{
		assert(!!lkup);
		assert(!meaning && sstate != SemState.error && sstate != SemState.failed, text(meaning," ",sstate));
	}out{
		if(!needRetry && sstate != SemState.error && sstate != SemState.failed)
			assert(meaning && meaning.scope_,text(this));
	}body{
		enum SemRet = q{ return indepvoid; };
		//needRetry = false; // TODO: why was this here?
		needRetry = true;
		if(allowDelay){
			sstate=SemState.begin; // reset

			if(recursiveLookup) mixin(Lookup!q{meaning; lkup, sc, this});
			else mixin(LookupHere!q{meaning; lkup, sc, this, onlyMixins});

			if(!meaning){
				// TODO: get rid of this. (It is required because of memory re-use.)
				// This can be removed when unresolved scopes will no longer be their own
				// abstraction.
				if(unresolved) unresolved = lkup.getUnresolved(sc, this, onlyMixins, false).force;
				if(unresolved){
					auto l = unresolved.potentialLookup(sc,this);
					if(l.length){
						needRetry = true;
						unresolved = null;
						return multidep(cast(Node[])l).dependent!void;
					}
					if(!unresolved.inexistent(sc,this)) mixin(ErrEplg);
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
			}
		}else{
			if(sstate == SemState.started){
				needRetry = true;
				tryAgain = true;
				mixin(GetUnresolved!q{unresolved;lkup,sc,this,onlyMixins,false});
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
		auto unresolved=sc.getUnresolved(sc, this, onlyMixins, true).force;
		if(unresolved&&!unresolved.inexistent(sc, this))
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
	IncompleteScope unresolved = null;
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

// useful for UFCS: a .identifier that fails lookup silently
class SilentModuleIdentifier: ModuleIdentifier{
	this(string name){super(name);}
	override void semantic(Scope sc){
		assert(!!sc.getModule);
		if(!mscope) mscope = sc.getModule().sc;
		if(!meaning){
			mixin(SemPrlg);
			assert(sstate != SemState.failed);
			mixin(Lookup!q{_;this,sc,mscope});
			if(sstate == SemState.failed) mixin(ErrEplg);
			if(needRetry) return;
		}
		Symbol.semantic(sc);
	}
}


abstract class CurrentExp: Expression{
	auto accessCheck = AccessCheck.all;
	Scope scope_;
	final FunctionDecl enclosingMemberFunction(){ return enclosingMemberFunction(scope_); }
	static FunctionDecl enclosingMemberFunction(Scope scope_){
		Declaration mfun=null;
		for(Declaration dl=scope_.getDeclaration(); dl && !dl.isAggregateDecl(); dl=dl.scope_.getDeclaration()){
			if(dl.stc&STCstatic) return null;
			mfun=dl;
		}
		return mfun.maybe!(mfun=>mfun.isFunctionDecl());
	}
	override void semantic(Scope sc){
		mixin(SemPrlg);
		scope_ = sc;
		auto aggr=sc.getAggregate();
		if(!aggr){
			sc.error(format("invalid use of '%s' outside of an aggregate declaration", toString()), loc);
			mixin(ErrEplg);
		}
		if(accessCheck!=AccessCheck.none){
			if(!enclosingMemberFunction()){
				sc.error(format("invalid use of '%s' outside of a nonstatic member function", toString()), loc);
				mixin(ErrEplg);

			}
		}

		mixin CreateBinderForDependent!("DetermineType");
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

	mixin DownCastMethod;
	mixin Visitors;
}
mixin template Semantic(T) if(is(T==CurrentExp)){}
mixin template Semantic(T) if(is(T==ThisExp)){
	protected override Dependent!Type determineType(Scope sc, AggregateDecl d){
		return d.getType().independent!Type;
	}
	override bool tmplArgEquals(Expression rhs){ return rhs.isThisExp()&&rhs.type.equals(type); }
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
	override bool tmplArgEquals(Expression rhs){ return rhs.isSuperExp()&&rhs.type.equals(type); }
}

mixin template Semantic(T) if(is(T==FieldExp)){

	mixin ContextSensitive;

	override Expression clone(Scope sc, InContext inContext, AccessCheck accessCheck, const ref Location loc){
		if(e1.isCurrentExp()) return e2.clone(sc, inContext, accessCheck, loc);
		auto fe1 = e1.clone(sc, inContext==InContext.fieldExp?inContext:InContext.none, accessCheck, loc);
		auto fe2 = e2.clone(sc, e2.inContext, accessCheck, loc);
		assert(cast(Symbol)fe2);
		auto r = New!(BinaryExp!(Tok!"."))(fe1,cast(Symbol)cast(void*)fe2);
		r.loc = loc;
		r.inContext = inContext;
		r.semantic(sc);
		return r;
	}

	Expression res;
	Expression ufcs; // TODO: we do not want this to take up space in every instance
	@property Expression member(){ return res ? res : e2; }

	AccessCheck accessCheck;
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e1});
		mixin(PropErr!q{e2});
		Type scopeThisType;
		auto msc = e1.getMemberScope();
		if(accessCheck == AccessCheck.init){
			accessCheck = e2.accessCheck;
			if(!e1.isType()) e2.accessCheck = e1.deferredAccessCheck();
		}
		if(e2.accessCheck!=AccessCheck.none) e2.loc=loc;

		Expression this_;
		if(!msc){
			if(auto ptr=e1.type.getHeadUnqual().isPointerTy())
				msc = ptr.ty.getMemberScope();
			if(!msc){
				this_ = e1.extractThis();
				goto Linexistent;
			}
			e1 = New!(UnaryExp!(Tok!"*"))(e1);
			mixin(SemChld!q{e1});
		}
		this_ = e1.extractThis();

		if(!e2.meaning){
			if(auto ident = e2.isIdentifier()){
				//e2.implicitCall = false;
				ident.recursiveLookup = false;
				//ident.lookup(msc);
				if(ident.sstate != SemState.failed){
					ident.inContext = InContext.fieldExp;
					mixin(Lookup!q{_;ident,sc,msc});
					if(auto nr=ident.needRetry) { needRetry=nr; return; }
					mixin(PropErr!q{ident});
				}
				if(ident.sstate == SemState.failed) goto Linexistent;
			}
		}
		{
		assert(!!e2.meaning);
		// TODO: find a better design here
		if(rewrite)
			return;
		e2.inContext = InContext.fieldExp;
		e2.semantic(sc);
		res = e2;
		mixin(Rewrite!q{res});
		auto rew=e2.rewrite;
		e2.rewrite = null;
		mixin(SemProp!q{e2});
		e2.rewrite=rew;
		////
		if(auto ae = res.isAddressExp()){
			if(auto sym=ae.e.isSymbol()){
				auto b=New!(BinaryExp!(Tok!"."))(e1, sym);
				b.loc=loc;
				auto r=New!(UnaryExp!(Tok!"&"))(b);
				r.loc=loc;
				transferContext(r);
				r.semantic(sc);
				mixin(RewEplg!q{r});
			}
		}else if(auto sym = res.isSymbol()){
			e2=sym;
			type = e2.type;
			Type thisType=sym.thisType();
			bool needThis = !!thisType;
			if(needThis){
				if(this_)
				if(sym.meaning.needsAccessCheck(AccessCheck.all))
				if(auto vd=sym.meaning.isVarDecl())
				if(vd.isField){
					assert(!!this_.type.getUnqual().isAggregateTy());
					auto stc = this_.type.getHeadSTC();
					type=type.applySTC(stc);

					assert(this_.sstate == SemState.completed);

					// delegates do not implicitly convert to const
					if(stc&STCconst && !e2.type.implicitlyConvertsTo(type).force){
						sc.error(format("cannot load field '%s' of type '%s' from const-qualified receiver",e2, e2.type), loc);
						sc.note(format("%s was declared here",kind),e2.meaning.loc);
						mixin(ErrEplg);
					}
					e2.type = type;
				}
				if(sym.meaning.needsAccessCheck(accessCheck)){
					needRetry=false;
					auto newThis_=this_;
					thisCheckAndRebind(sc, newThis_, thisType);
					mixin(SemCheck);
					if(!newThis_){
						sym.accessCheck=accessCheck;
						sym.performAccessCheck();
						mixin(SemProp!q{sym});
					}
					if(this_ && newThis_ !is this_){
						auto b = New!(BinaryExp!(Tok!"."))(newThis_,e2);
						b.loc = loc;
						auto r = New!(BinaryExp!(Tok!","))(this_,b);
						r.loc = loc;
						transferContext(r);
						r.semantic(sc);
						mixin(RewEplg!q{r});
					}
					goto Lok;
				}
			}else if(sym.meaning.needsAccessCheck(accessCheck)){
				sym.accessCheck=accessCheck;
				sym.performAccessCheck();
				mixin(SemProp!q{sym});
			}
		}else if(this_){
			static FieldExp concatenate(Expression base, FieldExp f){
				if(auto f2=f.e1.isFieldExp()){
					auto e1=concatenate(base, f2);
					auto r = New!(BinaryExp!(Tok!"."))(e1,f.e2);
					r.loc = f.loc;
					return r;
				}else if(auto sym=f.e1.isSymbol()){
					auto r = New!(BinaryExp!(Tok!"."))(base, sym);
					auto l=r.loc=base.loc.to(f.e1.loc);
					r = New!(BinaryExp!(Tok!"."))(r, f.e2);
					r.loc=l.to(f.e2.loc);
					return r;
				}else assert(0, text((a=>typeid(a))(f.e1)));
			}
			if(auto et=res.isExpTuple()){
				// TODO: can some cloning be avoided here?:
				auto exprs=new Expression[](et.length); // TODO: allocation
				TmpVarExp tmpe;
				Expression base;
				if(!AliasDecl.isAliasable(e1)){
					tmpe=New!TmpVarExp(e1);
					tmpe.loc=e1.loc;
					tmpe.semantic(sc);
					base=tmpe.sym;
				}else base=e1;
				size_t i=0;
				foreach(e;et.allIndices(sc,InContext.fieldExp,loc)){
					if(auto sym=e.isSymbol()){
						exprs[i]=New!(BinaryExp!(Tok!"."))(base, sym);
						exprs[i].loc=loc;
					}else if(auto fld=e.isFieldExp()){
						exprs[i]=concatenate(base, fld);
					}else exprs[i]=e;
					i++;
				}
				auto net = New!ExpTuple(exprs);
				net.loc=loc;
				Expression r;
				if(tmpe){
					r = New!(BinaryExp!(Tok!","))(tmpe, net);
					r.brackets++;
					r.loc = loc;
				}else r = net;
				transferContext(r);
				r.semantic(sc);
				mixin(RewEplg!q{r});
			}

			Expression r;
			if(auto fres=res.isFieldExp()){
				r=concatenate(e1, fres);
				transferContext(r);
				r.semantic(sc);
			}else r=res; // type or enum on instance. ignore side effects of e1

			mixin(RewEplg!q{r});
			/*// TODO: do we rather want this:
			// enum reference. we need to evaluate 'this', but it
			// does not matter for the field expression
			//assert(e2.meaning.stc & STCenum);
			auto r=New!(BinaryExp!(Tok!","))(this_,res);
			r.brackets++;
			r.loc=loc;
			r.semantic(sc);
			mixin(RewEplg!q{r});*/
		}
		if(!this_){
			// we do not have a 'this' pointer
			// and we do not need a 'this' pointer
			Expression r=res;
			if(auto sym=r.isSymbol()){
				// allow implicit call rewrite
				sym.sstate = SemState.begin;
				sym.inContext = InContext.none;
				transferContext(sym);
				sym.accessCheck = accessCheck;
				sym.semantic(sc);
			}
			mixin(RewEplg!q{r});
		}/+else{
			// we have a 'this' pointer that we don't need
		}+/
		}
	Lok:
		// in order to be able to reuse isImplicitlyCalled (TODO: improve)
		if(e2.isImplicitlyCalled(inContext)){
			auto b = New!(BinaryExp!(Tok!"."))(e1,e2);
			b.loc = loc;
			e2.ignoreProperty=true;
			auto args = Seq!(b,(Expression[]).init);
			auto r = e2.meaning.stc&STCproperty?New!PropertyCallExp(args):New!CallExp(args);
			r.loc = loc;
			r.semantic(sc);
			mixin(RewEplg!q{r});
		}
		assert(!!type);
		mixin(SemEplg);

	Linexistent:
		if(isBuiltInField(sc,this_)) return;
		// TODO: opDispatch
		// TODO: alias this
		if(e1 is this_&&!ufcs)
			if(auto id=e2.isIdentifier()){
				auto ufcs=New!SilentModuleIdentifier(id.name);
				ufcs.loc=e2.loc;
				ufcs.ignoreProperty=true;
				e2.transferContext(ufcs);
				if(!ufcs.inContext.among(InContext.called, InContext.instantiated))
					ufcs.inContext=InContext.called;
				this.ufcs=ufcs;
			}
		if(ufcs){
			assert(e1 is this_);
			mixin(SemChldPar!q{ufcs});
			if(ufcs.isSymbol()||ufcs.isType())
			if(ufcs.sstate == SemState.completed){
				bool incomplete=!!inContext.among(InContext.called,InContext.instantiated);
				incomplete&=!(ufcs.isSymbol()&&ufcs.isSymbol().meaning.stc&STCproperty);
				auto r = New!UFCSCallExp(ufcs, this_, incomplete);
				r.loc=loc;
				r.semantic(sc);
				mixin(RewEplg!q{r});
			}
		}

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

	override void noHope(Scope sc){
		if(e1.sstate!=SemState.completed) return;
		if(auto i=e2.isIdentifier()){
			if(i.meaning) return;
			auto msc = e1.getMemberScope();
			if(!msc) return;
			auto unresolved = msc.getUnresolved(sc,i, false, true).force;
			if(unresolved&&!unresolved.inexistent(sc,i))
				mixin(ErrEplg);
		}
	}

	/* given that 'this' of type thisType is required, check if
	   this_ can be used as the 'this' pointer
	 */
	private void thisCheckAndRebind(Scope sc,ref Expression this_, Type thisType){
		bool tryRebind(){
			auto thisExp=New!ThisExp(); // TODO: ensure this only happens once per symbol
			thisExp.loc=loc;
			thisExp.semantic(New!GaggingScope(sc));
			assert(thisExp.sstate.among(SemState.error,SemState.completed));
			if(thisExp.sstate==SemState.error) return false;
			this_=thisExp;
			return true;
		}
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
			tryRebind();
			if(!this_){
				// error message duplicated in Symbol.semantic
				sc.error(format("need 'this' to access %s '%s'",
				                e2.meaning?e2.kind:"member",e2.loc.rep),loc);
				if(e2.meaning) sc.note(format("%s was declared here",e2.kind),e2.meaning.loc);
				mixin(ErrEplg);
			}
		}
		{
		// successfully resolved non-tuple field expression that
		// requires 'this'
		auto etu = this_.type.getUnqual();
		mixin(RefConvertsTo!q{bool conv; etu, ttu, 0});
		if(!conv){
			tryRebind();
			etu=this_.type.getUnqual();
			mixin(RefConvertsTo!q{bool conv2; etu, ttu, 0});
			if(!conv2){
				sc.error(format("need 'this' of type '%s' to access %s '%s'",
				                thisType.toString(),e2.kind,e2.loc.rep),loc);
				mixin(ErrEplg);
			}
		}
		}
	Lok:;
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
		if(e2.meaning.isTemplateInstanceDecl()||e2.meaning.isNamespaceDecl())
			return e1.extractThis();
		return this;
	}
	override AccessCheck deferredAccessCheck(){
		if(isTuple()) return AccessCheck.all;
		if(!e2.meaning.needsAccessCheck(accessCheck)) return e1.deferredAccessCheck();
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

		assert(e2.inContext==InContext.fieldExp);

		mixin(MatchCallHelper!q{auto exp; e2, sc, loc, this_, args, context});
		if(!exp) return null.independent!Expression;
		assert(!!cast(Symbol)exp);
		auto sym = cast(Symbol)cast(void*)exp;
		e2 = sym;
		sstate = SemState.begin;
		type = null;
		semantic(e2.scope_);
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
			if(!isType) switch(name){
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
					if(accessCheck != AccessCheck.none){
						thisCheckAndRebind(sc, this_, ty);
						return true;
					}
					goto Lnorewrite;
				case "length":
					type = Type.get!Size_t();
					if(accessCheck != AccessCheck.none){
						thisCheckAndRebind(sc, this_, ty);
						return true;
					}
					goto Lnorewrite;
				default: break;
			}
		}
		if(auto tp=e1.isTuple()){
			if(name=="length"){
				r=LiteralExp.factory(Variant(tp.length, Type.get!Size_t()));
				goto Lrewrite;
			}
		}
		return false;
	Lrewrite:
		r.loc=loc;
		r.semantic(sc);
		mixin(RewEplg!q{r});
	Lnorewrite:
		mixin(SemEplg);
	}

	override bool isConstant(){ return e1.isConstant(); }
	override bool isConstFoldable(){ return e1.isConstFoldable(); }

	// TemplateDecl needs this.
	override bool tmplArgEquals(Expression rhs){
		if(e1.isCurrentExp()){
			if(auto sym = rhs.isSymbol())
				return e2.tmplArgEquals(sym);
		}
		if(auto fld = rhs.isFieldExp())
			return e2.tmplArgEquals(fld.e2) && e1.tmplArgEquals(fld.e1);
		return false;
	}

	override size_t tmplArgToHash(){
		import hashtable;
		if(e1.isCurrentExp()) return e2.tmplArgToHash();
		return FNV(e2.meaning.toHash(), e1.tmplArgToHash());
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

	mixin DownCastMethod;
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

	static VarDecl createDecl(Scope ascope, STC stc, Expression init_)in{
		assert(!!ascope);
	}body{
		// TODO: the allocation of a new identifier is unnecessary
		auto dollar = new VarDecl(stc, Type.get!Size_t(),
		                     New!Identifier("__dollar"), init_);
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
				Expression init_ = null;
				void createInit(Tuple tp){
					stc |= STCenum;
					init_ = LiteralExp.factory(Variant(tp.length, Type.get!Size_t()));
				}
				if(auto tp=e.isTuple()) createInit(tp);
				else if(e.type){ if(auto tp=e.type.isTuple()) createInit(tp); }

				// dollar variables outside function scope are 'static'
				auto decl=ascope.getDeclaration();
				if(!decl||!decl.isFunctionDef()) stc |= STCstatic;

				dollar = DollarExp.createDecl(ascope, stc, init_);
			}
			return dollar;
		}
	}
}


mixin template Semantic(T) if(is(T==FunctionLiteralExp)){
	protected FunctionDef createFunctionDef(FunctionTy fty,Identifier name, CompoundStm bdy){
		return New!FunctionDef(STC.init,fty,name,cast(BlockStm)null,cast(BlockStm)null,cast(Identifier)null,bdy);
	}
	override void semantic(Scope sc){
		mixin(SemPrlg);
		auto dg=createFunctionDef(fty,New!Identifier(uniqueIdent("__dgliteral")),bdy);
		if(which==Kind.none) dg.inferStatic=true;
		dg.inferAttributes=true; // TODO: re-enable
		auto decl=sc.getDeclaration();

		dg.sstate = SemState.begin;
		dg.scope_ = sc; // Symbol will use this scope to reason for analyzing DG
		auto sym=New!Symbol(dg, true, true);
		if(which==Kind.function_ || which!=Kind.delegate_ && !decl) dg.stc |= STCstatic;
		else if(decl&&decl.isReferenceAggregateDecl()) dg.stc |= STCfinal;
		sym.loc=dg.loc=loc;
		Expression e = New!(UnaryExp!(Tok!"&"))(sym);
		e.brackets++;
		e.loc=loc;
		transferContext(e);
		e.semantic(sc);

		if(auto enc=sc.getDeclaration())
			enc.nestedFunctionLiteral(dg);

		auto r = e;
		mixin(PropErr!q{r});
		mixin(RewEplg!q{r});
	}

	mixin ContextSensitive;
}

mixin template Semantic(T) if(is(T==ConditionDeclExp)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(!decl) decl=New!VarDecl(stc,ty,name,init_);
		if(!sym) sym=New!Symbol(decl);
		mixin(SemChld!q{decl,sym});
		type = decl.type;
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

	override Type clone(Scope,InContext,AccessCheck accessCheck,const ref Location) { return this; }

	final protected Type checkVarDeclError(Scope sc, VarDecl me)in{assert(sc);}body{
		if(me.name)
			sc.error(format("%s '%s' has invalid type '%s'", me.kind, me.name, this), me.loc);
		else
			sc.error(format("%s has invalid type '%s'", me.kind, this), me.loc);
		return New!ErrorTy();
	}
	Type checkVarDecl(Scope, VarDecl){return this;}

	Type getArray(ulong size){
		if(auto r=arrType.get(size,null)) return r;
		return arrType[size]=ArrayTy.create(this,size);
	}

	override Dependent!Expression matchCallHelper(Scope sc, const ref Location loc, Type this_, Expression[] args, ref MatchContext context){
		return null.independent!Expression;
	}
	override void matchError(Scope sc, Location loc, Type this_, Expression[] args){
		sc.error(format("%s '%s' is not callable",kind,toString()),loc);
	}



	private static funcliteralTQ(){string r;
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
				final Type get@(upperf(x))()in{
					assert(!isTypeTuple(),text("cannot create array of ",this));
				}body{
					if(@(x)Type) return @(x)Type;
					return @(x)Type=@(upperf(x))Ty.create(this);
				}
			});
		}
		return r;
	}mixin(funcliteralTQ());

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
	final Type adaptTo(Type from, ref InoutRes inoutRes){
		auto t1=this, t2=from;
		auto tu1=t1.getHeadUnqual(), tu2=t2.getHeadUnqual();
		if(tu1.isPointerTy() && tu2.isPointerTy()
		   || tu1.isDynArrTy() && tu2.isDynArrTy())
			t1=tu1, t2=tu2;
		return t1.adaptToImpl(t2, inoutRes);
	}

	Type adaptToImpl(Type from, ref InoutRes inoutRes){
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
	   be kept unique, since they may include default arguments
	 */
	bool equals(Type rhs){
		return this is rhs;
	}

	override Dependent!bool convertsTo(Type rhs){
		if(auto et=rhs.getHeadUnqual().isEnumTy()){
			mixin(GetEnumBase!q{auto base;et.decl});
			return convertsTo(base.applySTC(rhs.getHeadSTC()));
		}
		return rhs.getHeadUnqual() is Type.get!void() ?true.independent:
			implicitlyConvertsTo(rhs.getUnqual().getConst());
	}

	override Dependent!bool implicitlyConvertsTo(Type rhs){
		return this.refConvertsTo(rhs.getHeadUnqual(),0);
	}


	final Dependent!bool constConvertsTo(Type rhs){
		return !this.getUnqual().equals(rhs.getUnqual()) ?false.independent:
			implicitlyConvertsTo(rhs);
	}


	// bool isSubtypeOf(Type rhs){...}

	/* stronger condition than subtype relationship.
	   a 'num'-times reference to a this must be a subtype of
	   a 'num'-times reference to an rhs.
	*/

	Dependent!bool refConvertsTo(Type rhs, int num){
		assert(rhs);
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

		if(l2r ^ r2l) r = r2l ? this : rhs;

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

	Dependent!Type unify(Type rhs){
		if(rhs.isQualifiedTy()) return rhs.unify(this);
		return combine(rhs);
	}

	Type stripDefaultArguments(){ return this; }

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
	override bool tmplArgEquals(Expression rhs){
		if(auto type = cast(Type)rhs) return equals(type);
		return false;
	}
	override size_t tmplArgToHash(){
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
					return ft.addQualifiers(STC@(x)).getDelegate();
				}
				override Type in@(upperf(x))Context(){
					return ft.in@(upperf(x))Context().getDelegate();
				}
			});
		}
		return r;
	}
	mixin(__dgliteralQual());

	override Type stripDefaultArguments(){
		return ft.stripDefaultArguments().getDelegate();
	}
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
			if(!p.rtype && !p.init_) continue; // parameter type needs to be deduced
			p.semantic(sc); // TODO: rewriting parameters ever needed?
			assert(!p.rewrite);
		}
		foreach(p;params){mixin(PropRetry!q{p});}
		if(rret) mixin(PropErr!q{rret});
		if(ret) mixin(PropErr!q{ret});
		mixin(PropErr!q{params});
		params = Tuple.expandVars(sc,params);
		mixin(SemEplg);
	}

	override Type checkVarDecl(Scope sc, VarDecl me){
		return checkVarDeclError(sc,me);
	}

	bool hasUnresolvedParameters(){
		foreach(x;params) if(x.mustBeTypeDeduced()) return true;
		return false;
	}

	bool errorsInParams(){
		if(sstate != SemState.error) return false;
		foreach(x;params) if(x.sstate == SemState.error) return true;
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
				if(ty&&ty.sstate==SemState.completed&&ty.getHeadUnqual()!is Type.get!void()){
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

		final switch(res){
			foreach(x;M[1..$]){
				enum e = mixin("InoutRes."~x);
				enum i = "cache_inoutres_"~x;
				case e: if(mixin(i)) return mixin(i);
					auto r=dup();
					r.params = r.params.dup;
					foreach(ref p;r.params){
						p=p.ddup();
						p.type = p.type.resolveInout(res);
						p.rtype=null;
						p.stc=(p.stc&~STCinout)|p.type.getHeadSTC();
					}
					foreach(xx;M[1..$]) mixin("r.cache_inoutres_"~xx)=r;
					r.ret = r.ret.resolveInout(res);
					static if(e!=InoutRes.inout_)if(r.stc&STCinout){
						static if(e!=InoutRes.inoutConst)
							r=r.removeQualifiers(STCinout);
						static if(e==InoutRes.immutable_)
							r=r.addQualifiers(STCimmutable);
						else static if(e==InoutRes.const_)
							r=r.addQualifiers(STCconst);
						else static if(e==InoutRes.inoutConst)
							r=r.addQualifiers(STCconst);
					}
					return mixin(i)=r;
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
						import rope_;
						auto types = toTemplArgs(map!(_=>_.type)(ft.params[i..$]));
						//mt.typeMatch(New!TypeTuple(types));
						// TODO: this might be expensive:
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
		if(ret && ret.hasPseudoTypes()) ret=null;
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
		   any!(_=>_.init_ is null)(params[args.length..params.length])){
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
				if(p.stc&STClazy && at[i].getHeadUnqual() is Type.get!void())
					continue;
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

	private template CIT(bool implconv){
		static if(implconv) alias Dependent!bool CIT;
		else alias bool CIT;
	}
	private CIT!implconv compareImpl(bool implconv=false)(Type rhs){
		static if(implconv){ auto tt=true.independent, ff=false.independent; }
		else{ auto tt=true, ff=false; }
		// cannot access frame pointer to 'all'. TODO: file bug
		if(auto ft = rhs.isFunctionTy()){
			auto stc1 = stc, stc2 = ft.stc;
			// STC's could be inferred (TODO: is this exactly right?)
			if(hasUnresolvedParameters()) stc1&=~STCinferrable, stc2&=~STCinferrable;
			static if(implconv){
				stc1 &= ~STCproperty, stc2 &= ~STCproperty; // STCproperty does not matter
				stc1 &= ~STCauto, stc2 &= ~STCauto; // STCauto does not matter
				if(stc1 & STCsafe || stc1 & STCtrusted)
					stc1 &= ~STCsafe & ~STCtrusted, stc2 &= ~STCsafe & ~STCtrusted & ~STCsystem;
				// immutable -> const is ok
				if(stc1 & STCimmutable && stc2 & STCconst)
					stc1 &= ~STCimmutable, stc2 &= ~STCconst;
				// attributes that can be freely dropped:
				static STC[] droppable=[STCconst,STCimmutable,STCpure,STCnothrow,STCsafe];
				foreach(drop;droppable) if(stc1 & drop) stc1 &= ~drop, stc2 &= ~drop;
				// TODO: more implicit conversion rules
				if(ret){
					mixin(RefConvertsTo!q{bool rc;ret, ft.ret, 0});
					if(!rc) return ff;
				}
			}else if(ret && !ret.equals(ft.ret)) return ff;
			if(!((stc1==stc2 && params.length == ft.params.length) && vararg == ft.vararg))
				return ff;
			//all!(_=>_[0].type.equals(_[1].type))(zip(params,ft.params)) &&
			foreach(i,x; params)
				if(x.type && !x.type.equals(ft.params[i].type)||
				   (x.stc&(STCbyref|STClazy))!=(ft.params[i].stc&(STCbyref|STClazy)))
					return ff;
			return tt;
		}else return ff;
	}

	// TODO: rename and don't implement them
	override Dependent!bool refConvertsTo(Type rhs, int num){
		if(num<2) return compareImpl!true(rhs);
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

	override FunctionTy stripDefaultArguments(){
		assert(sstate==SemState.completed);
		if(strippedDefaultArguments) return strippedDefaultArguments;
		// TODO: get rid of the allocation in the common case
		Parameter stripParam(Parameter param){
			if(!param.rtype && !param.init_) return param; // parameter type yet to be deduced
			assert(param.sstate==SemState.completed);
			auto ntype=param.type.stripDefaultArguments();
			assert(ntype.sstate==SemState.completed);
			if(ntype!=param.type||param.init_){
				auto nparam=New!Parameter(param.stc,ntype,param.name,null);
				nparam.type=ntype;
				nparam.sstate=SemState.completed;
				return nparam;
			}
			return param;
		}
		auto nret=ret.stripDefaultArguments();
		auto nparams=params.map!stripParam.array; // TODO: allocation
		import util: any;
		if(nret !is ret || any!(a=>a[0]!is a[1])(zip(nparams,params))){
			// (this should be a precondition, but with broken overriding semantics, why bother:)
			assert(sstate==SemState.completed);
			strippedDefaultArguments=New!FunctionTy(stc,nret,nparams,vararg);
			strippedDefaultArguments.ret=nret;
			strippedDefaultArguments.sstate=SemState.completed;
			strippedDefaultArguments.scope_=scope_;
			strippedDefaultArguments.strippedDefaultArguments=strippedDefaultArguments;
		}else strippedDefaultArguments=this;
		return strippedDefaultArguments;
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
		//switch(diffq){ // wtf. DMD codegen bug?
		foreach(x; ToTuple!qualifiers){
			enum s=mixin("STC"~x);
			enum i="cache_"~x~(add?"":"_no");
			enum irev = i~".cache_"~x~(add?"_no":"");
			// alias ID!(mixin(i)) cache; // wut?
			if(diffq==s){ // case s:
				if(!mixin(i)){
					mixin(i) = dup();
					static if(add) mixin(i).stc|=s;
					else mixin(i).stc&=~s;
					mixin(irev)=this;
				}
				return mixin(i).modifyQualifiers!add(qual);
			}
		}
		/+default: +/assert(0, STCtoString(diffq));//}
	}

	DelegateTy dgtype;
	FunctionTy strippedDefaultArguments;

	enum qualifiers = ["const","immutable","inout","nothrow","pure","shared",
	                   "safe","trusted","system"];
	static string __dgliteralgenCaches(){
		string r;
		foreach(x; qualifiers) r~="FunctionTy cache_"~x~", cache_"~x~"_no;\n";
		foreach(x; __traits(allMembers,InoutRes)[1..$])  r~="FunctionTy cache_inoutres_"~x~";";
		r~="public void clearCaches(){"; // TODO: these are not all caches!
		r~="dgtype=null;";
		r~="strippedDefaultArguments=null;";
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
				r~=mixin(X!q{case Tok!"@(x)": r=Type.get!(BasicTypeRep!"@(x)")();break;});
			return r~`default: assert(0);}`;
		}());
		assert(r !is this,text(r));
		mixin(RewEplg!q{r});
	}

	override Type checkVarDecl(Scope sc, VarDecl me){
		if(op!=Tok!"void"||me.stc&STClazy) return this;
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
		 Tok!"dchar":4,Tok!"int":4,Tok!"uint":4,Tok!"long":5,Tok!"ulong":5,Tok!"cent":6,Tok!"ucent":6,Tok!"float":7,Tok!"double":7,Tok!"real":7,
		 Tok!"ifloat":-1,Tok!"idouble":-1,Tok!"ireal":-1,Tok!"cfloat":-2,Tok!"cdouble":-2,Tok!"creal":-2, Tok!"void":0];

	override BasicType isIntegral(){return strength[op]>0 && strength[op]<=6 ? this : null;}
	final BasicType isFloating(){return strength[op]==7 ? this : null;}
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
			case Tok!"cent": return Type.get!UCent();
			case Tok!"ucent": return Type.get!Cent();
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
					return Type.get!UCent().independent!Type;
				case 7:
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
		if(strength[bt.op]<7){
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
		if(strength[bt.op]<7){
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
		override Type adaptToImpl(Type from, ref InoutRes res){
			if(auto imm = from.isImmutableTy()){
				res = mergeIR(res, InoutRes.immutable_);
			}else if(auto con = from.isConstTy()){
				assert(!con.ty.isInoutTy()); // normal form: inout(const(T))
				res = mergeIR(res, InoutRes.const_);
			}else if(auto sha = from.isSharedTy()){
				// information could be burried, eg shared(const(int))
				return adaptToImpl(sha.ty, res);
			}else if(auto ino = from.isInoutTy()){
				res = mergeIR(res, ino.ty.isConstTy() ?
				                   InoutRes.inoutConst :
				                   InoutRes.inout_);
			}else res = mergeIR(res, InoutRes.mutable);

			return ty.getTailInout().adaptToImpl(from.getHeadUnqual(), res).getInout();
		}
		override Type resolveInout(InoutRes res){
			// Spec is ambiguous here. this assertion is not valid for
			// the implementation chosen:
			// assert(ty.resolveInout(res).equals(ty));
			auto rty=ty.resolveInout(res);
			final switch(res){
				case InoutRes.none, InoutRes.inout_:
					return this;
				case InoutRes.mutable:
					return rty;
				case InoutRes.immutable_:
					return rty.getImmutable();
				case InoutRes.const_:
					return rty.getConst();
				case InoutRes.inoutConst:
					return rty.getConst().getInout();
			}
		}
	}else{
		/* hand through adaptTo and resolveInout calls
		 */
		override Type adaptToImpl(Type from, ref InoutRes res){
			return mixin(`ty.getTail`~qual~`().adaptToImpl(from, res).get`~qual)();
		}
		override Type resolveInout(InoutRes res){
			return mixin(`ty.resolveInout(res).get`~qual)();
		}
	}

	override Dependent!void typeMatch(Type from){
		assert(!!from);
		static if(is(T==ConstTy)||is(T==InoutTy)){
			if(auto im=from.isImmutableTy()) from=im.ty;
			else{
				from=from.inConstContext();
				static if(is(T==InoutTy)) from=from.inInoutContext();
			}
		}else if(auto ccc = mixin(`from.is`~qual~`Ty()`)) from=ccc.ty;
		mixin(TypeMatch!q{_;mixin(`ty.getTail`~qual~`()`), from});
		return indepvoid;
	}

	override Dependent!Type unify(Type rhs){
		auto stc=getHeadSTC();
		auto rstc=rhs.getHeadSTC();
		mixin(Unify!q{auto unqual;getHeadUnqual(),rhs.getHeadUnqual()});
		return unqual.applySTC(stc).refCombine(unqual.applySTC(rstc),0);
	}

	override bool hasPseudoTypes(){
		return ty.hasPseudoTypes();
	}

	override bool equals(Type rhs){
		if(auto d=mixin(`rhs.is`~T.stringof)()) return ty.equals(d.ty);
		return false;
	}

	override Dependent!bool implicitlyConvertsTo(Type rhs){
		// TODO: aggregate types
		if(cast(AggregateTy)this||cast(AggregateTy)rhs)
			return super.implicitlyConvertsTo(rhs);
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

	override Type stripDefaultArguments(){
		return mixin(`ty.stripDefaultArguments().get`~qual);
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
mixin template GetTailOperations(string tail, string puthead){
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
		if(ty.isTypeTuple()){
			static if(is(T==PointerTy)){
				// TODO: propose expansion behaviour
				sc.error(format("cannot create pointer type for sequence '%s'", e), loc);
				mixin(ErrEplg);
			}else{
				// (there's no syntax for this)
				assert(0,format("cannot create array type for sequence '%s'", e));
			}
		}
		assert(ty.sstate==SemState.completed,text(e," ",ty," ",e.sstate," ",ty.sstate," ",e.needRetry," ",ty.needRetry));
		Type r;
		static if(is(T==ArrayTy)) r=ty.getArray(length);
		else r = mixin("ty.get"~T.stringof[0..$-2]~"()");

		mixin(RewEplg!q{r});
	}

	override Type adaptToImpl(Type from, ref InoutRes res){
		if(auto tt = mixin(`from.getHeadUnqual().is`~T.stringof)()){
			return mixin(`ty.adaptToImpl(tt.ty,res).`~puthead);
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
			return (!!rhs.isDynArrTy()).independent;
		else return implicitlyConvertsTo(rhs);
	}

	// this adds one indirection for pointers and dynamic arrays
	override Dependent!bool refConvertsTo(Type rhs, int num){
		// dynamic and static arrays can implicitly convert to void[]
		// pointer types can implicitly convert to void*
		static if(is(T==DynArrTy)||is(T==ArrayTy)||is(T==PointerTy)){
			static if(is(T==PointerTy)) auto vtt = Type.get!(void*)();
			else auto vtt = Type.get!(void[])();
			if(rhs.getUnqual() is vtt){
				static if(is(T==PointerTy)){
					auto c=rhs.isPointerTy();
					if(!c) goto Lsuper;
					auto elr=c.ty;
				}else{
					auto elr = rhs.getElementType();
					assert(!!elr);
				}
				auto ell = ty;
				auto stcr = elr.getHeadSTC(), stcl=ell.getHeadSTC();
				if(auto t=ell.refConvertsTo(ell.applySTC(stcr),num+1).prop)
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
	Lsuper: return super.refConvertsTo(rhs,num);
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

	override Type stripDefaultArguments(){
		return mixin(`ty.stripDefaultArguments().`~puthead);
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

mixin template Semantic(T) if(is(T==TypeofReturnExp)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		auto fun=sc.getFunction();
		if(!fun){
			sc.error("'typeof(return)' must be inside function",loc);
			mixin(ErrEplg);
		}
		fun.analyzeType();
		if(fun.type.hasUnresolvedReturn()){
			sc.error("'typeof(return)' cannot be used before return type is deduced",loc);
			mixin(ErrEplg);
		}
		auto r=fun.type.ret;
		if(!r) mixin(ErrEplg);
		mixin(RewEplg!q{r});
	}
}


mixin template Semantic(T) if(is(T==AggregateTy)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemEplg);
	}

	override Type checkVarDecl(Scope sc, VarDecl me){
		if(!decl.isReferenceAggregateDecl()&&!decl.bdy){
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

mixin template Semantic(T) if(is(T==EnumTy)){
	override Scope getMemberScope(){
		return decl.msc;
	}

	override string toString(){
		assert(!!decl.name);
		return decl.name.toString();
	}


	// (remove this for strongly typed enums)
	override Dependent!bool implicitlyConvertsTo(Type to){
		if(auto t=super.implicitlyConvertsTo(to).prop) return t;
		mixin(GetEnumBase!q{auto base;decl});
		return base.implicitlyConvertsTo(to);
	}

	override Dependent!bool convertsTo(Type to){
		if(auto t=super.convertsTo(to).prop) return t;
		mixin(GetEnumBase!q{auto base;decl});
		return base.convertsTo(to);
	}

	string valueToString(Variant value){
		foreach(m;decl.members){
			if(m.sstate!=SemState.completed) continue;
			assert(m.rinit&&m.rinit.isConstant());
			if(m.rinit.interpretV().opBinary!"is"(value))
				return toString()~"."~m.name.name;
		}
		assert(!!decl.base);
		auto rv=value.convertTo(decl.base);
		return "cast("~type.toString()~")"~rv.toString();
	}
}


// statements

mixin template Semantic(T) if(is(T==Statement)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		sc.error("feature not implemented",loc);
		mixin(ErrEplg);
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
			mixin(SemChld!q{sc=esc;s2});
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
		mixin(SemChldPar!q{sc=lsc;s});
		mixin(SemChldPar!q{e});// TODO: propose SemChld!q{sc=lsc;e}
		mixin(FinishDeduction!q{e});
		auto bl = Type.get!bool();
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

// TODO: this OO approach for opApply is a little verbose. better options?
class OpApplyFunctionLiteralExp: FunctionLiteralExp{
	ForeachStm lstm;
	this(FunctionTy ft, CompoundStm b, ForeachStm lstm)in{
		assert(!!lstm.retVar);
	}body{
		super(ft,b);
		this.lstm=lstm;
	}
	protected override FunctionDef createFunctionDef(FunctionTy fty,Identifier name, CompoundStm bdy){
		return New!OpApplyFunctionDef(STC.init,fty,name,bdy,lstm);
	}

	mixin DownCastMethod;
	mixin Visitors;
}
template Semantic(T) if(is(T==OpApplyFunctionLiteralExp)){ }
class OpApplyFunctionDef: FunctionDef{
	ForeachStm lstm;
	this(STC stc, FunctionTy fty, Identifier name, CompoundStm bdy, ForeachStm lstm)in{
		assert(!!lstm.retVar);
	}body{
		super(stc,fty,name,cast(BlockStm)null,cast(BlockStm)null,cast(Identifier)null,bdy);
		this.lstm=lstm;
		lstm.setOpApplyFunctionDef(this);
	}

	Statement[] gotos;
	int addGoto(Statement gto){
		gotos~=gto;
		return ForeachStm.opApplyReturnCode+cast(int)gotos.length;
	}
	protected override FunctionScope buildFunctionScope(){
		return New!FunctionScope(scope_, this);
	}
	protected override void undeclaredLabel(GotoStm gto){
		assert(cast(Identifier)gto.e);
		if(!gto.lower){
			auto ngto=New!GotoStm(gto.t,gto.e);
			ngto.loc=gto.loc;
			gto.lower=ForeachStm.createOpApplyReturn(addGoto(ngto),gto.loc);
		}
		mixin(SemChld!q{sc=gto.scope_;gto.lower});
	}

	mixin DownCastMethod;
	mixin Visitors;
}
template Semantic(T) if(is(T==OpApplyFunctionDef)){ }

mixin template Semantic(T) if(is(T==ForeachStm)){
	Statement lower;
	GaggingScope gsc=null;
	Identifier[] checkMembership;
	override void semantic(Scope sc){
		mixin(SemPrlg);
		{
		if(lower) goto Llowered;
		if(!lsc){lsc = New!BlockScope(sc); lsc.setLoopingStm(this);}
		mixin(SemChld!q{aggregate});
		mixin(FinishDeductionProp!q{aggregate});
		auto ty = aggregate.type;
		auto tyu = aggregate.type.getHeadUnqual();
		// foreach over built-in arrays
		Type et = null;
		if(auto tt = tyu.isArrayTy()) et = tt.ty;
		if(auto tt = tyu.isDynArrTy()) et = tt.ty;
		if(et){
			needRetry=false;
			lower=createArrayForeach(sc,ty,et);
			mixin(SemCheck);
			goto Llowered;
		}
		// TODO: foreach over string types with automatic decoding
		// TODO: foreach over associative arrays
		// TODO: finish: foreach with opApply
		if(!gsc){
			auto msc=aggregate.getMemberScope();
			if(msc) gsc=New!GaggingScope(msc);
		}
		void createMembershipTest(string s){
			checkMembership~=New!Identifier(s);
			checkMembership[$-1].willAlias();
			checkMembership[$-1].accessCheck=AccessCheck.none;
			if(!gsc) checkMembership[$-1].sstate=SemState.error;
		}
		if(!checkMembership.length) createMembershipTest(isReverse?"opApplyReverse":"opApply");
		mixin(SemChldPar!q{sc=gsc;checkMembership[0]});
		if(checkMembership[0].sstate==SemState.completed){
			needRetry=false;
			lower=createOpApplyForeach(sc);
			mixin(SemCheck);
			goto Llowered;
		}
		// TODO: finish: foreach over ranges
		if(checkMembership.length==1){
			createMembershipTest(isReverse?"back":"front"); // 1
			createMembershipTest("empty"); // 2
			createMembershipTest(isReverse?"popBack":"popFront"); // 3
		}
		assert(checkMembership.length>=4);
		foreach(i;1..4) mixin(SemChldPar!q{sc=gsc;checkMembership[i]});
		alias util.all all;
		if(all!(a=>a.sstate==SemState.completed)(checkMembership[1..4])){
			needRetry=false;
			lower=createRangeForeach(sc);
			mixin(SemCheck);
			goto Llowered;
		}
		}
		// TODO: foreach over delegates
		// TODO: foreach over Tuples
		// TODO: EXTENSION: foreach using opApply/range primitives with UFCS
	Llowered:
		if(lower) mixin(SemChld!q{lower});
		else{
			// TODO: assert(lower) instead
			foreach(var; vars) var.semantic(lsc); // TODO: fix?
			//mixin(SemChld!q{scope=lsc, bdy}); // TODO: implement this
			bdy.semantic(lsc); // TODO: get rid of direct call
			mixin(SemProp!q{sc=lsc;bdy});
			mixin(PropErr!q{vars, aggregate});
		}
		mixin(SemEplg);
	}

	private ForStm createArrayForeach(Scope sc,Type ty,Type et)in{
		assert(ty is aggregate.type);
		assert(et is ty.getElementType);
	}body{
		if(vars.length>2){
			sc.error("at most two loop variables allowed for array foreach",
					 vars[0].loc.to(vars[$-1].loc));
			mixin(ErrEplg);
		}
		ForeachVarDecl var=null;
		auto s_t = Type.get!Size_t();
		if(vars.length == 2){
			if(vars[0].rtype){
				vars[0].type = vars[0].rtype.typeSemantic(lsc);
				auto rtype=vars[0].rtype;
				mixin(SemProp!q{sc=lsc;rtype});
				if(!vars[0].type.equals(s_t)){ // TODO: This is a stub
					sc.error(format("invalid type '%s' for index variable '%s'", vars[0].rtype.loc.rep, vars[0].name.toString()), vars[0].rtype.loc);
					sstate = SemState.error;
				}
			}else vars[0].type = s_t;
			var=vars[0];
		}
		assert(vars.length);
		if(vars[$-1].rtype){
			vars[$-1].type = vars[$-1].rtype.typeSemantic(lsc);
			mixin(SemProp!q{sc=lsc;vars[$-1].rtype});
			mixin(ImplConvertsTo!q{auto iconv; et, vars[$-1].type});
			if(!iconv){
				sc.error(format("cannot implicitly convert from element type '%s' to '%s'", et.toString(), vars[$-1].rtype.loc.rep),vars[$-1].rtype.loc);
				sstate = SemState.error;
			}
		}else vars[$-1].type = et;

		auto agvar=New!ForeachVarDecl(STC.init,ty,null,aggregate);
		agvar.loc=aggregate.loc;
		agvar.presemantic(sc);
		scope Statement[] mdecls=[agvar];
		scope Statement[] mups=[vars[$-1]];
		import variant;
		auto left=LiteralExp.factory(Variant(0,s_t));
		left.loc=aggregate.loc;
		auto agsym=New!Symbol(agvar);
		agsym.loc=agvar.loc;
		auto lenid=New!Identifier("length");
		lenid.loc=agsym.loc;
		auto right=New!(BinaryExp!(Tok!"."))(agsym,lenid);
		right.loc=agsym.loc;
		auto agsymi=New!Symbol(agvar);
		agsymi.loc=vars[$-1].loc;
		auto indexvar=New!ForeachVarDecl(STC.init,s_t,null,isReverse?right:left);
		indexvar.loc=(vars.length==2?vars[0]:vars[$-1]).loc;
		auto symidx=New!Symbol(indexvar);
		symidx.loc=indexvar.loc;
		auto index=New!IndexExp(agsymi,[cast(Expression)symidx]);
		symidx.loc=agsym.loc;
		vars[$-1].init_=index;

		auto f=ForeachRangeStm.createForStmForRange(sc,var,indexvar,s_t,isReverse,left,right,bdy,mdecls,mups);
		f.loc=loc;
		return f;
	}

	private{ // TODO: this uses space in every ForeachStm instance:
		Expression opApplyExp=null;
		OpApplyFunctionDef oafun=null;
	}
	VarDecl retVar=null;
	void setOpApplyFunctionDef(OpApplyFunctionDef oafun)in{assert(!this.oafun);}body{
		this.oafun=oafun;
	}

	bool isOpApplyForeach(){ return !!opApplyExp; }
	enum opApplyReturnCode=2;
	public static ReturnStm createOpApplyReturn(int returnCode, Location loc){
		import variant;
		auto val=LiteralExp.factory(Variant(returnCode,Type.get!int()));
		auto ret=New!ReturnStm(val);
		ret.loc=loc;
		ret.isOpApplyReturn=true;
		return ret;
	}
	private Statement createOpApplyForeach(Scope sc){
		enum SemRet=q{ return null; };
		if(!opApplyExp){
			auto be=New!(BinaryExp!(Tok!"."))(aggregate,New!Identifier(isReverse?"opApplyReverse":"opApply"));
			be.loc=aggregate.loc;
			// GC:
			auto fty=New!FunctionTy(STC.init,null,vars.map!(a=>cast(Parameter)a).array,VarArgs.none);
			auto ret=createOpApplyReturn(0,loc);
			auto cbdy=New!CompoundStm([bdy,ret]);
			cbdy.loc=bdy.loc;
			assert(!retVar);
			retVar=New!VarDecl(STC.init,null,null,New!VoidInitializerExp());
			retVar.presemantic(sc);
			Expression lmb=New!OpApplyFunctionLiteralExp(fty,cbdy,this);
			lmb.loc=loc; // TODO: fix diagnostics!
			opApplyExp=New!CallExp(be,[lmb]);
			opApplyExp.loc=aggregate.loc;
		}
		mixin(SemChld!q{opApplyExp});
		mixin(ImplConvertsTo!q{auto conv;Type.get!byte(),opApplyExp.type});
		if(!conv){
			sc.error(format("opApply must return an integral type, not '%s'",opApplyExp.type),aggregate.loc);
			mixin(ErrEplg);
		}
		assert(!retVar.type || retVar.sstate==SemState.completed);
		// TODO: locations?
		Statement[] cases;
		import variant;
		// default: break;
		cases~=New!DefaultStm([cast(Statement)New!BreakStm(null)]);
		if(retVar.type){
			// case 2: return retVar;
			cases~=New!CaseStm([cast(Expression)LiteralExp.factory(Variant(opApplyReturnCode,Type.get!int()))],
							   [cast(Statement)New!ReturnStm(New!Symbol(retVar))]);
		}
		assert(!!oafun);
		foreach(i,gto;oafun.gotos){
			cases~=New!CaseStm([cast(Expression)LiteralExp.factory(Variant(opApplyReturnCode+1+i,Type.get!int()))],[gto]);
		}
		// TODO: more cases for goto and labelled break/continue
		auto swbdy=New!CompoundStm(cases);
		swbdy.loc=loc;
		auto sw=New!SwitchStm(false,opApplyExp,swbdy);
		sw.loc=loc;
		Statement r=sw;
		if(retVar.type){
			r=New!CompoundStm([cast(Statement)retVar,sw]);
			r.loc=loc;
		}
		return r;
	}

	private ForStm createRangeForeach(Scope sc){
		if(vars.length>1){
			assert(vars.length);
			sc.error("only one loop variable allowed for range foreach",vars[1].loc.to(vars[$-1].loc));
			mixin(ErrEplg);
		}
		//for(auto =rng;!rng.empty;rng.popFront);
		auto s1=New!ForeachVarDecl(STC.init,null,null,aggregate);
		s1.presemantic(sc);
		auto sym=New!Symbol(s1);
		sym.loc=vars[0].loc;
		auto iempty=New!Identifier("empty");
		iempty.loc=aggregate.loc;
		auto empty=New!(BinaryExp!(Tok!"."))(sym,iempty);
		empty.loc=iempty.loc;
		auto e1=New!(UnaryExp!(Tok!"!"))(empty);
		e1.loc=empty.loc;
		auto ipop=New!Identifier(isReverse?"popBack":"popFront");
		ipop.loc=aggregate.loc;
		auto pop=New!(BinaryExp!(Tok!"."))(sym,ipop);
		pop.loc=ipop.loc;
		auto e2=New!CallExp(pop,(Expression[]).init);
		e2.loc=pop.loc;
		auto ielem=New!Identifier(isReverse?"back":"front");
		ielem.loc=vars[0].loc;
		auto elem=New!(BinaryExp!(Tok!"."))(sym,ielem);
		elem.loc=ielem.loc;
		vars[0].init_=elem;
		auto s2=New!BlockStm([cast(Statement)vars[0],bdy]);
		auto f=New!ForStm(s1,e1,e2,s2);
		f.loc=loc;
		return f;
	}

private:
	BlockScope lsc;
}


mixin template Semantic(T) if(is(T==ForeachRangeStm)){
	ForStm lower;
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{left,right});
		mixin(TypeCombine!q{auto type;left,right});
		if(!type){
			sc.error(format("incompatible types '%s' and '%s' for foreach range",left.type,right.type),left.loc.to(right.loc));
			mixin(ErrEplg);
		}
		if(!lower){
			lower=createForStmForRange(sc,var,null,type,isReverse,left,right,bdy);
			lower.loc=loc;
		}
		mixin(SemChld!q{lower});
		mixin(SemEplg);
	}

	static ForStm createForStmForRange(Scope sc,ForeachVarDecl var,ForeachVarDecl idxvar,Type type,bool isReverse,Expression left, Expression right, Statement bdy, scope Statement[] mdecls=[],scope Statement[] mups=[]){
		if(var){ assert(!var.init_); var.init_=left; }
		if(!idxvar){
			idxvar=New!ForeachVarDecl(STC.init, type, null, isReverse?right:left);
			idxvar.loc=idxvar.init_.loc;
		}
		auto boundvar=New!ForeachVarDecl(STC.init, type, null, isReverse?left:right);
		boundvar.loc=boundvar.init_.loc;
		auto tmpl=isReverse?boundvar:idxvar;
		tmpl.presemantic(sc);
		auto tmpr=isReverse?idxvar:boundvar;
		tmpr.presemantic(sc);
		auto s1=New!CompoundStm(mdecls~[cast(Statement)tmpl,tmpr]);
		s1.loc=(var?var:left).loc.to(right.loc);
		auto syml=New!Symbol(tmpl);
		syml.loc=left.loc;
		auto symr=New!Symbol(tmpr);
		symr.loc=right.loc;
		auto e1=type.isBasicType()? // DMD seems to do this. Is this documented?
			New!(BinaryExp!(Tok!"<"))(syml,symr):
			New!(BinaryExp!(Tok!"!="))(syml,symr);
		e1.loc=syml.loc.to(symr.loc);
		Expression e2=null;
		Statement s2;
		if(!isReverse){
			e2=New!(UnaryExp!(Tok!"++"))(syml);
			e2.loc=e1.loc;
			if(var) var.init_=syml;
			s2=New!BlockStm((var?[cast(Statement)var]:[])~mups~[bdy]);
		}else{
			auto edec=New!(UnaryExp!(Tok!"--"))(symr);
			edec.loc=e1.loc;
			auto sdec=New!ExpressionStm(edec);
			sdec.loc=edec.loc;
			if(var) var.init_=symr;
			s2=New!BlockStm((var?[sdec,var]:[cast(Statement)sdec])~mups~[bdy]);
		}
		s2.loc=bdy.loc;
		return New!ForStm(s1,e1,e2,s2);
	}
}

import bst;
struct DisjointIntervalSet(T, alias l=(auto ref x)=>x.l,alias r=(auto ref x)=>x.r)
	if(is(typeof((T a,T b)=>l(a)<l(a)&&l(a)<l(b)&&l(b)<l(a)&&l(b)<l(b)&&
	                        r(a)<r(a)&&r(a)<r(b)&&r(b)<r(a)&&r(b)<r(b))))
{
	private static struct CompareR{
		T payload;
		int opCmp(CompareR rhs){ return opCmp(rhs); }
		int opCmp(ref CompareR rhs){
			static if(is(typeof(r(payload).opCmp(r(rhs.payload)))))
				return r(payload).opCmp(r(rhs.payload));
			else{
				auto a=r(payload),b=r(rhs.payload);
				return a<b?-1:a>b?1:0;
			}
		}
		int opCmp(typeof(r(payload)) rhs){ return opCmp(rhs); }
		int opCmp(ref typeof(r(payload)) rhs){
			static if(is(typeof(r(payload).opCmp(rhs))))
				return r(payload).opCmp(rhs);
			else{
				auto a=r(payload),b=rhs;
				return a<b?-1:a>b?1:0;
			}
		}
	}
	private Set!CompareR right;
	auto range(){ return right.range.map!(a=>a.payload); }
	alias range opSlice;
	private size_t _length;
	@property size_t length(){ return _length; }

	S tryIntersect(S)(
		T toIntersect,
		scope S delegate(T) intersected,
		scope S delegate() noneFound)
	{
		auto rng=right.from(l(toIntersect));
		if(!rng.empty && l(rng.front.payload)<=r(toIntersect))
			return intersected(rng.front.payload);
		return noneFound();
	}

	// TODO: how to accept both ref and non-ref delegates without using alias?
	S insertOrIntersect(S)(
		T toInsert,
		scope S delegate() inserted,
		scope S delegate(T)intersected)
	{
		return tryIntersect(toInsert, intersected, (){
			right.insert(CompareR(toInsert));
			_length++;
			return inserted();
		});
	}
}


mixin template Semantic(T) if(is(T==SwitchStm)){
	BlockScope lsc;

	SwitchLabelStm[] cases;
	DefaultStm theDefault;

	VarDecl tmpVarDecl, tmpVarDeclStr; // store temporary value and it's length/characters

	import variant;
	private struct ComparisonValue{
		Variant value;
		int opCmp(ComparisonValue rhs){ return opCmp(rhs); }
		int opCmp(ref ComparisonValue rhs){
			return value.opBinary!"<"(rhs.value)?-1:value.opBinary!">"(rhs.value)?1:0;
		}
	}
	private struct CaseRange{
		ComparisonValue l,r;
		SwitchLabelStm stm;
		size_t index;
	}
	private DisjointIntervalSet!CaseRange casesInOrder;

	bool addCase(CaseStm c, Scope sc){
		bool err=false;
		foreach(i,e;c.e){
			auto cv=ComparisonValue(e.interpretV());
			auto cr=CaseRange(cv,cv,c,i);
			CaseRange pr;
			casesInOrder.insertOrIntersect(cr, {}, (CaseRange p){ pr=p; });
			auto prev = pr.stm;
			if(!prev) continue;
			err=true;
			if(auto p=prev.isCaseStm()){
				sc.error(format("duplicate case '%s' in switch statement",
				                c.e[cr.index]), c.e[cr.index].loc);
				sc.note("previous case is here",p.e[pr.index].loc);
			}else if(auto p=prev.isCaseRangeStm()){
				sc.error(format("case '%s' already occurs in case range '%s..%s'",
				                c.e[0], p.e1, p.e2), c.e[0].loc);
				sc.note("this case range is here",p.loc);
			}else assert(0);
		}
		if(err) return false;
		cases ~= c;
		resolveGotoCase(c);
		return true;
	}
	bool addCaseRange(CaseRangeStm c, Scope sc){
		if(f){
			if(sc){
				sc.error("final switch statement cannot include a case range", c.loc);
				sc.note("enclosing final switch statement is here", loc);
			}
			return false;
		}

		auto cr=CaseRange(ComparisonValue(c.e1.interpretV()),
		                  ComparisonValue(c.e2.interpretV()), c);
		CaseRange pr;
		casesInOrder.insertOrIntersect(cr, {}, (CaseRange p){ pr=p; });
		auto prev = pr.stm;
		if(!prev){cases ~= c; resolveGotoCase(c); return true; }
		if(auto p=prev.isCaseStm()){
			sc.error(format("case range '%s..%s' includes duplicate case '%s'", c.e1, c.e2, p.e[pr.index]), c.e1.loc.to(c.e2.loc));
			sc.note("previous case is here",p.e[0].loc);
		}else if(auto p=prev.isCaseRangeStm()){
			auto l=pr.l.value.opBinary!">="(cr.l.value)?pr.l.value:cr.l.value,
				r=pr.r.value.opBinary!"<="(cr.r.value)?pr.r.value:cr.r.value;
			assert(l.opBinary!"<="(r));
			if(l==r){
				auto ce = pr.l.value.opBinary!">"(cr.l.value)?c.e2:c.e1;
				sc.error(format("case '%s' already occurs in case range '%s..%s' (case ranges are inclusive)", ce, p.e1, p.e2), ce.loc);
				sc.note("this case range is here", p.loc);
			}else{
				auto le=pr.l.value.opBinary!">="(cr.l.value)?p.e1:c.e1,
					re=pr.r.value.opBinary!">="(cr.l.value)?p.e2:c.e2;
				sc.error(format("case range '%s..%s' overlaps with previous case range '%s..%s' in cases '%s..%s'", c.e1, c.e2, p.e1, p.e2, le, re), c.e1.loc.to(c.e2.loc));
				sc.note("previous case range was here",p.loc);
			}
		}
		return false;
	}
	bool addDefault(DefaultStm d, Scope sc){
		if(!theDefault){
			theDefault = d;
			if(f){
				sc.error("final switch statement cannot have a default clause", theDefault.loc);
				sc.note("enclosing final switch statement is here", loc);
				return false;
			}
			return true;
		}
		if(sc){
			sc.error("switch statement already has a default branch", d.loc);
			sc.note("previous default branch is here", theDefault.loc);
		}
		return false;
	}
	GotoStm[][] switchGotos;

	private bool tryResolveGoto(GotoStm gto){
		if(gto.t == WhichGoto.caseExp){
			auto cv=ComparisonValue(gto.e.interpretV());
			auto cr=CaseRange(cv,cv);
			ILabeledStm target;
			casesInOrder.tryIntersect(cr, (CaseRange x){ target=x.stm; }, (){});
			if(target){ gto.resolveLabel(target); return true; }
		}else if(gto.t == WhichGoto.default_){
			if(theDefault){ gto.resolveLabel(theDefault); return true; }
		}
		return false;
	}
	private void resolveGotoCase(SwitchLabelStm stm){
		if(!switchGotos.length) return;
		assert(switchGotos.length==2);
		foreach(gto;switchGotos[1]){
			assert(gto.t == WhichGoto.case_);
			gto.resolveLabel(stm);
		}
		switchGotos[1]=[];
	}

	private bool resolveAllGotos(Scope sc){
		if(!switchGotos.length) return false;
		assert(switchGotos.length==2);
		bool err=false;
		foreach(gto;switchGotos[1]){
			sc.error("no further case statements after 'goto case'",gto.loc);
			err=true;
		}
		foreach(gto;switchGotos[0]){
			if(tryResolveGoto(gto)) continue;
			err=true;
			if(gto.t==WhichGoto.caseExp)
				sc.error(format("case '%s' cannot be found in switch statement",gto.e),gto.loc);
			else{
				assert(gto.t==WhichGoto.default_);
				if(f) sc.error("no default case in final switch statement",gto.loc);
			}
		}
		switchGotos=[];
		return err;
	}

	void addGoto(GotoStm gto)in{
		with(WhichGoto){
			assert(gto.t.among(caseExp,case_,default_));
			assert(gto.t !is caseExp||gto.e&&gto.e.sstate==SemState.completed&&gto.e.isConstant());
		}
	}body{
		if(!switchGotos.length) switchGotos.length=2; // GC allocations
		if(!tryResolveGoto(gto)) switchGotos[gto.t==WhichGoto.case_]~=gto;
	}

	enum Kind{
		invalid,
		sintegral,
		uintegral,
		string,
		wstring,
		dstring,
	}
	Kind kind;

	bool isIntegral(){ return kind==kind.uintegral||kind==kind.sintegral; }
	bool isString(){ return kind==Kind.string||kind==Kind.wstring||kind==Kind.dstring; }

	private static Kind determineStringKind(Type tt){
		return tt is Type.get!string()  ? Kind.string  :
			   tt is Type.get!wstring() ? Kind.wstring :
			   tt is Type.get!dstring() ? Kind.dstring :
				                          Kind.invalid ;
	}

	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(!lsc){lsc = New!BlockScope(sc); lsc.setSwitchStm(this);}
		mixin(SemChldPar!q{e});
		void expErr(lazy string err){
			sc.error(err, e.loc);
			e.sstate = SemState.error;
		}
		Type etyu;
		if(e.sstate==SemState.completed){
			assert(!!e.type);
			etyu=e.type.getHeadUnqual();
			kind = determineStringKind(etyu);
			if(kind==Kind.invalid){
				if(auto i=etyu.isIntegral()){
					kind = i.isSigned()?kind.sintegral:kind.uintegral;
				}else{
					if(auto et=etyu.isEnumTy()){
						assert(!!et.decl);
						Type base;
						do{
							mixin(GetEnumBase!q{base;et.decl});
							et=base.isEnumTy();
						}while(et&&base);
						if(!base) e.sstate=SemState.error;
						else{
							kind = determineStringKind(base);
							if(kind == Kind.invalid){
								if(auto i=base.isIntegral()){
									kind = i.isSigned()?kind.sintegral:kind.uintegral;
								}else{
									expErr("enum base of switch expression type should be a built-in string or integral type");
									e.sstate=SemState.error;
								}
							}
						}
					}else{
						sc.error(format("switch expression should be of built-in string or integral type instead of '%s'",e.type), e.loc);
						e.sstate=SemState.error;
					}
				}
			}
		}
		if(f&&e.sstate==SemState.completed&&!etyu.isEnumTy()){
			expErr(format("final switch expression should be of enumeration type instead of '%s'",e.type));
		}
		mixin(SemChldPar!q{sc=lsc;s});

		bool err=false;
		if(f&&e.sstate==SemState.completed){
			assert(!!cast(EnumTy)etyu);
			auto et=cast(EnumTy)cast(void*)etyu;
			if(et.decl){
				mixin(SemChld!q{et.decl});
				foreach(m;et.decl.members){
					assert(m.init_&&m.init_.isConstant());
					auto v=ComparisonValue(m.init_.interpretV());
					auto cr=CaseRange(v,v);
					if(!casesInOrder.tryIntersect(cr, (CaseRange _)=>true, ()=>false)){
						if(!err){
							sc.error("non-exhaustive final switch", loc);
							err=true;
						}
						sc.note(format("enum member '%s' not represented",m.name), m.loc);
					}
				}
			}else err=true;
		}
		if(!f&&!theDefault){
			sc.error("non-final switch statement requires a default clause", loc);
			err=true;
		}
		err|=resolveAllGotos(sc);
		if(err) mixin(ErrEplg);
		mixin(SemProp!q{e,s});
		assert(!tmpVarDecl);
		if(!tmpVarDecl){
			tmpVarDecl = New!TmpVarDecl(STC.init, null, null, e);
			tmpVarDecl.presemantic(sc);
		}
		if(!tmpVarDeclStr && this.isString()){
			tmpVarDeclStr = New!TmpVarDecl(STC.init, null, null, New!LengthExp(e));
			tmpVarDeclStr.presemantic(sc);
		}
		if(tmpVarDeclStr) mixin(SemChld!q{tmpVarDeclStr});
	    mixin(SemChld!q{tmpVarDecl});
		mixin(SemEplg);
	}
}

mixin template Semantic(T) if(is(T==SwitchLabelStm)) { }
mixin template Semantic(T) if(is(T==CaseStm)||is(T==CaseRangeStm)||is(T==DefaultStm)){
	static if(is(T==CaseStm)) Expression eLeftover=null;

	enum _which = is(T==CaseStm)?"case":is(T==CaseRangeStm)?"case range":"default";

	override void semantic(Scope sc){
		mixin(SemPrlg);
		auto sw = sc.getSwitchStm();
		if(!sw){
			sc.error(_which~" statement must occur in switch statement", loc);
			mixin(ErrEplg);
		}
		static if(is(T==CaseRangeStm)){
			alias SwitchStm.Kind K;
			if(sw.kind!=K.invalid&&!sw.kind.among(K.sintegral,K.uintegral)){
				sc.error("cannot use a case range within a "~to!string(sw.kind)~" switch statement", loc);
				mixin(SemChld!q{s});
				mixin(ErrEplg);
			}
		}

		static if(is(T==CaseStm)){
			foreach(x;e) x.prepareInterpret();
			mixin(SemChldPar!q{e});
			// TODO: use chain and only
			foreach(ref x;e) if(x.sstate == SemState.completed){
				x.interpret(sc);
				mixin(PropRetry!q{x});
			}
			if(eLeftover && eLeftover.sstate == SemState.completed){
				eLeftover.interpret(sc);
				mixin(PropRetry!q{eLeftover});
			}
		}else static if(is(T==CaseRangeStm)){
			e1.prepareInterpret(); e2.prepareInterpret();
			mixin(SemChldPar!q{e1,e2});
			e1.interpret(sc);
			e2.interpret(sc);
			mixin(PropRetry!q{e1,e2});
		}
		else static assert(is(T==DefaultStm));

		static if(!is(T==DefaultStm)){
			if(sw.e.sstate==SemState.completed){
				static if(is(T==CaseStm)) foreach(ref ee;e){
					if(ee.sstate==SemState.completed)
						mixin(ImplConvertToPar!q{ee,sw.e.type});
				}else static if(is(T==CaseRangeStm)){
					if(e1.sstate==SemState.completed)
						mixin(ImplConvertToPar!q{e1,sw.e.type});
					if(e2.sstate==SemState.completed)
						mixin(ImplConvertToPar!q{e2,sw.e.type});
				}else static assert(0);
			}
		}
		bool shouldInsert=true;
		static if(is(T==CaseStm)) shouldInsert&=util.all!(a=>a.sstate==SemState.completed)(e);
		static if(is(T==CaseRangeStm)){
			if(e1.sstate==SemState.completed&&e2.sstate==SemState.completed){
				if(e1.interpretV().opBinary!">"(e2.interpretV())){
					sc.error(format("lower bound '%s' exceeds upper bound '%s' in case range", e1, e2), e1.loc.to(e2.loc));
					mixin(SetErr!q{e1});
					shouldInsert=false;
				}
			}else shouldInsert=false;
		}
		if(shouldInsert&&addedToSwitch==SwInsState.notAdded)
			addedToSwitch=mixin(`sw.add`~__traits(identifier,T)[0..$-3])(this,sc)?
				SwInsState.added:SwInsState.error;
		mixin(SemChld!q{s});
		static if(is(T==CaseStm)) mixin(PropErr!q{e});
		static if(is(T==CaseRangeStm)) mixin(PropErr!q{e1,e2});
		if(SwInsState.added==SwInsState.error) mixin(ErrEplg);
		mixin(SemEplg);
	}
private:
	enum SwInsState{
		notAdded,
		added,
		error,
	}
	auto addedToSwitch=SwInsState.notAdded;
}

mixin template Semantic(T) if(is(T==ReturnStm)){
	bool performedAccessCheck=false;
	bool isOpApplyReturn=false;
	override void semantic(Scope sc){
		mixin(SemPrlg);

		if(e){
			mixin(SemChldExpPar!q{e});
			if(auto et=e.isExpTuple()){
				if(!performedAccessCheck){
					auto exps=new Expression[et.length];
					size_t i=0;
					foreach(Expression exp;et){
						exps[i]=exp.clone(sc, InContext.none, AccessCheck.all, e.loc);
						exps[i].checkAccess(sc, AccessCheck.all);
						i++;
					}
					performedAccessCheck=true;
					e=New!ExpTuple(exps);
					mixin(SemChldExpPar!q{e});
				}
			}
		}

		auto fun = sc.getFunction();
		VarDecl retVar=null;
		if(!isOpApplyReturn) for(;;){
			// TODO: this results in total runtime quadratic
			//       in nesting depth of opApply foreach loops
			if(auto oafun=fun.isOpApplyFunctionDef()){
				if(!retVar) retVar=oafun.lstm.retVar;
				fun=oafun.scope_.getFunction();
			}else break;
		}
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
		}else if(fun.type.ret !is Type.get!void()){
			sc.error(format("non-void function '%s' should return a value",fun.name),loc);
			mixin(ErrEplg);
		}
		// TODO: auto ref
		isRefReturn = cast(bool)(fun.type.stc&STCref);
		if(isRefReturn && e){
			// TODO: ref return should probably be banned for void returning functions
			if(!e.checkLvalue(sc,e.loc)) mixin(ErrEplg);
		}

		if(e&&!e.finishDeduction(sc)) mixin(ErrEplg);
		if(retVar){
			assert(!isOpApplyReturn);
			assert(!!fun.type.ret);
			if(!retVar.rtype) retVar.rtype=fun.type.ret;
			mixin(SemChldPar!q{sc=retVar.scope_;retVar});
			assert(retVar.sstate==SemState.completed);
			auto sym=New!Symbol(retVar);
			sym.loc=loc;
			// TODO: make sure no destructor will be called on retVar once destructors are implemented
			// TODO: make sure this will pass @safe-ty checks
			auto asng=New!(BinaryExp!(Tok!"="))(sym,e);
			asng.loc=loc;
			Statement astm=New!ExpressionStm(asng);
			astm.loc=loc;
			auto ret=ForeachStm.createOpApplyReturn(ForeachStm.opApplyReturnCode,loc);
			auto r=New!CompoundStm([astm,ret]);
			r.loc=loc;
			r.semantic(sc);
			mixin(RewEplg!q{r});
		}
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
				sc.error(_which~" statement must occur in "~_enc~" statement",loc);
				mixin(ErrEplg);
			}
		}else{
			if(!mixin(_name)){
				auto lstm = sc.lookupLabel(e);
				if(!lstm) goto Lerr;
				if(auto lp = mixin(`lstm.s.is`~_query)()){
					mixin(_name) = lp;
				}else goto Lerr;
				if(!sc.isEnclosing(getLoweredEnclosingStatement())) goto Lerr;
			}
		}
		{
		auto fun=sc.getFunction();
		if(auto oafun=fun.isOpApplyFunctionDef()){
			if(oafun.lstm is mixin(_name)){
				auto r=ForeachStm.createOpApplyReturn(is(T==BreakStm),loc);
				r.semantic(sc);
				mixin(RewEplg!q{r});
			}else if(oafun.scope_.isEnclosing(mixin(_name))){
				auto ngto=New!(typeof(this))(e);
				ngto.loc=loc;
				auto r=ForeachStm.createOpApplyReturn(oafun.addGoto(ngto),loc);
				r.semantic(sc);
				mixin(RewEplg!q{r});
			}
		}
		assert(!!mixin(_name));
		mixin(SemEplg);
		}
	Lerr:
		sc.error(format("enclosing label '%s' for "~_which~" statement not found",e.toString()),e.loc);
		mixin(ErrEplg);
	}

	final getLoweredEnclosingStatement(){
		auto enc=mixin(_name);
		assert(!!enc);
		typeof(enc) processLower(Statement lower){
			if(auto l=lower.isLoopingStm())
				return l;
			return enc;
		}
		if(auto fr=enc.isForeachStm()){
			if(fr.lower) return processLower(fr.lower);
			assert(fr.isOpApplyForeach());
			return enc;
		}
		if(auto fr=enc.isForeachRangeStm())
			return processLower(fr.lower);

		return enc;
	}

private:
	static if(is(T==ContinueStm)) LoopingStm theLoop;
	else static if(is(T==BreakStm)) BreakableStm brokenOne;
	else static assert(0);
}

mixin template Semantic(T) if(is(T==GotoStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(!scope_) scope_=sc;
		final switch(t) with(WhichGoto){
			case identifier:
				assert(cast(Identifier)e);
				sc.registerForLabel(this, cast(Identifier)cast(void*)e);
				break;
			case caseExp:
			case case_:
			case default_:
				if(e){
					assert(t==caseExp);
					mixin(SemChld!q{e});
					mixin(IntChld!q{e});
				}
				if(!theSwitch) theSwitch=sc.getSwitchStm();
				if(theSwitch){
					if(!lower) theSwitch.addGoto(this);
					auto fun=sc.getFunction();
					if(auto oafun=fun.isOpApplyFunctionDef()){
						if(oafun.scope_.isEnclosing(theSwitch)){
							if(!lower){
								auto ngto=New!(typeof(this))(t,e);
								ngto.loc=loc;
								ngto.theSwitch=theSwitch;
								lower=ForeachStm.createOpApplyReturn(oafun.addGoto(ngto),loc);
							}
							mixin(SemChld!q{lower});
						}
					}
					break;
				}
				sc.error(format("'%s' outside switch statement",this),loc);
				mixin(ErrEplg);
		}
		mixin(SemEplg);
	}
	void resolveLabel(ILabeledStm tgt){
		target = tgt;
	}

	// gotos may need to be rewritten when they have already been fully analyzed due to opApply:
	Scope scope_;
	Statement lower;
private:
	ILabeledStm target;
	SwitchStm theSwitch; // used for lowering opApply, there is no surface syntax
}

class WithBaseScope: Scope{
	Scope other;
	Expression sym;
	this(Scope other,Expression sym){ this.other=other; this.sym=sym; }
	private AliasDecl createAliasToDecl(Declaration decl){
		return New!AliasDecl(STC.init,New!VarDecl(STC.init,New!(BinaryExp!(Tok!"."))(sym,New!Symbol(decl)),New!Identifier(decl.name.name),Expression.init));
	}
	private Declaration getAlias(Declaration decl){
		if(!decl||typeid(decl) is typeid(DoesNotExistDecl))
			return decl;
		if(auto odecl=symtabLookup(this,decl.name))
			return odecl;
		auto a = createAliasToDecl(decl);
		a.semantic(this);
		return a;
	}
	override @property ErrorHandler handler(){ return other.handler; }
	override Dependent!Declaration lookupHereImpl(Scope view,Identifier name,bool onlyMixins){
		return other.lookupHereImpl(view,name,onlyMixins).depmap!(a=>getAlias(a));
	}
	override Dependent!IncompleteScope getUnresolvedHereImpl(Scope view, Identifier ident, bool onlyMixins, bool noHope){
		return other.getUnresolvedHereImpl(view,ident,onlyMixins,noHope);
	}
}

mixin template Semantic(T) if(is(T==WithStm)){
	BlockScope bsc;
	Expression exp = null;
	TmpVarExp tmp = null;
	Expression sym = null;

	private Expression createSymbol(Expression e,Expression this_){
		if(!this_) return e;
		if(e is this_) return tmp?tmp.sym:Type.get!void();
		if(auto fld=e.isFieldExp())
			return New!(BinaryExp!(Tok!"."))(createSymbol(fld.e1,this_),fld.e2);
		assert(0,text(e));
	}

	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(!exp) exp=e;
		mixin(SemChld!q{exp}); // TODO: maybe do not ignore s if error, but only lookup failures within it
		auto msc=exp.getMemberScope();
		if(!msc){
			// TODO: fix getMemberScope for built-in types
			sc.error("invalid 'with' expression",e.loc);
			mixin(ErrEplg);
		}
		auto this_=exp.extractThis();
		// silly special casing of void
		if(!tmp&&this_&&this_.type !is Type.get!void()) tmp=New!TmpVarExp(this_);
		if(tmp) mixin(SemChld!q{tmp});
		if(!sym) sym=createSymbol(exp,this_);
		mixin(SemChld!q{sym});
		if(!bsc){
			bsc=New!BlockScope(sc);
			if(tmp) msc=New!WithBaseScope(msc,sym);
			if(!bsc.addImport(msc,ImportKind.mixin_)) mixin(ErrEplg);
		}
		mixin(SemChld!q{sc=bsc;s});
		mixin(SemEplg);
	}
}

mixin template Semantic(T) if(is(T==CatchStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		sc.error("unimplemented feature CatchStm",loc);
		mixin(ErrEplg);
	}
}

mixin template Semantic(T) if(is(T==TryStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		sc.error("unimplemented feature TryStm",loc);
		mixin(ErrEplg);
	}
}

// declarations
mixin template Semantic(T) if(is(T==Declaration)){
	Scope scope_ = null;

	invariant(){assert(sstate != SemState.pre || !scope_, to!string(typeid(this)));}

	void pickupSTC(STC stc){
		this.stc|=~conflictingSTC(this.stc)&stc;
	}

	void potentialInsert(Scope sc, Declaration dependee){
		if(name) sc.potentialInsert(name, dependee, this);
	}
	void potentialRemove(Scope sc, Declaration dependee){
		if(name) sc.potentialRemove(name, dependee, this);
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

	override void semantic(Scope sc){
		if(sstate==SemState.pre) presemantic(sc);
		mixin(SemPrlg);
		mixin(SemEplg);
	}


	final bool isMember(){
		if(stc&STCstatic) return false;
		auto fd=isFunctionDecl();
		if(fd && fd.isConstructor()){
			// constructors are logically members of the enclosing scope
			auto decl=scope_.getDeclaration();
			if(!decl||!decl.isAggregateDecl()||decl.stc&STCstatic) return false;
			if(auto decl2=decl.scope_.getDeclaration)
				return !!decl2.isAggregateDecl();
		}
		if(auto decl=scope_.getDeclaration()) return !!decl.isAggregateDecl();
		return false;
	}

	/* Returns true if the declaration has to be checked for accessibility at
	   the given access check level.
	 */
	bool needsAccessCheck(AccessCheck check)in{assert(check!=AccessCheck.init);}body{
		return !(stc&STCstatic) && check == AccessCheck.all;
	}

	Dependent!Declaration matchCall(Scope sc, const ref Location loc, Type this_, Expression func, Expression[] args, ref MatchContext context){
		return null.independent!Declaration;
	}
	void matchError(Scope sc, Location loc, Type this_, Expression[] args){
		sc.error(format("%s '%s' is not callable",kind,name.toString()),loc);
	}

	Declaration matchInstantiation(Scope sc, const ref Location loc, bool gagged, bool isMixin, Expression owner, TemplArgsWithTypes args){
		if(sc) sc.error(format("can only instantiate templates, not %s%ss",kind,kind[$-1]=='s'?"e":""),loc);
		return null;
	}

	Declaration matchIFTI(Scope sc, const ref Location loc, Type this_, Expression func, TemplArgsWithTypes args, Expression[] funargs){
		if(sc) sc.error(format("%s '%s' is not a function template",kind, name.name),loc);
		return null;
	}

	// TODO: make OO instead of functional?
	static Dependent!bool isDeclAccessible(Declaration from, Declaration decl, Declaration mfun=null)in{
		assert(decl.sstate != SemState.pre);
	}body{
		bool show = from&&decl&&from.name&&decl.name&&from.name.name=="compare"&&decl.name.name=="o";

		// TODO: this check might be redundant
		if(decl.stc&STCstatic
		|| decl.stc&STCenum && decl.isVarDecl()
		|| decl.isTmpVarDecl()) // TODO: ok?
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
			if(dl is enc){
				return (!from.isAggregateDecl()||mfun&&mfun.isFunctionDecl()).independent;
			}
			if(auto raggr=dl.isReferenceAggregateDecl()){
				mixin(AggregateParentsInOrderTraversal!q{
					mixin(IsDeclAccessible!q{auto b; Declaration, parent, decl, mfun});
					if(b) return true.independent;
				});
			}
			if(from is enc) return (!from.isAggregateDecl()).independent;
			if(dl.stc & STCstatic) return false.independent;
			if(auto fn=dl.isFunctionDef()){
				if(auto fn2=decl.isFunctionDef()){
					fn2.notifyIfNot(STCstatic,fn);
				}else fn.canBeStatic = false;
			}
			// TODO: infer whether a template instantiation needs to be local or not
			mfun=dl;
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
	Expression initLeftover=null;
}

mixin template Semantic(T) if(is(T==VarDecl)){
	Type type;

	TupleContext tupleContext;
	bool isField=false; // TODO: would rather not store these

	override void presemantic(Scope sc){
		if(sstate != SemState.pre) return;
		if(!name){
			scope_ = sc;
			sstate = SemState.begin;
		}else super.presemantic(sc);
		if(sstate == SemState.error) type = null; // TODO: why is this here?
		if(auto decl=sc.getDeclaration())
			if(auto aggr = decl.isAggregateDecl())
				isField=true;
	}

	// used in Symbol to get the correct storage classes for the variable decl
	// TODO: this duplicates logic present in VarDecl.semantic
	enum SymbolResolve = q{
		assert(!!vd.type);
		vd.type.semantic(meaning.scope_);
		mixin(Rewrite!q{vd.type});
		mixin(CircErrMsg);
		mixin(SemProp!q{vd.type});
		type=vd.type;
		if(vd.type.sstate != SemState.error && vd.type.isTypeTuple()){
			mixin(MeaningSemantic); // TODO: does this generate invalid circ. dependencies?
			mixin(CircErrMsg);
			mixin(PropRetry!q{sc=meaning.scope_;meaning});
			if(vd.tupleContext){
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
		// if(vd.stc&(STCimmutable|STCconst) && vd.init_) vd.stc|=STCstatic;
	};

	final bool willInterpretInit()in{assert(!!init_);}body{
		return stc&(STCenum|STCstatic) || isField;
	}

	protected void defaultInit(){
		// convention: init_ is null means that the type should be zeroed out
		if(!init_ && type && type.sstate == SemState.completed){
			// default initializers
			if(auto aggr=type.getUnqual().isAggregateTy())
			if(auto strd=aggr.decl.isStructDecl()){
				init_ = New!StructConsExp(type,(Expression[]).init);
				init_.loc = loc;
				init_.initOfVar(this);
			}
		}

	}

	// allow EnumVarDecl to continue semantic
	void doSemEplg(){
		mixin(SemEplg);
	}

	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(rtype){
			type=rtype.typeSemantic(sc);
			mixin(PropRetry!q{rtype});
		}

		if(init_){
			init_.initOfVar(this);
			if(init_.sstate!=SemState.completed){
				if(willInterpretInit()) init_.prepareInterpret();
				mixin(SemChldExpPar!q{init_});
			}
			// deduce type
			if(!type && init_.sstate!=SemState.error) type=init_.type;
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

		{scope(exit) if(sstate==SemState.error) type=null;
			needRetry=false;
			mixin(SemProp!q{type});
			mixin(SemCheck);
		}
		type = type.applySTC(stc);
		// add appropriate storage classes according to type
		stc |= type.getHeadSTC();
		// TODO: this is controversial, and should only be done for fields
		// if(stc&(STCimmutable|STCconst) && init_) stc|=STCstatic;

		if(!init_) defaultInit(); // TODO: this is a hack (and incorrect, since some code relies on init_==null)

		if(init_){
			mixin(SemChldPar!q{init_});
			if(willInterpretInit()&&init_.sstate==SemState.completed){
				mixin(ImplConvertsTo!q{bool iconv;init_, type});
				// type deduction should finish before interpretation
				// expressions with no deduced type have type 'void'
				if(!iconv||type is Type.get!void()) mixin(FinishDeductionProp!q{init_});
				assert(init_.sstate == SemState.completed, to!string(init_));
				init_.interpret(sc);
				mixin(PropRetry!q{init_});
				// TODO: is there a more elegant way to handle array initialization?
			}
		}else if(stc&STCenum){
			sc.error("manifest constants must have initializers",loc);
			mixin(ErrEplg);
		}

		if(auto tp = type.isTypeTuple()){
			alias tupleContext tc;
			auto len = tp.length;
			if(!tc) tc = New!TupleContext();
			ExpTuple et = null;
			TypeTuple tt = null;
			if(init_ && init_.type){
				et=init_.isExpTuple();
				if(!et) tt=init_.type.isTypeTuple();
				if(et||tt){
					if(len!=(et?et.length:tt.length)){
						sc.error(format("tuple of %d elements cannot initialize tuple of %d elements",et.length,len),loc);
						mixin(ErrEplg);
					}
				}else{
					et = New!ExpTuple(len, init_);
					et.loc = init_.loc;
					init_ = et;
					mixin(SemChldPar!q{init_});
				}
				// better error message for type mismatch:
				if(!init_.isVoidInitializerExp()&&init_.sstate==SemState.completed){
					mixin(ImplConvertsTo!q{bool iconv; init_, type});
					if(!iconv) mixin(ImplConvertTo!q{init_, type});
				}
				///
			}
			if(init_) assert(tt || init_.sstate == SemState.error || et && et.length==len);
			// TODO: gc allocations
			if(!tc.vds && !tc.initLeftover){
				tc.vds = new VarDecl[cast(size_t)len];
				Expression commaLeft=null;
				if(init_){
					if(auto ce=init_.isCommaExp()){
						commaLeft=ExpTuple.splitCommaExp(ce, et);
						commaLeft.semantic(sc);
						assert(commaLeft.sstate == SemState.completed);
						init_ = et;
					}
					assert(et || !willInterpretInit());
				}
				if(commaLeft && !tc.vds.length) tc.initLeftover=commaLeft;
				foreach(i, ref x;tc.vds){
					auto id  = name?New!Identifier("__tuple_"~name.name~"_"~to!string(i)):null;
					auto ini = et?et.index(sc,InContext.none,init_.loc,i):null;
					if(!i && commaLeft){
						assert(ini);
						auto nini=New!(BinaryExp!(Tok!","))(commaLeft, ini);
						nini.loc=nini.e1.loc.to(nini.e2.loc);
						ini=nini;
					}
					x = newVarDecl(stc, tp.index(sc,InContext.none,loc,i), id, ini);
					x.sstate = SemState.begin;
					x.loc = loc;
					x.scope_=scope_;
					x.isField=isField;
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
					sym.willAlias();
					x = sym;
				}
			}
			foreach(x;tc.syms) mixin(SemChldPar!q{x});
			if(!tc.tupleAlias){
				auto stpl = New!ExpTuple(tc.syms); // TODO: can directly transfer ownership
				stpl.loc = loc;
				tc.tupleAlias = New!AliasDecl(STC.init, newVarDecl(STC.init, stpl, name, null));
				tc.tupleAlias.sstate = SemState.begin;
				tc.tupleAlias.loc = loc;
				tc.tupleAlias.scope_=scope_;
			}
			mixin(SemChld!q{tc.tupleAlias});
			if(init_) mixin(SemProp!q{init_});
			return doSemEplg(); // Symbol will rewrite the meaning
		}

		if(init_){
			mixin(SemProp!q{init_});
			// order is significant: fully interpreted expressions might carry information
			// that allows more implicit conversions
			if(!init_.isVoidInitializerExp()){
				mixin(ImplConvertTo!q{init_,type});
			}
			if(!willInterpretInit()) mixin(FinishDeductionProp!q{init_});
			else{
				mixin(IntChld!q{init_});
				if(stc&STCenum){
					prepareEnumInitializer();
					//mixin(SemCheck);
				}
			}
		}

		type = type.checkVarDecl(sc,this);
		mixin(SemProp!q{type});
		if(stc&STCref){ mixin(NoRetry); handleRef(sc); mixin(SemCheck); }
		if(isField){
			auto aggr = sc.getDeclaration().isAggregateDecl();
			assert(!!aggr);
			if(!(stc&(STCstatic|STCenum))) aggr.layoutChanged();
		}
		return doSemEplg();
	}

	private void prepareEnumInitializer(){
		assert(init_.isConstant()||init_.isArrayLiteralExp());
		// re-allocate mutable dynamic array constants everywhere:
		if(init_.type.isDynArrTy()&&init_.type.getElementType().isMutable()){
			if(auto lexp=init_.isLiteralExp()){
				init_=lexp.toArrayLiteral();
			}
		}
	}
	protected void handleRef(Scope sc){
		sc.error("local variables and fields cannot be ref", loc);
		mixin(ErrEplg);
	}
	final protected void actuallyHandleRef(Scope sc){
		if(init_&&!init_.checkLvalue(sc, init_.loc)) mixin(ErrEplg);
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
		if(name&&!name.length) return; // TODO: why is this here?
		super.presemantic(sc);
	}

	final bool mustBeTypeDeduced(){
		return !type && !rtype && !init_;
	}

	override void defaultInit(){} // parameters are not default-initialized

	override protected void handleRef(Scope sc){ return actuallyHandleRef(sc); }

protected:
	override Parameter newVarDecl(STC stc, Expression rtype, Identifier name, Expression initializer){
		return New!Parameter(stc,rtype,name,initializer);
	}
}

mixin template Semantic(T) if(is(T==ForeachVarDecl)){
protected:
	override ForeachVarDecl newVarDecl(STC stc, Expression rtype, Identifier name, Expression initializer){
		return New!ForeachVarDecl(stc,rtype,name,initializer);
	}
}

mixin template Semantic(T) if(is(T==CArrayDecl)||is(T==CArrayParam)){
	final void computeRtype(){
		for(;;)if(auto id=postfix.isIndexExp()){
			postfix = id.e;
			id.e = rtype;
			rtype = id;
		}else break;
	}
	override void semantic(Scope sc){
		computeRtype();
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

mixin template Semantic(T) if(is(T==ImportDecl)){
	override void potentialInsert(Scope sc, Declaration dependee){
		sc.potentialInsertArbitrary(dependee, this);
	}
	override void potentialRemove(Scope sc, Declaration dependee){
		sc.potentialRemoveArbitrary(dependee, this);
	}
	private string path;
	override void presemantic(Scope sc){
		assert(symbols.length);
		if(symbols.length>1){
			auto decls=new Declaration[symbols.length];
			foreach(i,ref x;decls){
				x = New!ImportDecl(stc, symbols[i..i+1]);
				x.loc = loc;
			}
			auto r=New!BlockDecl(STC.init,decls);
			r.loc=loc;
			r.semantic(sc);
			mixin(RewEplg!q{r});
		}
		if(sstate != SemState.pre) return;
		if(!(stc&STCvisibility)) stc|=STCprivate;
		sstate = SemState.begin;
		scope_ = sc;
		potentialInsert(sc, this);

		string computePath(Expression e){
			if(auto fe=e.isFieldExp()){
				assert(cast(Identifier)fe.e2);
				auto id=cast(Identifier)cast(void*)fe.e2;
				return computePath(fe.e1)~'/'~id.name;
			}else if(auto id=e.isIdentifier()) return id.name;
			else if(auto ib=e.isImportBindingsExp()){
				stc|=STCstatic;
				return computePath(ib.symbol);
			}else if(auto ass=e.isAssignExp()){
				stc|=STCstatic;
				return computePath(ass.e2);
			}else assert(0,text("TODO: ",e,typeid(e)));
		}

		path = computePath(symbols[0]);
	}
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(sstate == SemState.pre){
			presemantic(sc);
			if(rewrite) return;
		}
		scope(exit) if(!needRetry) potentialRemove(sc, this);
		auto cm = sc.getModule();
		assert(!!cm);
		auto repo = cm.repository;
		string err;
		auto m = repo.getModule(path, true, err);
		if(!m){
			if(err) sc.error(err, symbols[0].loc);
			mixin(ErrEplg);
		}
		if(!(stc&STCstatic)&&!sc.addImport(m.sc,importKindFromSTC(stc))) mixin(ErrEplg);;
		mixin(SemEplg);
	}
}


mixin template Semantic(T) if(is(T==EnumVarDecl)){
	EnumDecl enc;
	Expression rinit;
	EnumVarDecl prec;

	override void doSemEplg(){ }

	override void semantic(Scope sc){
		assert(enc.name&&sc is enc.msc||sc is enc.scope_);
		mixin(SemPrlg);
		if(!init_){
			if(!prec){
				init_ = LiteralExp.factory(Variant(0, Type.get!int()));
				init_.loc=loc;
			}else{
				mixin(SemChld!q{prec});
				assert(prec.rinit);
				if(!rtype) type=prec.type;
				auto previnit=prec.rinit.cloneConstant();
				auto one=LiteralExp.factory(Variant(1,Type.get!int()));
				// TODO: prettier error messages?
				init_=New!(BinaryExp!(Tok!"+"))(previnit,one);
				init_.loc=previnit.loc=one.loc=loc;
			}
		}
		needRetry=false;
		if(!rinit) super.semantic(sc);
		mixin(SemCheck);
		if(!prec&&!enc.base) enc.base=type;
		if(!rinit) rinit=init_;
		if(enc.name){
			auto ty=enc.getType();
			assert(!!ty);
			mixin(GetEnumBase!q{auto base;enc});
			assert(init_.type is type && base);
			mixin(ImplConvertsTo!q{auto b; type, base});
			if(!b){
				sc.error(format("incompatible initializer '%s' of type '%s' for enum member of base type '%s'",init_, init_.type, base), loc);
				mixin(ErrEplg);
			}
			mixin(ConvertTo!q{init_,ty});
		}
		mixin(SemEplg);
	}
}

mixin CreateBinderForDependent!("GetEnumBase");

mixin template Semantic(T) if(is(T==EnumDecl)){
	Type base;
	EnumTy type;
	final Type getType(){ return type; }
	final Dependent!Type getEnumBase()in{assert(rbase||!!name);}body{
		if(!base){
			if(!rbase){
				assert(!!msc);
				members[0].semantic(msc);
				mixin(Rewrite!q{members[0]});
				if(members[0].sstate != SemState.completed)
					return Dependee(members[0],msc).dependent!Type;
			}else{
				base=rbase.typeSemantic(msc);
				if(rbase.needRetry||rbase.sstate==SemState.error)
					return Dependee(members[0],msc).dependent!Type;
			}
			assert(!!base);
		}
		return base.independent;
	}

	override void presemantic(Scope sc){
		if(sstate != SemState.pre) return;
		if(name){
			super.presemantic(sc);
			type = New!EnumTy(this);
			msc = New!NestedScope(sc);
		}else scope_ = sc;
		foreach(m;members){
			m.enc=this;
			m.presemantic(msc?msc:sc);
		}
		sstate = SemState.begin;
		if(!members.length){
			sc.error("enumeration must have at least one member",loc);
			mixin(ErrEplg);
		}
		foreach(i,x;members[1..$]) x.prec=members[i];
		if(name||rbase){
			foreach(x;members){
				if(x.rtype){
					sc.error("explicit type only allowed in anonymous enum declarations"~(rbase?" without base type":""),x.rtype.loc);
					x.sstate=SemState.error;
				}
			}
		}
	}
	NestedScope msc;
	override void semantic(Scope sc){
		if(sstate == SemState.pre) presemantic(sc);
		mixin(SemPrlg);
		if(rbase&&(!base||base.sstate!=SemState.completed)){
			base=rbase.typeSemantic(sc);
			mixin(SemProp!q{rbase});
		}
		mixin(SemChld!q{sc=msc?msc:sc;members[0]});
		assert(members[0].init_.isConstant());
		if(name && !base) base=members[0].rinit.type;
		foreach(i,ref m;members[1..$])
			mixin(SemChldPar!q{sc=msc?msc:sc;m});
		mixin(PropErr!q{members[1..$]});
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
		needRetry = true;
		potentialInsert(sc, this);
	}

	private Statement evaluate(Scope sc){
		mixin(SemPrlg);
		scope(exit) if(sstate==SemState.error) potentialRemove(sc, this);
		cond.prepareInterpret();
		cond.prepareLazyConditionalSemantic();
		mixin(SemChld!q{cond});
		mixin(FinishDeductionProp!q{cond});

		mixin(ConvertTo!q{cond,Type.get!bool()});
		//cond = evaluateCondition(sc, cond);
		mixin(IntChld!q{cond});
		needRetry = false;
		potentialRemove(sc, this);
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

	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(sstate == SemState.pre) presemantic(sc);
		auto res = evaluate(sc);
		if(!res||res is this) return;
		assert(!!res);
		auto r=res;
		r.semantic(sc);
		mixin(RewEplg!q{r});
	}
private:
	bool lazyDup = false;
}


mixin template Semantic(T) if(is(T==StaticAssertDecl)){
	Expression a0Leftover=null, a1Leftover=null;
	override void presemantic(Scope sc){
		if(sstate != SemState.pre) return;
		sstate = SemState.begin;
		scope_=sc;
	}
	override void semantic(Scope sc){
		mixin(SemPrlg);

		do{
			if(a.length<1){
				sc.error("missing arguments to static assert", loc);
				mixin(ErrEplg);
			}
			a[0].prepareInterpret();
			a[0].prepareLazyConditionalSemantic();
			mixin(SemChldExp!q{a[0]});
			a=Tuple.expand(sc, AccessCheck.none, a, a0Leftover);
		}while(a.length<1||a[0].sstate!=SemState.completed);
		if(a.length>2){
		Ltoomany:
			sc.error("too many arguments to static assert", loc);
			mixin(ErrEplg);
		}else if(a.length==2) a[1].prepareInterpret();

		foreach(x; a) mixin(FinishDeduction!q{x});
		mixin(PropErr!q{a});
		auto bl=Type.get!bool();
		mixin(ConvertTo!q{a[0],bl});
		a[0].interpret(sc);
		if(a0Leftover) a0Leftover.interpret(sc);
		mixin(SemProp!q{a[0]});
		if(a0Leftover) mixin(SemProp!q{a0Leftover});

		if(!a[0].interpretV()){
			// work around finally block goto limitation...
			void printMessage(){
				sc.error(format("static assertion failure: '%s' is false",a[0].loc.rep), loc);
			}
			if(a.length == 1) printMessage();
			else try{
				mixin(SemChld!q{a[1]});
				a=Tuple.expand(sc, AccessCheck.none, a, a1Leftover);
				if(a.length>2) goto Ltoomany;
				if(a.length == 1) printMessage();
				else if(!a[1].isType()){
					a[1].interpret(sc);
					if(a1Leftover) a1Leftover.interpret(sc);
					mixin(SemProp!q{a[1]});
					if(a1Leftover) mixin(SemProp!q{a1Leftover});
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
			if(vd.init_){
				sc.error("alias declarations cannot have initializers",loc);
				mixin(ErrEplg);
			}
			if(auto cad=vd.isCArrayDecl()) cad.computeRtype();
			aliasee = vd.rtype;
		}else if(auto fd = decl.isFunctionDecl()){
			aliasee = fd.type;
		}else assert(0);}

		aliasee.weakenAccessCheck(AccessCheck.none);
		aliasee.willAlias();
		mixin(SemChld!q{aliasee});
		TemplateDecl.finishArgumentPreparation(sc, aliasee); // EXTENSION
		if(!isAliasable(aliasee)){
			sc.error("cannot alias an expression",loc);
			mixin(ErrEplg);
		}
		if(set){
			assert(set.scope_ is scope_);
			auto add=getAliasedDecl();
			if(!add||!add.isOverloadableDecl()&&!add.isOverloadSet()){
				scope_.redefinitionError(this, set);
				mixin(ErrEplg);
			}
		}
		mixin(SemEplg);
	}

	private static auto checkAliasImpl(bool wantSymbol=false)(Expression aliasee){
		static if(wantSymbol) alias Symbol R;
		else alias bool R;
		if(auto ae=aliasee.isAddressExp())
			if(aliasee.type.getFunctionTy())
				if(auto sym=ae.e.isSymbol()){
					static if(wantSymbol) return sym;
					else return true;
				}
		R go(Expression aliasee){
			if(auto sym=aliasee.isSymbol()){
				static if(wantSymbol) return sym;
				else return true;
			}
			static if(!wantSymbol)
				if(aliasee.isType()||aliasee.isConstant()||aliasee.isExpTuple())
					return true;
			if(auto fld=aliasee.isFieldExp()){
				auto r=go(fld.e1);
				if(!r && fld.e1.isCurrentExp){
					static if(wantSymbol) return fld.e2;
					else return true;
				}
				return r;
			}
			static if(wantSymbol) return null;
			else return false;
		}
		return go(aliasee);
	}

	static Symbol getAliasBase(Expression aliasee){
		return checkAliasImpl!true(aliasee);
	}
	static bool isAliasable(Expression aliasee){
		return checkAliasImpl!false(aliasee);
	}

	Declaration simpleAliasedDecl()in{
		assert(sstate == SemState.completed);
	}body{
		if(auto sym = aliasee.isSymbol()){
			assert(!!sym.meaning);
			return sym.meaning;
		}
		return null;
	}

	Declaration getAliasedDecl(){
		if(auto sym = aliasee.isSymbol()){
			assert(!!sym.meaning);
			return sym.meaning;
		}
		if(auto fd = aliasee.isFieldExp()){
			assert(!!fd.e2.meaning);
			return fd.e2.meaning;
		}
		assert(sstate != SemState.completed);
		return null;
	}

	Expression getAliasee(Scope sc, AccessCheck check, InContext inContext, const ref Location loc)in{
		assert(sstate == SemState.completed);
		assert(!aliasee.isSymbol());
	}body{
		auto r=aliasee.clone(sc, inContext, check, loc);
		if(auto et=r.isExpTuple()) et.accessCheck=check;
		else r.restoreAccessCheck(sc, check);
		return r;
	}

	void setOverloadSet(OverloadSet set)in{assert(this.set is null);}body{ this.set=set; }

private:
	Expression aliasee;
	OverloadSet set;
}


mixin template Semantic(T) if(is(T==BlockDecl)){
	override void potentialInsert(Scope sc, Declaration decl){
		foreach(x; decls) x.potentialInsert(sc, decl);
	}
	override void potentialRemove(Scope sc, Declaration decl){
		foreach(x; decls) x.potentialRemove(sc, decl);
	}

	override void pickupSTC(STC stc){
		super.pickupSTC(stc);
		foreach(x;decls) x.pickupSTC(stc);
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

	ShortcutScope shortcutScope; // store for forbidden inherited symbols
	                     // TODO: could be used to look up inherited members faster
	private static class ShortcutScope : NestedScope{
		ReferenceAggregateDecl raggr;
		this(ReferenceAggregateDecl raggr, Scope parent){
			super(parent);
			this.raggr=raggr;
		}
		public override void potentialAmbiguity(Identifier decl, Identifier lookup){
			error(format("declaration of '%s' "~suspiciousDeclDesc, decl), decl.loc);
			note(format("this lookup on subclass '%s' should have %s if it was valid", raggr.name,lookup.meaning?"resolved to it":"succeeded"), lookup.loc);
		}
	}

	void initShortcutScope(Scope parent){
		shortcutScope = new ShortcutScope(this, parent);
	}

	private Dependent!void fillShortcutScope(){
		if(!shortcutScope) return indepvoid;
		mixin(AggregateParentsInOrderTraversal!(q{
			foreach(decl; &parent.bdy.traverseInOrder){
				if(decl.name && decl.name.ptr){
					// TODO: check visibility!
					// TODO: handle the case where the meaning of a symbol does not
					// change due to inheritance, eg. due to imports or alias
					if(auto d=shortcutScope.lookupHere(shortcutScope, decl.name, false).value){
						if(typeid(d) is typeid(DoesNotExistDecl))
							shortcutScope.potentialAmbiguity(decl.name, d.name);
					}
				}
			}
		},"this"));
		return indepvoid;
	}

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
					assert(!!parent.scope_);
					parent.semantic(parent.scope_);
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

	private mixin CreateBinderForDependent!("InheritVtbl");

	private Identifier[const(char)*] sealedLookups;
	Dependent!(std.typecons.Tuple!(OverloadSet,ubyte)) lookupSealedOverloadSetWithRetry(Scope view, Identifier name){
		mixin(LookupHere!q{auto ovsc; asc, view, name, true});
		if(!ovsc){
			auto ident = sealedLookups.get(name.ptr, null);
			if(!ident){
				ident=New!Identifier(name.name);
				ident.recursiveLookup = false;
				ident.onlyMixins = true;
				ident.loc=name.loc;
				sealedLookups[name.ptr]=ident;
			}
			mixin(Lookup!q{_; ident, view, asc});
			if(auto nr=ident.needRetry) { return q(OverloadSet.init,nr).independent; }
			ovsc = ident.meaning;
		}

		return q(ovsc?ovsc.isOverloadSet():null,ubyte.init).independent;
	}

	Dependent!OverloadSet lookupSealedOverloadSet(Scope view, Identifier name){
		mixin(LookupSealedOverloadSetWithRetry!q{auto setnr;this,view,name});
		if(!setnr[1]) return setnr[0].independent;
		static class OverloadSetSealer : Expression{
			ReferenceAggregateDecl self;
			Scope view;
			Identifier name;
			this(ReferenceAggregateDecl self, Scope view, Identifier name, ubyte nr){
				this.self=self;
				this.view=view;
				this.name=name;
				needRetry = nr;
			}
			override void semantic(Scope sc){
				mixin(SemPrlg);
				mixin(LookupSealedOverloadSetWithRetry!q{auto setnr;self,view,name});
				if(setnr[1]) { needRetry=setnr[1]; return; }
				mixin(SemEplg);
			}
		}
		return Dependee(New!OverloadSetSealer(this,view,name,setnr[1]), null).dependent!OverloadSet;
	}

	private Dependent!void addToVtbl(FunctionDecl decl){
		// inherit vtbl (need to wait until parent is finished with semantic)
		mixin(InheritVtbl!q{ClassDecl parent; this});
		OverloadSet set=null;
		if(!parent) goto Lfresh;
		{
		mixin(LookupSealedOverloadSetWithRetry!q{auto setnr; parent, asc, decl.name});
		if(setnr[1]){ needRetry=setnr[1]; return indepvoid; }
		set=setnr[0];
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
	public final void findFirstNParents(size_t n,bool weak=false)in{
		assert(n<=parents.length);
	}body{
		if(!rparents) rparents = parents.map!(a=>a.ddup).array; // uncontrolled gc allocation
		if(n<=knownParents) return;
		alias scope_ sc;
		foreach(i,ref x; parents[knownParents..n]){
			if(x.sstate == SemState.error) continue;
			if(!weak) x.semantic(sc);
			mixin(Rewrite!q{x});
		}
		Expression dummyLeftover=null;
		parents = Tuple.expand(scope_, AccessCheck.none, parents, dummyLeftover, rparents);
		assert(!dummyLeftover);
		auto knownBefore = knownParents;
		updateKnownParents(); // valid because only prior unknown parents can cause expansion
		foreach(i, ref x; parents[knownBefore..knownParents]){
			if(x.sstate == SemState.error) continue;
			assert(x.sstate == SemState.completed);
			auto ty = x.typeSemantic(sc);
			static bool checkInheritance(Type ty, Scope sc, const ref Location loc){
				auto agg = ty.isAggregateTy();
				if(!agg && ty.sstate == SemState.completed ||
				   agg && !agg.decl.isReferenceAggregateDecl()){
					sc.error("base specifier must name a class or interface",loc);
					return false;
				}
				if(agg && !agg.decl.bdy){
					sc.error(format("base '%s' is incomplete",agg),loc);
					return false;
				}
				return true;
			}
			if(ty && !checkInheritance(ty,sc,rparents[knownBefore+i].loc))
				x = New!ErrorTy();
		}
		assert(parents.length==rparents.length,text(parents," ",rparents));
	}

	final override Expression unresolvedParent()out(x){
		//assert(!x||x.needRetry); // !!!!?
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
		mixin CreateBinderForDependent!("CheckCircularInheritance",);
		mixin CreateBinderForDependent!("FillShortcutScope",);

		mixin(CheckCircularInheritance!q{_;this});
		mixin(InheritVtbl!q{ClassDecl _; this});
		if(!parents.length) goto Lvtbl;
		{
		assert(parents[0].sstate==SemState.error||!!cast(AggregateTy)parents[0]);
		bool hasExplicitBaseClass = false;
		if(parents[0].sstate != SemState.error){
			{alias scope_ sc;mixin(SemChld!q{rparents[0]});}
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
			{alias scope_ sc;mixin(SemChldPar!q{rparents[1+i]});}
		}
		}
	Lvtbl:
		enum SemRet = q{ return; };
		if(bdy) foreach(decl; &bdy.traverseInOrder){
			if(auto fd = decl.isFunctionDecl()){
				if(vtbl.has(fd)) continue;
				mixin CreateBinderForDependent!("AddToVtbl");
				mixin(AddToVtbl!(q{_;this,fd},false));
				mixin(SemCheck);
			}
		}
		bool[FunctionDecl] hiders;
		foreach(x; vtbl.vtbl){
			if(x.state != VtblState.needsOverride) continue;
			// TODO: one could maybe optimize this:
			mixin(LookupSealedOverloadSetWithRetry!q{auto ovsnr; this, asc, x.fun.name});
			if(ovsnr[1]){ needRetry=ovsnr[1]; return; }
			auto ovs=ovsnr[0];
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
			x.state = VtblState.inherited;
		}
		//if(auto parent = parentClass())
		//mixin(PropRetry!q{parent});
		mixin(FillShortcutScope!q{_;this});
		mixin(PropErr!q{rparents});
		if(bdy) foreach(decl; &bdy.traverseInOrder) mixin(PropErr!q{decl});
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
				stack.circularInheritanceError(scope_,rad);
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
		void circularInheritanceError(Scope sc, ReferenceAggregateDecl start){
			// TODO: uncontrolled allocations
			auto arr = initial[0..min(num,$)].dup;
			auto k = overrun.keys, v = overrun.values;
			//import std.algorithm;
			sort!"a[1]<b[1]"(zip(k,v));
			arr~=k;
			arr=arr.find(start);
/+			auto first=iota(0,arr.length).reduce!((a,b)=>arr[a].sourcePriority<arr[b].sourcePriority?a:b);
+/ // TODO: report DMD bug
			size_t j=0;
			foreach(i;1..arr.length)
				if(arr[i].sourcePriority<arr[j].sourcePriority)
					j=i;
			auto rdecls=chain(arr[j+1..$],arr[0..j+1]);

			bool first = true;
			foreach(x;zip(chain(rdecls[1..rdecls.length],rdecls[0..1]),rdecls).retro){ // TODO: dollar
				alias util.all all;
				assert(all!(a=>cast(AggregateTy)a)(x[1].parents));
				auto rparent = zip(x[1].parents,x[1].rparents)
					.find!((a,b)=>(cast(AggregateTy)cast(void*)a[0]).decl is b)(x[0])
					.front[1];
				mixin(SetErr!q{rparent});
				if(first) sc.error("circular inheritance",rparent.loc);
				else sc.note("part of inheritance cycle",rparent.loc);
				first = false;
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
mixin template Semantic(T) if(is(T==UnionDecl)){
	override void presemantic(Scope sc){
		if(name) stc|=STCstatic;
		super.presemantic(sc);
	}
}

mixin template Semantic(T) if(is(T==AggregateDecl)){
	/* overridden in ReferenceAggregateDecl */
	protected void findParents(){ }
	protected Expression unresolvedParent(){ return null; }
	protected void finishInheritance()in{assert(!unresolvedParent());}body{ }

	override void presemantic(Scope sc){
		if(sstate != SemState.pre) return;
		if(auto decl=sc.getDeclaration())
			if(auto aggr=decl.isAggregateDecl())
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

private:
	AggregateTy type;
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

abstract class OverloadableDecl: Declaration{
	this(STC stc,Identifier name){super(stc,name);}
	override OverloadableDecl isOverloadableDecl(){return this;}
}

class OverloadSet: Declaration{
	// A lookup that sealed this overloadset:
	// TODO: less conservative strategy only forbidding inserting overloads
	// that are superior matches to prior lookups / overrides?
	Identifier sealingLookup = null;

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
		assert(!sealingLookup);
		assert(!decls.length||decls[0].name.name is decl.name.name);
		assert(!tdecls.length||tdecls[0].name.name is decl.name.name);
		assert(!adecls.length||adecls[0].name.name is decl.name.name);
	}body{
		if(!loc.line) loc=decl.loc;
		if(auto td=decl.isTemplateDecl()) tdecls~=td;
		else decls~=decl;
		// TODO: check that all overloads are @property or non-property (?)
		// TODO: detect @property function templates (?)
		if(decl.stc&STCproperty) stc|=STCproperty;
		if(auto v=decl.stc&STCvisibility) stc|=v; // TODO: detect conflicts
	}

	void addAlias(AliasDecl decl)in{
		assert(!sealingLookup);
		assert(!decls.length||decls[0].name.name is decl.name.name);
		assert(!tdecls.length||tdecls[0].name.name is decl.name.name);
		assert(!adecls.length||adecls[0].name.name is decl.name.name);
	}body{
		decl.setOverloadSet(this);
		adecls~=decl;
	}

	bool hasFunctions(){
		alias util.any any;
		return any!(a=>a.isFunctionDecl())(decls)||
			any!(a=>a.iftiDecl())(tdecls);
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

	private static struct Matched{
		MatchContext context; // context for matching of function call
		FunctionDecl decl;

		Match tmatch; // match level of template instantiation
		Declaration tdecl;

		/+ //just for documentation for now
		bool isMatch(){ return context.match!=Match.none && (decl || tdecl); }
		bool isFunctionMatch(){ return decl && !tdecl; }
		bool isTemplateMatch(){ return tdecl && !decl; }
		bool isIftiMatch(){ return decl && tdecl; }+/
	}

	private mixin CreateBinderForDependent!("CanOverride");
	// TODO: make this a public member function of function decl instead
	private static Dependent!bool canOverride(FunctionDecl fd, FunctionDecl fun){
		alias util.all all;
		import std.range;
		if(fd.stc & STCnonvirtual) return false.independent;
		// analyze function types
		fun.analyzeType();
		mixin(Rewrite!q{fun.type});
		fd.analyzeType();
		mixin(Rewrite!q{fd.type});
		if(fun.type.sstate==SemState.error) return Dependee(fun.type, fd.scope_).dependent!bool;
		if(fd.type.sstate==SemState.error) return Dependee(fd.type, fd.scope_).dependent!bool;
		if(fun.type.needRetry) return Dependee(fun.type, fd.scope_).dependent!bool;
		if(fd.type.needRetry) return Dependee(fd.type, fd.scope_).dependent!bool;
		// end analyzing types

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
	final Dependent!FunctionDecl findOverrider(FunctionDecl fun)in{
		assert(fun.scope_.getDeclaration().maybe!(a=>a.isFunctionDef())||!!sealingLookup);
	}body{
		// TODO: multi-dep
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
	final Dependent!FunctionDecl determineOverride(FunctionDecl fun)in{
		assert(fun.scope_.getDeclaration().maybe!(a=>a.isFunctionDef())||!!sealingLookup);
	}body{
		size_t num = 0;
		foreach(ref decl; decls){
			decl.semantic(decl.scope_);
			mixin(Rewrite!q{decl});
			auto fd=decl.isFunctionDecl();
			if(!fd) continue;
			/*
			if(fd.needRetry||fd.sstate == SemState.error)
			return Dependee(fd,fd.scope_).dependent!FunctionDecl;// TODO: check if we really do not need this*/
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

	private static void thisSTCIsBetter(alias str, R)(R stcr, STC stc, ref size_t num){
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

	override Dependent!Declaration matchCall(Scope sc, const ref Location loc, Type this_, Expression func, Expression[] args, ref MatchContext context){

		if(tdecls.length||adecls.length)
			return New!FunctionOverloadMatcher(this, sc, loc, this_, func, args).independent!Declaration;
		if(decls.length == 1) return decls[0].matchCall(sc, loc, this_, func, args, context);

		auto matches = new Matched[decls.length]; // pointless GC allocation
		foreach(i,decl; decls){
			if(decl.sstate == SemState.error){
				auto fd=decl.isFunctionDecl();
				if(!fd||fd.type.errorsInParams())
					return Dependee(decl,decl.scope_).dependent!Declaration;
			}
			mixin(MatchCall!q{auto matched; decls[i], null, loc, this_, func, args, matches[i].context});
			assert(!matched||cast(FunctionDecl)matched);
			matches[i].decl = cast(FunctionDecl)cast(void*)matched;
		}

		// TODO: some work is lost if this kicks in. significant?
		mixin(DetermineMostSpecialized!q{FunctionDecl r; this, matches, this_, context});

		if(!r) foreach(a;args)
		if(auto ae = a.isAddressExp())
		if(ae.isUndeducedFunctionLiteral()){
			return New!FunctionOverloadMatcher(this, sc, loc, this_, func, args).independent!Declaration;
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
				// matching static the right way is better
				if(!(bestMatches[0].decl.stc&STCstatic) != !this_ && !(match.decl.stc&STCstatic) == !this_)
					continue;
				if(!(bestMatches[0].decl.stc&STCstatic) == !this_ && !(match.decl.stc&STCstatic) != !this_){
					swap(bestMatches[0], bestMatches[i+1]);
					continue;
				}
				// inout functions are less specialized
				if(bestMatches[0].context.inoutRes==InoutRes.none&&match.context.inoutRes!=InoutRes.none)
					continue;
				if(alas2 && bestMatches[0].context.inoutRes!=InoutRes.none&&match.context.inoutRes==InoutRes.none){
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
		auto best = reduce!max(Match.none, map!(a=>a.tmatch)(tmatches));
		if(best == Match.none) return indepvoid;

		TemplateDecl cand = null;
		size_t cpos;
		foreach(i,ref c; tmatches){
			if(c.tmatch!=best){
				c.tdecl = c.decl = null;
				continue;
			}
			assert(cast(TemplateInstanceDecl)c.tdecl);
			cand = c.tdecl.isTemplateInstanceDecl().parent;
			cpos = i;
			break;
		}
		if(!cand) return indepvoid;
		foreach(ref c; tmatches[cpos+1..$]){
			if(c.tmatch!=best){
				c.tdecl = c.decl = null;
				continue;
			}
			assert(cast(TemplateInstanceDecl)c.tdecl);
			auto altCand = c.tdecl.isTemplateInstanceDecl().parent;
			mixin(AtLeastAsSpecialized!q{bool alas; altCand, cand});
			if(alas) { cand = altCand; }
		}
		foreach(ref c; tmatches){
			if(!c.tdecl) continue;
			assert(cast(TemplateInstanceDecl)c.tdecl);
			auto altCand = c.tdecl.isTemplateInstanceDecl().parent;
			mixin(AtLeastAsSpecialized!q{bool alas; altCand, cand});
			if(!alas) { c.tdecl = c.decl = null; }
		}
		return indepvoid;
	}

	private FunctionDecl cand; // TODO: somewhat fragile, maybe better to just recompute
	private FunctionDecl altCand;
	final override void matchError(Scope sc, Location loc, Type this_, Expression[] args){
		if(count == 1){
			if(!adecls.length)
				return (decls.length?decls[0]:tdecls[0]).matchError(sc,loc,this_,args);
		}
		if(altCand is null){
			sc.error(format("no matching function for call to '%s(%s)'",name,join(map!"a.type.toString()"(args),",")), loc);
			// TODO: better criterium for filter
			foreach(decl; chain(decls,tdecls.filter!(a=>!!a.iftiDecl))){
				if(auto fdef = decl.isFunctionDecl())
					if(fdef.type.sstate == SemState.error) continue;
				sc.note(format("candidate %s not viable", decl.kind), decl.loc); // TODO: say why
			}
			foreach(decl; adecls){
				auto add = decl.getAliasedDecl();
				if(add){
					if(auto fdef = add.isFunctionDecl())
						if(fdef.type.sstate == SemState.error) continue;
				}else continue;
				sc.note("candidate alias not viable", decl.loc);
				sc.note(format("this is the aliased %s", add.kind), add.loc);
			}
		}else{
			assert(cand !is altCand);
			// TODO: list all of the most specialized functions
			sc.error(format("call to '%s' is ambiguous",name), loc);
			sc.note("candidate function",cand.loc);
			sc.note("candidate function",altCand.loc);
		}
	}

	override Declaration matchInstantiation(Scope sc, const ref Location loc, bool gagged, bool isMixin, Expression owner, TemplArgsWithTypes args){
		if(tdecls.length==0)
			return decls[0].matchInstantiation(sc, loc, gagged, isMixin, owner, args);
		if(tdecls.length==1) return tdecls[0].matchInstantiation(sc, loc, gagged, isMixin, owner, args);
		return New!TemplateOverloadMatcher(this, sc, loc, gagged, isMixin, owner, args);
	}

	final void instantiationError(Scope sc, const ref Location loc, TemplateInstanceDecl[] insts, TemplArgsWithTypes args){
		size_t c=0;
		foreach(x;insts) if(x) c++;
		assert(c!=1);
		if(!c){
			sc.error(format("no matching template for instantiation '%s!(%s)'",name,join(map!"a.toString()"(args.args),",")),loc);
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

	override Declaration matchIFTI(Scope sc, const ref Location loc, Type this_, Expression func, TemplArgsWithTypes args, Expression[] funargs){
		if(tdecls.length==0)
			return decls[0].matchIFTI(sc, loc, this_, func, args, funargs);
		if(tdecls.length==1) return tdecls[0].matchIFTI(sc, loc, this_, func, args, funargs);
		return New!FunctionOverloadMatcher(this, sc, loc, this_, func, args, funargs);
	}

	override @property string kind(){
		if(count==1) return decls.length?decls[0].kind:tdecls[0].kind;
		return "overload set";
	}

	public final @property size_t count(){ return decls.length + tdecls.length + adecls.length; }

// private: // TODO: introduce again
	OverloadableDecl[] decls;
	TemplateDecl[] tdecls;
	AliasDecl[] adecls;
}


class CrossScopeOverloadSet : Declaration{
	Declaration[] decls;

	private static void removeDuplicates(ref Declaration[] decls){
		// TODO: optimize
		bool[Declaration] has;
		foreach(ref d;decls){
			if(d in has){
				swap(d,decls[$-1]);
				decls=decls[0..$-1];
			}
			has[d]=true;
		}
	}

	static Declaration buildDecl(Scope sc, Declaration[] decls, Declaration alt){
		if(!decls.length) return alt;
		removeDuplicates(decls);
		if(decls.length==1) return decls[0];
		alias util.all all;
		if(all!(a=>!a.isCrossScopeOverloadSet())(decls)){
			auto r=New!CrossScopeOverloadSet(decls);
			r.scope_=sc;
			return r;
		}
		Declaration[] ndecls;
		foreach(d;decls){
			if(auto ov=d.isCrossScopeOverloadSet())
				ndecls~=ov.decls;
			else ndecls~=d;
		}
		return buildDecl(sc, ndecls, alt);
	}
	/+private+/ this(Declaration[] decls)in{
		assert(decls.length>1);
		foreach(x;decls[1..$]) assert(x.name.name == decls[0].name.name);
	}body{
		this.decls=decls;
		super(STC.init, decls[0].name);
		sstate = SemState.completed;
		loc=decls[0].loc;
	}

	static class OverloadResolver(string op,TT...) : Declaration{
		// TODO: report DMD bug. This does not work if TT is called T instead

		static if(TT.length) TT args;
		Declaration[] decls;
		this(Scope sc, TT args, Declaration[] decls){
			static if(TT.length) this.args=args;
			this.decls=decls;
			super(STC.init, decls[0].name);
		}
		override void semantic(Scope sc){
			mixin(SemPrlg);
			mixin(op);
			if(sstate == SemState.pre){scope_=sc; sstate = SemState.begin; }
			Declaration r=null;
			foreach(decl;decls){
				if(!decl) continue;
				if(!r){ r=decl; continue; }
				// TODO: report DMD bug, filter should obviously work
				auto numMatches = 0;
				for(size_t i=0;i<decls.length;i++){
					if(decls[i]) swap(decls[numMatches++], decls[i]);
				}
				if(sc) reportConflict(sc, loc, decls[0..numMatches]);//filter!(function(a)=>!!a)(decls));
				mixin(ErrEplg);
			}
			mixin(RewEplg!q{r});
		}
		final override void matchError(Scope sc, Location loc, Type this_, Expression[] args){
			// TODO: get rid of this override.
		}
	}

	override Dependent!Declaration matchCall(Scope sc, const ref Location loc, Type this_, Expression func, Expression[] args, ref MatchContext context){

		enum op=q{
			foreach(ref decl;decls){
				if(decl&&decl.sstate!=SemState.error){
					MatchContext dummy;
					mixin(MatchCall!q{decl;decl,null,loc,args, dummy});
				}
			}
		};

		auto r=New!(OverloadResolver!(op,Type,Expression,Expression[]))(sc, this_, func, args, decls.dup);
		r.loc=loc;
		r.semantic(sc);
		return r.independent!Declaration;
	}

	override Declaration matchInstantiation(Scope sc, const ref Location loc, bool gagged, bool isMixin, Expression owner, TemplArgsWithTypes args){
		auto insts=decls.dup;
		foreach(ref ifti;insts) ifti = ifti.matchInstantiation(sc, loc, gagged, isMixin, owner, args);
		auto r=New!(OverloadResolver!(instOp))(sc,insts);
		r.loc=loc;
		r.semantic(sc);
		return r;
	}
	enum instOp=q{
		foreach(ref decl; decls){
			mixin(SemChld!q{decl});
			if(decl.sstate == SemState.error) decl = null;
		}
	};

	override Declaration matchIFTI(Scope sc, const ref Location loc, Type this_, Expression func, TemplArgsWithTypes args, Expression[] funargs){
		auto iftis=decls.dup;
		foreach(ref ifti;iftis) ifti = ifti.matchIFTI(null, loc, this_, func, args, funargs);
		auto r=New!(OverloadResolver!(instOp))(sc, iftis);
		r.loc=loc;
		r.semantic(sc);
		return r;
	}
	static void reportConflict(R)(Scope sc, const ref Location loc, R decls)in{
		assert(!!sc&&!decls.empty);
	}body{
		// TODO: improve error messages
		sc.error(format("conflicting declarations for a lookup of '%s'",decls.front.name),loc);
		foreach(decl;decls) sc.note("part of conflict", decl.loc);
	}
	final void reportConflict()(Scope sc, Location loc){ // workaround for DMD bug
		reportConflict(sc, loc, decls);
	}

	override @property string kind(){
		return "cross-scope overload set";
	}

	override bool needsAccessCheck(AccessCheck check){ return false; }

	override string toString(){ return join(map!(to!string)(decls)); }

	mixin DownCastMethod;
}


// TODO: should those be nested classes of OverloadSet? Silly indentation...
abstract class SymbolMatcher: Declaration{
	OverloadSet set;
	Expression func;
	MatchContext context; // will be picked up by Symbol

	private bool _hasFailedToMatch = false;
	final @property bool hasFailedToMatch(){ return _hasFailedToMatch; }
	protected void failMatching(){
		_hasFailedToMatch = true;
		mixin(SemEplg);
	}

	abstract void emitError(Scope sc_); // in{ assert(hasFailedToMatch()); }

	this(OverloadSet set, const ref Location loc, Expression func){
		super(set.stc,set.name);
		this.set=set;
		this.func = func;
		this.loc=loc;
	}

	mixin DownCastMethod;
}

class TemplateOverloadMatcher: SymbolMatcher{
	OverloadSet.Matched[] insts;
	TemplArgsWithTypes args;
	this(OverloadSet set, Scope sc, const ref Location loc, bool gagged, bool isMixin, Expression func, TemplArgsWithTypes args){
		this.args=args;
		super(set, loc, func);
		// TODO: gc allocation
		insts = new OverloadSet.Matched[](set.tdecls.length);
		foreach(i, ref x; insts)
			x.tdecl=set.tdecls[i].matchInstantiation(sc, loc, false, isMixin, func, args);
		enum SemRet = q{return;}; // TODO: remove
		mixin(RetryEplg);
	}
	override void semantic(Scope sc){
		mixin(SemPrlg);
		foreach(ref x; insts){
			if(!x.tdecl) continue;
			mixin(SemChldPar!q{x.tdecl});
			auto inst=x.tdecl.isTemplateInstanceDecl();
			assert(!!inst);
			if(inst.hasFailedToMatch()){
				x.tmatch = Match.none;
				x.tdecl = null;
			}else x.tmatch=inst.match;
			assert(!x.tdecl||x.tdecl.sstate==SemState.error||inst.completedMatching);
		}
		mixin(EliminateLessSpecializedTemplateMatches!q{_;OverloadSet,insts});
		size_t c = 0;
		foreach(x; insts) if(x.tdecl){ mixin(PropErr!q{x.tdecl}); c++; }
		if(c==1) foreach(r; insts) if(r.tdecl) mixin(RewEplg!q{r.tdecl});
		failMatching();
	}

	override void emitError(Scope sc_){
		if(sc_) set.instantiationError(sc_, loc, cast(TemplateInstanceDecl[])insts, args);
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

	Expression[] args;

	Type this_;

	UnaryExp!(Tok!"&")[][] literals;

	OverloadSet.Matched[] matches;
	OverloadSet.Matched[] tmatches;
	Declaration[] iftis;
	// match the eponymous declaration
	// if it was not determined by IFTI.
	Expression[] eponymous;

	size_t[] positions;

	this(OverloadSet set, Scope sc, const ref Location loc, Type this_, Expression func, Expression[] args)in{
		assert(set.count>0);
	}body{
		this.this_=this_;
		this.args=args;
		super(set, loc, func);
		// TODO: GC allocations
		matches = new OverloadSet.Matched[](set.decls.length);
		tmatches = new OverloadSet.Matched[](set.tdecls.length);
		iftis = new Declaration[](set.tdecls.length);
		foreach(i, ref x; iftis){
			tmatches[i].tmatch=Match.none;
			x=set.tdecls[i].matchIFTI(sc, loc, this_, func, templArgs, args);
		}

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
		enum SemRet=q{return;};// TODO: remove
		mixin(RetryEplg);
	}

	bool matchATemplate = false;
	TemplArgsWithTypes templArgs;

	this(OverloadSet set, Scope sc, const ref Location loc, Type this_, Expression func, TemplArgsWithTypes templArgs, Expression[] args){
		matchATemplate = true;
		this.templArgs = templArgs;
		this(set, sc, loc, this_, func, args);
	}

	TemplateInstanceDecl waitFor = null;
	FunctionDecl rewriteIfOk = null;

	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(waitFor){
			if(waitFor.sstate != SemState.started){
				mixin(SemChld!q{sc=waitFor.scope_;waitFor});
			}
			assert(!!rewriteIfOk);
			auto r=rewriteIfOk;
			mixin(RewEplg!q{r});
		}

		foreach(ad; set.adecls){
			if(ad.sstate == SemState.error) continue;
			ad.semantic(set.scope_);
			mixin(PropRetry!q{ad});
		}

		assert(iftis.length == set.tdecls.length);
		foreach(i, ref x; iftis){
			if(!x) continue;
			if(eponymous.length && eponymous[i]) continue;

			auto tid=x.isTemplateInstanceDecl();
			if(!tid || !tid.completedMatching){
				x.semantic(sc);
				mixin(SemProp!q{x});
			}

			assert(!!cast(TemplateInstanceDecl)x);
			auto inst = cast(TemplateInstanceDecl)cast(void*)x;
			assert(!!inst.completedMatching);
			if(inst.hasFailedToMatch()){ x=null; continue; }
			tmatches[i].tmatch=inst.match;
			if(!inst.finishedInstantiation()){
				inst.finishInstantiation(false);
				mixin(Rewrite!q{inst});
				x=inst;
			}

			auto fd = inst.iftiDecl();
			if(!fd){
				// if(!matchATemplate) continue; // TODO: do we want this?
				if(inst.sstate != SemState.completed && inst.sstate != SemState.started){
					if(inst.isGagged()&&sc&&sc.handler.showsEffect()) inst.ungag();
					inst.startAnalysis();
					x.semantic(sc);
				}
				mixin(SemProp!q{x}); // TODO: show instantiation site
				fd = inst.iftiDecl();
				if(!fd){
					// TODO: gc allocation
					if(!eponymous.length) eponymous = new Expression[](iftis.length);
					// this creates identifiers without location, as we don't want those
					// to show up in circular dependency traces
					// TODO: accessCheck?
					auto id=New!Identifier(x.name.name);
					id.errorOnMatchingFailure=false;
					auto be=New!(BinaryExp!(Tok!"."))(New!Symbol(x), id);
					(eponymous[i]=be).willCall();
					continue;
				}
			}
			assert(!!fd);

			fd.analyzeType();
			if(auto nr=fd.type.needRetry) { needRetry = nr; return; }
		}
		// resolve the eponymous declarations that are not determined by IFTI.
		foreach(ref x; eponymous) if(x){
			x.semantic(sc);
			if(x.sstate==SemState.error){
				if(auto sym=x.isSymbol()){
					if(sym.isSymbolMatcher){
						assert(!sym.errorOnMatchingFailure);
						x=null;
						continue;
					}
				}
			}
			mixin(SemProp!q{x});
			auto sym = x.isSymbol();
			if(!sym || !sym.meaning.isFunctionDecl()){
				mixin(MatchCall!q{x; x, sc, loc, args});
				if(!x) continue;
				mixin(PropRetry!q{sc=null;x});
			}
		}

		if(!matchATemplate){
			mixin(DetermineFunctionMatches!q{_;this, sc});
			foreach(l1;literals[0..$-1]) foreach(ref l2;l1){mixin(SemChldPar!q{l2});}
		}

		MatchContext tcontext;
		mixin(DetermineTemplateMatches!q{_;this});

		// TODO: error handling
		FunctionDecl r=null;
		mixin(DetermineMostSpecialized!q{auto t; set, tmatches, this_, tcontext});
		auto cand = set.cand, altCand = set.altCand;
		mixin(DetermineMostSpecialized!q{auto f; set, matches, this_, context});

		TemplateInstanceDecl inst;
		if(context.match>=tcontext.match) r=f;
		else if(t){
			r=t;
			context = tcontext;
			inst = r.extractTemplateInstance();
			if(inst.sstate != SemState.completed && inst.sstate != SemState.started){
				if(inst.isGagged()&&sc&&sc.handler.showsEffect) inst.ungag();
				inst.startAnalysis();
				inst.semantic(sc);
			}

			if(matchATemplate){mixin(RewEplg!q{inst});}
		}
		// TODO: could re-use the function literal arguments of the most specialized function
		if(!r){
			if(!set.cand && !set.altCand || tcontext.match>context.match)
				set.cand = cand, set.altCand = altCand;
			// TODO: more adequate error message in the matchATemplate case
			failMatching();
		}else{
			if(inst&&inst.sstate != SemState.completed){
				waitFor = inst;
				rewriteIfOk = r;
			}else mixin(RewEplg!q{r});
		}
	}

	override void emitError(Scope sc){
		if(sc) set.matchError(sc, loc, this_, args);
	}

private:
	mixin CreateBinderForDependent!("DetermineFunctionMatches");
	mixin CreateBinderForDependent!("DetermineTemplateMatches");
	mixin CreateBinderForDependent!("ConvertLiterals");
	Dependent!void determineFunctionMatches(Scope sc){
		enum SemRet = q{ return indepvoid };
	    trymatch: foreach(i,decl; set.decls){
			adjustArgs(args, i);
			foreach(a; args) if(a.sstate == SemState.error) continue trymatch;
			//auto matched=set.decls[i].matchCall(null, loc, args, matches[i].context);
			mixin(MatchCall!q{auto matched; set.decls[i], null, loc, this_, func, args, matches[i].context});
			assert(!matched||cast(FunctionDecl)matched);
			matches[i].decl = cast(FunctionDecl)cast(void*)matched;
			if(matches[i].decl){
				mixin(ConvertLiterals!q{_;this,sc, args, matches[i].decl});
				if(hasErrors(args)) matches[i].decl=null;
			}
		}
		restoreArgs(args);
		return indepvoid;
	}

	Dependent!void determineTemplateMatches()in{
		assert(set.tdecls.length == iftis.length);
	}body{
		MatchContext tcontext;
		foreach(i,ref x; iftis){
			scope(success) if(!tmatches[i].tdecl) tmatches[i].tmatch=Match.none;
			if(!x) continue;
			assert(!!cast(TemplateInstanceDecl)x);
			auto inst = cast(TemplateInstanceDecl)cast(void*)x;
			assert(inst.finishedInstantiation());
			auto fd = inst.iftiDecl();
			if(!fd){
				if(eponymous.length<=i || !eponymous[i]) continue;
				assert(eponymous[i].sstate == SemState.completed && cast(Symbol)eponymous[i],text(eponymous));
				auto sym = (cast(Symbol)cast(void*)eponymous[i]);
				fd = sym.meaning.isFunctionDecl();
			}else{
				if(fd.type.sstate==SemState.error)
					return Dependee(fd.type,null).dependent!void;
				mixin(MatchCall!q{auto tmp; fd, null, loc, this_, func, args, tcontext});
				assert(!tmp||cast(FunctionDecl)tmp);
				fd = cast(FunctionDecl)cast(void*)tmp;
			}
			if(!fd) continue;

			assert(fd.type.sstate == SemState.completed
			       || (!fd.type.ret || fd.type.ret.sstate == SemState.error)
			       && !fd.type.errorsInParams(),
			       text(fd.type.sstate));

			tmatches[i].decl = fd;
			tmatches[i].tdecl = fd.extractTemplateInstance();
			tmatches[i].context = tcontext;
		}
		mixin(EliminateLessSpecializedTemplateMatches!q{_;OverloadSet,tmatches});
		return indepvoid;
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

	GaggingScope gscope;
	Dependent!void convertLiterals(Scope sc,Expression[] args, FunctionDecl decl){
		if(positions.length&&!gscope) gscope=New!GaggingScope(sc);
		foreach(i;positions){
			if(args[i].sstate == SemState.error) continue;
			if(auto ae=args[i].isAddressExp()){
				if(ae.isUndeducedFunctionLiteral()){
					if(decl.type.params[i].type){
						args[i]=args[i].implicitlyConvertTo(decl.type.params[i].type);
						args[i].semantic(gscope);
						if(args[i].needRetry)
							return Dependee(args[i], gscope).dependent!void;
						mixin(FinishDeduction!q{args[i]});
					}
				}
			}
		}
		return indepvoid;
	}
}




mixin template Semantic(T) if(is(T==FunctionDecl)){

	final bool isConstructor(){
		return name && name.name == "this";
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
		type.stc|=mask&stc&~(STCauto);
	}

	void analyzeType(){
		propagateSTC();
		if(isConstructor()) type.ret=Type.get!void();
		type.semantic(scope_);
	}

	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(sstate == SemState.pre) presemantic(sc);
		analyzeType();
		if(!type.ret&&type.hasAutoReturn()){
			sc.error("function body required for return type inference",loc);
			mixin(ErrEplg);
		}
		mixin(SemProp!q{type});
		mixin(SemEplg);
	}
	override bool needsAccessCheck(AccessCheck check){
		return super.needsAccessCheck(check);
	}

	// TODO: would like Dependent!FunctionDecl for return type
	override Dependent!Declaration matchCall(Scope sc, const ref Location loc, Type this_, Expression func, Expression[] args, ref MatchContext context){
		enum SemRet = q{ return this.independent!Declaration; };
		// semantically analyze the type if necessary
		type.semantic(scope_); // TODO: get rid of direct call
		//mixin(SemProp!q{type});
		if(auto nr=type.needRetry) { needRetry = nr; mixin(SemRet); }
		mixin(PropErr!q{type});
		if(!isMember()&&!isConstructor()) this_ = null;
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

		mixin(MatchCall!q{auto rr; rhs, null, loc, this_, null, pt, dummy});
		assert(!rr||cast(FunctionDecl)rr);
		auto r=cast(FunctionDecl)cast(void*)rr;
		assert(!r||r.type.sstate == SemState.completed);
		// prefer function definitions to their own forward declarations
		if(r && !isFunctionDef() && rhs.isFunctionDef() && type.equals(rhs.type)
		   && stc == rhs.stc && scope_ is rhs.scope_) // TODO: consider linkage
			return false.independent;
		return (!!r).independent;
	}

	override void matchError(Scope sc, Location loc, Type this_, Expression[] args){
		alias util.any any; // TODO: file bug
		if(args.length > type.params.length
		|| any!(_=>_.init_ is null)(type.params[args.length..type.params.length])){
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
				incompatibleThisError(sc, loc, this_.getHeadSTC(), type.stc&STCtypeconstructor,this);
			}
			foreach(i,p; type.params){
				void displayNote(){
					if(p.name) sc.note(format("while matching function parameter '%s'",p.name),p.loc);
					else sc.note("while matching function parameter",p.loc);
				}
				if(!(p.stc & STCbyref)){
					if(p.stc&STClazy && at[i].getHeadUnqual() is Type.get!void())
						continue;
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

	static void incompatibleThisError(Scope sc, Location loc, STC hstc, STC fstc, FunctionDecl fd){
		// TODO: this allocates
		if(fd.isConstructor()){
			string stcstr(STC stc){
				return stc?"'"~STCtoString(stc)~"'-qualified":"unqualified";
			}
			string n(string stcstr){
				return stcstr[1].among('a','e','i','o','u')?"n":"";
			}
			auto hstcstr=stcstr(hstc), fstcstr=stcstr(fstc);
			auto n1=n(hstcstr), n2=n(fstcstr);

			sc.error(format("cannot construct a%s %s object using a%s %s constructor",n1,hstcstr,n2,fstcstr), loc);
		}else{
			auto hstcstr=hstc?"'"~STCtoString(hstc)~"'":"mutable";
			auto fstcstr=fstc?"'"~STCtoString(fstc)~"'":"mutable";

			sc.error(format("receiver for %s '%s' is %s, but %s is required", fd.kind, fd.name, hstcstr, fstcstr), loc);
		}
	}



	final TemplateDecl templatizeLiteral(Scope sc, const ref Location loc)in{
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

		auto ident = New!Identifier(name.name);
		ident.loc = loc;
		auto uexp = New!(UnaryExp!(Tok!"&"))(ident);
		uexp.loc = loc;
		uexp.brackets++;

		auto alias_ = New!AliasDecl(STC.init, New!VarDecl(STC.init,uexp,New!Identifier(tmplname),Expression.init));

		static class FunclitTemplateDecl: TemplateDecl{
			this(STC stc, Identifier name, TemplateParameter[] prm, BlockDecl b, Scope sc){
				super(false,stc,name,prm,Expression.init,b);
				sstate=SemState.begin;
				scope_=sc;
			}
			// OO FTW!
			override FunctionDecl iftiDecl(){
				assert(!!cast(FunctionDecl)bdy.decls[0]);
				return cast(FunctionDecl)cast(void*)bdy.decls[0];
			}
		}

		auto t=New!FunclitTemplateDecl(stc&STCstatic, New!Identifier(tmplname), tparams,
		                           New!BlockDecl(STC.init,[cast(Declaration)this,alias_]),sc);

		t.loc = loc;
		return t;
	}
}

mixin template Semantic(T) if(is(T==FunctionDef)){
	FunctionScope fsc;

	protected FunctionScope buildFunctionScope(){
		return New!FunctionScope(scope_, this);
	}

	override void analyzeType(){
		assert(!!scope_);
		propagateSTC();
		if(isConstructor()) type.ret=Type.get!void();
		if(!fsc){
			if(auto ti=scope_.getTemplateInstance())
				if(!ti.isMixin) inferAttributes=true;
			fsc = buildFunctionScope();
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
			if(sstate == SemState.error){
				needRetry=false;
				scope_=sc;
			}
		}
		analyzeType();
		if(auto nr=type.needRetry) { needRetry = nr; return; }
		mixin(PropErr!q{type});

		if(type.sstate == SemState.error) sstate = SemState.error, needRetry=false;

		mixin(SemChldPar!q{sc=fsc; bdy});

		if(type.hasUnresolvedReturn()){
			type.resolveReturn(Type.get!void());
		}
		needRetry=false;
		resolveForwardReferencedLabels();
		mixin(SemCheck);
		mixin(PropErr!q{type, bdy});
		auto infer=possibleSTCs&inferredSTCs;
		if(infer&STCstatic) infer&=~STCimmutable;
		stc |= infer;
		propagateSTC();
		mixin(SemEplg);
	}

	private void resolveForwardReferencedLabels(){
		foreach(gto;&fsc.unresolvedLabels){
			assert(cast(Identifier)gto.e);
			if(auto lbl = fsc.lookupLabelHere(cast(Identifier)cast(void*)gto.e))
				gto.resolveLabel(lbl);
			else undeclaredLabel(gto);
		}
	}

	protected void undeclaredLabel(GotoStm gto){
		fsc.error(format("use of undeclared label '%s'",gto.e.toString()), gto.e.loc);
		sstate = SemState.error;
	}


	mixin HandleNestedDeclarations;

	/* specifies whether or not to infer the 'static' qualifier
	 */

	bool inferStatic;
	bool inferAttributes;
	@property STC inferredSTCs(){
		auto infer=(inferStatic?STCstatic:STC.init)|(inferAttributes?STCinferrable:STC.init);
		if(isMember()||isConstructor()) infer&=~STCimmutable;
		return infer;
	}

	bool finishedInference(){
		return sstate==SemState.completed||!inferredSTCs();
	}

	void cancelInference(){
		inferStatic=false;
		inferAttributes=false;
	}

	private STC possibleSTCs; // DMD does not allow initialization here. TODO: fix this
	@property bool canBeStatic(){
		return !!(possibleSTCs&STCstatic);
	}
	@property void canBeStatic(bool b)in{assert(!b||canBeStatic);}body{
		if(!b) impossibleSTCs(STCstatic);
	}

	final void addContextPointer() in{
		assert(sstate == SemState.completed);
		assert(inferredSTCs()&STCstatic);
		assert(stc&STCstatic);
	}body{
		assert(canBeStatic);
		stc&=~STCstatic;
	}

	void rescope(Scope sc){
		if(scope_ !is sc){
			scope_=sc; // eg. matching overloads
			if(fsc) fsc.parent=scope_;
		}
	}

	void notifyIfNot(STC stc,FunctionDef other){
		if(other is this) return;
		other.possibleSTCs=other.possibleSTCs&(~stc|stc&possibleSTCs);
		if(finishedInference()) return;
		// assert(0, text("TODO ",this)); // TODO!
	}
	private void impossibleSTCs(STC stc){
		possibleSTCs&=~stc;
	}

}

mixin template Semantic(T) if(is(T==UnittestDecl)){
	static bool enabled = false;
	Scope utsc;

	override void presemantic(Scope sc){
		if(sstate!=SemState.pre) return;
		scope_=sc;
		sstate=SemState.begin;
	}
	override void semantic(Scope sc){
		if(enabled)	super.semantic(sc);
		else mixin(SemEplg);
	}
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
						if(x.type.getHeadUnqual().isSomeString())
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
	Expression aLeftover=null;
	static if(is(T==MixinExp)) alias Expression R; // workaround
	else static if(is(T==MixinStm)) alias Statement R;
	else static if(is(T==MixinDecl)) alias Declaration R;
	static if(is(T==MixinDecl)){
		override void potentialInsert(Scope sc, Declaration dependee){
			sc.potentialInsertArbitrary(dependee,this);
		}
		override void potentialRemove(Scope sc, Declaration dependee){
			sc.potentialRemoveArbitrary(dependee,this);
		}

		override void presemantic(Scope sc){
			if(sstate != SemState.pre) return;
			scope_ = sc;
			sstate = SemState.begin;
			potentialInsert(sc, this);
		}
		Declaration mixedin;
	}else static if(is(T==MixinExp)){
		AccessCheck accessCheck = accessCheck.all;
		mixin ContextSensitive;
	}
	private R evaluate(Scope sc){
		mixin(SemPrlg);
		foreach(x;a) x.prepareInterpret();
		mixin(SemChld!q{a});

		if(a.length<1){
			sc.error("missing argument for string mixin", loc);
			mixin(ErrEplg);
		}else if(a.length>1){
			sc.error("too many arguments for string mixin", loc);
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
			sc.error("expected string argument for string mixin", a[0].loc);
			mixin(ErrEplg);
		}
		foreach(i,t; types) if(i+1==which)
			mixin(ImplConvertTo!q{a[0],t});
		assert(a[0].sstate == SemState.completed);

		a[0].interpret(sc);
		if(aLeftover) aLeftover.interpret(sc);
		mixin(SemProp!q{a[0]});
		if(aLeftover) mixin(SemProp!q{aLeftover});

		auto str = a[0].interpretV().convertTo(Type.get!string()).get!string();
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
			transferContext(r);
		}else static if(is(T==MixinStm)) auto r=New!CompoundStm(parseStatements(src,sc.handler)); // TODO: use CompoundStm instead
		else static if(is(T==MixinDecl)) auto r=New!BlockDecl(STC.init,parseDeclDefs(src,sc.handler));
		else static assert(0);

		if(sc.handler.nerrors != nerrors) mixin(ErrEplg);

		else static if(is(T==MixinDecl)) r.pickupSTC(stc);
		r.semantic(sc);
		// ohan.note("mixed in here", loc);
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
		static if(is(T==MixinDecl)){
			scope(success) if(rewrite||sstate==SemState.error) potentialRemove(sc, this);
		}
		mixin(SemCheck);
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
