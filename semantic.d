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

enum SemRet = q{
	static if(is(typeof(return)==void)) return;
	else static if(is(typeof(this):typeof(return))) return this;
	else static if(is(typeof(return)==bool)) return true;
	else return null;
};

template MultiArgument(alias a,string s) if(s.canFind(",")){
	enum ss=s.split(",");
	enum MultiArgument={
		string r;
		foreach(t;ToTuple!ss) r~=a!(mixin(X!q{@(t)}));
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
	enum ConstFold=mixin(X!q{
		@(s).constFold(sc);
		mixin(Rewrite!q{@(s)});
	});
}


template PropErr(string s) if(!s.canFind(",")){
	enum PropErr=s.length?mixin(X!q{
		static if(is(typeof(@(s)): Node)){
			if(@(s).sstate==SemState.error){
				//import std.stdio; writeln("propagated error from ",@(s)," to ",this);
				@(ErrEplg)
			}
		}else{
			foreach(x;@(s)){
				if(x.sstate==SemState.error){
					//import std.stdio; writeln("propagated error from ",x," to ",this);
					@(ErrEplg)
				}
			}
		}
	}):mixin(X!q{if(sstate==SemState.error){@(NoRetry)@(SemRet)}});
}
template PropErr(string s) if(s.canFind(",")){ alias MultiArgument!(.PropErr,s) PropErr; }

template PropRetryNoRew(string s) if(!s.canFind(",")){
	enum PropRetryNoRew=mixin(X!q{
		static assert(!is(typeof(_nR)));
		if(auto _nR=@(s).needRetry){
			needRetry = _nR;
			if(_nR==2) @(s).needRetry=false;
			//dw("propagated retry ",_nR," from ",@(s)," to ",toString()," @",__LINE__);
			Scheduler().addDependency(this, @(s));
			@(SemRet)
		}
	});
}

template PropRetry(string s) if(!s.canFind(",")){
	enum PropRetry=Rewrite!s~PropRetryNoRew!s;
}

template PropRetry(string s) if(s.canFind(",")){ alias MultiArgument!(.PropRetry,s) PropRetry; }

template SemProp(string s){ enum SemProp = PropRetry!s~PropErr!s; }

enum CheckRewrite=mixin(X!q{ if(rewrite) @(SemRet); });

enum SemCheck=CheckRewrite~mixin(X!q{ if(needRetry||sstate==SemState.error){@(SemRet)} });

private template _SemChldImpl(string s, string op){ // TODO: get rid of duplication
	template Doit(string v){
		enum Doit=mixin(X!((op[0..3]!="exp"?q{
						if(@(v).sstate != SemState.completed)
							}:"")~q{@(v).@(op);@(Rewrite!v);}));
	}
	enum ss=s.split(",");
	enum _SemChldImpl={
		string r;
		foreach(t;ToTuple!ss){
			r~=mixin(X!q{
				static if(is(typeof(@(t)): Node)){
					@(Doit!t)
					if(@(t).sstate != SemState.completed) mixin(PropRetryNoRew!q{@(t)});
					else{
						static if(is(typeof(@(t)): Expression) && !is(typeof(@(t)):Type)
						          &&(!is(typeof(this):Expression)||is(typeof(this):Type)))
							mixin(ConstFold!q{@(t)});
					}
				}else{
					foreach(ref x;@(t)){
						@(Doit!q{x})
						if(x.sstate != SemState.completed) mixin(PropRetryNoRew!q{x});
						else{
							static if(is(typeof(x): Expression) && !is(typeof(x):Type)
							          &&(!is(typeof(this):Expression)||is(typeof(this):Type)))
								if(x.sstate == SemState.completed) mixin(ConstFold!q{x});
						}
					}
					static if(is(typeof(@(t)): Expression[])){
						pragma(msg, typeof(this)," @(t)");
						@(t)=Tuple.expand(@(t));
						mixin(PropErr!q{@(t)});
					}
				}
			});
		}
		return r;
	}();
}

template SemChld(string s){ // perform semantic analysis on child node, propagate all errors
	enum SemChld=_SemChldImpl!(s,q{semantic(sc)})~PropErr!s;
}

template SemChldPar(string s){
	enum SemChldPar=_SemChldImpl!(s,q{semantic(sc)});
}

template SemChldExp(string s){ // perform semantic analysis on child node, require that it is an expression
	enum SemChldExp=_SemChldImpl!(s,q{expSemantic(sc)})~PropErr!s;
}

template SemChldExpPar(string s){
	enum SemChldExpPar=_SemChldImpl!(s,q{expSemantic(sc)});
}

template ConvertTo(string s) if(s.split(",").length==2){
	enum ss = s.split(",");
	enum ConvertTo=mixin(X!q{
		assert(!@(ss[0]).rewrite && @(ss[0]).sstate == SemState.completed);
		@(ss[0])=@(ss[0]).convertTo(@(ss[1]));
		mixin(SemChldExp!q{@(ss[0])});
		assert(!@(ss[0]).rewrite);
	});
}

template ImplConvertTo(string s) if(s.split(",").length==2){
	enum ss = s.split(",");
	enum ImplConvertTo=mixin(X!q{
		assert(!@(ss[0]).rewrite && @(ss[0]).sstate == SemState.completed,@(ss[0]).toString()~" "~to!string(@(ss[0]).rewrite)~" "~to!string(@(ss[0]).sstate));
		@(ss[0])=@(ss[0]).implicitlyConvertTo(@(ss[1]));
		mixin(SemChldExp!q{@(ss[0])});
		assert(!@(ss[0]).rewrite);
	});
}

template ImplConvertToPar(string s) if(s.split(",").length==2){
	enum ss = s.split(",");
	enum ImplConvertToPar=mixin(X!q{
		assert(!@(ss[0]).rewrite && @(ss[0]).sstate == SemState.completed);
		@(ss[0])=@(ss[0]).implicitlyConvertTo(@(ss[1]));
		mixin(SemChldExpPar!q{@(ss[0])});
		assert(!@(ss[0]).rewrite);
	});
}


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
			if(ident.recursiveLookup && typeid(ident) !is typeid(LookupIdentifier)){
				if(!ident.meaning){
					ident.lookup(sc);
					mixin(PropRetry!q{@(e)});
				}
				if(ident.sstate == SemState.failed) mixin(SemChld!q{@(e)});

				if(ident.sstate != SemState.error && ident.meaning){
					@(e) = ident.reverseEponymousLookup(sc);
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
	if(sstate == SemState.error||sstate == SemState.completed||rewrite){_Lreturn: @(SemRet)}
});

// removed because they crash the program when compiled with DMD sometimes
/+	debug scope(failure){
		static if(is(typeof(sc))) sc.note("here!",loc);
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
	Scheduler().removeNode(this);	
};

enum SemEplg=q{
	mixin(NoRetry);
	sstate = SemState.completed;
}~SemRet;

template RewEplg(string s) if(!s.canFind(",")){
	enum RewEplg=mixin(X!q{
		assert(!rewrite," rewrite mustn't be set already");
		rewrite = @(s);
		static assert(is(typeof(return)==void)||is(typeof(return)==bool));
		@(SemRet)
	});
}

enum ErrEplg=q{
	mixin(NoRetry);
	//dw(this," ",__LINE__);
	sstate=SemState.error;
}~SemRet;

template SetErr(string s) if(!s.canFind(",")){
	enum t=s.length?s~".":"";
	enum SetErr=mixin(X!q{
		@(t)needRetry=false; // TODO: macrolize?
		Scheduler().removeNode(@(s.length?s:"this"));
		@(t)sstate=SemState.error;
	});
}

enum RetryEplg=q{
	/+if(!needRetry)+/
	assert(sstate != SemState.error,"1");
	Identifier.tryAgain = true;
	needRetry = true;
}~SemRet;

enum RetryBreakEplg=q{
	assert(sstate != SemState.error,"2");
	needRetry = true;
}~SemRet;

template Semantic(T) if(is(T==Node)){
	// TODO: needRetry and sstate could be final properties to save one byte of space
	// profile to see if it is worth it.
	Node rewrite;
	SemState sstate = SemState.begin;
	ubyte needRetry = false; // needRetry == 2: unwind stack for circular dep handling

	invariant(){
		assert(sstate!=SemState.error||needRetry!=1, "needRetry and error "~to!string(typeid(this))~(cast(Identifier)this?" "~(cast(Identifier)this).name:"")~" Identifier.tryAgain: "~to!string(Identifier.tryAgain)~" needRetry: "~to!string(needRetry));}

	void semantic(Scope s)in{assert(sstate>=SemState.begin);}body{
		s.error("unimplemented feature",loc);
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
		assert(sstate != SemState.completed || type && type.sstate == SemState.completed);
	}
	override void semantic(Scope sc){ sc.error("unimplemented feature "~to!string(typeid(this)),loc); mixin(ErrEplg); }


	Type typeSemantic(Scope sc){
		Expression me=this;
		if(sstate != SemState.completed){ // TODO: is this ok?
			me.semantic(sc);
			mixin(Rewrite!q{me});
			if(auto ty=me.isType()) return ty;
			if(me is this) mixin(SemCheck);
			else mixin(SemProp!q{me});
		}
		sc.error(format("%s '%s' is used as a type",me.kind,me.toString()),loc);
		mixin(ErrEplg);
	}

	final void expSemantic(Scope sc){
		semantic(sc);
		auto f = this;
		mixin(Rewrite!q{f});
		if(f.sstate == SemState.completed && f.isType()){
			//sc.error(format("%s '%s' is not an expression", f.kind, loc.rep), loc);
			sc.error(format("%s '%s' is not an expression", f.kind, f.toString()), loc);
			rewrite = null;
			mixin(ErrEplg);
		}
	}

	final void weakenAccessCheck(AccessCheck check){
		//TODO: why is WeakenCheck 'a nested function and not accessible' if it is not static?
		static struct WeakenCheck{
			immutable AccessCheck check;
			void perform(Symbol self){
				self.accessCheck = min(self.accessCheck, check);
			}
			// if a function literal is directly called,
			// we can decrease its access check level as
			// well
			void perform(CallExp self){
				if(auto fl=self.e.isFunctionLiteralExp())
					runAnalysis!WeakenCheck(fl.bdy, check);
			}
		}
		
		runAnalysis!WeakenCheck(this,check);
	}

	bool isConstant(){ return false; }

	Expression clone(Scope sc, const ref Location loc)in{
		assert(sstate == SemState.completed);
	}body{
		Expression r;
		if(isConstant) r=cloneConstant();
		else r=ddup(); // TODO: symbols?
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
		if(!isConstant() || fdontConstFold) return;
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

	bool implicitlyConvertsTo(Type rhs)in{assert(sstate == SemState.completed);}body{
		if(type.implicitlyConvertsTo(rhs)) return true;
		auto l = type.getHeadUnqual().isIntegral(), r = rhs.getHeadUnqual().isIntegral();
		if(l && r){
			// note: r.getLongRange is always valid for basic types
			if(l.op == Tok!"long" || l.op == Tok!"ulong"){
				auto rng = getLongRange();
				return r.getLongRange().contains(rng)
					|| r.flipSigned().getLongRange().contains(rng);
			}else{
				auto rng = getIntRange();
				return r.getIntRange().contains(rng)
					|| r.flipSigned().getIntRange().contains(rng);
			}
		}
		return false;
	}
	Expression implicitlyConvertTo(Type to)in{
		assert(to.sstate == SemState.completed);
	}body{
		if(type is to) return this;
		auto r = New!ImplicitCastExp(to,this);
		r.loc = loc;
		return r;
	}
	bool typeEquals(Type rhs)in{assert(sstate == SemState.completed);}body{
		return type.equals(rhs);
	}

	// careful: this has to be kept in sync with Type.mostGeneral
	final Type typeMostGeneral(Expression rhs)in{
		assert(sstate == SemState.completed && sstate == rhs.sstate);
	}body{
		Type r   = null;
		bool l2r = this.implicitlyConvertsTo(rhs.type);
		bool r2l = rhs.implicitlyConvertsTo(this.type);

		if(l2r ^ r2l){
			r = r2l ? type : rhs.type;
			STC stc = this.type.getHeadSTC() & rhs.type.getHeadSTC();
			r.getHeadUnqual().applySTC(stc);
		}
		return r;
	}
	final Type typeCombine(Expression rhs)in{
		assert(sstate == SemState.completed && sstate == rhs.sstate);
	}body{
		if(auto r = typeMostGeneral(rhs)) return r;
		return type.combine(rhs.type);
	}


	bool convertsTo(Type rhs)in{assert(sstate == SemState.completed);}body{
		if(implicitlyConvertsTo(rhs)) return true;
		if(type.convertsTo(rhs.getUnqual().getConst())) return true;
		return false;
	}

	final Expression convertTo(Type to)in{assert(type&&to);}body{
		if(type is to) return this;
		if(implicitlyConvertsTo(to)) return implicitlyConvertTo(to);
		auto r = New!CastExp(STC.init,to,this);
		r.loc = loc;
		return r;
	}

	Expression matchCall(scope Expression[] args, ref MatchContext context)in{
		assert(sstate == SemState.completed);
	}body{
		auto r=type.matchCall(args, context) ? this : null;
		return r;
	}
	void matchError(Scope sc, Location loc, Expression[] args){
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
	bool templateParameterEquals(Expression rhs){
		assert(sstate == SemState.completed,"not completed sstate "~toString());
		if(auto exp = rhs){
			if(!type.equals(exp.type)) return false;
			if(isConstant() && exp.isConstant())
				return interpretV()==exp.interpretV();
		}
		return false;
	}
}
//pragma(msg, __traits(classInstanceSize,Expression)); // 0u. TODO: reduce and report

mixin template Semantic(T) if(is(T==LiteralExp)){

	static Expression factory(Variant value, Type type){
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

	final bool isPolyString(){return lit.type == Tok!"``";}

	override bool typeEquals(Type rhs){
		if(super.typeEquals(rhs)) return true;
		if(!isPolyString()) return false;
		return rhs is Type.get!wstring()||rhs is Type.get!dstring();
	}

	override bool implicitlyConvertsTo(Type rhs){
		if(super.implicitlyConvertsTo(rhs)) return true;
		if(type.getHeadUnqual().isSomeString())
			if(auto ptr = rhs.isPointerTy()){
				return implicitlyConvertsTo(ptr.ty.getDynArr());
			}
		if(!isPolyString()) return false;
		return Type.get!wstring().implicitlyConvertsTo(rhs)
			|| Type.get!dstring().implicitlyConvertsTo(rhs);
	}


	override IntRange getIntRange(){
		if(auto bt = type.isIntegral()){
			auto v = value.get!ulong();
			bool s = bt.isSigned() || bt.bitSize()<32;
			return IntRange(cast(int)v,cast(int)v,s);
		}
		return super.getIntRange();
	}
	override LongRange getLongRange(){
		if(auto bt = type.isIntegral()){
			auto v = value.get!ulong();
			bool s = bt.isSigned() || bt.bitSize()<64;
			return LongRange(v,v,s);
		}
		return super.getLongRange();
	}
}

mixin template Semantic(T) if(is(T==ArrayLiteralExp)){
	override void semantic(Scope sc){
		if(!lit.length){type=Type.get!EmptyArray(); mixin(SemEplg);}
		mixin(SemChld!q{lit});
		auto ty=lit[0].type;
		foreach(i,x;lit[1..$]){
			if(!x.implicitlyConvertsTo(ty)){
				bool ok = true;
				if(!ty.implicitlyConvertsTo(x.type))
					foreach(y;lit[0..i+1]) if(!y.implicitlyConvertsTo(x.type)) goto Lnot;
				ty = x.type;
				continue;
			Lnot:
				if(auto newty=ty.combine(x.type)) ty=newty;
				else{
					sc.error(format("incompatible type '%s' in array of '%s'",x.type,ty),x.loc);
					mixin(ErrEplg);
				}
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

	override bool implicitlyConvertsTo(Type rhs){
		if(super.implicitlyConvertsTo(rhs)) return true;
		if(rhs.getHeadUnqual() is Type.get!(void[])()) return true;
		Type et = rhs.getElementType();
		if(auto arr = rhs.getHeadUnqual().isArrayTy())
			if(arr.length != lit.length) return false;
		if(!et) return false;
		foreach(x; lit) if(!x.implicitlyConvertsTo(et)) return false;
		return true;
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
		mixin(SemPrlg);
		//mixin(SemChldPar!q{e});
		if(e.sstate != SemState.completed){
			e.semantic(sc_); // TODO: get rid of direct call
			mixin(PropRetry!q{e});
		}

		if(!ascope) ascope = New!DollarScope(sc_, this);
		alias ascope sc;

		if(e.isType()){
			auto r=typeSemantic(sc); // TODO: ok?
			mixin(SemCheck);
			assert(!!r);
			mixin(RewEplg!q{r});
		}else if(auto et=e.isExprTuple()){
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
			if(!isConstant()){
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

	override Type typeSemantic(Scope sc_){
		//mixin(SemChld!q{e});
		e.semantic(sc_); // TODO: get rid of direct call
		mixin(SemProp!q{e});

		auto tp = e.isTuple();

		Type ty;
		if(!tp || !a.length){
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
			else sc.error("can only specify one dimension for static array",a[0].loc.to(a[$-1].loc));
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
		mixin(SemPrlg);
		//mixin(SemChldPar!q{e});
		if(e.sstate != SemState.completed){
			e.semantic(sc_); // TODO: get rid of direct call
			mixin(PropRetry!q{e});
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
			if(!rng[0].overlaps(LongRange(0,length-1,false))
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
			if(!isConstant()){
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
		if(a.length<1){
			sc.error("missing arguments to assert", loc);
			mixin(ErrEplg);
		}else if(a.length>2){
			sc.error("too many arguments to assert", loc);
			mixin(ErrEplg);
		}
		mixin(SemChld!q{a});
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
				if(auto s=e.isSymbol()){
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
								//mixin(SemChld!q{fdef});
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
				sc.error(format("cannot take address of expression '%s'",e.loc.rep),loc);
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
	static if(S==Tok!"+"||S==Tok!"-"||S==Tok!"~"||S==Tok!"!")
	override bool isConstant(){
		if(auto sym=e.isSymbol()){assert(sym.meaning); return !!(sym.meaning.stc&STCstatic);}
		return e.isConstant();
	}
	static if(S==Tok!"&"){

	override bool implicitlyConvertsTo(Type rhs){
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
			}else
				if(auto ptr = rhsu.isPointerTy()   ){
				if(auto ft  = ptr.ty.isFunctionTy()){
					return fd.type.getPointer()
						.implicitlyConvertsTo(rhsu);
				}
			}
		}}
		return super.implicitlyConvertsTo(rhs);
	}

	override Expression matchCall(scope Expression[] args, ref MatchContext context){
		return e.matchCall(args, context);
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
						if(auto ty = e.type.isIntegral()){
							static if(is(R==IntRange)){
								r = r.narrow(ty.isSigned(),ty.bitSize());
							}else{
								auto nr = r.narrow(ty.isSigned(),ty.bitSize());
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

class TemplateInstanceDecl: Declaration{
	Expression[] args;
	Expression constraint;
	BlockDecl bdy;
	TemplateScope paramScope;

	/* some arguments might have been deduced while matching, so this
	   instance just refers to the instance that has complete arguments
	*/
	TemplateInstanceDecl completeInstance;

	this(STC stc, Identifier name, Expression[] args, Expression constraint, BlockDecl bdy){
		super(stc, name);
		this.args=args;
		this.constraint = constraint;
		this.bdy=bdy; // NOTE: bdy is the original template body at this point!

		// See if the eponymous declaration can be determined without analyzing
		// the template body. This is required for IFTI and template constraints.
		foreach(x; bdy.decls) if(x.name && x.name.name == name.name) eponymousDecl = x;
	}

	override void buildInterface(){
		mixin(SemPrlg);
		bdy.buildInterface();
		mixin(SemProp!q{bdy});
	}

	override void semantic(Scope sc){
		assert(!completeInstance);
		mixin(SemPrlg);
		assert(sstate == SemState.begin);
		sstate = SemState.started;
		scope(exit) if(sstate == SemState.started) sstate = SemState.begin;
		if(constraint){
			assert(constraint.type is Type.get!bool());
			assert(constraint.isConstant() && constraint.interpretV());
		}
		//mixin(SemChld!q{bdy});
		bdy.semantic(bdy.scope_);
		mixin(SemProp!q{bdy});
		mixin(SemEplg);
	}

	private{
		Declaration eponymousDecl;
		Parameter[] constraintEponymousFunctionParameters;
		Scope constraintScope;
	}

	// TODO: this bypasses the framework
	void analyzeConstraint(){
		if(constraint.sstate == SemState.error ||
		   constraint.sstate == SemState.completed && constraint.isConstant())
			return;

		if(!constraintScope){
			constraintScope = paramScope.cloneNested(paramScope.iparent);
			if(eponymousDecl) if(auto fd = eponymousDecl.isFunctionDecl()){
				// TODO: gc allocation
				constraintEponymousFunctionParameters = fd.type.params.dup;
				foreach(ref x; constraintEponymousFunctionParameters)
					x=x.ddup;
			}
		}

		foreach(x; constraintEponymousFunctionParameters){
			x.semantic(constraintScope);
			mixin(Rewrite!q{x});
			mixin(PropRetry!q{x});
			if(x.sstate == SemState.error)
				mixin(SetErr!q{constraint});
		}
		mixin(PropErr!q{constraint});

		constraint.prepareInterpret();
		constraint.semantic(constraintScope);
		mixin(SemProp!q{constraint});
		constraint=constraint.convertTo(Type.get!bool());
		constraint.semantic(constraintScope);
		mixin(SemProp!q{constraint});
		constraint.interpret(constraintScope);
		mixin(SemProp!q{constraint});
		needRetry=false;
	}


	/* template instances serve as containers for other declarations
	   they do not need to be checked for accessibility
	 */
	override bool needsAccessCheck(AccessCheck check){ return false; }

	override string kind(){return "template instance";}
	override string toString(){ return name.toString()~"!("~join(map!(to!string)(args),",")~")"; }

	mixin DownCastMethod;
	mixin Visitors;
}

interface Tuple{
	Expression index(Scope sc, const ref Location loc, ulong index)
		in{assert(index<length);}
	Expression slice(Scope sc, const ref Location loc, ulong a, ulong b)
		in{assert(a<=b && b<length);}

	@property ulong length();

	int opApply(int delegate(Expression) dg);


	static Expression[] expand(Expression[] a){
		// TODO: this is very naive and inefficient
		Expression[] r;
		typeof(r.length) index = 0;
		foreach(i,x;a){
			if(auto tp=x.isTuple()){
				foreach(y; tp) y.loc=x.loc;
				if(auto et=x.isExprTuple()){
					et.accessCheckSymbols();
					r~=a[index..i]~et.exprs;
				}else if(auto tt=x.isTypeTuple())
					r~=a[index..i]~cast(Expression[])tt.types;
				index=i+1;
			}
		}
		return index?r~a[index..$]:a;
	}

	static VarDecl[] expand(Scope sc, VarDecl[] a) in{
		alias util.all all;
		assert(all!(_=>!_.rtype&&!_.init||_.sstate == SemState.completed)(a));
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
	static Parameter[] expand(Scope sc,Parameter[] a){
		return cast(Parameter[])expand(sc,cast(VarDecl[])a);
	}

}

class ExprTuple: Expression, Tuple{
	/* indexing an expression tuple might create a symbol reference
	   therefore we need to remember the access check level.
	 */
	AccessCheck accessCheck = AccessCheck.all;

	this(Scope sc, scope Expression[] exprs)in{
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


	Tuple isTuple(){return this;}

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
		return New!ExprTuple(sc,exprs[cast(size_t)a..cast(size_t)b]);
	}
	@property ulong length(){ return exprs.length;}

	int opApply(int delegate(Expression) dg){
		foreach(x; exprs) if(auto r = dg(x)) return r;
		return 0;
	}

	override void semantic(Scope sc){
		mixin(SemPrlg);
		alias util.all all;
		if(all!(_=>cast(bool)_.isType())(exprs)){
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

	override ExprTuple clone(Scope sc, const ref Location loc){
		auto r = ddup();
		foreach(ref x; r.exprs) x = x.clone(sc,loc);
		r.loc = loc;
		return r;
	}


	override string toString(){return "("~join(map!(to!string)(exprs),",")~")";}
	override @property string kind(){return "tuple";}

	override bool isConstant(){
		alias util.all all;
		return all!(_=>_.isConstant())(exprs);
	}

	mixin DownCastMethod;
	mixin Visitors;

private:
	Expression[] exprs;
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

	Tuple isTuple(){return this;}
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

	int opApply(int delegate(Expression) dg){
		foreach(x; types) if(auto r = dg(x)) return r;
		return 0;
	}

	override string toString(){return "("~join(map!(to!string)(types),",")~")";}
	override @property string kind(){return "type tuple";}

	override bool equals(Type rhs){
		if(auto tt = rhs.isTypeTuple()) return types == tt.types;
		return false;
	}

	mixin DownCastMethod;
	mixin Visitors;

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

				mixin(ImplConvertTo!q{rspec, type});
				mixin(IntChld!q{rspec});
			}
			assert(!spec);
		}else if(rspec){
			spec = rspec.typeSemantic(sc);
			mixin(SemProp!q{rspec});
		}
		mixin(SemEplg);
	}

	invariant(){assert(sstate != SemState.completed || !rtype || !!type);}
}

mixin template Semantic(T) if(is(T==TemplateDecl)){
	override void semantic(Scope sc){
		if(sstate == SemState.pre) presemantic(sc);
		mixin(SemPrlg);
		bdy.pickupSTC(stc);
		foreach(x; params) x.sstate = max(x.sstate,SemState.begin);
		mixin(SemChld!q{params});
		sc.getModule().addTemplateDecl(this);
		mixin(SemEplg);
	}

	/* templates are always accessible, it is the contents of their instantiations
	   that might not be.
	 */
	override bool needsAccessCheck(AccessCheck check){ return false; }

	TemplateInstanceDecl getInstance(Expression[] args, bool justMatch=false)in{
		assert(sstate == SemState.completed);
		alias util.all all;
		assert(all!(_=>_.sstate == SemState.completed &&(_.isType()||_.isConstant()||_.isSymbol())||_.isAddressExp()&&_.isAddressExp().e.isSymbol())(args),{
				string r;
				foreach(x;args){
					r~=text(x," ",x.sstate == SemState.completed," ",!!x.isType(),!!x.isConstant(),!!x.isSymbol(),'\n');
				}
				return r;
			}());
	}body{
		if(auto r=lookup(args)){
			if(!justMatch && r.bdy is bdy) r = finish(r);
			return r;
		}

		auto r=New!TemplateInstanceDecl(stc,New!Identifier(name.name),args,
		                                constraint?constraint.ddup():null,bdy);
		
		Scope sc = scope_;

		auto tuplepos = params.length;
		foreach_reverse(i,x; params)
			if(x.which == WhichTemplateParameter.tuple) tuplepos = i;

		if(r.bdy.stc&STCstatic){ // TODO: fix!
			size_t maxn = 0;
			foreach(i,x;args){
				if(i>=tuplepos || params[i].which == WhichTemplateParameter.alias_){
					if(auto sym = x.isSymbol()){
						assert(!!sym.meaning && sym.meaning.scope_,sym.to!string);
						if(sym.meaning.stc & STCstatic
						||!sym.meaning.scope_.getDeclaration())
							continue;
						// TODO: consider the context scope instead
						auto n = sym.meaning.scope_.getNesting();
						if(n>=maxn){
							maxn=n;
							assert(n>maxn||sc==scope_||sc==sym.meaning.scope_);
							sc = sym.meaning.scope_;
						}
					}
				}
			}
		}
		r.scope_ = scope_;
		r.sstate = SemState.begin;
		Expression[16] _resolved; // should be long enough for everyone
		Expression[] resolved;
		if(params.length<=_resolved.length) resolved = _resolved[0..params.length];
		else resolved = new Expression[params.length]; // still make sure it is okay

		if(args.length<tuplepos||args.length>tuplepos&&tuplepos==params.length) return null;
		foreach(i,x; params[0..tuplepos]){
			final switch(x.which) with(WhichTemplateParameter){
				case alias_:
					resolved[i] = args[i];
					break;
				case constant:
					assert(!!x.type && x.type.sstate == SemState.completed);
					assert(!x.rspec || x.rspec.sstate == SemState.completed);

					if(!args[i].implicitlyConvertsTo(x.type)) return null;
					// TODO: implicit conversion is wasteful on GC
					if(x.rspec){
						auto conv=args[i].implicitlyConvertTo(x.type);
						// TODO: this assertion might be invalid for delegates
						conv.semantic(null);
						mixin(Rewrite!q{conv});
						assert(conv.sstate == SemState.completed,"TODO "~conv.to!string);
						if(args[i].interpretV()!=x.rspec.interpretV()) return null;
					}
					resolved[i] = args[i];
					break;
				case type, this_:
					if(!args[i].isType()||x.spec&&!args[i].implicitlyConvertsTo(x.spec))
						return null;
					resolved[i] = args[i];
					break;
				case tuple:
					assert(0);
			}
		}

		alias util.any any;
		if(tuplepos&&any!(_=>_ is null)(resolved[0..tuplepos-1]))
			return null; // TODO: cache this information


		if(tuplepos<params.length){
			// TODO: gc allocation
			Expression[] expr = args[tuplepos..$];
			Expression et = New!ExprTuple(sc,expr);
			et.semantic(scope_);
			mixin(Rewrite!q{et});
			assert(et.sstate == SemState.completed);
			resolved[tuplepos]=et;
		}

		r.paramScope = New!TemplateScope(scope_,sc,r);

		foreach(i,x;resolved){
			// TODO: don't leak references
			// TODO: pass delegate/function pointer arguments symbolically

			if(x.isSymbol()||x.isType()||x.isExprTuple()){
				auto al = New!AliasDecl(STC.init, New!VarDecl(STC.init, x, params[i].name, null));
				al.semantic(r.paramScope);
				debug{
					mixin(Rewrite!q{al});
					assert(al.sstate == SemState.completed);
				}
			}else{
				auto en = New!VarDecl(STCenum, null, params[i].name, x);
				en.semantic(r.paramScope);
				debug{
					mixin(Rewrite!q{en});
					assert(en.sstate == SemState.completed);
				}
			}
		}

		add(r);
		if(justMatch) return r;
		return finish(r);
	}

	private TemplateInstanceDecl finish(TemplateInstanceDecl r)in{
		assert(sstate == SemState.completed);
		assert(r.bdy is bdy);
	}body{
		auto bdyscope=New!NestedScope(r.paramScope);
		r.bdy = r.bdy.ddup();

		auto sc = r.paramScope.iparent;
		if(sc !is scope_) r.bdy.stc&=~STCstatic;

		r.bdy.presemantic(bdyscope);
		assert(r.bdy.scope_ is bdyscope);
		if(sc !is scope_){
			auto decl=sc.getDeclaration();
			assert(!!decl);
			decl.nestedTemplateInstantiation(r);
		}
		return r;
	}

	// TODO: IFTI

	override TemplateDecl matchInstantiation(Expression[] args){
		assert(!!scope_);
		if(sstate != SemState.completed){
			semantic(scope_);
			assert(!rewrite);
			mixin(SemCheck);
		}
		assert(sstate == SemState.completed);

		auto inst = getInstance(args, true);

		if(!inst){
			needRetry=false;
			return null;
		}
		if(inst.constraint){
			inst.analyzeConstraint();
			if(inst.needRetry){needRetry=true; return this;}
			if(inst.constraint.sstate==SemState.error||!inst.constraint.interpretV()){
				inst.constraint.sstate = SemState.error;
				needRetry=false;
				mixin(SetErr!q{inst});
				return null;
			}
		}
		needRetry=false;
		return this;
	}
	void instantiationError(Scope sc, Location loc, scope Expression[] args){
		// TODO: more explicit error message
		sc.error("instantiation does not match template declaration",loc);
	}

/+	void updateInstances(scope TemplateInstanceDecl delegate(/*scope*/TemplateInstanceDecl) dg){
		foreach(ref x; instances) if(x.bdy !is bdy) x = dg(x);
	}+/

	void instancesBuildInterface(){
		foreach(ref x; instances){
			if(x.bdy is bdy) continue;
			x.buildInterface();
			mixin(Rewrite!q{x});
		}
	}

	void instancesSemantic(){
		foreach(ref x; instances){
			if(x.bdy is bdy) continue;
			x.semantic(null); // TODO: ok?
			mixin(Rewrite!q{x});
		}
	}

private:
	TemplateInstanceDecl[] instances; // TODO!!: replace with O(#args) lookup!
	TemplateInstanceDecl lookup(Expression[] args){
		TemplateInstanceDecl r = null;
		foreach(x; instances){
			alias util.all all;
			if(args.length == x.args.length &&
			   all!(_=>_[0].templateParameterEquals(_[1]))(zip(x.args, args)))
			{ r=x; break; }
		}
		if(r&&r.completeInstance){
			assert(r.bdy is bdy);
			r=r.completeInstance;
			assert(!r.completeInstance);
		}
		return r;
	}
	void add(TemplateInstanceDecl decl){
		instances~=decl;
	}
}

mixin template Semantic(T) if(is(T==TemplateInstanceExp)){
	bool firstlookup = true;
	override void semantic(Scope sc){
		mixin(SemPrlg);

		// eponymous template trick
		if(!!res){
			mixin(SemChld!q{res});
			if(!eponymous.meaning && eponymous.sstate != SemState.failed){
				eponymous.recursiveLookup = false;
				eponymous.lookup(res.getMemberScope());
			}
			mixin(SemProp!q{eponymous});
			if(eponymous.sstate == SemState.failed){
				needRetry=false;
				auto r = res;
				mixin(RewEplg!q{r});
			}
			Expression r=New!(BinaryExp!(Tok!"."))(res, eponymous);
			r.loc=loc;
			r.semantic(sc);
			// TODO: are there other code locations that might create
			// a circular dependency like this?
			mixin(Rewrite!q{r});
			if(r.needRetry==2){mixin(PropRetry!q{r});}
			mixin(RewEplg!q{r});
		}

		mixin(RevEpoLkup!q{e});
		foreach(x; args) if(x.sstate != SemState.completed) x.prepareInterpret();

		mixin(SemChld!q{e,args});

		Expression e1 = null;
		Expression container = null;
		auto sym = e.isSymbol();
		if(!sym){
			if(auto fld = e.isFieldExp()){
				container = fld.e1;
				sym = fld.e2;
			}else{
				// TODO: this error message has a duplicate in Declaration.instantiationError
				sc.error(format("can only instantiate templates, not %ss",e.kind),loc);
				mixin(ErrEplg);
			}
		}

		foreach(i,ref x; args){
			if(x.sstate != SemState.completed) continue;
			if(args[i].isType()) continue;
			if(auto ae=x.isAddressExp()) if(auto lit=ae.e.isSymbol()){
				// turn the function literal into a function declaration
				lit.isFunctionLiteral=false;
				if(auto fd = lit.meaning.isFunctionDecl()){
				if(fd.type.hasUnresolvedParameters()){
					lit.sstate = SemState.begin;
					fd.sstate = SemState.pre;
					fd.scope_ = null;
					lit.meaning = fd.templatizeLiteral();
					lit.meaning.semantic(sc);
					mixin(Rewrite!q{lit.meaning});
					assert(lit.meaning.sstate == SemState.completed);
					x = lit;
				}}
				continue;
			}
			if(!x.isSymbol()&&!x.isType()){
				x.interpret(sc);
				mixin(PropRetry!q{x});
			}
		}

		mixin(SemChld!q{args});

		if(!decl||needRetry){
			decl = sym.meaning.matchInstantiation(args);
			if(!decl){
				if(sym.meaning.sstate != SemState.error)
					sym.meaning.instantiationError(sc,loc,args);
				mixin(ErrEplg);
			}
			mixin(SemProp!q{decl});
		}
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
		sym = New!Symbol(decl.getInstance(args));
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
private:
	Expression res;
	Identifier eponymous;
	TemplateDecl decl;
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
						mixin(ConvertTo!q{e2,bl});
					}else{
						mixin(SemChldExp!q{e2});
						type = bl;
					}
					mixin(ConstFold!q{e2});
					mixin(SemEplg);
				}
			}
		}
		mixin(SemChldExp!q{e1,e2});
		// constant folding done by hijacking the SemEplg macro TODO: better options?
		auto c1 = e1.isConstant(), c2 = e2.isConstant();
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
						if(e2.implicitlyConvertsTo(elt)) e2=e2.implicitlyConvertTo(elt);
						else e2=e2.implicitlyConvertTo(type);
					}else{
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
			bool conv1 = e2.implicitlyConvertsTo(e1.type);
			bool conv2 = e1.implicitlyConvertsTo(e2.type);
			if(conv1 ^ conv2){
				if(conv1) ty = e1.type;
				else ty = e2.type;
			}else if(auto tt=e1.typeCombine(e2)) ty=tt;
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
			e1=e1.convertTo(bl);
			// allow (bool) && (void), (bool) || (void)
			auto ty2 = e2.type.getHeadUnqual();
			if(ty2 !is Type.get!void()){
				e2=e2.convertTo(bl);
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

					if(auto ty=t1.combine(t2)){
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
					}
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

			if(f1 && f2){
				if(e1.implicitlyConvertsTo(el2)){
					f1 = false;
					el1 = e1.type;
				}
				if(e2.implicitlyConvertsTo(el1)){
					f2 = false;
					el2 = e2.type;
				}
			}

			// TODO: if arr1 is of type int[][], what is the meaning of arr1~[]?
			switch(f1<<1|f2){
				case 0b11: // both are arrays
					if(auto mg=e1.typeMostGeneral(e2)){
						type = mg.getElementType();
						if(el1 !is el2) type = type.getHeadUnqual();
					}else if(auto ty = el1.refCombine(el2, 0)){
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
										type = type.get!(immutable(T))().refCombine(elo,0);
										break;
									}
								}
							}
					}
					break;
				case 0b10: // array ~ element
					if(e2.implicitlyConvertsTo(el1)) type = el1;
					else if(e2.implicitlyConvertsTo(e1.type)){f2=true; type = el1;}
					break;
				case 0b01: // element ~ array
					if(e1.implicitlyConvertsTo(el2)) type = el2;
					else if(e1.implicitlyConvertsTo(e2.type)){f1=true; type = el2;}
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

				if(f1) e1=e1.convertTo(type); // TODO: this leaves noise in the AST
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
			sc.error(format("incompatible types '%s' and '%s' for binary "~TokChars!S,e1.type,e2.type),loc);
			mixin(ErrEplg);
		}
	}

	override bool isConstant(){
		static if(S==Tok!"is" || S==Tok!"!is") return false;
		else return e1.isConstant() && e2.isConstant();
	}

	static if(isAssignOp(S) && S!=Tok!"=")
		override bool isLvalue(){
			return true;
		}

	static if(S==Tok!"~"){ // '~' always reallocates, therefore conversion semantics are less strict
		override bool implicitlyConvertsTo(Type rhs){
			if(super.implicitlyConvertsTo(rhs)) return true;
			// the type qualifiers of the head of the element type are unimportant.
			// example: if arr1, arr2 are of type int[], then arr1~arr2 implicitly converts to immutable(int)[]
			// example: if arr is of type int*[] then arr~arr implicitly converts to const(int)*[]
			Type ell = type.getElementType(), elr = rhs.getElementType();
			if(ell&&elr&&ell.getHeadUnqual().refConvertsTo(elr.getHeadUnqual(), 0)) return true;
			// if both operands implicitly convert to the result type, their concatenation does too.
			// example: [1,2,3]~[4,5,6] implicitly converts to short[]
			// example: 2 ~ [3,4,5] implicitly converts to short[]
			if(auto rel = rhs.getElementType()){
				auto el1 = e1.type.getElementType(), el2 = e2.type.getElementType();
				if(el1 && el1.equals(e2.type))      // array ~ element
					return e1.implicitlyConvertsTo(rhs) && e2.implicitlyConvertsTo(rel);
				else if(el2 && el2.equals(e1.type)) // element ~ array
					return e1.implicitlyConvertsTo(rel) && e2.implicitlyConvertsTo(rhs);
			}
			return e1.implicitlyConvertsTo(rhs) && e2.implicitlyConvertsTo(rhs);
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
					}else static if(isIntRelationalOp(S)){
						static if(S==Tok!"is") enum S = Tok!"==";
						else static if(S==Tok!"!is") enum S = Tok!"!=";
						auto it = e1.type.isIntegral();
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
							return mixin(`r1.min`~TokChars!S~`r2.min`)?@(x)(1,1,true):@(x)(0,0,true);
						static if(S==Tok!"=="){
							return r1.overlaps(r2)?@(x)(0,1,true):@(x)(0,0,true);
						}else static if(S==Tok!"!="){
							return r1.overlaps(r2)?@(x)(0,1,true):@(x)(1,1,true);
						}else static if(S==Tok!">"){
							return r1.gr(r2)  ? @(x)(1,1,true)
								 : r1.leq(r2) ? @(x)(0,0,true)
								 :              @(x)(0,1,true);
						}else static if(S==Tok!">="){
							return r1.geq(r2) ? @(x)(1,1,true)
								 : r1.le(r2)  ? @(x)(0,0,true)
								 :              @(x)(0,1,true);
						}else static if(S==Tok!"<"){
							return r1.le(r2)  ? @(x)(1,1,true)
								 : r1.geq(r2) ? @(x)(0,0,true)
								 :              @(x)(0,1,true);
						}else static if(S==Tok!"<="){
							return r1.leq(r2) ? @(x)(1,1,true)
								 : r1.gr(r2)  ? @(x)(0,0,true)
								 :              @(x)(0,1,true);
						}
					}else static if(isRelationalOp(S)){
						return super.get@(x)(); // TODO!
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
		type = e2.typeCombine(e3);
		if(!type){
			sc.error(format("incompatible types for ternary operator: '%s' and '%s'",e2.type,e3.type),loc);
			mixin(ErrEplg);
		}
		if(!isConstant()){
			mixin(ConstFold!q{e1});
			mixin(ConstFold!q{e2});
			mixin(ConstFold!q{e3});
		}
		mixin(SemEplg);
	}

	bool isConstant(){
		return e1.isConstant() && e2.isConstant() && e3.isConstant();
	}

	override bool isLvalue(){
		return e2.isLvalue() && e3.isLvalue();
	}

	override bool implicitlyConvertsTo(Type rhs){
		if(super.implicitlyConvertsTo(rhs)) return true;
		return e2.implicitlyConvertsTo(rhs) && e3.implicitlyConvertsTo(rhs);
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
		if(!gscope) gscope = New!GaggingScope(sc);
		auto f = ty.typeSemantic(gscope);
		mixin(PropRetry!q{ty});
		if(ty.sstate == SemState.error) goto no;
		Token tok;
		switch(which){
			case WhichIsExp.type:
				goto yes;
			case WhichIsExp.isEqual, WhichIsExp.implicitlyConverts:
				if(tparams.length) goto default;
				if(tySpec){
					auto g = tySpec.typeSemantic(sc);
					mixin(SemProp!q{tySpec});

					if(which == WhichIsExp.isEqual && f.equals(g) ||
					   which == WhichIsExp.implicitlyConverts && f.implicitlyConvertsTo(g))
						goto yes;
					else goto no;
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


// abstracts a symbol. almost all circular dependency diagnostics are located here.
// CallExp is aware of the possibility circular dependencies too, because it plays an
// important role in overloaded symbol resolution
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

	auto accessCheck = AccessCheck.all;
	this(Declaration m, bool strong=false, bool isfunlit=false)in{
		assert(m&&1);
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
					errsc = x.scope_;
					break;
				}else if(x.meaning.scope_.handler.showsEffect()){
					errsc = x.meaning.scope_;
					break;
				}
			}
			errsc.error("circular dependencies are illegal",loc);
			circ = null;
			mixin(SetErr!q{});
			foreach_reverse(x; clist[1..$]){
				errsc.note("part of dependency cycle here",x.loc);
				mixin(SetErr!q{x});
			}
			clist=[];
		}else{
			needRetry = 2;
			clist~=this;
		}
	}
	// interpretation can lead to circular dependencies
	// this is mixed into Expression.interpret
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
		debug scope(exit) assert(needRetry==2||!circ,toString());
		mixin(SemPrlg);
		scope_=sc;
		assert(!!meaning);

		if(needRetry) sstate = SemState.begin;
		if(sstate >= SemState.started){
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
			needRetry = false; // TODO: why needed?
			mixin(CircErrMsg);
			mixin(SemCheck);
			mixin(PropRetry!q{meaning});
			mixin(PropErr!q{meaning});
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
			needParamDeduction=any!(_=>_.mustBeTypeDeducted())(fd.type.params);
		}

		if(isStrong){
			if(!needParamDeduction){
				mixin(MeaningSemantic);
				mixin(CircErrMsg);
				mixin(SemProp!q{meaning});
			}
		}

		// those are not virtual functions because of centralized symbol dependency handling
		// TODO: make specific parts virtual functions of the relevant classes instead

		if(auto vd=meaning.isVarDecl()){
			if(!vd.type || vd.stc & STCenum || (vd.init&&vd.stc&(STCimmutable|STCconst)&&vd.willInterpretInit())){
				mixin(MeaningSemantic);
				mixin(CircErrMsg);
				mixin(SemProp!q{meaning});
			}
			assert(!!vd.type);

			mixin(VarDecl.SymbolResolve);
			if(vd.stc&STCenum){
				if(vd.init){
					assert(vd.init.isConstant());
					needRetry=false;
					auto r=vd.init.cloneConstant();
					r.loc = loc;
					mixin(RewEplg!q{r});
				}else assert(meaning.sstate == SemState.error);
			}

		}else if(auto fd=meaning.isFunctionDecl()){
			if(!needParamDeduction){
				if(fd.type.hasUnresolvedReturn()){
					mixin(MeaningSemantic);
					mixin(CircErrMsg);
					mixin(SemProp!q{meaning});
				}else fd.propagateSTC();
			}
			fd.type.semantic(meaning.scope_);
			assert(!fd.rewrite);
			if(needParamDeduction) type = Type.get!void();
			else type = fd.type;
		}else if(auto tm=meaning.isTemplateInstanceDecl()){
			// circular template instantiations are allowed
			// those just don't carry forward the information
			// whether the template compiled or not.
			if(meaning.sstate != SemState.started){
				mixin(MeaningSemantic);
				mixin(CircErrMsg);
				mixin(SemProp!q{meaning});
			}
			type=Type.get!void();
		}else if(auto ov=meaning.isOverloadSet()){
			foreach(x; ov.decls) if(auto fd = x.isFunctionDecl()){
				if(fd.type.hasUnresolvedReturn()){
					fd.semantic(fd.scope_);
					mixin(Rewrite!q{fd});
					mixin(CircErrMsg);
					mixin(SemProp!q{fd});
				}else{
					fd.propagateSTC();
					fd.type.semantic(fd.scope_);
					mixin(Rewrite!q{fd.type});
					mixin(CircErrMsg);
					mixin(SemProp!q{fd.type});
				}
				fd.type.semantic(meaning.scope_);
				assert(!fd.rewrite);
			}
			if(ov.decls.length==1)
				if(auto fd=ov.decls[0].isFunctionDecl()){
					meaning = fd;
					type = fd.type;
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
			mixin(RewEplg!q{r});
		}

		needRetry = false;
		performAccessCheck();
		mixin(SemCheck);

		mixin(SemEplg);
	}

	void performAccessCheck() in{assert(meaning && scope_);}body{
		if(meaning.needsAccessCheck(accessCheck))
		if(auto decl = scope_.getDeclaration()){
			if(!decl.isDeclAccessible(meaning)){
				// TODO: better error message?
				if(meaning.scope_.getDeclaration().isFunctionDef())
					scope_.error(format("cannot access the context in which '%s' is stored", loc.rep),loc);
				else
					// error message duplicated in FieldExp.semantic
					scope_.error(format("need 'this' to access %s '%s'",kind,loc.rep),loc);

				scope_.note(format("%s was declared here",kind),meaning.loc);
				mixin(ErrEplg);
			}
		}		
	}

	override string toString(){
		auto tmpl=meaning.isTemplateInstanceDecl();
		if(!tmpl){
			if(auto nsts=cast(NestedScope)meaning.scope_)
			if(auto tmps=cast(TemplateScope)nsts.parent)
				tmpl=tmps.tmpl;
		}
		if(tmpl && meaning.name.name==tmpl.name.name)
			return meaning.name.name~"!("~join(map!(to!string)(tmpl.args),",")~")";
		return meaning.name.name;
	}
	override @property string kind(){return meaning.kind;}

	// TODO: maybe refactor
	override Scope getMemberScope(){
		if(auto tmpl=meaning.isTemplateInstanceDecl()) return tmpl.bdy.scope_;
		return super.getMemberScope();
	}

	final Type thisType(){
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
	override AccessCheck deferredAccessCheck(){
		if(!meaning.needsAccessCheck(accessCheck)) return accessCheck;
		return super.deferredAccessCheck();
	}

	override bool isConstant(){
		assert(!!meaning,toString());
		//if(meaning.stc|STCstatic) return true;
		if(auto vd = meaning.isVarDecl()) return !!(vd.stc&STCenum);
		return false;
	}
	// DMD 2.058/2.059 behave approximately like this:
	/+override bool typeEquals(Type rhs){
		if(meaning.stc&STCenum)
		if(auto vd = meaning.isVarDecl()) return vd.init.typeEquals(rhs);
		return super.typeEquals(rhs);
	}+/

	override bool implicitlyConvertsTo(Type rhs){
		if(meaning.stc&STCenum)
		if(auto vd = meaning.isVarDecl()) return vd.init.implicitlyConvertsTo(rhs);
		return super.implicitlyConvertsTo(rhs);
	}

	// override Type isType(){...} // TODO.
	override bool isLvalue(){
		//import std.stdio; wrietln(meaning," ",meaning.stc);
		return !(meaning.stc&STCrvalue) &&
			(meaning.isVarDecl() || meaning.isOverloadSet() || meaning.isFunctionDecl());
	}

	/* This assumes that the reference to the Symbol is kept unique during SA
	 */
	override Expression matchCall(scope Expression[] args, ref MatchContext context){
		if(auto m = meaning.matchCall(args, context)){
			// resolve the overload in place and then rely on
			// semantic to catch eventual circular dependencies:
			meaning = m;
			sstate = SemState.begin;
			type = null;
			Symbol.semantic(scope_);
			return this;
		}
		return super.matchCall(args, context);
	}
	override void matchError(Scope sc, Location loc, scope Expression[] args){
		meaning.matchError(sc,loc,args);
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
		if(auto sym = cast(Symbol)rhs) return meaning is sym.meaning;
		return false;
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
struct MatchContext{
	auto inoutRes = InoutRes.none;
	auto match = Match.exact;
}

// aware of circular dependencies
mixin template Semantic(T) if(is(T==CallExp)){
	override void semantic(Scope sc){ // TODO: type checking
		// parameter passing
		mixin(SemPrlg);
		mixin(RevEpoLkup!q{e});
		mixin(SemChldPar!q{e});
		mixin(SemChldExp!q{args});
		mixin(PropErr!q{e});

		MatchContext context;
		if(auto c = fun !is null ? fun : e.matchCall(args, context)){
			fun = c;
			mixin(SemChld!q{fun});
		}else{
			mixin(SemProp!q{e}); // display error only once
			e.matchError(sc,loc, args);
			mixin(ErrEplg);
		}
		mixin(SemProp!q{e}); // catch errors generated in matchCall
		assert(fun && fun.type);
		auto tt = fun.type.getFunctionTy();
		assert(!!tt);
		if(adapted is null)
		foreach(i,x; tt.params[0..args.length]){
			if(x.stc & STClazy){
				if(adapted is null) adapted = new Expression[args.length];
				else if(adapted[i]) continue;
				auto ft = New!FunctionTy(STC.init, args[i].type,cast(Parameter[])[],VarArgs.none);
				auto bs = New!BlockStm(cast(Statement[])[New!ReturnStm(args[i])]); // TODO: gc allocates []
				auto dg = New!FunctionLiteralExp(ft,bs,FunctionLiteralExp.Kind.delegate_);
				adapted[i] = dg;
				static struct Reset{ void perform(Node self){self.sstate = SemState.begin;} }
				runAnalysis!Reset(args[i]); // TODO: dangerous...
			}
		}
		mixin(SemChld!q{adapted});

		type = tt.ret.resolveInout(context.inoutRes);

		if(tt.params.length > args.length){
			// //  TODO: this allocates rather heavily
			// args ~= array(map!(_=>_.init.dup)(tt.params[args.length..$]);
			sc.error("default parameters not implemented yet",loc);
			mixin(ErrEplg);
		}
		foreach(i,x; tt.params[0..args.length]){
			auto pty = x.type.resolveInout(context.inoutRes);
			args[i]=args[i].implicitlyConvertTo(pty);
		}
		mixin(SemChld!q{args});
		mixin(ConstFold!q{e});
		foreach(ref x; args) mixin(ConstFold!q{x});
		mixin(SemEplg);
	}

	override bool isLvalue(){ return !!(e.type.getFunctionTy().stc & STCref); }

	Expression fun;
	Expression[] adapted;
}


// everything concerning error gagging is centralized here
import error;
class GaggingErrorHandler: ErrorHandler{
	override void error(lazy string, Location){ nerrors++; }
	override void note(lazy string, Location){ /* do nothing */ }

	/* for errors that span gagging boundaries, this is important information
	 */
	override bool showsEffect(){ return false; }
}

class GaggingScope: NestedScope{
	this(Scope parent){super(parent); handler=New!GaggingErrorHandler();}
	override bool insert(Declaration decl){
		// cannot insert into gagging scope
		return false;
	}

	override void error(lazy string, Location){ /* do nothing */ }
	override void note(lazy string, Location){ /* do nothing */ }

	// forward other members:
	override Declaration lookup(Identifier ident, lazy Declaration alt){
		return parent.lookup(ident,alt);
	}

	override Scope getUnresolved(Identifier ident){
		return parent.getUnresolved(ident);
	}

	override FunctionDef getFunction(){return parent.getFunction();}
}



mixin template Semantic(T) if(is(T==CastExp)){
	protected bool checkConv(Scope sc){
		if(e.convertsTo(type)) return true;
		sc.error(format("cannot cast expression '%s' of type '%s' to '%s'",e.loc.rep,e.type,type),e.loc);
		//error(format("no viable conversion from type '%s' to '%s'",e.type,type),e.loc);
		return false;
	}

	//mixin(DownCastMethods!ImplicitCastExp);
	ImplicitCastExp isImplicitCastExp(){return null;}

	override void semantic(Scope sc){
		// TODO: sanity checks etc.
		mixin(SemPrlg);
		mixin(SemChldExp!q{e});

		if(!ty) {
			// TODO: works differently for classes..?
			type = e.type.getHeadUnqual().applySTC(stc);
		}else{
			type=ty.typeSemantic(sc);
			mixin(SemProp!q{ty});
			type=type.applySTC(stc);
		}

		if(!checkConv(sc)) mixin(ErrEplg);


		// implicitly typed delegate literals convert to both function and
		// delegate. furthermore, (implicit) casts can be used to determine
		// the argument types
		// TODO: this is heavy fp style. is there a better design?
		if(auto uexp = e.isAddressExp()            ){ // TODO: reduce the DMD bug
		if(auto sym = uexp.e.isSymbol()            ){
		if(auto fd  = sym.meaning.isFunctionDef()  ){
			if(sym.type is Type.get!void()){
				assert(!!type.getFunctionTy());
				fd.type.resolve(type.getFunctionTy());
				uexp.sstate = sym.sstate = SemState.begin;
				mixin(SemChld!q{e});
			}
			if(auto dg = type.getHeadUnqual().isDelegateTy()){
				if(fd.stc&STCstatic && fd.deduceStatic){
					assert(sym.isStrong && uexp.type.getFunctionTy());
					if(uexp.type.getFunctionTy().getDelegate()
					   .implicitlyConvertsTo(dg)){
						fd.addContextPointer();
						uexp.sstate = sym.sstate = SemState.begin;
					}
				}
			}
		}}}
		mixin(SemChld!q{e});

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
		if(type.isPointerTy() || e.type.isPointerTy()) return false; // TODO: ok?
		if(e.type.implicitlyConvertsTo(type)) return e.isConstant();
		if(type.getHeadUnqual().isPointerTy()) return false;
		if(type.getHeadUnqual() is Type.get!void()) return false;
		return e.isConstant();
	}

	override bool implicitlyConvertsTo(Type rhs){
		if(super.implicitlyConvertsTo(rhs)) return true;//TODO: does this work out correctly?
		return e.implicitlyConvertsTo(rhs);
	}

	override Expression implicitlyConvertTo(Type rhs){
		if(!super.implicitlyConvertsTo(rhs)){
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

	IntRange getIntRange(){
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
	LongRange getLongRange(){
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

	protected override bool checkConv(Scope sc){
		if(e.implicitlyConvertsTo(type)) return true;
		sc.error(format("cannot implicitly convert expression '%s' of type '%s' to '%s'",e.loc.rep,e.type,type),e.loc); // TODO: replace toString with actual representation
		return false;
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
		if(sstate != SemState.failed){
			lookup(lkup);
			if(needRetry) return;
		}
		if(sstate == SemState.failed){
			sc.error(format("undefined identifier '%s'",name), loc);
			mixin(ErrEplg);
		}
		super.semantic(sc);
	}

	/* looks up the given identifier in the scope given by the first argument.
	   the second argument

	   + if needRetry is set after the call, then the lookup should be retried later
	   + if sstate is SemState.error after the call, then the lookup failed
	   + if the lookup succeeds, then 'meaning' will become initialized
	 */

	final Identifier lookup(Scope lkup)in{
		assert(!!lkup);
		assert(!meaning && sstate != SemState.error && sstate != SemState.failed);
	}out(result){
		assert(result is this);
		if(!needRetry && sstate != SemState.error && sstate != SemState.failed)
			assert(!!meaning && !!meaning.scope_);
	}body{
		needRetry = false;
		if(allowDelay){
			sstate=SemState.begin; // reset

			if(unresolved){
				if(!unresolved.inexistent(this)) mixin(ErrEplg);
				unresolved = null;
				tryAgain = true;
			}

			meaning=recursiveLookup?lkup.lookup(this, null):lkup.lookupHere(this, null);

			if(!meaning){
				sstate = SemState.started;
				mixin(RetryBreakEplg);
			}else if(typeid(this.meaning) is typeid(DoesNotExistDecl)){
				meaning = null;
				needRetry=false;
				sstate = SemState.failed;
				return this;
			}else needRetry=false;
		}else{
			if(sstate == SemState.started) unresolved=lkup.getUnresolved(this);
			sstate = SemState.begin;
			mixin(RetryEplg);
		}
		return this;
	}

	/* performs reverse eponymous lookup for eponymous templates
	   eg. T foo(T)(T arg){return foo!T(arg);} and
	   eg. double foo(T)(T arg){return foo(2.0);} should compile
	   TODO: is there maybe a way to optimize the requirements for the caller?
	   at the moment, the caller is required to keep around two references just in case
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
}


mixin template Semantic(T) if(is(T==FieldExp)){

	ExprTuple tuple;
	@property Expression member(){ return tuple ? tuple : e2; }

	AccessCheck accessCheck;
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e1});
		Type scopeThisType;
		auto msc = e1.getMemberScope();
		auto this_ = e1.extractThis();

		if(accessCheck == AccessCheck.init){
			accessCheck = e2.accessCheck;
			if(!e1.isType()) e2.accessCheck = e1.deferredAccessCheck();
		}

		if(e2.accessCheck!=AccessCheck.none) e2.loc=loc;

		if(!msc){
			if(auto ptr=e1.type.getHeadUnqual().isPointerTy())
				msc = ptr.ty.getMemberScope();
			if(!msc) goto Linexistent;
			// TODO: auto-dereference
		}

		if(!e2.meaning){
			if(auto ident = e2.isIdentifier()){
				ident.recursiveLookup = false;
				ident.lookup(msc);
				mixin(SemProp!q{ident});
				if(ident.sstate == SemState.failed) goto Linexistent;
			}
		}

		assert(!!e2.meaning);
		// TODO: find a better design here
		e2.semantic(sc);
		Expression res = e2;
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
					type=type.applySTC(this_.type.getHeadSTC());
				}

				if(sym.meaning.needsAccessCheck(accessCheck))
					return thisCheck(sc, this_, thisType);

			}
		}else if(this_){
			if(auto et = res.isExprTuple()){
				tuple = et;
				type = et.type;
				mixin(SemEplg);
			}else{
				// enum reference. we need to evaluate 'this', but it
				// does not matter for the field expression
				//assert(e2.meaning.stc & STCenum);
				auto r=New!(BinaryExp!(Tok!","))(this_,res);
				r.loc=loc;
				r.semantic(sc);
				mixin(RewEplg!q{r});
			}
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
		if(auto t=symb.meaning.isTemplateInstanceDecl())
			tmpl=t;

		if(tmpl)
			sc.error(format("no member '%s' for %s '%s'",member.toString(),e1.kind,e1),loc);
		else
			sc.error(format("no member '%s' for type '%s'",member.toString(),e1.isType()?e1:e1.type),loc);
		mixin(ErrEplg);
	}

	/* given that 'this' of type thisType is required, check if
	   this_ can be used as the 'this' pointer
	 */
	private void thisCheck(Scope sc,Expression this_, Type thisType){
		if(!this_){
			// error message duplicated in Symbol.semantic
			sc.error(format("need 'this' to access %s '%s'",
			                e2.kind,e2.loc.rep),loc);
			mixin(ErrEplg);
		}
		assert(this_.sstate == SemState.completed);
		
		if(!this_.type.getUnqual().refConvertsTo(thisType.getUnqual(),0)){
			sc.error(format("need 'this' of type '%s' to access %s '%s'",
			                thisType.toString(),e2.kind,e2.loc.rep),loc);
			mixin(ErrEplg);
		}
		// successfully resolved non-tuple field expression that
		// requires 'this'
		mixin(SemEplg);
	}


	override bool implicitlyConvertsTo(Type rhs){
		return member.implicitlyConvertsTo(rhs);
	}
	override bool isLvalue(){
		return member.isLvalue();
	}

	override Scope getMemberScope(){
		return member.getMemberScope();
	}
	override Expression extractThis(){
		if(tuple) return null; // tuples do not provide a 'this' pointer
		if(e2.meaning.isTemplateInstanceDecl()) return e1.extractThis();
		return this;
	}
	override AccessCheck deferredAccessCheck(){
		if(tuple) return AccessCheck.all;
		if(!e2.meaning.needsAccessCheck(accessCheck)) return accessCheck;
		return super.deferredAccessCheck();
	}

	// TODO: consider 'this'-pointer for matching
	override Expression matchCall(scope Expression[] args, ref MatchContext context){
		if(tuple) return null;
		auto exp = e2.matchCall(args, context);
		if(!exp) return null;
		assert(!!cast(Symbol)exp);
		auto sym = cast(Symbol)cast(void*)exp;
		e2 = sym;
		sstate = SemState.begin;
		type = null;
		FieldExp.semantic(e2.scope_);
		Expression r = this;
		mixin(Rewrite!q{r});
		return r;
	}
	override void matchError(Scope sc, Location loc, scope Expression[] args){
		if(tuple) super.matchError(sc,loc,args);
		return e2.matchError(sc,loc,args);
	}

	import vrange;
	override IntRange getIntRange(){ return member.getIntRange(); }
	override LongRange getLongRange(){ return member.getLongRange(); }


	/* rewrites built-in fields and returns whether it was a built-in
	 */
	bool isBuiltInField(Scope sc,Expression this_)in{
		assert(!tuple);
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
		auto dg=New!FunctionDef(STC.init,fty,New!Identifier(uniqueIdent("__dgliteral")),cast(BlockStm)null,cast(BlockStm)null,cast(Identifier)null,bdy, which==Kind.none);
		auto decl=sc.getDeclaration();
		if(which==Kind.function_ || decl&&decl.isAggregateDecl())
			dg.stc |= STCstatic;
		dg.sstate = SemState.begin;
		dg.scope_ = sc; // Symbol will use this scope to reason for analyzing DG
		Expression e=New!Symbol(dg, true, true);
		e.loc=loc;
		e = New!(UnaryExp!(Tok!"&"))(e);
		e.brackets++;
		e.loc=loc;
		e.semantic(sc);
		
		if(auto enc=sc.getDeclaration()) if(auto fd=enc.isFunctionDef()){
			fd.nestedFunctionLiteral(dg);
		}

		auto r = e;
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
		assert(!rewrite||!!cast(Type)rewrite);
		auto r=rewrite?cast(Type)cast(void*)rewrite:this;
		mixin(Rewrite!q{r});
		return r;
	}

	override Type clone(Scope,const ref Location) { return this; }

	final protected Type checkVarDeclError(Scope sc, VarDecl me){
		sc.error(format("%s '%s' has invalid type '%s'", me.kind, me.name, this), me.loc);
		return New!ErrorTy();
	}
	Type checkVarDecl(Scope, VarDecl){return this;}

	Type getArray(long size){
		if(auto r=arrType.get(size,null)) return r;
		return arrType[size]=ArrayTy.create(this,size);
	}

	Expression matchCall(scope Expression[] args, ref MatchContext context){
		return null;
	}
	void matchError(Scope sc, Location loc, Expression[] args){
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
		auto tt = isFunctionTy();
		if(!tt){
			if(auto dgt = isDelegateTy()) tt = dgt.ft;
			else if(auto fpt = isPointerTy()){
				assert(cast(FunctionTy)fpt.ty);
				tt = cast(FunctionTy)cast(void*)fpt.ty;
			}
		}
		return tt;
	}


	/* used for IFTI, template type parameter matching
	   and for matching inout. the formal parameter type is adapted
	   to match the actual argument as good as possible.
	 */
	Type adaptTo(Type from, ref InoutRes inoutRes){
		return this;
	}

	Type resolveInout(InoutRes inoutRes){
		return this;
	}

	/* important for is-expressions and parameter matching:
	   function, delegate and function pointer types cannot always
	   be kept unique, since they may include default parameters
	 */
	bool equals(Type rhs){
		return this is rhs;
	}

	override bool convertsTo(Type rhs){
		return implicitlyConvertsTo(rhs.getUnqual().getConst())
			|| rhs.getHeadUnqual() is Type.get!void();
	}

	override bool implicitlyConvertsTo(Type rhs){
		return this.refConvertsTo(rhs.getHeadUnqual(),0);
	}

	final bool constConvertsTo(Type rhs){
		return this.getUnqual().equals(rhs.getUnqual())
		    && this.refConvertsTo(rhs,0);
	}

	// bool isSubtypeOf(Type rhs){...}

	/* stronger condition than subtype relationship.
	   a 'num'-times reference to a this must be a subtype of
	   a 'num'-times reference to an rhs.
	*/
	bool refConvertsTo(Type rhs, int num){
		if(this is rhs) return true;
		if(num < 2){
			if(auto d=rhs.isConstTy()) return refConvertsTo(d.ty.getTailConst(), 0);
		}
		return false;
	}

	final protected Type mostGeneral(Type rhs){
		if(rhs is this) return this;
		Type r   = null;
		bool l2r = this.implicitlyConvertsTo(rhs);
		bool r2l = rhs.implicitlyConvertsTo(this);
		if(l2r ^ r2l){
			r = r2l ? this : rhs;
			STC stc = this.getHeadSTC() & rhs.getHeadSTC();
			r = r.getHeadUnqual().applySTC(stc);
		}
		return r;
	}

	final protected Type refMostGeneral(Type rhs, int num){
		if(rhs is this) return this;
		Type r   = null;
		bool l2r = this.refConvertsTo(rhs, num);
		bool r2l = rhs.refConvertsTo(this, num);
		if(l2r ^ r2l){
			r = r2l ? this : rhs;
			if(!num){
				STC stc = this.getHeadSTC() & rhs.getHeadSTC();
				r = r.getHeadUnqual().applySTC(stc);
			}
		}
		return r;
	}

	/* common type computation. roughly TDPL p60
	   note: most parts of the implementation are in subclasses
	*/

	Type combine(Type rhs){
		if(auto r = mostGeneral(rhs)) return r;
		auto unqual = rhs.getHeadUnqual();
		if(unqual !is rhs) return unqual.combine(this);
		return null;
	}

	Type refCombine(Type rhs, int num){
		if(auto d=rhs.isQualifiedTy()) return d.refCombine(this, num);
		if(auto r = refMostGeneral(rhs, num)) return r;
		if(num < 2){
			if(num) return getConst().refCombine(rhs.getConst(), 0);
			auto tconst = getTailConst();
			if(this !is tconst) return tconst.refCombine(rhs.getTailConst(), 0);
		}
		return null;
	}

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
}


mixin template Semantic(T) if(is(T==DelegateTy)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{ft});
		mixin(SemEplg);
	}

	Expression matchCall(scope Expression[] args, ref MatchContext context){
		return ft.matchCall(args, context) ? this : null;
		return null;
	}

	override bool equals(Type rhs){
		if(auto dgt = rhs.isDelegateTy()) return ft.equals(dgt.ft);
		return false;
	}

	override bool refConvertsTo(Type rhs, int num){
		if(auto dgt = rhs.isDelegateTy()) return ft.refConvertsTo(dgt.ft, num+1);
		return super.refConvertsTo(rhs,num);
	}
	
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
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(rret){
			ret = rret.typeSemantic(sc);
			mixin(PropRetry!q{rret});
		}
		if(ret) mixin(SemChldPar!q{ret});
		foreach(p; params){
			if(!p.rtype && !p.init) continue; // parameter type needs to be deduced
			if(p.sstate==SemState.pre) p.sstate = SemState.begin; // never insert into scope
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
		foreach(x;params) if(x.mustBeTypeDeducted()) return true;
		return false;
	}


	void resolve(FunctionTy rhs)in{
		assert(!!rhs);
	}body{
		if(!ret) ret = rhs.ret;
		foreach(i,p; params[0..min($,rhs.params.length)])
			if(!p.type) p.type = rhs.params[i].type;
	}
	
	void resolve(Expression[] args){
		foreach(i,p; params[0..min($,args.length)])
			if(!p.type) p.type = args[i].type;
	}


	FunctionTy matchCall(scope Expression[] args, ref MatchContext context){
		alias util.any any; // TODO: file bug
		if(args.length > params.length ||
		   any!(_=>_.init is null)(params[args.length..params.length])){
				context.match=Match.none;
				return null;
		}

		resolve(args);

		immutable len = args.length;
		auto at = new Type[len]; // GC allocation, could be done on stack!
		// TODO: make behave like actual overloading
		foreach(i,p; params[0..len]){
			at[i] = p.type.adaptTo(args[i].type, context.inoutRes);
		}

		foreach(i,ref x;at) x = x.resolveInout(context.inoutRes);
		// the code that follows assumes the four matching level semantics
		static assert(Match.min == 0 && Match.max == Match.exact && Match.exact == 3);

		Match match = Match.exact;
		foreach(i,p; params[0..len]){
			if(!(params[i].stc & STCbyref)){
				if(args[i].typeEquals(at[i])) continue;
				if(!args[i].implicitlyConvertsTo(at[i])){
					match = Match.none;
					break;
				}else if(args[i].type.constConvertsTo(at[i])){
					if(match == Match.exact) match = Match.convConst;
				}else match = Match.convert; // Note: Match.none breaks the loop
			}else if(params[i].stc & STCref){
				if(!args[i].typeEquals(at[i]) || !args[i].isLvalue()){
					match = Match.none;
					break;
				}
			}else{// if(params[i].stc & STCout){
				assert(params[i].stc & STCout);
				if(!params[i].type.refConvertsTo(at[i],1) ||
				   !args[i].isLvalue() || !args[i].type.isMutable()){
					match = Match.none;
					break;
				}
			}
		}
		context.match = match;
		return match == Match.none ? null : this;
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
				if(stc1 & STCpure) stc1 &= ~STCpure, stc2 &= ~STCpure;
				if(stc1 & STCnothrow) stc1 &= ~STCnothrow, stc2 &= ~STCnothrow;
				if(stc1 & STCconst) stc1 &= ~STCconst, stc2 &= ~STCconst;
				if(stc2 & STCdisable) stc1 &= ~STCdisable, stc2 &= ~STCdisable;
				// TODO: more implicit conversion rules
			}
			if(!((stc1==stc2 && (!ret||ret.equals(ft.ret)) &&
			     params.length == ft.params.length) &&
			     vararg == ft.vararg)) return false;
			//all!(_=>_[0].type.equals(_[1].type))(zip(params,ft.params)) &&
			foreach(i,x; params)
				if(x.type && !x.type.equals(ft.params[i].type)) return false;
			return true;
		}else return false;
	}

	bool refConvertsTo(Type rhs, int num){
		if(num<2) return compareImpl!true(rhs);
		else return compareImpl!false(rhs);
	}


	DelegateTy getDelegate()in{
		assert(sstate==SemState.completed);
	}body{
		if(dgtype) return dgtype;
		dgtype = New!DelegateTy(this);
		dgtype.semantic(null); // TODO: ok?
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
		diffq&=-diffq;
		switch(diffq){
			foreach(x; ToTuple!qualifiers){
				enum s=mixin("STC"~x);
				enum i=x~(add?"_":"_no");
				enum irev = i~"."~x~(add?"_no":"_");
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
		foreach(x; qualifiers) r~="FunctionTy "~x~"_, "~x~"_no;\n";

		r~="public void clearCaches(){ dgtype=null;";
		foreach(x; qualifiers) r~=x~"_=null;"~x~"_no=null;";
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

	override bool implicitlyConvertsTo(Type rhs){
		if(auto bt=rhs.getHeadUnqual().isBasicType()){ // transitive closure of TDPL p44
			if((op == Tok!"void")) return false;
			if(strength[op]>=0 && strength[bt.op]>0) return strength[op]<=strength[bt.op];
			if(strength[bt.op]==-2) return true;
			return strength[op] == -1 && strength[bt.op] == -1; // both must be imaginary
		}
		return false;
	}

	override bool convertsTo(Type rhs){
		if(super.convertsTo(rhs)) return true;
		// all basic types except void can be cast to each other
		if(auto bt=rhs.getUnqual().isBasicType())
			return op != Tok!"void" || bt.op == Tok!"void";
		return false;
	}

	override Type combine(Type rhs){
		if(this is rhs.getHeadUnqual()) return this;
		if(auto bt=rhs.getHeadUnqual().isBasicType()){
			if(strength[op]>=0&&strength[bt.op]>=0){
				if(strength[op]<4&&strength[bt.op]<4) return Type.get!int();
				if(strength[op]<strength[bt.op]) return bt;
				if(strength[op]>strength[bt.op]) return this;
			}else{
				if(strength[bt.op]==-2) return bt.complCombine(this);
				else if(strength[bt.op]==-1) return bt.imagCombine(this);
			}
			switch(strength[op]){
				case -2:
					return complCombine(bt);
				case -1: // imaginary types
					return imagCombine(bt);
				case 4:
					return Type.get!uint();
				case 5:
					return Type.get!ulong();
				case 6:
					if(op==Tok!"float" && bt.op==Tok!"float") return this;
					else if(op!=Tok!"real" && bt.op!=Tok!"real") return Type.get!double();
					else return Type.get!real();
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

	override bool equals(Type rhs){
		if(auto d=mixin(`rhs.is`~T.stringof)()) return ty.equals(d.ty);
		return false;
	}

	override bool implicitlyConvertsTo(Type rhs){
		// getHeadUnqual never returns a qualified type ==> no recursion
		return getHeadUnqual().implicitlyConvertsTo(rhs.getHeadUnqual());
	}

	override bool convertsTo(Type rhs){
		return getUnqual().convertsTo(rhs);
	}

	override bool refConvertsTo(Type rhs, int num){
		if(this is rhs) return true;
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
		return false;
	}

	override Type combine(Type rhs){
		if(this is rhs) return this;
		// special rules apply to basic types:
		if(rhs.isBasicType()) return getHeadUnqual().combine(rhs);
		if(auto r = mostGeneral(rhs)) return r;
		auto lhs = getHeadUnqual();
		rhs = rhs.getHeadUnqual();
		if(auto r = lhs.combine(rhs)) return r;
		return null;
	}

	override Type refCombine(Type rhs, int num){
		if(auto r = refMostGeneral(rhs, num)) return r;
		if(num<2){
			static if(is(T==ConstTy)||is(T==ImmutableTy)){
				auto r = rhs.getConst();
				if(rhs is r) return null; // stop recursion
				return refCombine(r,num);
			}else{
				auto l=getConst(), r=rhs.getConst();
				if(this is l && rhs is r) return null; // stop recursion
				return l.refCombine(r,num);
			}
		}
		return null;
	}

	/* members
	 */

	Scope getMemberScope(){ return getUnqual().getMemberScope(); }


	ulong getSizeof(){return ty.getSizeof();}

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
					return @(tail).in@(upperf(q))Context().@(puthead);;
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

	override bool equals(Type rhs){
		if(auto c=mixin(`rhs.is`~T.stringof)()){
			static if(is(T==ArrayTy)) if(c.length!=length) return false;
			return ty.equals(c.ty);
		}
		return false;
	}

	static if(is(T==ArrayTy)){
		override bool implicitlyConvertsTo(Type rhs){
			return super.implicitlyConvertsTo(rhs)
				|| ty.getDynArr().implicitlyConvertsTo(rhs);
		}

	}

	override bool convertsTo(Type rhs){
		if(super.convertsTo(rhs)) return true;
		rhs = rhs.getHeadUnqual();
		static if(is(T==PointerTy))
			return rhs.isPointerTy() || rhs.isBasicType();
		else static if(is(T==DynArrTy))
			return cast(bool)rhs.isDynArrTy();
		else return implicitlyConvertsTo(rhs);
	}

	// this adds one indirection for pointers and dynamic arrays
	override bool refConvertsTo(Type rhs, int num){
		// dynamic and static arrays can implicitly convert to void[]
		static if(is(T==DynArrTy)||is(T==ArrayTy)){
			if(rhs.getUnqual() is Type.get!(void[])()){
				auto ell = getElementType(), elr = rhs.getElementType();
				auto stcr = elr.getHeadSTC(), stcl=getHeadSTC();
				if(ell.refConvertsTo(ell.getUnqual().applySTC(stcr),num+1))
					return true;
			}
		}
		static if(is(T==ArrayTy))
			if(auto tt = rhs.getElementType()) if(tt.equals(ty)) return true;
		if(auto c=mixin(`rhs.is`~T.stringof)()){
			static if(is(T==ArrayTy)) return c.length==length&&ty.refConvertsTo(c.ty,num);
			else return ty.refConvertsTo(c.ty,num+1);
		}
		return super.refConvertsTo(rhs,num);
	}
	override Type combine(Type rhs){
		if(auto r = mostGeneral(rhs)) return r;
		auto unqual = rhs.getHeadUnqual();
		return unqual.refCombine(this, 0);
	}
	override Type refCombine(Type rhs, int num){
		if(auto c=mixin(`rhs.is`~T.stringof)())
			if(auto d=ty.refCombine(c.ty,num+!is(T==ArrayTy)))
				return mixin(`d.`~puthead);
		return super.refCombine(rhs,num);
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

	Expression matchCall(scope Expression[] args, ref MatchContext context){
		if(auto ft=ty.isFunctionTy()) return ft.matchCall(args, context) ? this : null;
		return null;
	}


	static if(is(T==ArrayTy) || is(T==DynArrTy)):
	override Type getElementType(){return ty;}
}

mixin template Semantic(T) if(is(T==NullPtrTy)){
	override bool refConvertsTo(Type rhs, int num){
		// TODO: add || rhs.isClassTy()
		if(!num && rhs.isPointerTy()) return true;
		return super.refConvertsTo(rhs, num);
	}
	override bool implicitlyConvertsTo(Type rhs){
		if(super.implicitlyConvertsTo(rhs)) return true;
		auto rhsu = rhs.getHeadUnqual();
		return rhsu.isDynArrTy()
			|| rhsu is Type.get!EmptyArray()
			|| rhsu.isDelegateTy();
	}

	override ulong getSizeof(){
		// TODO: this is not true for all machines
		return Type.get!Size_t().getSizeof();
	}
}
mixin template Semantic(T) if(is(T==EmptyArrTy)){
	override bool refConvertsTo(Type rhs, int num){
		if(!num){
			if(rhs.isDynArrTy()) return true;
			if(auto arr = rhs.isArrayTy()) return arr.length == 0;
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
		//f = f.constFold(sc); // TODO: should this be done at all?
		if(f.isType()){
			sc.error(format("typeof argument '%s' is not an expression",e.loc.rep),e.loc);
			mixin(ErrEplg);
        }else e=f;

/+		if(!e.type){
			auto r=Type.get!void();
			mixin(RewEplg!q{r});
		}+/

		assert(!!e.type && e.type.sstate == SemState.completed,to!string(e)~" : "~to!string(e.type));

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

	override AggregateScope getMemberScope(){
		return decl.asc;
	}

	override string toString(){
		TemplateInstanceDecl tmpl;
		if(auto nsts=cast(NestedScope)decl.scope_)
		if(auto tmps=cast(TemplateScope)nsts.parent)
			tmpl=tmps.tmpl;
		if(tmpl && decl.name.name==tmpl.name.name)
			return decl.name.name~"!("~join(map!(to!string)(tmpl.args),",")~")";
		return decl.name.name;
	}
}


// statements

mixin template Semantic(T) if(is(T==Statement)){
	override void semantic(Scope sc){
		sc.error("unimplemented feature",loc);
		sstate = SemState.error;
	}
}

mixin template Semantic(T) if(is(T==EmptyStm)){
	override void semantic(Scope sc){
		sstate = SemState.completed;
	}
}

mixin template Semantic(T) if(is(T==BlockStm)){
	void semanticNoScope(Scope sc){
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

	override void semantic(Scope sc){
		if(!mysc) mysc = New!BlockScope(sc);
		semanticNoScope(mysc);
	}
private:
	Scope mysc = null;
	size_t current = 0; // points to the next child to be semantically analyzed
	invariant(){assert(sstate!=SemState.completed || current == s.length);}
}

mixin template Semantic(T) if(is(T==LabeledStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		sc.insertLabel(this);
		mixin(SemChld!q{s});
		mixin(SemEplg);
	}
}


mixin template Semantic(T) if(is(T==ExpressionStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChldExp!q{e});
		mixin(SemEplg);
	}
}

mixin template Semantic(T) if(is(T==IfStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(!tsc) tsc = New!BlockScope(sc);
		auto bl = Type.get!bool();
		e.expSemantic(tsc); // TODO: get rid of direct call
		mixin(PropRetry!q{e});
		if(e.sstate == SemState.completed){e=e.convertTo(bl); e.semantic(tsc);} // TODO: ditto
		if(e.sstate == SemState.completed) mixin(ConstFold!q{e});
		mixin(PropRetry!q{e});
		s1.semantic(tsc); // TODO: ditto
		mixin(PropRetry!q{s1});
		if(s2){
			if(!esc) esc = New!BlockScope(sc);
			s2.semantic(esc); // TODO: ditto
			mixin(PropErr!q{s2});
		}
		mixin(SemProp!q{e,s1});
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
		e.semantic(lsc); // TODO: ditto
		mixin(PropRetry!q{e});
		if(e.sstate == SemState.completed){e=e.convertTo(bl);e.semantic(lsc);} // TODO: ditto
		if(e.sstate == SemState.completed) mixin(ConstFold!q{e});
		s.semantic(lsc); // TODO: ditto
		mixin(SemProp!q{e,s});
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
		s.semantic(lsc); // TODO: ditto
		mixin(PropRetry!q{s}); // TODO: needed?
		mixin(SemChldPar!q{e});// TODO: propose SemChld!q{scope=lsc, e}
		mixin(PropRetry!q{e});
		if(e.sstate == SemState.completed){e=e.convertTo(bl);e.semantic(lsc);} // TODO: get rid of direct call
		if(e.sstate == SemState.completed) mixin(ConstFold!q{e});
		mixin(SemProp!q{s,e});
		mixin(SemEplg);
	}
private:
	BlockScope lsc;
}


mixin template Semantic(T) if(is(T==ForStm)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(!lscs1){lscs1 = New!BlockScope(sc);}
		if(s1){ // s1 is NoScope
			if(auto bl=s1.isBlockStm()) bl.semanticNoScope(lscs1);
			else s1.semantic(lscs1); // TODO: get rid of direct call
			mixin(PropRetry!q{s1});
		}
		if(!lsc){ lsc = New!BlockScope(lscs1); lsc.setLoopingStm(this); }
		if(e1){
			e1.semantic(lsc); // TODO: ditto
			mixin(PropRetry!q{e1});
			auto bl = Type.get!bool();
			if(e1.sstate == SemState.completed){e1=e1.convertTo(bl);e1.semantic(lsc);}// TODO: ditto
			if(e1.sstate == SemState.completed) mixin(ConstFold!q{e1});
			mixin(PropRetry!q{e1});
		}
		if(e2){
			e2.semantic(lsc); // TODO: ditto
			if(e2.sstate == SemState.completed) mixin(ConstFold!q{e2});
			mixin(PropRetry!q{e2});
		}
		s2.semantic(lsc); // TODO: ditto
		mixin(PropRetry!q{s2});
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
						mixin(SemProp!q{vars[0].rtype});
						if(!vars[0].type.implicitlyConvertsTo(s_t)){ // TODO: This is a stub
							sc.error(format("invalid type '%s' for index variable '%s'", vars[0].rtype.loc.rep, vars[0].name.toString()), vars[0].rtype.loc);
							sstate = SemState.error;
						}
					}else vars[0].type = s_t;
					curparam++;
				}
				if(curparam < vars.length){
					if(vars[curparam].rtype){
						vars[curparam].type = vars[curparam].rtype.typeSemantic(lsc);
						mixin(SemProp!q{vars[curparam].rtype});
						if(!et.implicitlyConvertsTo(vars[curparam].type)){
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
		mixin(SemProp!q{bdy});
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
		assert(fun && fun.type);
		// TODO: auto ref
		isRefReturn = cast(bool)(fun.type.stc&STCref);
		if(isRefReturn && (assert(!!e),!e.checkLvalue(sc,e.loc))) mixin(ErrEplg);

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


	// TODO: reduce DMD bug in presence of the out contract
	void presemantic(Scope sc){//out(result){
		//assert(result is this); // TODO: remove return type?
		//}body{ // insert into symbol table, but don't do the heavy processing yet
		if(sstate != SemState.pre) return;
		sstate = SemState.begin;
		if(!name){sc.error("unimplemented feature "~to!string(typeid(this)),loc); sstate = SemState.error; return;} // TODO: obvious
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

	FunctionDecl matchCall(scope Expression[] args, ref MatchContext context){
		return null;
	}
	void matchError(Scope sc, Location loc, scope Expression[] args){
		sc.error(format("%s '%s' is not callable",kind,name.toString()),loc);
	}

	TemplateDecl matchInstantiation(Expression[] args){
		return null;
	}
	void instantiationError(Scope sc, Location loc, scope Expression[] args){
		sc.error(format("can only instantiate templates, not %ss",kind),loc);
	}

	// TODO: make OO instead of functional?
	bool isDeclAccessible(Declaration decl)in{
		assert(decl.sstate != SemState.pre);
	}body{
		if( decl.stc&STCstatic
		|| decl.stc&STCenum && decl.isVarDecl() )
		//|| decl.isTemplateDecl() || decl.isTemplateInstanceDecl()) // TODO
			return true;
		auto enc = decl.scope_.getDeclaration();
		if(!enc) return true; // eg. delegate literals at module scope
		// if(this is enc) return true;
		if(this is enc) return !isAggregateDecl();
		for(Declaration dl=this; dl !is null && dl !is enc; dl=dl.scope_.getDeclaration()){
			if(dl.stc & STCstatic) return false;
			if(auto fn=dl.isFunctionDef()) fn.canBeStatic = false;
		}
		return true;
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
			mixin(PropRetry!q{meaning});
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

	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(rtype){
			type=rtype.typeSemantic(sc);
			mixin(PropRetry!q{rtype});
		}
		if(init){
			if(init.sstate!=SemState.completed){
				if(willInterpretInit()) init.prepareInterpret();
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

		if(!type||type.sstate==SemState.error) mixin(ErrEplg);

		assert(type.sstate == SemState.completed);

		if(auto tp = type.isTypeTuple()){
			alias tupleContext tc;
			auto len = tp.length;
			if(!tc) tc = New!TupleContext();
			ExprTuple et = null;
			if(init){
				et=init.isExprTuple();
				if(et){
					if(len!=et.length){
						sc.error(format("tuple of %d elements cannot be assigned to tuple of %d elements",et.length,len),loc);
						mixin(ErrEplg);
					}
				}else{
					init = et = New!ExprTuple(sc, len, init);
					mixin(SemChldPar!q{init});
				}
			}
			if(init) assert(et && et.length==len && init.sstate == SemState.completed);
			// TODO: gc allocations
			if(!tc.vds){
				tc.vds = new VarDecl[cast(size_t)len];
				foreach(i, ref x;tc.vds){
					auto id  = New!Identifier("__tuple_"~name.name~"_"~to!string(i));
					auto ini = init?et.index(sc,loc,i):null;
					x = New!VarDecl(stc, tp.index(sc,loc,i), id, ini);
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
					sym.loc = loc; // TODO: fix
					sym.scope_=scope_;
					x = sym;
				}
			}
			mixin(SemChld!q{tc.syms});
			if(!tc.tupleAlias){
				auto stpl = New!ExprTuple(sc,tc.syms); // TODO: can directly transfer ownership
				stpl.loc = loc;
				tc.tupleAlias = New!AliasDecl(STC.init, New!VarDecl(STC.init, stpl, name, null));
				tc.tupleAlias.sstate = SemState.begin;
				tc.tupleAlias.loc = loc;
				tc.tupleAlias.scope_=scope_;
			}
			mixin(SemChld!q{tc.tupleAlias});
			mixin(SemEplg); // Symbol will rewrite the meaning
		}

		type = type.applySTC(stc).checkVarDecl(sc,this);
		// add appropriate storage classes according to type
		stc |= type.getHeadSTC();
		// TODO: this is controversial, and should only be done for fields
		// if(stc&(STCimmutable|STCconst) && init) stc|=STCstatic;

		mixin(PropErr!q{type});

		if(init){
			mixin(SemChld!q{init});
			/+if(!init.implicitlyConvertsTo(type)){
				sc.error(format("initializing '%s' from incompatible type '%s'",rtype.loc.rep,init.type.toString()),loc);
				mixin(ErrEplg);
			}+/
			mixin(ImplConvertTo!q{init,type});
			if(willInterpretInit()){
				assert(init.sstate == SemState.completed, to!string(init));
				mixin(IntChld!q{init});
			}
		}else if(stc&STCenum){
			sc.error("manifest constants must have initializers",loc);
			mixin(ErrEplg);
		}
		mixin(SemEplg);
	}

	void matchError(Scope sc, Location loc, scope Expression[] args){
		sc.error(format("%s '%s' of type '%s' is not callable",kind,name.toString(),type.toString()),loc);
	}

	override @property string kind(){
		return isField?"field":"variable";
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
/+	protected struct PotentialDeclEntry{Identifier name; size_t degree;}
	abstract protected ???[] getRequiredSymbols();
	abstract protected PotentialDeclEntry[] getPotentiallyProvidedSymbols();+/
}


mixin template Semantic(T) if(is(T==StaticIfDecl)){
	override void presemantic(Scope sc){
		scope_=sc;
		if(sstate == SemState.pre) sstate = SemState.begin;
	}

	private Statement evaluate(Scope sc){
		mixin(SemPrlg);
		{
			cond.prepareInterpret();
			cond.prepareLazyConditionalSemantic();
			mixin(SemChld!q{cond});
		}
		mixin(ConvertTo!q{cond,Type.get!bool()});
		//cond = evaluateCondition(sc, cond);
		mixin(IntChld!q{cond});
		needRetry = false;
		if(cond.interpretV()){
			if(lazyDup) { lazyDup = false; bdy = bdy.ddup(); }
			if(auto d=bdy.isDeclaration()) d.pickupSTC(stc);
			return bdy;
		}else if(els){
			if(lazyDup) { lazyDup = false; els = els.ddup(); }
			if(auto d=els.isDeclaration()) d.pickupSTC(stc);
			return els;
		}else{
			lazyDup = false;
			mixin(SemEplg);
		}
	}

	override void buildInterface(){
		assert(!!scope_);
		auto r = evaluate(scope_).isDeclaration();
		if(r is this) return;
		assert(!!r);
		mixin(SemCheck);
		r.presemantic(scope_);
		mixin(RewEplg!q{r});
	}

	override void semantic(Scope sc){
		mixin(SemPrlg);
		needRetry = false;
		auto res = evaluate(sc);
		if(res is this) return;
		assert(!!res);
		mixin(SemCheck);
		if(auto decl = res.isDeclaration()) decl.presemantic(sc);
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
		if(a.length<1){
			sc.error("missing arguments to static assert", loc);
			mixin(ErrEplg);
		}else if(a.length>2){
			sc.error("too many arguments to static assert", loc);
			mixin(ErrEplg);
		}
		a[0].prepareInterpret();
		if(a.length==2) a[1].prepareInterpret();

		mixin(SemChld!q{a});
		auto bl=Type.get!bool();
		mixin(ImplConvertTo!q{a[0],bl});
		mixin(IntChld!q{a[0]});

		if(!a[0].interpretV()){
			// work around finally block goto limitation...
			enum printMessage = q{
				sc.error(format("static assertion failure: '%s' is false",a[0].loc.rep), loc);
			};
			if(a.length == 1) mixin(printMessage);
			else try{
				mixin(SemChld!q{a[1]});
				mixin(IntChld!q{a[1]});
				sc.error(a[1].interpretV().get!string(), loc);
			}finally if(sstate == SemState.error) mixin(printMessage);
			mixin(ErrEplg);
		}
		mixin(SemEplg);
	}
}

mixin template Semantic(T) if(is(T==AliasDecl)){
	override void semantic(Scope sc){
		if(sstate == SemState.pre) presemantic(sc);
		mixin(SemPrlg);
		if(!aliasee)
		if(auto vd = decl.isVarDecl()){
			if(vd.init){
				sc.error("alias declarations cannot have initializers",loc);
				mixin(ErrEplg);
			}
			aliasee = vd.rtype;
		}else if(auto fd = decl.isFunctionDecl()){
			aliasee = fd.type;
		}else assert(0);

		aliasee.weakenAccessCheck(AccessCheck.none);
		mixin(SemChld!q{aliasee});
		if(!aliasee.isSymbol() && !aliasee.isType() && !aliasee.isConstant() && !aliasee.isExprTuple()){
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
		if(auto et=r.isExprTuple()) et.accessCheck=check;
		return r;
	}

private:
	Expression aliasee;
}


mixin template Semantic(T) if(is(T==BlockDecl)){
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
			if(x.needRetry==2) mixin(PropRetry!q{x});
		}
		foreach(x; decls) mixin(PropRetry!q{x});
	}

	override void semantic(Scope sc){
		if(sstate == SemState.pre) presemantic(sc);
		mixin(SemPrlg);
		foreach(ref x; decls){
			x.semantic(sc); // TODO: get rid of direct call
			mixin(Rewrite!q{x});
			if(x.needRetry==2) mixin(PropRetry!q{x});
		}
		foreach(ref x; decls) mixin(PropRetry!q{x});
		mixin(PropErr!q{decls});
		mixin(SemEplg);
	}
}

mixin template Semantic(T) if(is(T==AggregateDecl)){
	override void presemantic(Scope sc){
		if(sstate != SemState.pre) return;
		if(auto aggr=sc.getAggregate())
			if(aggr.isValueAggregateDecl()||isValueAggregateDecl())
				stc|=STCstatic;

		super.presemantic(sc);

		scope_ = sc;
		if(!asc) asc = New!AggregateScope(this);

		bdy.presemantic(asc);
	}

	override void buildInterface(){
		mixin(SemPrlg);
		bdy.buildInterface();
		mixin(PropRetry!q{bdy});
	}

	override void semantic(Scope sc){
		if(sstate == SemState.pre) presemantic(sc);
		mixin(SemPrlg);
		bdy.semantic(asc);
		mixin(SemProp!q{bdy});
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
		layoutKnown = false;
	}

private:
	AggregateTy type;
	bool layoutKnown = true;
}


mixin template Semantic(T) if(is(T==Parameter)){
	override void presemantic(Scope sc){
		// NOTE: cannot rely on being in a function
		// parameters might be analyzed in the
		// template constraint scope as well
		if(!name.length) return;
		super.presemantic(sc);
	}

	final bool mustBeTypeDeducted(){
		return !type && !rtype && !init;
	}

}

mixin template Semantic(T) if(is(T==CArrayDecl)||is(T==CArrayParam)){

	override void semantic(Scope sc){
		while(postfix !is name){
			assert(!!cast(IndexExp)postfix);
			auto id = cast(IndexExp)cast(void*)postfix;
			postfix = id.e;
			id.e = rtype;
			rtype = id;
		}
		super.semantic(sc);
	}
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
}

abstract class OverloadableDecl: Declaration{ // semantic node
	this(STC stc,Identifier name){super(stc,name);}
	override OverloadableDecl isOverloadableDecl(){return this;}
}

class OverloadSet: Declaration{ // purely semantic node

	private bool _matchedOne = false; // TODO: remove

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
		assert(!decls.length||decls[0].name.name==decl.name.name);
		assert(!_matchedOne, "TODO!"); // TODO:
	}body{
		decls~=decl;
	}

	/* accessibility of overloads is checked after they have been resolved
	 */
	override bool needsAccessCheck(AccessCheck check){ return false; }

	override string toString(){return join(map!(to!string)(decls),"\n");}
	override OverloadSet isOverloadSet(){return this;}


	private static struct Matched{ // local structs cannot be qualified yet
		MatchContext context;      // TODO: move into matchCall
		FunctionDecl decl;
	}

	override FunctionDecl matchCall(scope Expression[] args, ref MatchContext context){
		_matchedOne = true;
		if(decls.length == 1) return decls[0].matchCall(args,context);
		auto matches = new Matched[decls.length]; // pointless GC allocation
		foreach(i,decl; decls){
			if(decl.sstate != SemState.error)
				matches[i].decl = decls[i].matchCall(args, matches[i].context);
		}

		foreach(i,decl; decls) if(matches[i].decl is null) matches[i].context.match = Match.none;

		auto best = reduce!max(map!(_=>_.context.match)(matches));
		if(best == Match.none){
			context.match = Match.none;
			altCand = -1;
			return null;
		}
		//TODO: the following line causes an ICE, reduce.
		//auto bestMatches = matches.partition!(_=>_.context.match!=best)();
		//auto numBest = bestMatches.length;
		size_t numBest = 0;
		for(size_t i=0;i<matches.length;i++){
			if(matches[i].context.match==best)
				swap(matches[numBest++], matches[i]);
		}
		if(numBest == 1){
			context = matches[0].context;
			return matches[0].decl;
		}
		auto bestMatches = matches[0..numBest];
		// find the most specialized match
		size_t candidate = 0;
		foreach(i, match; bestMatches[1..$]){
			// if there is a declaration that is at least as specialized
			// then it cannot be the unique best match
			if(match.decl.atLeastAsSpecialized(bestMatches[candidate].decl))
				candidate = i+1;
		}
		swap(bestMatches[0], bestMatches[candidate]);
		context = bestMatches[0].context;

		foreach(i, match; bestMatches[1..$]){
			if(!bestMatches[0].decl.atLeastAsSpecialized(match.decl)
			 || match.decl.atLeastAsSpecialized(bestMatches[0].decl)){
				// at least two identically good matches
				altCand = i+1;
				return null;
			}
		}
		altCand=candidate;
		return bestMatches[0].decl;
	}

	private size_t altCand; // TODO: somewhat fragile, maybe better to just recompute
	override void matchError(Scope sc, Location loc, scope Expression[] args){
		if(decls.length == 1) return decls[0].matchError(sc,loc,args);
		if(altCand==-1){
			sc.error(format("no matching function for call to '%s(%s)'",name,join(map!"a.type.toString()"(args),",")), loc);
			foreach(decl; decls){
				if(auto fdef = decl.isFunctionDecl())
					if(fdef.type.sstate == SemState.error) continue;
				sc.note("candidate function not viable", decl.loc);
			}
		}else{
			assert(0 != altCand);
			// TODO: list all of the most specialized functions
			sc.error(format("call to '%s' is ambiguous",name), loc);
			sc.note("candidate function",decls[0].loc);
			sc.note("candidate function",decls[altCand].loc);
		}
	}

	override TemplateDecl matchInstantiation(Expression[] args){
		int n;
		TemplateDecl w = null;
		foreach(x; decls){
			if(auto td = x.isTemplateDecl()){
				n++;
				w = td;
			}
		}
		if(n==1) return w.matchInstantiation(args);
		return null; // TODO!
	}

	override void instantiationError(Scope sc, Location loc, scope Expression[] args){
		int n;
		TemplateDecl w = null;
		foreach(x; decls){
			if(auto td = x.isTemplateDecl()){
				n++;
				w = td;
			}
		}
		if(n==1) return w.instantiationError(sc,loc,args);
		return super.instantiationError(sc,loc,args);
	}

// private: // TODO: introduce again, temporary hack in BinaryExp!(Tok!"&")
	OverloadableDecl[] decls;
}

mixin template Semantic(T) if(is(T==FunctionDecl)){
	final public void propagateSTC(){
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
	override void semantic(Scope sc){
		mixin(SemPrlg);
		propagateSTC();
		if(type.hasAutoReturn()){
			sc.error("function body required for return type inference",loc);
			mixin(ErrEplg);
		}
		mixin(SemChld!q{type});
		mixin(SemEplg);
	}

	private bool isMemberFunction(){
		if(auto decl=scope_.getDeclaration()) return !!decl.isAggregateDecl();
		return false;
	}
	override bool needsAccessCheck(AccessCheck check){
		if(check==AccessCheck.memberFuns) return isMemberFunction();
		return super.needsAccessCheck(check);
	}

	override FunctionDecl matchCall(scope Expression[] args, ref MatchContext context){
		// semantically analyze the type if necessary
		type.semantic(scope_); // TODO: get rid of direct call
		mixin(SemProp!q{type});
		return type.matchCall(args,context) ? this : null;
	}

	bool atLeastAsSpecialized(FunctionDecl rhs){
		MatchContext dummy;
		// GC allocations, unneeded
		// TODO: allocate this on the stack
		auto pt = array(map!(function Expression (_)=>new StubExp(_.type))(type.params));
		return !!rhs.matchCall(pt, dummy);
	}

	override void matchError(Scope sc, Location loc, scope Expression[] args){
		alias util.any any; // TODO: file bug
		if(args.length > type.params.length ||
		   any!(_=>_.init is null)(type.params[args.length..type.params.length])){
			sc.error(format("too %s arguments to function '%s'",args.length<type.params.length?"few":"many", signatureString()[0..$-1]),loc);
			sc.note("declared here",this.loc);
			return;
		}
		int num=0;
		InoutRes inoutRes;
		auto at = new Type[args.length];
		foreach(i,p; type.params){
			at[i] = p.type.adaptTo(args[i].type, inoutRes);
		}
		foreach(ref x;at) x = x.resolveInout(inoutRes);
		foreach(i,p; type.params){
			if(!args[i].implicitlyConvertsTo(at[i])) num++;
		}
		if(num>1){
			sc.error(format("incompatible argument types (%s) to function '%s'", join(map!"a.type.toString()"(args),","),signatureString()[0..$-1]),loc);
			sc.note("declared here",this.loc);
		}else{
			foreach(i,p; type.params){
				void displayNote(){
					if(p.name) sc.note(format("while matching function parameter '%s'",p.name),p.loc);
					else sc.note("while matching function parameter",p.loc);

				}
				if(!(p.stc & STCbyref)){
					if(!args[i].implicitlyConvertsTo(at[i])){
						if(args[i].sstate == SemState.error) continue;
						// trigger consistent error message
						args[i].implicitlyConvertTo(at[i]).semantic(sc);
						displayNote();
						break;
					}
				}else if(p.stc&STCref){
					if(args[i].checkLvalue(sc, args[i].loc)){
						sc.error(format("type of 'ref' argument '%s' does not match parameter type '%s'",args[i].type.toString(),p.type.toString()),loc);
						displayNote();
						break;
					}
				}else{// if(p.stc&STCout){
					assert(p.stc&STCout);
					if(!args[i].checkMutate(sc, args[i].loc)){
						displayNote();
						break;
					}
					if(!p.type.refConvertsTo(args[i].type,1)){
						sc.error(format("incompatible argument type '%s' for 'out' parameter of type '%s'", args[i].type, p.type),loc);
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
		size_t nump = 0;
		foreach(x;type.params) if(x.mustBeTypeDeducted()) nump++;
		// TODO: gc allocations
		TemplateParameter[] tparams = new TemplateParameter[nump];
		immutable static string namebase = "__T";
		size_t j=-1;
		// TODO: can the scope be kept clean by using some tricks?
		foreach(i,ref x; tparams){
			while(!type.params[++j].mustBeTypeDeducted()) {}
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

		auto alias_ = New!AliasDecl(STC.init, New!VarDecl(STC.init,New!(UnaryExp!(Tok!"&"))(New!Identifier(name.name)),New!Identifier(tmplname),Expression.init));

		auto t=New!TemplateDecl(false,STC.init, New!Identifier(tmplname),
		                        tparams, Expression.init,
		                        New!BlockDecl(STC.init,[cast(Declaration)this,alias_]));

		t.loc = loc;
		return t;
	}
}

mixin template Semantic(T) if(is(T==FunctionDef)){
	override void semantic(Scope sc){
		mixin(SemPrlg);
		propagateSTC();
		if(sstate == SemState.pre){
			presemantic(sc); // add self to parent scope
			if(sstate == SemState.error) needRetry=false;
		}
		if(!fsc){
			fsc = New!FunctionScope(sc, this);
			foreach(p; type.params){
				if(p.sstate == SemState.pre) p.sstate = SemState.begin;
				if(p.name) if(!fsc.insert(p)) p.sstate = SemState.error;
			}
		}

		foreach(x; type.params){
			x.semantic(fsc);
			assert(!x.rewrite);
			mixin(PropRetry!q{x});
		}

		mixin(SemChldPar!q{type});

		if(type.sstate == SemState.error) sstate = SemState.error, needRetry=false;

		bdy.semanticNoScope(fsc);
		if(sstate != SemState.error) mixin(PropRetry!q{bdy}); // TODO: is this ok?

		if(type.hasUnresolvedReturn()){
			// foo
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
	bool canBeStatic = true;
}

mixin template Semantic(T) if(is(T==PragmaDecl)){
	override void presemantic(Scope sc){
		if(sstate != SemState.pre) return;
		if(auto b=bdy.isDeclaration()) b.presemantic(sc);
		sstate = SemState.begin;
	}
	override void semantic(Scope sc){
		mixin(SemPrlg);
		if(args.length<1){sc.error("missing arguments to pragma",loc); mixin(ErrEplg);}
		if(auto id=args[0].isIdentifier()){
			bool intprt = true;
			switch(id.name){
				case "__p":
					intprt = false;
				case "msg":
					if(args.length<2){if(bdy)mixin(SemChld!q{bdy}); mixin(SemEplg);}
					//foreach(ref x; args[1..$]) x = x.semantic(sc);
					//mixin(SemChldPar!q{args[1..$]});
					auto a = args[1..$];
					foreach(x; a) x.prepareInterpret();
					foreach(ref x;a) mixin(SemChld!q{x});
					foreach(ref x; a)
						if(!x.isType() && !x.isExprTuple() && intprt){
							mixin(IntChld!q{x});
						}

					import std.stdio;
					foreach(x; a)
						if(!x.isType() && !x.isExprTuple() && intprt)
							stderr.write(x.interpretV().get!string());
						else stderr.write(x.toString());
					stderr.writeln();
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
						auto ty=args[1].type.isIntegral();
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
	static if(is(R==Declaration)){
		override void presemantic(Scope sc){
			if(sstate != SemState.pre) return;
			scope_ = sc;
			sstate = SemState.begin;
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
	}
	private R evaluate(Scope sc){
		mixin(SemPrlg);
		if(a.length<1){
			sc.error("missing arguments to string mixin", loc);
			mixin(ErrEplg);
		}else if(a.length>2){
			sc.error("too many arguments to string mixin", loc);
			mixin(ErrEplg);
		}

		a[0].prepareInterpret();
		mixin(SemChld!q{a});
		int which;
		Type[3] types = [Type.get!(const(char)[])(),
		                 Type.get!(const(wchar)[])(),
		                 Type.get!(const(dchar)[])()];
		foreach(i,t;types) if(!which && a[0].implicitlyConvertsTo(t)) which=cast(int)i+1;
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

		static if(is(T==MixinExp)) auto r=parseExpression(src,sc.handler);
		else static if(is(T==MixinStm)) auto r=New!BlockStm(parseStatements(src,sc.handler)); // TODO: use CompoundStm instead
		else static if(is(T==MixinDecl)) auto r=New!BlockDecl(STC.init,parseDeclDefs(src,sc.handler));
		else static assert(0);

		if(sc.handler.nerrors != nerrors) mixin(ErrEplg);

		static if(is(T==MixinStm)) r.semanticNoScope(sc);
		else static if(is(T==MixinExp)) r.semantic(sc);
		else static if(is(T==MixinDecl)) r.pickupSTC(stc);
		else static assert(0);
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
		if(is(T==MixinDecl)) r.semantic(sc);
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
