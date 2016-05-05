// Written in the D programming language.

import lexer, expression, semantic, scope_, type;
import util;
import std.string;
import std.conv: to;
import std.typecons : q=tuple, Q=Tuple;
import std.algorithm : max;

private template NotYetImplemented(T){
	static if(is(T _==BinaryExp!S,TokenType S) || is(T==ABinaryExp) || is(T==AssignExp))
		enum NotYetImplemented = false;
	else static if(is(T _==UnaryExp!S,TokenType S)||is(T _==PostfixExp!S,TokenType S))
		enum NotYetImplemented = false;
		else enum NotYetImplemented = !is(T==Expression) && !is(T==ExpTuple) && !is(T:Type) && !is(T:Symbol) && !is(T==FieldExp) && !is(T:LiteralExp) && !is(T==CastExp) && !is(T==ArrayLiteralExp) && !is(T==IndexExp) && !is(T==SliceExp) && !is(T==TernaryExp) && !is(T==CallExp) && !is(T==UFCSCallExp) && !is(T==MixinExp) && !is(T==IsExp) && !is(T==AssertExp) && !is(T==LengthExp) && !is(T==PtrExp) && !is(T==DollarExp) && !is(T==CurrentExp) && !is(T==ThisExp) && !is(T==SuperExp) && !is(T==TemporaryExp) && !is(T==TmpVarExp) && !is(T==StructConsExp) && !is(T==NewExp);
}

enum IntFCEplg = mixin(X!q{needRetry = false; @(SemRet);});
template IntFCChldNoEplg(string s){
	enum IntFCChldNoEplg = {
		string r;
		auto ss=s.split(",");
		foreach(t; ss){
			r~=mixin(X!q{
				@(t)._interpretFunctionCalls(sc);
				mixin(PropRetry!(q{@(t)},false));
			});
		}
		return r~PropErr!s;
	}();
}
template IntFCChld(string s){
	enum IntFCChld=IntFCChldNoEplg!s~IntFCEplg;
}

// should never be interpreted:
mixin template Interpret(T) if(is(T==MixinExp) || is(T==IsExp)){
	override bool checkInterpret(Scope sc){assert(0);}
	override void interpret(Scope sc){assert(0);}
	override void _interpretFunctionCalls(Scope sc){assert(0);}
}
mixin template Interpret(T) if(is(T:Expression) && NotYetImplemented!T){
	override void interpret(Scope sc){
		assert(sc, "expression "~toString()~" was assumed to be interpretable");
		sc.error(format("expression '%s' is not interpretable at compile time yet %s",toString(),typeid(this)),loc);
		mixin(ErrEplg);
	}
}

mixin template Interpret(T) if(is(T==Expression)){

	final void prepareInterpret(){
		weakenAccessCheck(AccessCheck.ctfe);
	}

	final void prepareLazyConditionalSemantic(){
		static struct ApplyLazyConditionalSemantic{
			void perform(BinaryExp!(Tok!"||") self){ self.lazyConditionalSemantic = true; }
			void perform(BinaryExp!(Tok!"&&") self){ self.lazyConditionalSemantic = true; }
		}
		runAnalysis!ApplyLazyConditionalSemantic(this);
	}

	// scope may be null if it is evident that the expression can be interpreted
	bool checkInterpret(Scope sc)in{assert(sstate == SemState.completed);}body{
		assert(sc, loc.rep);
		sc.error(format("%s '%s' is not interpretable at compile time",kind,loc.rep),loc);
		mixin(SetErr!q{});
		return false;
	}
	static int numint = 0;
	void interpret(Scope sc)in{
		assert(sstate == SemState.completed);
	}body{
		if(rewrite) return;

		void fixupLocations(Expression r){
			r.loc=loc;
			r.type=type;
			//pragma(msg, __traits(allMembers,ArrayLiteralExp)); // TODO: report bug
			if(auto tl = isArrayLiteralExp()){
				if(auto rl = r.isArrayLiteralExp())
					copyLocations(rl,tl);
			}
		}

		//assert(!numint);
		if(isAConstant()) return;
		if(!checkInterpret(sc)) mixin(ErrEplg);
		_interpretFunctionCalls(sc);
		auto x = this;
		mixin(Rewrite!q{x});
		fixupLocations(x);
		if(this is x) mixin(SemCheck);
		else mixin(SemProp!q{x});
		auto r = x.interpretV().toExpr();
		r.dontConstFold();
		if(this is r) mixin(SemCheck);
		fixupLocations(r);
		assert(!isConstant() || !needRetry); // TODO: file bug, so that this can be 'out'
		rewrite = null;
		if(this !is r) mixin(RewEplg!q{r});
	}

	Variant interpretV()in{assert(sstate == SemState.completed, to!string(this));}body{
		//return Variant.error(format("expression '%s' is not interpretable at compile time"),loc.rep);
		return Variant("TODO: cannot interpret "~to!string(this)~" yet",Type.get!string());
		//return Variant.init;
	}

	final Expression cloneConstant()in{assert(!!isConstant()||isArrayLiteralExp());}body{
		auto r = interpretV().toExpr();
		r.type = type;
		if(isArrayLiteralExp()){
			assert(cast(LiteralExp)r);
			r = (cast(LiteralExp)cast(void*)r).toArrayLiteral();
		}
		return r;
	}

	// for interpret.d internal use only, protection system cannot express this.
	void _interpretFunctionCalls(Scope sc){}
}

// TODO: investigate the void[][] = [[[2]]]; case some more
void copyLocations(ArrayLiteralExp r, ArrayLiteralExp a){
	assert(r.lit.length == a.lit.length);
	foreach(i,x;a.lit){
		r.lit[i].loc = x.loc;
		if(auto rl = r.lit[i].isArrayLiteralExp()){
			if(auto al = x.isArrayLiteralExp()){
				copyLocations(rl, al);
			}
		}
	}
}

mixin template Interpret(T) if(is(T==CastExp)){
	override bool checkInterpret(Scope sc){
		if(e.sstate != SemState.completed) return true;
		bool sanityCheck(){
			auto t1=e.type.getHeadUnqual(), t2=type.getHeadUnqual();
			auto cvt1=t1, cvt2=t2;
			if(auto e1=t1.isEnumTy()) cvt1=e1.decl.base;
			if(auto e2=t2.isEnumTy()) cvt2=e2.decl.base;
			assert(cvt1&&cvt2);
			// TODO: comprehensive treatment of unique expressions
			if(e.isUnique()) cvt1=t1.getUnqual(), cvt2=t2.getUnqual();
			if(cvt1.equals(cvt2)) return true;
			auto impld = cvt1.implicitlyConvertsTo(cvt2);
			assert(!impld.dependee); // analysis has already determined this
			if(impld.value||cvt1.isBasicType()&&cvt2.isBasicType()) return true;

			auto t1u=t1.getUnqual();
			if(t1u is Type.get!(void[])() && t2.isDynArrTy()||
			   t1u is Type.get!(void*)() && t2.isPointerTy())
				return true;

			auto le=e.isLiteralExp();
			auto el = type.getElementType();
			if(el&&le&&le.isPolyString()&&el.getHeadUnqual() !is Type.get!void())
				return !!type.getHeadUnqual().isSomeString();
			return false;
		}
		if(!sanityCheck()){
			sc.error(format("cannot interpret cast from '%s' to '%s' at compile time",e.type,type),loc);
			return false;
		}
		return e.checkInterpret(sc);
	}
	override Variant interpretV(){
		auto le=e.isLiteralExp(); // polysemous string literals might be cast
		auto el = type.getElementType();
		if(el&&le&&le.isPolyString()&&el.getHeadUnqual() !is Type.get!void()){
			auto vle=e.interpretV();
			auto typeu = type.getHeadUnqual();
			if(typeu.isSomeString()) return vle.convertTo(type);
			// TODO: allocation ok?
			Variant[] r = new Variant[vle.length];
			foreach(i,ref x;r) x = vle[i].convertTo(el);
			return Variant(r,r,type);
		}else return e.interpretV().convertTo(type);
	}

	override void _interpretFunctionCalls(Scope sc){
		mixin(IntFCChldNoEplg!q{e});
		if(!invokedSemantic){
			sstate=SemState.begin;
			needRetry=false;
			semantic(sc);
		}
		if(needRetry){ sstate=SemState.completed; return; }
		invokedSemantic=true;
		mixin(IntChld!q{e});
		auto t1u=e.type.getUnqual(), t2=type.getHeadUnqual();
		if(t1u is Type.get!(void[])() && t2.isDynArrTy()||
		   t1u is Type.get!(void*)() && t2.isPointerTy()){
			auto cnt=e.interpretV().getContainer();
			auto ty2=t2.isDynArrTy()?t2.getElementType():t2.isPointerTy().ty;
			auto t1=null;
			if(cnt.length){
				auto ty1=cnt[0].getType();
				mixin(RefConvertsTo!q{bool c; ty1, ty2, 0});
				if(!c){
					sc.error(format("cannot interpret cast from '%s' aliasing a '%s' to '%s' at compile time", e.type,t2.isDynArrTy()?ty1.getDynArr():ty1.getPointer(),type), loc); // TODO: 'an'
					mixin(ErrEplg);
				}
			}
		}
		mixin(IntFCEplg);
	}
private:
	bool invokedSemantic=false;
}

mixin template Interpret(T) if(is(T==Type)){
	override bool checkInterpret(Scope sc){return true;}
	override void interpret(Scope sc){return this;}
}mixin template Interpret(T) if(!is(T==Type) && is(T:Type)){}

mixin template Interpret(T) if(is(T==Symbol)){
	override bool checkInterpret(Scope sc){
		if(meaning.sstate == SemState.error) return false;
		if(isConstant()) return true;
		return super.checkInterpret(sc);
	}

	override Variant interpretV(){
		if(auto vd = meaning.isVarDecl()){
			assert(meaning.sstate == SemState.completed);
			assert(vd.init, text(this," ",loc));
			return vd.init.interpretV();
		}
		assert(0);
	}

	override void _interpretFunctionCalls(Scope sc){
		makeStrong(); // TODO: maybe not optimal
		return semantic(scope_);
	}

}mixin template Interpret(T) if(is(T==Identifier)||is(T==ModuleIdentifier)){}

mixin template Interpret(T) if(is(T==FieldExp)){
	override bool checkInterpret(Scope sc){
		// more or less duplicated above
		if(!e2.meaning.isVarDecl()) return false;
		if(e2.meaning.sstate == SemState.error) return false;
		if(e2.isConstant()) return true;
		auto this_=e1.extractThis();
		return this_&&this_.checkInterpret(sc);
	}

	override Variant interpretV(){
		if(e2.isConstant()) return e2.interpretV();
		auto value=e1.interpretV();
		auto aggr=value.get!(Variant[VarDecl])();
		// TODO: handle the case when the variable decl does not occur
		assert(cast(VarDecl)e2.meaning);
		return aggr[cast(VarDecl)cast(void*)e2.meaning];
	}

	override void _interpretFunctionCalls(Scope sc){
		mixin(IntFCChld!q{e1});
	}
}
mixin template Interpret(T) if(is(T==BinaryExp!(Tok!"."))){ } // (workaround for DMD bug)

mixin template Interpret(T) if(is(T==LengthExp)||is(T==PtrExp)){
	override bool checkInterpret(Scope sc){
		return e.checkInterpret(sc);
	}
	override Variant interpretV(){
		static if(is(T==LengthExp)) return Variant(e.interpretV().length, type);
		else return e.interpretV().ptr;
	}

	override void _interpretFunctionCalls(Scope sc){
		mixin(IntFCChld!q{e});
	}
}

mixin template Interpret(T) if(is(T==DollarExp)){
	override bool checkInterpret(Scope sc){ return true; }
	ulong ivalue = 0xDEAD_BEEF__DEAD_BEEF;
	override Variant interpretV(){ return Variant(ivalue, Type.get!Size_t()); }

	static void resolveValue(Expression[] e, ulong value){
		static struct DollarResolve{
			ulong value;
			void perform(DollarExp self){ self.ivalue = value; }


			// crosstalk between const-folding and bytecode
			// interpretation. see CTFEInterpret!DollarExp
			// for the rest of the implementation
			// TODO: this could be done by rewriting dollar exp
			// instead of saving a value in the existing exp
			void perform(Symbol self){
				if(self.isFunctionLiteral)
				if(auto fd=self.meaning.isFunctionDef)
					runAnalysis!DollarResolve(fd, value);
			}
		}
		foreach(x;e) runAnalysis!DollarResolve(x, value);
	}
}

mixin template Interpret(T) if(is(T==CurrentExp)||is(T==ThisExp)||is(T==SuperExp)){}

mixin template Interpret(T) if(is(T==LiteralExp)){
	private template getTokOccupied(T){
		enum vocc = to!string(getOccupied!T);
		static if(vocc == "wstr") enum occ = "str";
		else static if(vocc == "dstr") enum occ = "str";
		else static if(vocc == "fli80") enum occ = "flt80";
		else enum occ = vocc;
		enum getTokOccupied = occ;
	}
	private Variant value;
	this(Token lit){ // TODO: suitable contract
		this.lit=lit;
		if(lit.type==Tok!"true") lit.int64=1;
		else if(lit.type==Tok!"false") lit.int64=0;
		swtch:switch(lit.type){
			foreach(x; ToTuple!literals){
				static if(x!="null"){
					alias typeof(mixin(x)) U;
					enum occ = getTokOccupied!U;
					static if(x=="``w"||x=="``d"){
						case Tok!x: value=Variant(to!U(mixin(`lit.`~occ)),Type.get!U()); break swtch;
					}else static if(x==".0fi"||x==".0i"||x==".0Li"){
						case Tok!x: value=Variant(cast(U)(mixin(`lit.`~occ)*1i),Type.get!U()); break swtch;
					}else{
						case Tok!x: value=Variant(cast(U)mixin(`lit.`~occ),Type.get!U()); break swtch;
					}
				}else{
					// TODO: DMD allows Variant(null). Why?
					case Tok!x: value=Variant(null,Type.get!(typeof(null))()); break swtch;
				}
			}
			default: assert(0, to!string(lit.type));
		}
	}
	this(Variant value){ this.value = value; }

	static LiteralExp create(alias New=New,T)(T val){//workaround for long standing bug
		auto le = New!LiteralExp(Variant(val));
		le.semantic(null);
		assert(!le.rewrite);
		return le;
	}


	override bool checkInterpret(Scope sc){ return true; }
	override void interpret(Scope sc){ }
	override Variant interpretV(){ return value; }

	final ArrayLiteralExp toArrayLiteral()in{
		assert(!!type.getElementType());
		assert(!type.isSomeString());
	}body{
		auto arr=value.get!(Variant[])();
		// TODO: allocation ok?
		Expression[] lit = new Expression[arr.length];
		foreach(i,ref x;lit){
			x = arr[i].toExpr();
			if(x.type.getElementType()&&!x.type.isSomeString())
				if(auto le=x.isLiteralExp()){
					x=le.toArrayLiteral();
					continue;
				}
		}
		// TODO: this sometimes leaves implicit casts from typeof([]) in the AST...
		auto r=New!ArrayLiteralExp(lit);
		r.loc=loc;
		r.type=type;
		r.semantic(null); // TODO: ok?
		assert(!r.rewrite);
		return r;
	}
}

mixin template Interpret(T) if(is(T==ArrayLiteralExp)){
	override bool checkInterpret(Scope sc){
		// TODO: this is a kludge
		foreach(x; lit) if(auto ce=x.isCommaExp()) if(ce.e1.isTmpVarExp()) return true;
		bool ok = true;
		foreach(x; lit) if(!x.checkInterpret(sc)) ok=false;
		if(litLeftover && !litLeftover.checkInterpret(sc)) ok=false;
		return ok;
	}

	override Variant interpretV(){
		// TODO: this GC allocation is probably justified
		Variant[] res = new Variant[lit.length];
		foreach(i, ref x; res) x = lit[i].interpretV();
		return Variant(res,res,type);
	}

	override void _interpretFunctionCalls(Scope sc){
		// TODO: this is a kludge
		foreach(x; lit)
			if(auto ce=x.isCommaExp())
				if(auto tmpv=ce.e1.isTmpVarExp())
					return callWrapper(sc,tmpv.ctfeCallWrapper,null);

		foreach(ref x; lit){
			x._interpretFunctionCalls(sc);
			mixin(PropRetry!q{x});
		}
		if(litLeftover){
			litLeftover._interpretFunctionCalls(sc);
			mixin(SemProp!q{litLeftover});
		}
		mixin(PropErr!q{lit});
		mixin(IntFCEplg);
	}
}

mixin template Interpret(T) if(is(T==IndexExp)){
	override bool checkInterpret(Scope sc){
		assert(a.length<=1);
		return e.checkInterpret(sc)&(!a.length||a[0].checkInterpret(sc))
			&(!aLeftover||aLeftover.checkInterpret(sc));
	}
	override Variant interpretV(){
		if(a.length==0) return e.interpretV();
		assert(a.length==1);
		if(e.type.getUnqual() is Type.get!(void[])())
			return Variant(null, Type.get!void());
		auto lit = e.interpretV();
		auto ind = a[0].interpretV();
		return lit[ind];
	}

	override void _interpretFunctionCalls(Scope sc){
		e._interpretFunctionCalls(sc);
		if(e.sstate == SemState.completed){
			e.interpret(sc);
			mixin(Rewrite!q{e});
		}
		if(ascope.dollar){
			mixin(SemProp!q{e});
			auto len = e.interpretV().length;
			DollarExp.resolveValue(a, len);
			if(aLeftover) DollarExp.resolveValue((&aLeftover)[0..1], len);
		}
		if(a.length){
			assert(a.length==1);
			a[0]._interpretFunctionCalls(sc);
		}
		if(aLeftover){
			aLeftover._interpretFunctionCalls(sc);
			mixin(SemProp!q{aLeftover});
		}
		if(a.length) mixin(SemProp!q{a[0]});
		mixin(SemProp!q{e});
		if(a.length==1){
			auto len = e.interpretV().length;
			a[0].interpret(sc);
			mixin(SemProp!q{a[0]});
			if(a[0].interpretV().get!ulong()>=len){
				sc.error(format("array index %s is out of bounds [0%s..%d%s)",
				         a[0].toString(), Size_t.suffix, len, Size_t.suffix), a[0].loc);
				mixin(ErrEplg);
			}
		}
		mixin(IntFCEplg);
	}
}

mixin template Interpret(T) if(is(T==SliceExp)){
	override bool checkInterpret(Scope sc){
		return e.checkInterpret(sc) & l.checkInterpret(sc) & r.checkInterpret(sc);
	}
	override Variant interpretV(){
		auto lit=e.interpretV();
		return lit[l.interpretV()..r.interpretV()];
	}

	override void _interpretFunctionCalls(Scope sc){
		e._interpretFunctionCalls(sc);

		if(ascope.dollar){
			mixin(SemProp!q{e});
			auto len = e.interpretV().length;
			Expression[2] e = [l,r];
			DollarExp.resolveValue(e[], len);
		}

		l._interpretFunctionCalls(sc);
		r._interpretFunctionCalls(sc);
		mixin(SemProp!q{l,r});
		if(e.sstate == SemState.completed){
			e.interpret(sc);
			mixin(Rewrite!q{e});
		}
		l.interpret(sc);
		r.interpret(sc);
		mixin(SemProp!q{e,l,r});
		auto len = e.interpretV().length;
		auto a = l.interpretV().get!ulong();
		auto b = r.interpretV().get!ulong();

		if(a>len || b>len){
			sc.error(format("slice indices [%s..%s] are out of bounds [0%s..%d%s]",
			                l.toString(),r.toString(),Size_t.suffix,len,Size_t.suffix),
			         l.loc.to(r.loc));
			mixin(ErrEplg);
		}
		if(a>b){
			sc.error("lower slice index exceeds upper slice index",l.loc.to(r.loc));
			mixin(ErrEplg);
		}
		mixin(IntFCEplg);
	}
}

mixin template Interpret(T) if(is(T==AssertExp)){
	override bool checkInterpret(Scope sc){
		foreach(x; a) if(auto ce=x.isCommaExp()) if(ce.e1.isTmpVarExp()) return true;
		return a[0].checkInterpret(sc) & (!aLeftover||aLeftover.checkInterpret(sc));
	}
	override Variant interpretV(){return Variant(null,Type.get!void());}

	override void _interpretFunctionCalls(Scope sc){
		// TODO: this is a kludge
		foreach(x; a)
			if(auto ce=x.isCommaExp())
				if(auto tmpv=ce.e1.isTmpVarExp())
					return callWrapper(sc,tmpv.ctfeCallWrapper,null);

		a[0]._interpretFunctionCalls(sc);
		mixin(PropRetry!q{a[0]});
		if(a.length>1){
			a[1]._interpretFunctionCalls(sc);
			mixin(PropRetry!q{a[1]});
		}
		mixin(PropErr!q{a});
		auto cond = a[0].interpretV();
		if(aLeftover){
			aLeftover._interpretFunctionCalls(sc);
			mixin(SemProp!q{aLeftover});
		}
		if(!cond){
			if(a.length<2||!a[1].checkInterpret(sc)){
				if(a[0].loc.rep=="false"||a[0].loc.rep=="0")
					// don't state the obvious:
					sc.error("assertion failure", loc);
				else sc.error(format("assertion failure: %s is false",a[0].loc.rep), loc);
			}else{
				auto expr = a[1];
				sc.error(expr.interpretV().get!string(), loc);
			}
			mixin(ErrEplg);
		}
		mixin(IntFCEplg);
	}
}

mixin template Interpret(T) if(is(T _==UnaryExp!S,TokenType S)){
	static if(is(T _==UnaryExp!S,TokenType S)):
	static if(S==Tok!"&"||S==Tok!"*"){
		// TODO: some operations may be handled more efficiently than invoking byte code
		// compilation by doing direct computation.
		override bool checkInterpret(Scope sc){
			return e.checkInterpret(sc);
		}
		override void _interpretFunctionCalls(Scope sc){
			callWrapper(sc,ctfeCallWrapper,null);
		}
	private:
		FunctionDef ctfeCallWrapper;

	}else static if(S!=Tok!"++"&&S!=Tok!"--"):
	override bool checkInterpret(Scope sc){return e.checkInterpret(sc);}
	override Variant interpretV(){
		return e.interpretV().opUnary!(TokChars!S)();
	}

	override void _interpretFunctionCalls(Scope sc){mixin(IntFCChld!q{e});}
}

mixin template Interpret(T) if(is(T _==PostfixExp!S,TokenType S)){}

mixin template Interpret(T) if(is(T==ExpTuple)){
	override bool checkInterpret(Scope sc){
		bool r=true;
		if(isConstant()) return r;
		foreach(x;exprs) r&=x.checkInterpret(sc);
		return r;
	}
	override Variant interpretV(){
		auto vals=new Variant[](exprs.length);
		foreach(i,x;exprs) vals[i]=exprs[i].interpretV();
		assert(!!cast(TypeTuple)type);
		return Variant(vals, cast(TypeTuple)cast(void*)type);
	}
}

mixin template Interpret(T) if(is(T==ABinaryExp)||is(T==AssignExp)){}
mixin template Interpret(T) if(is(T _==BinaryExp!S, TokenType S) && !is(T==BinaryExp!(Tok!"."))){
	static if(is(T _==BinaryExp!S, TokenType S)):
	static if(!isAssignOp(S)):
	override bool checkInterpret(Scope sc){
		static if(S==Tok!",") if(e1.isTmpVarExp()) return true;
		return e1.checkInterpret(sc)&e2.checkInterpret(sc);
	}
	override Variant interpretV(){
		// first two conditions are a workaround for a segfault in DMD
		static if(S==Tok!"is"){
			return Variant(!e1.interpretV().opBinary!"!is"(e2.interpretV),Type.get!bool());
		}else static if(S==Tok!"in"){
			return Variant(!e1.interpretV().opBinary!"!in"(e2.interpretV),Type.get!bool());
		}else static if(S==Tok!","){
			return e2.interpretV();
		}else static if(isRelationalOp(S)||isArithmeticOp(S)||isBitwiseOp(S)||isShiftOp(S)||isLogicalOp(S))
			return e1.interpretV().opBinary!(TokChars!S)(e2.interpretV());
		else static if(S==Tok!"~"){
			// TODO: this might be optimized. this gc allocates
			// TODO: get rid of bulky string special casing code
			if(auto ety = e1.type.getElementType()){
				if(ety.getUnqual().equals(e2.type.getUnqual())){
					Variant rhs = e2.interpretV();
					if(ety is Type.get!(immutable(char))())
						rhs = Variant(""c~rhs.get!char(),type);
					else if(ety is Type.get!(immutable(wchar))())
						rhs = Variant(""w~rhs.get!wchar(),type);
					else if(ety is Type.get!(immutable(dchar))())
						rhs = Variant(""d~rhs.get!dchar(),type);
					else{ auto r=[rhs];rhs = Variant(r,r,ety.getDynArr()); }
					return e1.interpretV().opBinary!"~"(rhs);
				}
			}

			if(auto ety = e2.type.getElementType()){
				if(e1.type.getUnqual().equals(ety.getUnqual())){
				   auto lhs = e1.interpretV();
				   if(ety is Type.get!(immutable(char))())
					   lhs = Variant(""c~lhs.get!char(),ety);
				   else if(ety is Type.get!(immutable(wchar))())
					   lhs = Variant(""w~lhs.get!wchar(),ety);
				   else if(ety is Type.get!(immutable(dchar))())
					   lhs = Variant(""d~lhs.get!dchar(),ety);
				   else{ auto l=[lhs];lhs = Variant(l,l,ety.getDynArr()); }
				   return lhs.opBinary!"~"(e2.interpretV());
				}
			}
			return e1.interpretV().opBinary!"~"(e2.interpretV());
		}else return super.interpretV();
	}

	override void _interpretFunctionCalls(Scope sc){
		static if(S==Tok!","){
			if(auto tve=e1.isTmpVarExp())
				callWrapper(sc,tve.ctfeCallWrapper,null);
			else mixin(IntFCChld!q{e1,e2});
		}else static if(S==Tok!"/"){
			mixin(IntFCChldNoEplg!q{e1,e2});
			if(type.isIntegral() && e2.interpretV() == Variant(0,type)){
				sc.error("divide by zero",loc);
				mixin(ErrEplg);
			}
			mixin(IntFCEplg);
		}/+else static if(S==Tok!"is"||S==Tok!"!is"){
			mixin(IntFCChldNoEplg!q{e1,e2});
			assert(e1.type is e2.type);

			// TODO: allow comparing values against 'null' or '[]'

			sc.error("cannot interpret '"~TokChars!S~"' expression during compile time", loc);
			mixin(ErrEplg);
		}+/else static if(S==Tok!"&&"||S==Tok!"||"){
			mixin(IntFCChldNoEplg!q{e1});
			assert(e1.type is Type.get!bool());
			if(cast(bool)e1.interpretV()^(S==Tok!"&&")){mixin(RewEplg!q{e1});}
			mixin(IntFCChld!q{e2});
		}else mixin(IntFCChld!q{e1,e2});
	}
}

mixin template Interpret(T) if(is(T==TernaryExp)){
	override bool checkInterpret(Scope sc){
		return e1.checkInterpret(sc)&e2.checkInterpret(sc)&e3.checkInterpret(sc);
	}
	override Variant interpretV(){
		auto r = e1.interpretV();
		assert(r.getType() is Type.get!bool(), to!string(r.getType()));
		return r ? e2.interpretV() : e3.interpretV();
	}

	override void _interpretFunctionCalls(Scope sc){mixin(IntFCChld!q{e1,e2,e3});}
}

mixin template Interpret(T) if(is(T==TemporaryExp)){}
mixin template Interpret(T) if(is(T==TmpVarExp)){
	override bool checkInterpret(Scope sc){
		assert(!!tmpVarDecl.init);
		return true; // be optimistic
	}
	override Variant interpretV(){ return Variant(null, Type.get!void()); }
	override void _interpretFunctionCalls(Scope sc){
		assert(!!tmpVarDecl.init);
		mixin(IntFCChld!q{tmpVarDecl.init});
	}
	FunctionDef ctfeCallWrapper;
}


mixin template Interpret(T) if(is(T==StructConsExp)||is(T==NewExp)){
	override bool checkInterpret(Scope sc){
		return true; // be optimistic
	}
	override void _interpretFunctionCalls(Scope sc){
		// TODO: all StructConsExp's making it until here do not call a constructor,
		// because those initialize temporary variables, which invoke the interpreter instead
		// use this fact to avoid invoking the byte code interpreter
		callWrapper(sc,ctfeCallWrapper,consCall?consCall.e:null);
	}
private:
	FunctionDef ctfeCallWrapper;
}


mixin template Interpret(T) if(is(T==CallExp)){
	//private Variant val;
	override bool checkInterpret(Scope sc){
		return true; // be optimistic
	}

	override void _interpretFunctionCalls(Scope sc){
		callWrapper(sc,ctfeCallWrapper,e);
	}
	//sc.error(format("cannot interpret function call '%s' at compile time",toString()),loc);
	//	mixin(ErrEplg);
private:
	FunctionDef ctfeCallWrapper;
}
mixin template Interpret(T) if(is(T==UFCSCallExp)){ }


class CTFERetryException: Exception{Node node;this(Node n){super("");node = n;}}
class UnwindException: Exception{Location loc; this(Location loc){this.loc=loc;super("");}}
class SilentUnwindException: Exception{this(){super("");}}

void dependentCTFE(T)(Dependent!T node){
	if(node.dependee){
		if(node.dependee.node.needRetry){
			throw new CTFERetryException(node.dependee.node);
		}else{
			assert(node.dependee.node.sstate == SemState.error);
			throw new UnwindException(node.dependee.node.loc);
		}
	}
}

// bytecode interpreter for functions
import expression, declaration, statement;

enum Instruction : uint{
	hlt,
	hltstr,
	nop,
	// flow control
	jmp,                        // jump to (constant) location of argument
	jz,                         // jump if zero
	jnz,                        // jump if non-zero
	call,                       // function call
	ret,                        // return from function
	// stack control
	push,                       // push 1
	pop,                        // pop 1
	push2,                      // push 2
	pop2,                       // pop 2
	popn,                       // pop n
	pushp,                      // push 1 from constant stack location
	popp,                       // pop and store 1 to constant stack location
	pushp2,                     // push 2s to consecutive constant stack locations
	popp2,                      // pop and store 2 to consecutive constant stack locations
	pushpn,                     // pop and store to n consecutive constant stack locations
	poppn,                      // pop and store n to consecutive constant stack locations
	pushr,                      // pop 1 and push stack location given by value
	popr,                       // pop 2 and store higher to stack location given by lower
	pushr2,                     // pop 1 and push 2 consecutive stack locations given by value
	popr2,                      // pop 3, store 2 higher to stack location given by lowest
	pushrn,                     // pop 1 and push n consecutive stack locations given by value
	poprn,                      // pop n+1, store n higher to stack location given by lowest
	poprkv,                     // like popr, but keep value on stack (dup-rot-popr)
	poprkr,                     // like popr, but keep stack reference on stack
	poprkv2,                    // like popr2, but keep value on stack
	poprkr2,                    // like popr2, but keep stack reference on stack
	poprkvn,                    // like poprn, but keep value on stack
	poprkrn,                    // like poprn, but keep stack reference on stack
	pushcn,                     // push n consecutive heap stack locations given by top
	popcn,                      // pop n consecutive heap stack locations given by top
	popckvn,                    // like popcn, but keep value on stack
	popckrn,                    // like popcn, but keep heap stack location on stack
	pushccn,                    // ltop: n, top: number of heap stacks to traverse
	popccn,                     // ltop: n, top: number of heap stacks to traverse
	popcckvn,                   // like popccn, but keep value
	popcckrn,                   // like popccn, but keep location (and number of heap stacks)
	ptrfc,                      // create pointer to context
	ptrfcc,                     // create pointer to enclosing context
	pushcontext,                // push address of an enclosing context on the stack
	swap,                       // swap topmost values
	swap2,                      // swap topmost value pairs
	swapn,                      // swap topmost n-tuples
	dup,                        // push top of stack
	dup2,                       // duplicate the 2 topmost stack entries
	dupn,                       // duplicate the n topmost stack entries
	rot,                        // rotate the 3 topmost entries by moving top 2 entries down
	rot2,                       // rotate the 3 topmost pairs of 2
	rot221,                     // rotate the 2 topmost pairs of 2 and the following entry
	alloca,                     // pop 1 and reserve stack space
	allocc,                     // create a context of fixed size and push to stack
	// temporaries
	tmppush,                    // pop 1 and push to temporary stack
	tmppop,                     // pop 2 and push to temporary stack
	// type conversion
	int2bool,                   // pop 1, convert to bool and push 1
	real2bool,                  // pop 2, interpret as real convert to bool and push 1
	uint2real,                  // pop 1, convert to real, push 2
	real2uint,                  // pop 2, convert to ulong push 1
	int2real,                   // pop 1, interpret as signed, convert to real, push 2
	real2int,                   // pop 2, convert to long, interpret as ulong, push 1
	float2real,                 // pop 1, interpret as float, convert to real, push 2
	real2float,                 // pop 2, convert to float, push 1
	double2real,                // pop 1, interpret as double, convert to real, push 2
	real2double,                // pop 2, convert to double, push 1
	trunc,                      // truncate top to given number of bits
	truncs,                     // truncate top to given number of bits, sign extend
	// arithmetics
	negi,                       // negate top of stack
	noti,                       // ~ top of stack
	notb,                       // ! top of stack
	// integer
	addi,                       // add 2 ulongs
	subi,                       // subtract top from ltop
	muli,                       // multiply 2 ulongs
	divi,                       // divide ltop by top unsigned
	divsi,                      // divide ltop by top signed
	modi,                       // ltop%top unsigned
	modsi,                      // ltop%top signed
	// float
	addf,
	subf,
	mulf,
	divf,
	modf,
	// double
	addd,
	subd,
	muld,
	divd,
	modd,
	// real
	addr,
	subr,
	mulr,
	divr,
	modr,
	// shifts
	shl32,                      // logic shift left, shamt below 32
	shr32,                      // logic shift right, shamt below 32
	sar32,                      // shift arithmetic right, shamt below 32
	shl64,                      // logic shift left, shamt below 64
	shr64,                      // logic shift right, shamt below 64
	sar64,                      // shift arithmetic right, shamt below 64
	// bitwise ops
	or,
	xor,
	and,
	// comparison
	cmpei,                      // compare for equality
	cmpli,                      // signed <
	cmpbi,                      // unsigned <
	cmplei,                     // signed <=
	cmpbei,                     // unsigned <=
	cmpnei,                     // compare for inequality
	cmpgi,                      // signed >
	cmpai,                      // unsigned >
	cmpgei,                     // signed >=
	cmpaei,                     // unsigned >=
	// float
	cmpisf,
	cmpef,
	cmplf,
	cmplef,
	cmpnef,
	cmpgf,
	cmpgef,
	// double
	cmpisd,
	cmped,
	cmpld,
	cmpled,
	cmpned,
	cmpgd,
	cmpged,
	// real
	cmpisr,
	cmper,
	cmplr,
	cmpler,
	cmpner,
	cmpgr,
	cmpger,
	// array operations
	ptra,                       // get pointer field
	lengtha,                    // get length field
	setlengtha,                 // set length field
	newarray,                   // creates an array, stack top is length
	makearray,                  // pop values from the stack and turn them into an array
	appenda,
	concata,
	// arrays of simple types
	loada,                      // stack top is the index
	loadak,                     // like loada, but keep array and index on stack
	storea,
	storeakr,
	storeakv,
	slicea,
	// array of arrays (not actually required anymore, but instruction size is smaller)
	loadaa,
	loadaak,
	storeaa,
	storeaakr,
	storeaakv,
	// pointers
	loadap,                    // generate a pointer to an array location
	ptrtoa,
	addp,                      // add an integer to a pointer
	cmpep,
	cmpbp,
	cmpbep,
	cmpnep,
	cmpap,
	cmpaep,
	// fields
	loadf,                     // args: off, len, pop pointer and load field
	loadfkr,
	storef,                    // args: off, len, pop data and pointer and store to field
	storefkr,
	storefkv,
	ptrf,
	// casts from void[] and void*
	castfromvarr,
	castfromvptr,
	// virtual methods
	fetchvtbl,                 // if there already is a vtbl, use it (if the child does have it as well)
	fetchoverride,             // there is no vtbl, always determine overrides dynamically
	// partially analyzed functions
	analyzeandfail,
	// error handling table
	errtbl,
}

private enum isize = Instruction.sizeof;

size_t numArgs(Instruction inst){
	alias Instruction I;
	enum TBD = -1;
	static int[] args =
		[// flow control
		 I.hlt: 0, I.hltstr: 0,
		 I.jmp: 1, I.jz: 1, I.jnz: 1, I.call: 1, I.ret: 0,
		 // stack control
		 I.push:  1, I.pop:  0, I.popn: 1, I.pushp:  1, I.popp:  1,
		 I.push2: 2, I.pop2: 0, I.pushp2: 1, I.popp2: 1, I.pushpn: 2, I.poppn: 2,
		 I.pushcn: 1, I.popcn: 1, I.popckvn: 1, I.popckrn: 1,
		 I.pushccn: 1, I.popccn: 1, I.popcckvn: 1, I.popcckrn: 1,
		 I.ptrfc: 1, I.ptrfcc: 1, I.pushcontext: 1,
		 I.pushr: 0, I.popr: 0, I.pushr2: 0, I.popr2: 0, I.pushrn: 1, I.poprn: 1,
		 I.poprkv: 0, I.poprkr: 0, I.poprkv2: 0, I.poprkr2: 0, I.poprkvn: 1, I.poprkrn: 1,
		 I.swap: 0, I.swap2: 0, I.swapn: 1, I.dup: 0, I.dup2: 0, I.dupn: 1,
		 I.rot: 0, I.rot2: 0, I.rot221: 0,
		 I.alloca: 0, I.allocc: 1,
		 // temporaries
		 I.tmppush: 0, I.tmppop: 0,
		 // type conversion
		 I.int2bool:   0, I.real2bool:  0,
		 I.uint2real:  0, I.real2uint:  0,
		 I.int2real:   0, I.real2int:   0,
		 I.float2real: 0, I.real2float: 0,
		 I.double2real:0, I.real2double:0,
		 I.trunc:      1, I.truncs:     1,
		 // arithmetics
		 I.negi: 0, I.noti: 0, I.addi: 0, I.subi: 0,I.muli: 0,
		 I.divi: 0, I.divsi: 0, I.modi: 0, I.modsi: 0,
		 I.addf: 0, I.subf: 0, I.mulf: 0, I.divf: 0,
		 I.addd: 0, I.subd: 0, I.muld: 0, I.divd: 0,
		 I.addr: 0, I.subr: 0, I.mulr: 0, I.divr: 0,
		 I.shl32: 0, I.shr32: 0, I.sar32: 0, I.shl64: 0, I.shr64: 0, I.sar64: 0,
		 // comparison
		 I.cmpei: 0, I.cmpli: 0, I.cmpbi: 0, I.cmplei: 0, I.cmpbei: 0,
		 I.cmpnei: 0, I.cmpgi: 0, I.cmpai: 0, I.cmpgei: 0, I.cmpaei: 0,
		 I.cmpisf: 0, I.cmpef: 0, I.cmplf: 0, I.cmplef: 0, I. cmpnef: 0, I.cmpgf: 0, I.cmpgef: 0,
		 I.cmpisd: 0, I.cmped: 0, I.cmpld: 0, I.cmpled: 0, I. cmpned: 0, I.cmpgd: 0, I.cmpged: 0,
		 I.cmpisr: 0, I.cmper: 0, I.cmplr: 0, I.cmpler: 0, I. cmpner: 0, I.cmpgr: 0, I.cmpger: 0,
		 // array operations
		 I.ptra: 0, I.lengtha: 1, I.setlengtha: 1,
		 I.newarray: 1, I.makearray: 1, I.appenda: 0, I.concata: 0,
		 I.loada: 1, I.loadak: 1, I.storea: 1, I.storeakr: 1, I.storeakv: 1, I.slicea: 1,
		 I.loadaa: 0, I.loadaak: 0, I.storeaa: 0, I.storeaakr: 0, I.storeaakv: 0,
		 // pointer operations
		 I.loadap: 1, I.ptrtoa: 0, I.addp: 1,
		 I.cmpep: 0, I.cmpbp: 0, I.cmpbep: 0, I. cmpnep: 0, I.cmpap: 0, I.cmpaep: 0,
		 // field operations
		 I.loadf: 2, I.loadfkr: 2, I.storef: 2, I.storefkr: 2, I.storefkv: 2, I.ptrf: 2,
		 // virtual methods
		 I.fetchvtbl: 1,
		 I.fetchoverride: 1,
		 // partially analyzed functions
		 I.analyzeandfail: 2,
		 // casts from void[] and void*
		 I.castfromvarr: 1, I.castfromvptr: 1,
		 // error handling table
		 I.errtbl: 0,
		 ];
	if(inst>=args.length) return 0;
	return args[inst];
}

bool isUnsafe(Instruction inst){
	alias Instruction I;
	static bool[] fail =
		[// flow control
		 I.hlt: 1, I.hltstr:1, I.call: 1,
		 // stack control
		 I.pushcn: 1, I.popcn: 1, I.popckvn: 1, I.popckrn: 1,
		 I.pushccn: 1, I.popccn: 1, I.popcckvn: 1, I.popcckrn: 1,
		 I.ptrfc: 1, I.ptrfcc: 1, I.pushcontext: 1,
		 // arithmetics
		 I.divi: 1, I.divsi: 1, I.modi: 1, I.modsi: 1,
		 I.shl32: 1, I.shr32: 1, I.sar32: 1, I.shl64: 1, I.shr64: 1, I.sar64: 1,
		 // array operations
		 I.loada: 1, I.loadak: 1, I.storea: 1, I.storeakr: 1, I.storeakv: 1, I.slicea: 1,
		 I.loadaa: 1, I.loadaak: 1, I.storeaa: 1, I.storeaakr: 1, I.storeaakv: 1,
		 // pointer operations
		 I.loadap: 1, I.ptrtoa: 1,
		 // field operations
		 I.loadf: 1, I.loadfkr: 1, I.storef: 1, I.storefkr: 1, I.storefkv: 1, I.ptrf: 1,
		 // casts from void[] and void*
		 I.castfromvarr: 1, I.castfromvptr: 1,
		 I.max: 0
		 ];
	return fail[inst];
}
alias Node ErrorInfo;

private class HltErrorInfo: Node{
	// to make it non-abstract, it has to implement those:
	override string kind(){assert(0);}// kind
	override void _doAnalyze(scope void delegate(Node) dg){assert(0);}
	override inout(Node) ddup()inout{assert(0);}
	string err;
	Location loc;
}

alias immutable(ulong)[] ByteCode;

import variant;

// a conservatively garbage collected ulong[] + stack top pointer, convenience methods
struct Stack{
	ulong[] stack;
	static assert(ulong.sizeof>=(void*).sizeof);
	size_t stp=-1;
	//@property length(){return stack.length;}
	@property empty(){return stp==-1;}

	private void pushl()(ulong c){ // TODO: get rid of this
		if(stp+1>=stack.length){
			void[] va = stack;
			if(!va.length) va.length+=ulong.sizeof;
			va.length *= 2; stack=cast(ulong[])va;
		}
		stack[++stp]=c;
	}
	void allocate(size_t c){
		void[] va = stack;
		va.length+=c*ulong.sizeof;
		stack = cast(ulong[])va;
	}
	void push(T)(T c){
		enum sz = (ulong.sizeof-1+T.sizeof)/ulong.sizeof;
		foreach(i;0..sz) pushl(0);
		static if(T.alignof<=ulong.alignof)
			*cast(Unqual!T*)(stack.ptr+stp-sz+1)=c;
		else{
			import core.stdc.string;
			memcpy(stack.ptr+stp-sz+1, &c, c.sizeof);
		}
	}
	void pushRaw(void[] c){
		auto sz = (ulong.sizeof-1+c.length)/ulong.sizeof;
		foreach(i;0..sz) pushl(0);
		//(cast(void[])stack[stp+1-sz..stp+1])[0..c.length]=c[];
		// we want to allow overlapping copies here
		import core.stdc.string;
		memmove(stack.ptr+stp+1-sz, c.ptr, (cast(void[])c).length);
	}
	void[] popRawSliceStack(size_t size){
		auto sz = (ulong.sizeof-1+size)/ulong.sizeof;
		void[] r = (cast(void[])stack[stp+1-sz..stp+1])[0..size];
		pop(sz);
		return r;
	}
	ulong pop()(){return stack[stp--];}
	void pop()(size_t num){assert(stp+1>=num);stp-=num;}
	T pop(T)() if(!is(T:ulong)){
		enum sz = (ulong.sizeof-1+T.sizeof)/ulong.sizeof;
		T c=void;
		static if(T.alignof<=ulong.alignof)
			c=*cast(T*)(stack.ptr+stp-sz+1);
		else{
			import core.stdc.string;
			memcpy(&c,stack.ptr+stp-sz+1,c.sizeof);
		}
		pop(sz);
		return c;
	}

	void popFront(size_t num)in{assert(stp+1>=num);}body{
		if(!num) return;
		foreach(i, ref x; stack[0..stp+1-num]) x=stack[num+i];
		stp-=num;
	}

	ref ulong top(){return stack[stp];}
	ref ulong ltop(){return stack[stp-1];}
	string toString(){
		import std.conv;
		return to!string(stack[0..stp+1]);
	}
}

struct ByteCodeBuilder{
/+	/* byte code may contain unique references to constant data, eg. string data
	   this struct simulates an ulong[], which is conservatively searched for
	   pointers by the GC.
	   TODO: this seems not to be a very nice design
	   TODO: disabled this and now literalexp is responsible for keeping the references
	   alive. Is this better?
	 */

	struct ConservativeUlongArray{
		ulong[] data;
		@property size_t length(){return data.length;}
		ref ConservativeUlongArray opOpAssign(string op : "~",T)(T dat){
			void[] tmp = data;
			static if(!is(T X:X[])){
				ulong appn = dat;
				tmp ~= *cast(void[ulong.sizeof]*)&appn;
			}else tmp~=cast(void[])dat;
			data = cast(ulong[])tmp;
			return this;
		}
		ref ulong opIndex(size_t i){ return data[i]; }

		ByteCode opCast(T: ByteCode)(){return cast(ByteCode)data;}
	}

	private ConservativeUlongArray byteCode;+/
	private ulong[] byteCode;
	private ErrorInfo[] errtbl;
	private size_t stackOffset=0;
	private size_t contextOffset=0;
	private size_t iloc;

	void addStackOffset(size_t amt){stackOffset+=amt;}
	size_t getStackOffset(){return stackOffset;}
	void addContextOffset(size_t amt){contextOffset+=amt;}
	size_t getContextOffset(){return contextOffset;}

	ulong getLocation(){return byteCode.length;}

	ByteCode getByteCode(){
		static if(ErrorInfo.sizeof%ulong.sizeof)
			if(errtbl.length*ErrorInfo.sizeof%ulong.sizeof){
			errtbl~=null;
			assert(!((cast(ulong)errtbl.ptr)%ulong.sizeof));
		}
		auto r = cast(ByteCode)((byteCode~=Instruction.errtbl)~=cast(ByteCode)errtbl);
		byteCode = null;
		return r;
	}
	ErrorInfo[] getErrtbl(){return errtbl;} // so that it does not get garbage collected
	void ignoreResult(size_t size){
		if(size) emitPop(size);
	}
	void error(string err, Location loc){
		// TODO: shouldn't allocate if no error occurs!
		// (replace by argument to hlt)
		auto erri = New!HltErrorInfo();
		erri.err = err;
		erri.loc = loc;
		emitUnsafe(Instruction.hlt, erri);
	}

	void emit(Instruction inst)in{assert(!isUnsafe(inst), to!string(inst)~" is unsafe");}body{
		assert(byteCode.length<ulong.max); // TODO: add this restriction explicitly
		iloc = byteCode.length;
		byteCode~=inst;
	}

	void emitUnsafe(Instruction inst, ErrorInfo info)in{assert(isUnsafe(inst));}body{
		byteCode~=inst;
		errtbl~=info;
	}

	void emitDup(ulong num){
		if(num == 0) return;
		if(num == 1) return emit(Instruction.dup);
		if(num == 2) return emit(Instruction.dup2);
		emit(Instruction.dupn);
		emitConstant(num);
	}

	void emitSwap(ulong num){
		if(num == 0) return;
		if(num == 1) return emit(Instruction.swap);
		if(num == 2) return emit(Instruction.swap2);
		emit(Instruction.swapn);
		emitConstant(num);
	}
	void emitTmppush(ulong num){
		foreach(i;0..num) emit(Instruction.tmppush);
	}
	void emitTmppop(ulong num){
		foreach(i;0..num) emit(Instruction.tmppop);
	}

	void emitPop(ulong num)in{assert(num);}body{
		if(num == 1) return emit(Instruction.pop);
		if(num == 2) return emit(Instruction.pop2);
		emit(Instruction.popn);
		emitConstant(num);
	}

	void emitPushp(ulong num)in{assert(num);}body{
		if(num == 1) return emit(Instruction.pushp);
		if(num == 2) return emit(Instruction.pushp2);
		emit(Instruction.pushpn);
		emitConstant(num);
	}

	void emitPopp(ulong num)in{assert(num);}body{
		if(num == 1) return emit(Instruction.popp);
		if(num == 2) return emit(Instruction.popp2);
		emit(Instruction.poppn);
		emitConstant(num);
	}

	void emitPushr(ulong num)in{assert(num);}body{
		if(num == 1) return emit(Instruction.pushr);
		if(num == 2) return emit(Instruction.pushr2);
		emit(Instruction.pushrn);
		emitConstant(num);
	}

	void emitPopr(ulong num)in{assert(num);}body{
		if(num == 1) return emit(Instruction.popr);
		if(num == 2) return emit(Instruction.popr2);
		emit(Instruction.poprn);
		emitConstant(num);
	}

	void emitConstant(ulong c){
		byteCode~=c;
	}
	void emitConstant(float c){
		byteCode~=*cast(uint*)&c;
	}
	void emitConstant(double c){
		byteCode~=*cast(ulong*)&c;
	}
	void emitConstant(real c){
		static if(real.sizeof == 12){
			byteCode~=*cast(ulong*)&c;
			byteCode~=*((cast(uint*)&c)+2);
		}else static if(real.sizeof == 16){
			byteCode~=*cast(ulong*)&c;
			byteCode~=*((cast(ulong*)&c)+1);
		}else static assert(0);
	}

	void emitPushConstant()(void[] mem){
		auto len=mem.length/ulong.sizeof;
		auto ul=cast(ulong[])mem[0..len*ulong.sizeof];
		foreach(x;ul){
			emit(Instruction.push);
			emitConstant(x);
		}
		if(mem.length%ulong.sizeof){
			auto diff=mem.length-len*ulong.sizeof;
			ulong x=0;
			(cast(void*)&x)[0..diff]=mem[len*ulong.sizeof..$];
			emit(Instruction.push);
			emitConstant(x);
		}
	}
	void emitPushConstant(T)(T v)if(!is(T==void[])){ emitPushConstant((cast(void*)&v)[0..T.sizeof]); }

	void emitNullPointer(){ emitPushConstant(cast(void[BCPointer.sizeof])BCPointer.init); }

	struct Label{
		ByteCodeBuilder* outer;
		size_t loc = -1; // no allocation if label used exactly once
		size_t[] locs;
		ulong pos = -1;
		void here()in{
			assert(outer && loc == -1 || outer.byteCode[loc] == ~0);
		}body{
			pos = cast(ulong)outer.byteCode.length;
			if(loc == -1) return;
			assert(outer.byteCode.length<=ulong.max); // TODO: add this restriction explicitly
			outer.byteCode[loc] = pos;
			foreach(l; locs) outer.byteCode[l] = pos;
		}

		bool initialized(ref ByteCodeBuilder bld){return outer is &bld;}
	}

	Label getLabel(){
		return Label(&this);
	}
	Label emitLabel(){
		auto r = Label(&this, byteCode.length);
		emitConstant(~0);
		return r;
	}
	void emitLabel(ref Label lbl)in{assert(lbl.initialized(this));}body{
		if(~lbl.pos) emitConstant(lbl.pos);
		else{
			if(!~lbl.loc) lbl.loc=byteCode.length;
			else lbl.locs ~= byteCode.length;
			emitConstant(~0);
		}
	}

	struct Alloca{
		private{
			ByteCodeBuilder* outer;
			size_t loc;
			size_t origoff;
		}
		void done(){
			outer.byteCode[loc] = cast(ulong)(outer.stackOffset-origoff);
		}
	}

	Alloca emitAlloca(){
		emit(Instruction.push);
		auto r = Alloca(&this, byteCode.length, stackOffset);
		emitConstant(~0);
		emit(Instruction.alloca);
		return r;
	}

	struct Allocc{
		private{
			ByteCodeBuilder* outer;
			size_t loc;
		}
		void done(){
			outer.byteCode[loc] = cast(ulong)outer.contextOffset;
		}
	}

	Allocc emitAllocc(){
		emit(Instruction.allocc);
		auto r = Allocc(&this, byteCode.length);
		emitConstant(~0);
		return r;
	}
}

abstract class LValueStrategy{
	abstract void emitStore(ref ByteCodeBuilder);  // store value on top of stack in address
	abstract void emitStoreKR(ref ByteCodeBuilder);// keep address on stack
	abstract void emitStoreKV(ref ByteCodeBuilder);// keep value on stack

	abstract void emitLoad(ref ByteCodeBuilder); // load value at address
	void emitLoadKR(ref ByteCodeBuilder bld){ // load value at address, keep address
		dupR(bld);
		emitLoad(bld);
	}
	final void dupR(ref ByteCodeBuilder bld){
		bld.emitDup(lvBCSize);
	}
	abstract @property size_t lvBCSize();


	abstract void emitPointer(ref ByteCodeBuilder);

	LValueStrategy emitFieldLV(ref ByteCodeBuilder bld, size_t off, size_t len, size_t ctlen, ErrorInfo info, VarDecl vd){
		emitPointer(bld);
		auto r = LVfield(off, len, ctlen, info);
		return r;
	}
}
static class LVfield: LValueStrategy{
	size_t off, len, ctlen;
	ErrorInfo info;
	static opCall(size_t off, size_t len, size_t ctlen, ErrorInfo info){
		return new LVfield(off, len, ctlen, info);
	}
	private this(size_t off, size_t len, size_t ctlen, ErrorInfo info){
		this.off=off;
		this.len=len;
		this.ctlen=ctlen;
		this.info=info;
	}
	override @property size_t lvBCSize(){
		return bcPointerBCSize;
	}
	override void emitStore(ref ByteCodeBuilder bld){
		bld.emitUnsafe(Instruction.storef, info);
		bld.emitConstant(off);
		bld.emitConstant(len);
	}
	override void emitStoreKR(ref ByteCodeBuilder bld){
		bld.emitUnsafe(Instruction.storefkr, info);
		bld.emitConstant(off);
		bld.emitConstant(len);
	}
	override void emitStoreKV(ref ByteCodeBuilder bld){
		bld.emitUnsafe(Instruction.storefkv, info);
		bld.emitConstant(off);
		bld.emitConstant(len);
	}
	override void emitLoad(ref ByteCodeBuilder bld){
		bld.emitUnsafe(Instruction.loadf, info);
		bld.emitConstant(off);
		bld.emitConstant(len);
	}
	override void emitLoadKR(ref ByteCodeBuilder bld){
		bld.emitUnsafe(Instruction.loadfkr, info);
		bld.emitConstant(off);
		bld.emitConstant(len);
	}
	override void emitPointer(ref ByteCodeBuilder bld){
		bld.emitUnsafe(Instruction.ptrf, info);
		bld.emitConstant(off);
		bld.emitConstant(ctlen);
	}
}

auto LVpopcc(Type elty, ErrorInfo info){
	return new LVpopc(getBCSizeof(elty), getCTSizeof(elty), info, true);
}

class LVpopc: LValueStrategy{
	ulong n;
	size_t ctsiz;
	ErrorInfo info;
	bool iscc;
	static opCall(Type elty, ErrorInfo info){
		return new LVpopc(getBCSizeof(elty), getCTSizeof(elty), info, false);
	}
	private this(ulong nn,size_t ct, ErrorInfo inf, bool iscc){
		n = nn;
		ctsiz=ct;
		info = inf;
		this.iscc=iscc;
	}
	@property size_t lvBCSize(){ return 1+iscc; }

	override void emitStore(ref ByteCodeBuilder bld){
		bld.emitUnsafe(iscc?Instruction.popccn:Instruction.popcn, info);
		bld.emitConstant(n);
	}
	override void emitStoreKR(ref ByteCodeBuilder bld){
		bld.emitUnsafe(iscc?Instruction.popcckrn:Instruction.popckrn, info);
		bld.emitConstant(n);
	}
	override void emitStoreKV(ref ByteCodeBuilder bld){
		bld.emitUnsafe(iscc?Instruction.popcckvn:Instruction.popckvn, info);
		bld.emitConstant(n);
	}

	override void emitLoad(ref ByteCodeBuilder bld){
		bld.emitUnsafe(iscc?Instruction.pushccn:Instruction.pushcn, info);
		bld.emitConstant(n);
	}

	override void emitPointer(ref ByteCodeBuilder bld){
		bld.emitUnsafe(iscc?Instruction.ptrfcc:Instruction.ptrfc, info);
		bld.emitConstant(ctsiz);
	}
}


class LVpopr: LValueStrategy{
	ulong n;
	static opCall(ulong n){
		return new LVpopr(n);
	}

	private this(ulong nn){
		n = nn;
	}
	override @property size_t lvBCSize(){ return 1; }

	override void emitStore(ref ByteCodeBuilder bld){
		if(n==1) bld.emit(Instruction.popr);
		else if(n==2) bld.emit(Instruction.popr2);
		else{
			bld.emit(Instruction.poprn);
			bld.emitConstant(n);
		}
	}
	override void emitStoreKR(ref ByteCodeBuilder bld){
		if(n==1) bld.emit(Instruction.poprkr);
		else if(n==2) bld.emit(Instruction.poprkr2);
		else{
			bld.emit(Instruction.poprkrn);
			bld.emitConstant(n);
		}
	}
	override void emitStoreKV(ref ByteCodeBuilder bld){
		if(n==1) bld.emit(Instruction.poprkv);
		else if(n==2) bld.emit(Instruction.poprkv2);
		else{
			bld.emit(Instruction.poprkvn);
			bld.emitConstant(n);
		}
	}

	override void emitLoad(ref ByteCodeBuilder bld){
		if(n==1) bld.emit(Instruction.pushr);
		else if(n==2) bld.emit(Instruction.pushr2);
		else{
			bld.emit(Instruction.pushrn);
			bld.emitConstant(n);
		}
	}
	override void emitLoadKR(ref ByteCodeBuilder bld){
		bld.emit(Instruction.dup);          // duplicate address
		if(n==1) bld.emit(Instruction.pushr);
		else if(n==2) bld.emit(Instruction.pushr2);
		else{
			bld.emit(Instruction.pushrn);
			bld.emitConstant(n);
		}
	}

	override void emitPointer(ref ByteCodeBuilder bld){
		assert(0, "cannot create stack references");
	}

	override LValueStrategy emitFieldLV(ref ByteCodeBuilder bld, size_t off, size_t len, size_t ctlen, ErrorInfo, VarDecl){
		assert(off+len<=n);
		// TODO: byte code support for offsetted poprs
		static class FieldLV: LVpopr{
			size_t off;
			alias n len;
			this(size_t off, size_t len){
				this.off = off;
				super(len);
			}
			private void adjust(ref ByteCodeBuilder bld){
				bld.emit(Instruction.push);
				bld.emitConstant(off);
				bld.emit(Instruction.addi);
			}
			// TODO: those are inefficient
			private static _emitAll(){
				string r;
				foreach(s;["emitStore", "emitStoreKR", "emitStoreKV"]){
					r~=mixin(X!q{
							override void @(s)(ref ByteCodeBuilder bld){
								bld.emitTmppush(len);
								adjust(bld);
								bld.emitTmppop(len);
								super.@(s)(bld);
							}
						});
				}
				return r;
			}
			mixin(_emitAll());
			override void emitLoad(ref ByteCodeBuilder bld){
				adjust(bld);
				super.emitLoad(bld);
			}
			override void emitLoadKR(ref ByteCodeBuilder bld){
				adjust(bld);
				super.emitLoadKR(bld);
				// reset adjustment
				bld.emitTmppush(len);
				bld.emit(Instruction.push);
				bld.emitConstant(off);
				bld.emit(Instruction.subi);
				bld.emitTmppop(len);
			}
			override LValueStrategy emitFieldLV(ref ByteCodeBuilder bld, size_t off, size_t len, size_t ctlen, ErrorInfo, VarDecl vd){
				return new FieldLV(this.off+off, len);
			}
		}
		return new FieldLV(off, len);
	}
}

LVstorea LVpointer(Type elty, ErrorInfo info){ // TODO: use loadf and storef
	return new LVstorea(elty, info, true);
}
class LVstorea: LValueStrategy{
	ulong els;
	ulong bcsiz;
	bool isarr;
	int signedBitSize=-1;
	bool isptr;
	ErrorInfo info;
	static opCall(Type elty, ErrorInfo info){
		return new LVstorea(elty, info, false);
	}
	static bool isArrElement(Type elty){
		auto unq=elty.getHeadUnqual();
		return unq.isDynArrTy()&&unq.getElementType().getHeadUnqual() !is Type.get!(void)();
	}
	private this(Type elty, ErrorInfo inf, bool ptr){
		isarr = isArrElement(elty);
		if(!isarr) els = getCTSizeof(elty);
		bcsiz = getBCSizeof(elty);
		if(auto i=elty.isIntegral()){
			if(i.isSigned())
				signedBitSize=i.bitSize();
		}
		info = inf;
		isptr=ptr;
	}
	override @property size_t lvBCSize(){
		// an index and a pointer or slice
		assert(getBCSizeof(Type.get!ulong())==1);
		return isptr?bcPointerBCSize:1+bcSliceBCSize;
	}
	private void ptrPrlg(ref ByteCodeBuilder bld, bool isstore){
		if(isptr){
			if(isstore) bld.emitTmppush(bcsiz);
			bld.emitUnsafe(Instruction.ptrtoa, info);
			bld.emit(Instruction.push);
			bld.emitConstant(0);
			if(isstore) bld.emitTmppop(bcsiz);
		}
	}
	private void ptrKREplg(ref ByteCodeBuilder bld, bool isstore){
		if(isptr){
			if(!isstore) bld.emitTmppush(bcsiz);
			bld.emit(Instruction.pop);  // pop index
			bld.emit(Instruction.ptra); // restore pointer from array
			if(!isstore) bld.emitTmppop(bcsiz);
		}
	}
	override void emitStore(ref ByteCodeBuilder bld){
		ptrPrlg(bld,true);
		bld.emitUnsafe(isarr?Instruction.storeaa:Instruction.storea, info);
		if(!isarr) bld.emitConstant(els);
	}
	override void emitStoreKR(ref ByteCodeBuilder bld){
		ptrPrlg(bld,true);
		bld.emitUnsafe(isarr?Instruction.storeaakr:Instruction.storeakr, info);
		if(!isarr) bld.emitConstant(els);
		ptrKREplg(bld,true);
	}
	override void emitStoreKV(ref ByteCodeBuilder bld){
		ptrPrlg(bld,true);
		bld.emitUnsafe(isarr?Instruction.storeaakv:Instruction.storeakv, info);
		if(!isarr) bld.emitConstant(els);
	}

	private void emitSignedAdjust(ref ByteCodeBuilder bld){
		if(signedBitSize!=-1&&signedBitSize<64){
			bld.emit(Instruction.truncs);
			bld.emitConstant(signedBitSize);
		}
	}

	override void emitLoad(ref ByteCodeBuilder bld){
		ptrPrlg(bld,false);
		bld.emitUnsafe(isarr?Instruction.loadaa:Instruction.loada, info);
		if(!isarr) bld.emitConstant(els);
		emitSignedAdjust(bld);
	}
	override void emitLoadKR(ref ByteCodeBuilder bld){
		ptrPrlg(bld,false);
		bld.emitUnsafe(isarr?Instruction.loadaak:Instruction.loadak, info);
		if(!isarr) bld.emitConstant(els);
		emitSignedAdjust(bld);
		ptrKREplg(bld,false);
	}

	override void emitPointer(ref ByteCodeBuilder bld){
		if(!isptr){
			bld.emitUnsafe(Instruction.loadap, info);
			bld.emitConstant(els);
		}
	}
}

class LVconditional: LValueStrategy{
	LValueStrategy strat1, strat2;
	static opCall(LValueStrategy strat1, LValueStrategy strat2){
		return new LVconditional(strat1, strat2);
	}
	private this(LValueStrategy s1, LValueStrategy s2){
		strat1 = s1;
		strat2 = s2;
	}
	override @property size_t lvBCSize(){
		assert(strat1.lvBCSize==strat2.lvBCSize);
		return strat1.lvBCSize;
	}
	private static _emitAll(){
		string r;
		foreach(s;["emitStore", "emitStoreKR", "emitStoreKV",
		           "emitLoad", "emitLoadKR", "emitPointer"]){
			r~=mixin(X!q{
				override void @(s)(ref ByteCodeBuilder bld){
					alias Instruction I;
					bld.emit(I.tmppop);
					bld.emit(I.jz);
					auto otherwise=bld.emitLabel();
					strat1.@(s)(bld);
					bld.emit(I.jmp);
					auto end=bld.emitLabel();
					otherwise.here();
					strat2.@(s)(bld);
					end.here();
				}
			});
		}
		return r;
	}
	mixin(_emitAll());
}

class LVlength: LValueStrategy{
	LValueStrategy array;
	ulong els;
	static opCall(LValueStrategy array, Type elt){
		return new LVlength(array, getCTSizeof(elt));
	}
	private this(LValueStrategy s, ulong el){
		array = s;
		els = el;
	}
	override @property size_t lvBCSize(){ return array.lvBCSize; }
	private static _emitAll(){
		string r;
		foreach(s;["emitStore", "emitStoreKR"]){
			r~=mixin(X!q{
				override void @(s)(ref ByteCodeBuilder bld){
					bld.emitTmppush(1);
					array.emitLoadKR(bld);
					bld.emitTmppop(1);
					bld.emit(Instruction.setlengtha);
					bld.emitConstant(els);
					array.@(s)(bld);
				}
			});
		}
		foreach(s;["emitLoad", "emitLoadKR"]){
			r~=mixin(X!q{
				override void @(s)(ref ByteCodeBuilder bld){
					array.@(s)(bld);
					bld.emit(Instruction.lengtha);
					bld.emitConstant(els);
				}
			});
		}

		return r;
	}
	mixin(_emitAll());

	override void emitStoreKV(ref ByteCodeBuilder bld){
		bld.emitTmppush(1);
		array.emitLoadKR(bld);
		bld.emitTmppop(1);
		bld.emit(Instruction.setlengtha);
		bld.emitConstant(els);
		array.emitStoreKV(bld);
		bld.emit(Instruction.lengtha);
		bld.emitConstant(els);
	}

	override void emitPointer(ref ByteCodeBuilder bld){
		assert(0, "cannot take the address of an array length");
	}
}

class LVtuple: LValueStrategy{
	private LValueStrategy[] tpl;
	private TypeTuple ty;
	private size_t vsize;
	static opCall(LValueStrategy[] tpl, TypeTuple ty){ return new LVtuple(tpl, ty); }
	private this(LValueStrategy[] tpl, TypeTuple ty){
		this.tpl=tpl; this.ty=ty;
		this.vsize=getBCSizeof(ty);
	}

	override @property size_t lvBCSize(){
		size_t r=0;
		foreach(x;tpl) r+=x.lvBCSize;
		return r;
	}

	private void emitStoreImpl(ref ByteCodeBuilder bld, bool kr, bool kv){
		// create temporary scratch space on stack
		auto boff=bld.getStackOffset(), off=boff;
		bld.addStackOffset(vsize);
		bld.emitPopp(vsize);
		bld.emitConstant(boff);
		if(kr) bld.emitDup(lvBCSize);
		bld.emitTmppush(lvBCSize);
		foreach(i,x;ty.allIndices()){
			auto len=getBCSizeof(x);
			bld.emitTmppop(tpl[i].lvBCSize);
			bld.emitPushp(len);
			bld.emitConstant(off);
			tpl[i].emitStore(bld);
			off+=len;
		}
		if(kv){
			bld.emitPushp(vsize);
			bld.emitConstant(boff);
		}
	}
	override void emitStore(ref ByteCodeBuilder bld){
		emitStoreImpl(bld, false, false);
	}
	override void emitStoreKR(ref ByteCodeBuilder bld){
		emitStoreImpl(bld, true, false);
	}
	override void emitStoreKV(ref ByteCodeBuilder bld){
		emitStoreImpl(bld, false, true);
	}
	override void emitLoad(ref ByteCodeBuilder bld){ assert(0, "TODO"); }

	override void emitPointer(ref ByteCodeBuilder bld){
		bld.emitTmppush(lvBCSize);
		foreach(x;tpl){
			bld.emitTmppop(x.lvBCSize);
			x.emitPointer(bld);
		}
	}
}


string toString(ByteCode byteCode){
	import std.conv;
	int off = 0;
	string r;
	while(off<byteCode.length){
		r~=to!string(off)~": "~to!string(cast(Instruction)byteCode[off]);
		auto args = numArgs(cast(Instruction)byteCode[off]);
		if(byteCode[off]==Instruction.errtbl) break;
		off++;
		if(args==2) r~=" "~to!string(byteCode[off])~", "~to!string(byteCode[off+1]);
		else if(args==1) r~=" "~to!string(byteCode[off]);
		off+=args;
		r~="\n";
	}
	return r;
}


/* for debugging purposes
 */
bool _displayByteCode = false;
bool _displayByteCodeIntp = false;

import error;

template CheckPointer(string s) if(s.split(",").length==3){
	enum ss = s.split(",");
	enum ptr = ss[0];
	enum off = ss[1];
	enum len = ss[2];
	enum CheckPointer = mixin(X!q{
		{ alias @(ptr) r;
		if(r.ptr<r.container.ptr || cast(ulong*)r.ptr+@(off)+@(len)>cast(ulong*)(r.container.ptr+r.container.length)){
			tmp[0] = r.ptr is null;
			tmp[1] = r.container.length&&r.ptr == r.container.ptr+r.container.length; // off by one at the end
			tmp[2] = cast(ulong)r.ptr;
			tmp[3] = cast(ulong)r.container.ptr; // for checking of off by one at the beg.
			goto Linvalidpointer;
		}}
	});
}

void doInterpret(ByteCode byteCode, ref Stack stack, ErrorHandler handler)in{
	assert(stack.stack.length>0);
}body{
	import core.stdc.string;
Ltailcall:
	size_t ip = 0;
	size_t nargs = stack.stp+1;
	bool keepr = false, keepv = false;
	ulong[5] tmp;
	auto tmpstack = Stack(tmp[]);
	import std.stdio;
	scope(success) if(_displayByteCodeIntp) writeln("stack: ",stack);
	for(;;){
		if(_displayByteCodeIntp){
			writeln("stack: ",stack);
			// if(ip>3) writeln("context: ", (cast(ulong*)stack.stack[nargs-1])[0..3]);
			write("inst: ",cast(Instruction)byteCode[ip]);
			if(numArgs(cast(Instruction)byteCode[ip])){
				write(" ",byteCode[ip+1]);
				if(numArgs(cast(Instruction)byteCode[ip])==2)
					write(", ",byteCode[ip+2]);
			}
			writeln();
		}

		swtch:final switch(cast(Instruction)byteCode[ip++]){
			alias Instruction I;
			case I.hlt:
					goto Lhlt;
			case I.hltstr:
				goto Lhltstr;
			case I.nop: break;
			// flow control:
			case I.jz:
				if(!stack.pop()) goto case I.jmp;
				ip++;
				break;
			case I.jnz:
				if(stack.pop()) goto case I.jmp;
				ip++;
			break;
			case I.jmp:
				//writeln("jumping to ",byteCode[ip]);
				ip = cast(size_t)byteCode[ip]; break;
			case I.call:
				auto nfargs = cast(size_t)byteCode[ip++];
				Symbol sym = cast(Symbol)cast(void*)stack.pop();

				if(!sym) goto Lnullfunction;
				if(sym.meaning.sstate != SemState.completed){
					// allow interpretation of partially analyzed function
					// (TODO: fix implementation)
					/+if(!sym.meaning.isFunctionDecl() || sym.meaning.sstate != SemState.started)
						sym.makeStrong();+/
					sym.makeStrong();
					// running semantic might bork up the in-memory data by
					// changing its layout. In this case, restart the computation
					tmpstack.push(AggregateDecl.getVersion());
					// TODO: allow detailed discovery of circular dependencies
					auto inContext=sym.inContext;
					sym.inContext=InContext.fieldExp;
					sym.semantic(sym.scope_);
					sym.inContext=inContext;
					Expression e = sym;
					mixin(Rewrite!q{e});
					assert(!!cast(Symbol)e, text(e));
					sym = cast(Symbol)cast(void*)e;
					if(sym.needRetry||tmpstack.pop()!=AggregateDecl.getVersion()){
						// TODO: make as unlikely as possible
						throw new CTFERetryException(sym);
					}
				}

				if(sym.sstate == SemState.error) goto Linvfunction;
				assert(cast(FunctionDef)sym.meaning);
				FunctionDef def = cast(FunctionDef)cast(void*)sym.meaning;

				if(byteCode[ip] == I.ret){ // tail calls
					// clean up stack
					stack.popFront(nargs);
					byteCode = def.byteCode;

					if(def.sstate != SemState.completed)
						def.resetByteCode();

					goto Ltailcall;
				}

				stack.stp-=nfargs;
				Stack newstack = Stack(stack.stack[stack.stp+1..$], nfargs-1);
				doInterpret(def.byteCode, newstack, handler);

				if(def.sstate != SemState.completed)
					def.resetByteCode;

				if(newstack.stack.ptr!=stack.stack.ptr+stack.stp+1){
					stack.stack = stack.stack[0..stack.stp+1];
					void[] va = stack.stack;
					va.assumeSafeAppend();
					va~=newstack.stack;
					stack.stack = cast(typeof(stack.stack))va;
				}else stack.stack=stack.stack.ptr[0..stack.stp+1+newstack.stack.length];
				stack.stp+=newstack.stp+1;
				break;
			case I.ret:
				// clean up stack
				stack.popFront(nargs);
				return;
			// stack control:
			case I.push:
				stack.push(byteCode[ip++]);
				break;
			case I.pop:
				stack.pop();
				break;
			case I.push2:
				stack.push(byteCode[ip++]);
				stack.push(byteCode[ip++]);
				break;
			case I.pop2:
				stack.pop(); stack.pop();
				break;
			case I.popn:
				auto n = byteCode[ip++];
				foreach(i;0..n) stack.pop();
				break;
			case I.pushp:
				stack.push(stack.stack[cast(size_t)byteCode[ip++]]);
				break;
			case I.popp:
				stack.stack[cast(size_t)byteCode[ip++]]=stack.pop();
				break;
			case I.pushp2:
				auto loc = cast(size_t)byteCode[ip++];
				stack.push(stack.stack[loc]);
				stack.push(stack.stack[loc+1]);
				break;
			case I.popp2:
				auto loc = cast(size_t)byteCode[ip++];
				stack.stack[loc+1] = stack.pop();
				stack.stack[loc] = stack.pop();
				break;
			case I.pushpn:
				auto n   = cast(size_t)byteCode[ip++];
				auto loc = cast(size_t)byteCode[ip++];
				foreach(i;0..n) stack.push(stack.stack[loc++]);
				break;
			case I.poppn:
				auto n   = cast(size_t)byteCode[ip++];
				auto loc = cast(size_t)byteCode[ip++]+n;
				foreach(i;0..n) stack.stack[--loc] = stack.pop();
				break;

			case I.pushcn:
				auto bcctx = *cast(BCPointer*)&stack.stack[nargs-bcPointerBCSize];
				auto ctx = cast(ulong*)bcctx.ptr;
				auto ctxc = cast(ulong[])bcctx.container;
				auto n = cast(size_t)byteCode[ip++];
				auto loc = cast(size_t)stack.pop();
				mixin(CheckPointer!q{bcctx, loc, n});
				foreach(i;0..n) stack.push(ctx[loc++]);
				break;
			case I.popckvn:
				keepv = true; goto case I.popcn;
			case I.popckrn:
				keepr = true; goto case I.popcn;
			case I.popcn:
				auto bcctx = *cast(BCPointer*)&stack.stack[nargs-bcPointerBCSize];
				auto ctx = cast(ulong*)bcctx.ptr;
				auto n = cast(size_t)byteCode[ip++];
				auto loc = cast(size_t)stack.stack[stack.stp-n];
				mixin(CheckPointer!q{bcctx, loc, n});
				loc+=n;
				foreach(i;0..n) ctx[--loc]=stack.pop();
				if(keepr) keepr = false;
				else stack.pop(); // throw away loc
				if(keepv){
					foreach(i;0..n) stack.push(ctx[loc++]);
					keepv=false;
				}
				break;
			case I.pushccn:
				auto ctx = *cast(BCPointer*)&stack.stack[0];
				auto n = cast(size_t)byteCode[ip++];
				auto numc = cast(size_t)stack.pop();
				assert(numc>0);
				auto loc = cast(size_t)stack.pop();
				foreach(i;1..numc){
					mixin(CheckPointer!q{ctx, 0, bcPointerBCSize});
					ctx = *cast(BCPointer*)ctx.ptr;
				}
				mixin(CheckPointer!q{ctx, loc, n});
				foreach(i;0..n) stack.push((cast(ulong*)ctx.ptr)[loc++]);
				break;
			case I.popcckvn:
				keepv = true; goto case I.popccn;
			case I.popcckrn:
				keepr = true; goto case I.popccn;
			case I.popccn:
				auto ctx = *cast(BCPointer*)&stack.stack[0];
				auto n = cast(size_t)byteCode[ip++];
				auto numc = cast(size_t)stack.stack[stack.stp-n];
				assert(numc>0);
				auto loc = cast(size_t)stack.stack[stack.stp-n-1];
				foreach(i;1..numc){
					mixin(CheckPointer!q{ctx, 0, bcPointerBCSize});
					ctx = *cast(BCPointer*)ctx.ptr;
				}
				mixin(CheckPointer!q{ctx, loc, n});
				loc+=n;
				foreach(i;0..n) (cast(ulong*)ctx.ptr)[--loc]=stack.pop();
				if(keepr) keepr = false;
				else{
					stack.pop();
					stack.pop();
				}
				if(keepv){
					keepv = false;
					foreach(i;0..n) stack.push((cast(ulong*)ctx.ptr)[loc++]);
				}
				break;
			case I.ptrfc:
				auto ctx = *cast(BCPointer*)&stack.stack[nargs-bcPointerBCSize];
				auto siz = cast(size_t)byteCode[ip++];
				auto loc = cast(size_t)stack.pop();
				mixin(CheckPointer!q{ctx, loc, (siz+ulong.sizeof-1)/ulong.sizeof});
				void[] r = (ctx.ptr+loc*ulong.sizeof)[0..siz];
				stack.push(BCPointer(r, r.ptr));
				break;
			case I.ptrfcc:
				auto ctx = *cast(BCPointer*)&stack.stack[0];
				auto siz = cast(size_t)byteCode[ip++];
				auto numc = cast(size_t)stack.pop();
				assert(numc>0);
				auto loc = cast(size_t)stack.pop();
				foreach(i;1..numc){
					mixin(CheckPointer!q{ctx, 0, bcPointerBCSize});
					ctx = *cast(BCPointer*)ctx.ptr;
				}
				void[] r = (ctx.ptr+loc*ulong.sizeof)[0..siz];
				stack.push(BCPointer(r, r.ptr));
				break;
			case I.pushcontext:
				auto numc = cast(size_t)byteCode[ip++];
				if(!numc) stack.push(*cast(BCPointer*)&stack.stack[nargs-bcPointerBCSize]);
				else{
					auto ctx = *cast(BCPointer*)&stack.stack[0];
					foreach(i;1..numc){
						mixin(CheckPointer!q{ctx, 0, bcPointerBCSize});
						ctx = *cast(BCPointer*)ctx.ptr;
					}
					stack.push(ctx);
				}
				break;
			case I.pushr:
				auto loc = cast(size_t)stack.pop();
				stack.push(stack.stack[loc]);
				break;
			case I.popr:
				auto val = stack.pop();
				auto loc = cast(size_t)stack.pop();
				stack.stack[loc] = val;
				break;
			case I.pushr2:
				auto loc = cast(size_t)stack.pop();
				stack.push(stack.stack[loc]);
				stack.push(stack.stack[loc+1]);
				break;
			case I.popr2:
				auto val2 = stack.pop();
				auto val1 = stack.pop();
				auto loc = cast(size_t)stack.pop();
				stack.stack[loc]  =val1;
				stack.stack[loc+1]=val2;
				break;
			case I.pushrn:
				auto n   = cast(size_t)byteCode[ip++];
				auto loc = cast(size_t)stack.pop();
				foreach(i;0..n) stack.push(stack.stack[loc++]);
				break;
			case I.poprkrn:
				keepr = true; goto case I.poprn;
			case I.poprn:
				auto n   = cast(size_t)byteCode[ip++];
				auto loc = cast(size_t)stack.stack[stack.stp-n]+n;
				foreach(i;0..n) stack.stack[--loc]=stack.pop();
				if(keepr) keepr = false;
				else stack.pop(); // throw away loc
				break;
			case I.poprkv:
				auto val = stack.pop();
				auto loc = cast(size_t)stack.pop();
				stack.stack[loc] = val;
				stack.push(val);
				break;
			case I.poprkr:
				auto val = stack.pop();
				auto loc = cast(size_t)stack.top();
				stack.stack[loc] = val;
				break;
			case I.poprkv2:
				auto val2 = stack.pop();
				auto val1 = stack.pop();
				auto loc = cast(size_t)stack.pop();
				stack.stack[loc]  =val1;
				stack.stack[loc+1]=val2;
				stack.push(val1);
				stack.push(val2);
				break;
			case I.poprkr2:
				auto val2 = stack.pop();
				auto val1 = stack.pop();
				auto loc = cast(size_t)stack.top();
				stack.stack[loc]  =val1;
				stack.stack[loc+1]=val2;
				break;
			case I.poprkvn:
				auto n   = cast(size_t)byteCode[ip]; // pushrn increases ip
				auto loc = cast(size_t)stack.stack[stack.stp-n]+n;
				foreach(i;0..n) stack.stack[--loc]=stack.pop();
				goto case I.pushrn; // restore value
			case I.swap:
				auto v1 = stack.pop();
				auto v2 = stack.pop();
				stack.push(v1);
				stack.push(v2);
				break;
			case I.swap2:
				auto a2 = stack.pop();
				auto a1 = stack.pop();
				auto b2 = stack.pop();
				auto b1 = stack.pop();
				stack.push(a1);
				stack.push(a2);
				stack.push(b1);
				stack.push(b2);
				break;
			case I.swapn:
				auto n = cast(size_t)byteCode[ip++];
				for(auto i=stack.stp-2*n+1, j=stack.stp-n+1;j<=stack.stp; i++, j++)
					swap(stack.stack[i], stack.stack[j]);
				break;
			case I.dup:
				stack.push(stack.top());
				break;
			case I.dup2:
				stack.push(stack.stack[stack.stp-1]);
				stack.push(stack.stack[stack.stp-1]);
				break;
			case I.dupn:
				auto n = cast(size_t)byteCode[ip++];
				foreach(i;0..n) stack.push(stack.stack[stack.stp-n+1]);
				break;
			case I.rot:
				auto top = stack.pop();
				auto ltop = stack.pop();
				auto lltop = stack.pop();
				stack.push(top);
				stack.push(lltop);
				stack.push(ltop);
				break;
			case I.rot2:
				auto top2 = stack.pop();
				auto top1 = stack.pop();
				auto ltop2 = stack.pop();
				auto ltop1 = stack.pop();
				auto lltop2 = stack.pop();
				auto lltop1 = stack.pop();
				stack.push(top1);
				stack.push(top2);
				stack.push(lltop1);
				stack.push(lltop2);
				stack.push(ltop1);
				stack.push(ltop2);
				break;
			case I.rot221:
				auto top2 = stack.pop();
				auto top1 = stack.pop();
				auto ltop2 = stack.pop();
				auto ltop1 = stack.pop();
				auto lltop = stack.pop();
				stack.push(top1);
				stack.push(top2);
				stack.push(lltop);
				stack.push(ltop1);
				stack.push(ltop2);
				break;
			case I.alloca:
				auto amt = cast(size_t)stack.pop();
				foreach(i;0..amt) stack.push(0); // TODO: do in one go
				nargs += amt;
				foreach(i; nargs..stack.stp+1)
					swap(stack.stack[i], stack.stack[i-amt]);
				break;
			case I.allocc: // heap allocation of context
				auto amt = cast(size_t)byteCode[ip++];
				auto ctx = new void[amt*ulong.sizeof];
				stack.push(BCPointer(ctx, ctx.ptr));
				nargs+=bcPointerBCSize;
				break;
			// temporaries
			case I.tmppush:
				tmpstack.push(stack.pop());
				break;
			case I.tmppop:
				stack.push(tmpstack.pop());
				break;
			// type conversion
			case I.int2bool:
				stack.top() = cast(bool)stack.top();
				break;
			case I.real2bool:
				stack.push(cast(bool)stack.pop!real());
				break;
			case I.trunc:
				stack.top()&=(1UL<<byteCode[ip++])-1;
				break;
			case I.truncs:
				auto bits = byteCode[ip++];
				auto mask = (1UL<<bits)-1;
				stack.top()&=mask;
				if(stack.top() & (1UL<<bits-1)) stack.top()|=~mask;
				break;
			case I.uint2real:
				stack.push(cast(real)stack.pop());
				break;
			case I.real2uint:
				stack.push(cast(ulong)stack.pop!real());
				break;
			case I.int2real:
				stack.push(cast(real)cast(long)stack.pop());
				break;
			case I.real2int:
				stack.push(cast(long)stack.pop!real());
				break;
			case I.real2double:
				stack.push(cast(double)stack.pop!real());
				break;
			case I.double2real:
				stack.push(cast(real)stack.pop!double());
				break;
			case I.real2float:
				stack.push(cast(float)stack.pop!real());
				break;
			case I.float2real:
				stack.push(cast(real)stack.pop!float());
				break;
			// arithmetics
			case I.negi:
				stack.top() = -stack.top();
				break;
			case I.noti:
				stack.top() = ~stack.top();
				break;
			case I.notb:
				stack.top() = !stack.top();
				break;
			case I.addi:
				auto val = stack.pop();
				stack.top()+=val;
				break;
			case I.subi:
				auto val = stack.pop();
				stack.top()-=val;
				break;
			case I.muli:
				auto val = stack.pop();
				stack.top()*=val;
				break;
			case I.divi:
				auto val = stack.pop();
				if(val){ stack.top()/=val; break; }
				goto Ldivbyzero;
			case I.divsi:
				long val = stack.pop();
				if(val){ stack.top()=cast(long)stack.top()/val; break; }
				goto Ldivbyzero;
			case I.modi:
				auto val = stack.pop();
				if(val){ stack.top()%=val; break; }
				goto Ldivbyzero;
			case I.modsi:
				long vall = stack.pop();
				if(vall){ stack.top()=cast(long)stack.top()%vall; break; }
				goto Ldivbyzero;

				foreach(tt; ToTuple!(["float","double","real"])){
					enum s = tt[0];
					mixin("alias "~tt~" T;");
					case mixin(`I.add`~s):
						stack.push(stack.pop!T()+stack.pop!T());
						break swtch;
					case mixin(`I.sub`~s):
						auto val = stack.pop!T();
						stack.push(stack.pop!T()-val);
						break swtch;
					case mixin(`I.mul`~s):
						stack.push(stack.pop!T()*stack.pop!T());
						break swtch;
					case mixin(`I.div`~s):
						auto val = stack.pop!T();
						stack.push(stack.pop!T()/val);
						break swtch;
					case mixin(`I.mod`~s):
						auto val = stack.pop!T();
						stack.push(stack.pop!T()%val);
						break swtch;
			}

			// shifts
			case I.shl32:
				auto val = stack.pop();
				if(val<32){ stack.top()<<=val; break; }
				tmp[0] = val; // shamt
				tmp[1] = 31;  // max shamt
				goto Lshiftoutofrange;
			case I.shr32:
				auto val = stack.pop();
				if(val<32){ stack.top()>>>=val; break; }
				tmp[0] = val; // shamt
				tmp[1] = 31;  // max shamt
				goto Lshiftoutofrange;
			case I.sar32:
				long val = stack.pop();
				if(val<32){ stack.top()=cast(long)stack.top()>>val; break; }
				tmp[0] = val; // shamt
				tmp[1] = 31;  // max shamt
				goto Lshiftoutofrange;
			case I.shl64:
				auto val = stack.pop();
				if(val<64){ stack.top()<<=val; break; }
				tmp[0] = val; // shamt
				tmp[1] = 63;  // max shamt
				goto Lshiftoutofrange;
			case I.shr64:
				auto val = stack.pop();
				if(val<64){ stack.top()>>>=val; break; }
				tmp[0] = val; // shamt
				tmp[1] = 63;  // max shamt
				goto Lshiftoutofrange;
			case I.sar64:
				long val = stack.pop();
				if(val<64){ stack.top()=cast(long)stack.top()>>val; break; }
				tmp[0] = val; // shamt
				tmp[1] = 63;  // max shamt
				goto Lshiftoutofrange;
			// bitwise ops
			case I.or:
				auto val = stack.pop();
				stack.top()|=val;
				break;
			case I.xor:
				auto val = stack.pop();
				stack.top()^=val;
				break;
			case I.and:
				auto val = stack.pop();
				stack.top()&=val;
				break;
			// comparison
			case I.cmpei:
				auto val = stack.pop();
				stack.top()=stack.top()==val;
				break;
			case I.cmpnei:
				auto val = stack.pop();
				stack.top()=stack.top()!=val;
				break;
			case I.cmpli:
				long val = stack.pop();
				stack.top()=cast(long)stack.top()<val;
				break;
			case I.cmplei:
				long val = stack.pop();
				stack.top()=cast(long)stack.top()<=val;
				break;
			case I.cmpbi:
				auto val = stack.pop();
				stack.top()=stack.top()<val;
				break;
			case I.cmpbei:
				auto val = stack.pop();
				stack.top()=stack.top()<=val;
				break;
			case I.cmpgi:
				long val = stack.pop();
				stack.top()=cast(long)stack.top()>val;
				break;
			case I.cmpai:
				auto val = stack.pop();
				stack.top()=stack.top()>val;
				break;
			case I.cmpgei:
				long val = stack.pop();
				stack.top()=cast(long)stack.top()>=val;
				break;
			case I.cmpaei:
				auto vall = stack.pop();
				stack.top()=stack.top()>=vall;
				break;

			foreach(tt; ToTuple!(["float","double","real"])){
				enum s = tt[0];
				mixin("alias "~tt~" T;");
				enum ops=[["is","is"],["e","=="],["l","<"],["le","<="],["ne","!="],["g",">"],["ge",">="]];

				foreach(i; ToTuple!([0,1,2,3,4,5,6])){
					enum op = ops[i];
					case mixin(`I.cmp`~op[0]~s):
						auto val = stack.pop!T();
						stack.push(mixin(`stack.pop!T() `~op[1]~` val`));
						break swtch;
				}
			}
			// array operations
			case I.ptra:
				auto bcs = stack.pop!BCSlice();
				stack.push(bcs.getPtr());
				break;
			case I.lengtha:
				auto els = cast(size_t)byteCode[ip++];
				auto bcs = stack.pop!BCSlice();
				stack.push(bcs.getLength()/els);
				break;
			case I.setlengtha:
				auto els = cast(size_t)byteCode[ip++];
				auto len = cast(size_t)stack.pop();
				auto bcs = stack.pop!BCSlice();
				bcs.setLength(len*els); // TODO: check for overflow?
				stack.push(bcs);
				break;
			case I.newarray:
				auto els = cast(size_t)byteCode[ip++];
				auto len = cast(size_t)stack.pop();
				stack.push(BCSlice(new void[els*len]));
				break;
			case I.makearray:
				auto els = cast(size_t)byteCode[ip++];
				auto len = cast(size_t)stack.pop();
				auto siz=((els+ulong.sizeof-1)/ulong.sizeof);
				auto stlen = len*siz;
				assert(nargs+stlen<=stack.stp+1);
				auto el = stack.stack[stack.stp+1-stlen..stack.stp+1];
				auto r = new void[els*len];

				for(size_t i=0,j=0;i<el.length;i+=siz,j+=els)
					memcpy(&r[j], &el[i], els);

				stack.pop(stlen);
				stack.push(BCSlice(r));
				break;
			case I.appenda:
				auto arr2 = stack.pop!BCSlice().slice;
				auto arr1 = stack.pop!BCSlice().slice;
				stack.push(BCSlice(arr1 ~= arr2));
				break;
			case I.concata:
				auto arr2 = stack.pop!BCSlice().slice;
				auto arr1 = stack.pop!BCSlice().slice;
				stack.push(BCSlice(arr1 ~ arr2));
				break;
			case I.loadak:
				keepr = true; goto case I.loada;
			case I.loada:
				auto els = cast(size_t)byteCode[ip++];
				auto i = cast(size_t)stack.pop();
				auto bcs = stack.pop!BCSlice();
				if(keepr){
					stack.push(bcs);
					stack.push(i);
					keepr=false;
				}
				auto r = bcs.slice;
				assert(!(r.length%els));
				if(i*els>=r.length) {
					tmp[0] = i;            // index
					tmp[1] = r.length/els; // array dimension
					goto Loutofbounds;
				}
				stack.pushRaw(r[i*els..(i+1)*els]);
				break;
			case I.storeakr:
				keepr = true; goto case I.storea;
			case I.storeakv:
				keepv = true; goto case I.storea;
			case I.storea:
				auto els = cast(size_t)byteCode[ip++];
				auto data = stack.popRawSliceStack(els);
				//assert(els<=16);
				//auto v2 = els>8?stack.pop():0;
				//auto v1 = stack.pop();
				auto i = cast(size_t)stack.pop();
				auto bcs = stack.pop!BCSlice();
				auto r = bcs.slice;
				assert(!(r.length%els));
				if(i*els>=r.length) {
					tmp[0] = i;            // index
					tmp[1] = r.length/els; // array dimension
					goto Loutofbounds;
				}
				r[i*els..(i+1)*els]=data[];
				if(keepr){
					stack.push(bcs);
					stack.push(i);
					keepr = false;
				}
				if(keepv){
					stack.pushRaw(data);
					keepv = false;
				}
				break;
			case I.slicea:
				auto els = cast(size_t)byteCode[ip++];
				auto r = cast(size_t)stack.pop();
				auto l = cast(size_t)stack.pop();
				auto a = stack.pop!BCSlice();
				if(l*els<=r*els && r*els<=a.slice.length){
					a.slice = a.slice[l*els..r*els];
					stack.push(a);
					break;
				}
				tmp[0] = l;
				tmp[1] = r;
				tmp[2] = a.slice.length/els;
				goto Lsliceoutofbounds;
			// arrays of arrays
			case I.loadaa:
				auto i = cast(size_t)stack.pop();
				auto bcs = stack.pop!BCSlice();
				auto r = cast(BCSlice[])bcs.slice;
				if(i<r.length) { stack.push(r[i]); break; }
				tmp[0] = i;            // index
				tmp[1] = r.length;     // array dimension
				goto Loutofbounds;
			case I.loadaak:
				auto i = cast(size_t)stack.pop();
				auto bcs = stack.pop!BCSlice();
				auto r = cast(BCSlice[])bcs.slice;
				stack.push(bcs);
				stack.push(i);
				if(i<r.length) { stack.push(r[i]); break; }
				tmp[0] = i;            // index
				tmp[1] = r.length;     // array dimension
				goto Loutofbounds;
				break;
			case I.storeaakr:
				keepr = true; goto case I.storeaa;
			case I.storeaakv:
				keepv = true; goto case I.storeaa;
			case I.storeaa:
				auto v = stack.pop!BCSlice();
				auto i = cast(size_t)stack.pop();
				auto bcs = stack.pop!BCSlice();
				auto r = cast(BCSlice[])bcs.slice;
				if(i>=r.length) {
					tmp[0] = i;            // index
					tmp[1] = r.length;     // array dimension
					goto Loutofbounds;
				}
				r[i]=v;
				if(keepr){
					stack.push(bcs);
					stack.push(i);
					keepr = false;
				}
				if(keepv){
					stack.push(v);
					keepv = false;
				}
				break;
			// pointer operations
			case I.loadap:
				auto els = cast(size_t)byteCode[ip++];
				auto i   = cast(size_t)stack.pop();
				auto bcs = stack.pop!BCSlice();
				auto ptr = bcs.getPtr();
				ptr.ptr+=i*els;
				stack.push(ptr);
				break;
			case I.ptrtoa:
				auto r = stack.pop!BCPointer();
				if(r.ptr>=r.container.ptr && r.ptr<r.container.ptr+r.container.length){
					stack.push(BCSlice(r.container, r.ptr[0..r.container.ptr+r.container.length-r.ptr]));
					break;
				}
				tmp[0] = r.ptr is null; // is null
				tmp[1] = r.container.length&&r.ptr == r.container.ptr+r.container.length; // off by one at the end
				tmp[2] = cast(ulong)r.ptr;
				tmp[3] = cast(ulong)r.container.ptr; // for checking of off by one at the beg.
				goto Linvalidpointer;
			case I.addp:
				auto els = cast(size_t)byteCode[ip++];
				auto val = cast(size_t)stack.pop();
				auto ptr = stack.pop!BCPointer();
				ptr.ptr+=val*els;
				stack.push(ptr);
				break;

				enum ops=[["e","=="],["b","<"],["be","<="],["ne","!="],["a",">"],["ae",">="]];

				foreach(i; ToTuple!([0,1,2,3,4,5])){
					enum op = ops[i];
					case mixin(`I.cmp`~op[0]~'p'):
						auto b = stack.pop!BCPointer();
						auto a = stack.pop!BCPointer();
						stack.push(mixin(`a.ptr`~op[1]~`b.ptr`));
						break swtch;
				}
			// field operations
			case I.loadfkr:
				keepr = true; goto case I.loadf;
			case I.loadf:
				auto off = cast(size_t)byteCode[ip++];
				auto len = cast(size_t)byteCode[ip++];
				auto bptr = stack.pop!BCPointer();
				auto ptr = cast(ulong*)bptr.ptr;
				if(keepr){
					stack.push(bptr);
					keepr = false;
				}
				mixin(CheckPointer!q{bptr, off, len});
				foreach(i;off..off+len) stack.push(ptr[i]);
				break;
			case I.storefkr:
				keepr = true; goto case I.storef;
			case I.storefkv:
				keepv = true; goto case I.storef;
			case I.storef:
				auto off = cast(size_t)byteCode[ip++];
				auto len = cast(size_t)byteCode[ip++];
				auto data = stack.stack[stack.stp+1-len..stack.stp+1];
				stack.stp -= len;
				auto bptr = stack.pop!BCPointer();
				auto ptr = cast(ulong*)bptr.ptr;
				if(keepr){
					stack.push(bptr);
					keepr=false;
				}
				mixin(CheckPointer!q{bptr, off, len});
				foreach(i,x;data) ptr[off+i]=x;
				if(keepv){
					stack.pushRaw(data);
					keepv=false;
				}
				break;
			case I.ptrf:
				auto off = cast(size_t)byteCode[ip++]*ulong.sizeof;
				auto len = cast(size_t)byteCode[ip++];
				auto ptr = stack.pop!BCPointer();
				import std.algorithm: min;
				void[] container=ptr.ptr[off..off+len];
				if(!(ptr.container.ptr<=container.ptr&&container.ptr+len<=ptr.container.ptr+ptr.container.length)) container=[];
				stack.push(BCPointer(container,ptr.ptr+off));
				break;
			// virtual methods
			case I.fetchvtbl:
				auto index = cast(size_t)byteCode[ip++];
				auto aggr = cast(ReferenceAggregateDecl)cast(void*)stack.pop();
				static assert(Symbol.sizeof<=(void*).sizeof&&(void*).sizeof<=ulong.sizeof);
				stack.push(cast(ulong)cast(void*)aggr.bcFetchVTBL(index));
				break;
			case I.fetchoverride:
				auto fun = cast(FunctionDecl)cast(void*)byteCode[ip++];
				auto aggr = cast(ReferenceAggregateDecl)cast(void*)stack.pop();
				static assert(Symbol.sizeof<=(void*).sizeof&&(void*).sizeof<=ulong.sizeof);
				stack.push(cast(ulong)cast(void*)aggr.bcFetchOverride(fun));
				break;
			// partially analyzed functions
			case I.analyzeandfail:
				auto stm = cast(Node)cast(void*)byteCode[ip++];
				auto sc = cast(Scope)cast(void*)byteCode[ip++];
				static struct MakeStrong{
					void perform(Symbol sym){
						// TODO: this is a little hacky, is there a more elegant way?
						if(sym.meaning&&sym.meaning.isFunctionDecl() && sym.meaning.sstate <= SemState.started)
							sym.meaning.sstate = SemState.begin;
					}
				}
				import analyze;
				runAnalysis!MakeStrong(stm);
				stm.semantic(sc); // TODO!
				throw new UnwindException(stm.loc);
				// casts from void[] and void*
				{
					enum castfromcode=q{
						auto ltt = stack.pop();
						auto t1 = cast(Type)cast(void*)ltt;
						auto t2 = *cast(Type*)&byteCode[ip++];
						auto rcd = t1.refConvertsTo(t2,0);
						if(auto d=rcd.dependee) throw new CTFERetryException(d.node);
						if(!rcd.value){
							tmp[0] = ltt;
							goto Lcastfailure;
						}
					};
					case I.castfromvarr:
						auto slice = stack.pop!BCSlice();
						mixin(castfromcode);
						stack.push(slice);
						break;
					case I.castfromvptr:
						auto ptr = stack.pop!BCPointer();
						mixin(castfromcode);
						stack.push(ptr);
						break;
				}
			case I.errtbl:
				assert(0, "TODO: static definite return analysis");
		}
	}
	ErrorInfo obtainErrorInfo(){
		size_t i, j;
		for(i=0, j=0;i<ip; i++){
			if(isUnsafe(cast(Instruction)byteCode[i])) j++;
			i+=numArgs(cast(Instruction)byteCode[i]);
		}
		for(; byteCode[i]!=Instruction.errtbl; i++)
			i+=numArgs(cast(Instruction)byteCode[i]);

		return (cast(ErrorInfo[])byteCode[i+1..$])[j-1];
	}
	void fail(Location loc){ throw new UnwindException(loc); }
Ldivbyzero:
	auto info0 = obtainErrorInfo();
	handler.error("divide by zero", info0.loc);
	fail(info0.loc);
Loutofbounds:
	auto info1 = obtainErrorInfo();
	auto s_t = Type.get!Size_t();
	if(s_t.getSizeof()==uint.sizeof) tmp[0] = cast(uint)tmp[0];
	else assert(s_t.getSizeof()==ulong.sizeof);
	handler.error(format("array index %s%s is out of bounds [0%s..%d%s)",tmp[0],Size_t.suffix,Size_t.suffix,tmp[1],Size_t.suffix),info1.loc);
	fail(info1.loc);
Lshiftoutofrange:
	auto info2 = obtainErrorInfo();
	bool isSigned;
	if(auto e = cast(BinaryExp!(Tok!"<<"))info2) isSigned=(cast(BasicType)e.e2.type).isSigned();
	else if(auto e = cast(BinaryExp!(Tok!">>"))info2) isSigned=(cast(BasicType)e.e2.type).isSigned();
	else if(auto e = cast(BinaryExp!(Tok!">>>"))info2) isSigned=(cast(BasicType)e.e2.type).isSigned();
	if(isSigned) handler.error(format("shift amount of %d is outside the range 0..%d", cast(long)tmp[0], tmp[1]),info2.loc);
	else handler.error(format("shift amount of %d is outside the range 0..%d", tmp[0], tmp[1]),info2.loc);
	fail(info2.loc);
Linvalidpointer:
	auto info3 = obtainErrorInfo();
	bool offby1=cast(bool)tmp[1];
	if(!offby1){
		auto exp=cast(Expression)info3;
		if(!exp.type.isFunctionTy())// TODO: this should not even be reached
		if(exp && tmp[2]+getCTSizeof(exp.type)==tmp[3]) offby1 = true;
	}
	handler.error(format("%s pointer dereference%s",tmp[0]?"null":"invalid",offby1?" (off by one)":""), info3.loc);
	fail(info3.loc);
Lsliceoutofbounds:
	auto info4 = obtainErrorInfo();
	auto s_t2 = Type.get!Size_t();
	if(s_t2.getSizeof()==uint.sizeof) tmp[0]=cast(uint)tmp[0], tmp[1]=cast(uint)tmp[1];
	else assert(s_t2.getSizeof()==ulong.sizeof);
	if(tmp[0]>tmp[2]||tmp[1]>tmp[2]){
		handler.error(format("slice indices [%dU..%dU] are out of bounds [0U..%dU]",tmp[0],tmp[1],tmp[2]),info4.loc);
	}else{
		assert(tmp[0]>tmp[1]);
		handler.error(format("lower slice index %dU exceeds upper slice index %dU",tmp[0],tmp[1]),info4.loc);
	}
	fail(info4.loc);
Lnullfunction:
	auto info5 = obtainErrorInfo();
	assert(!!cast(CallExp)info5);
	auto ce = cast(CallExp)cast(void*)info5;
	handler.error(format("null %s dereference", ce.e.type.isDelegateTy?"delegate":"function pointer"),ce.loc);
	fail(info5.loc);
Lcastfailure:
	auto castinfo = obtainErrorInfo();
	assert(!!cast(CastExp)castinfo);
	auto cae = cast(CastExp)cast(void*)castinfo;
	auto t1 = cast(Type)cast(void*)tmp[0];
	handler.error(format("cannot interpret cast from '%s' aliasing a '%s' to '%s' at compile time", cae.e.type,t1,cae.type), cae.loc); // TODO: 'an'
	fail(castinfo.loc);
Linvfunction:
	auto info6 = obtainErrorInfo();
	handler.error("interpretation of invalid function failed", info6.loc);
	fail(info6.loc);
Lhlt:
	auto hltinfo = cast(HltErrorInfo)cast(void*)obtainErrorInfo();
	handler.error(hltinfo.err, hltinfo.loc);
	fail(hltinfo.loc);
Lhltstr:
	auto hltsinfo = obtainErrorInfo();
	string err = cast(string)stack.pop!BCSlice().slice;
	handler.error(err, hltsinfo.loc);
	fail(hltsinfo.loc);
}


mixin template CTFEInterpret(T) if(!is(T==Node)&&!is(T==FunctionDef)&&!is(T==TemplateDecl)&&!is(T==TemplateInstanceDecl) && !is(T==BlockDecl) && !is(T==PragmaDecl) && !is(T==EmptyStm) && !is(T==CompoundStm) && !is(T==ILabeledStm) && !is(T==LabeledStm) && !is(T==ExpressionStm) && !is(T==IfStm) && !is(T==ForStm) && !is(T==ForeachStm) && !is(T==ForeachRangeStm) && !is(T==WhileStm) && !is(T==DoStm) && !is(T==SwitchStm) && !is(T==SwitchLabelStm) && !is(T==CaseStm) && !is(T==CaseRangeStm) && !is(T==DefaultStm) && !is(T==LiteralExp) && !is(T==ArrayLiteralExp) && !is(T==ReturnStm) && !is(T==CastExp) && !is(T==Symbol) && !is(T==FieldExp) && !is(T==ConditionDeclExp) && !is(T==VarDecl) && !is(T==Expression) && !is(T==ExpTuple) && !is(T _==BinaryExp!S,TokenType S) && !is(T==ABinaryExp) && !is(T==AssignExp) && !is(T==TupleAssignExp) && !is(T==TernaryExp)&&!is(T _==UnaryExp!S,TokenType S) && !is(T _==PostfixExp!S,TokenType S) &&!is(T==Declarators) && !is(T==BreakStm) && !is(T==ContinueStm) && !is(T==GotoStm) && !is(T==WithStm) && !is(T==BreakableStm) && !is(T==LoopingStm) && !is(T==SliceExp) && !is(T==AssertExp) && !is(T==CallExp) && !is(T==Declaration) && !is(T==PtrExp)&&!is(T==LengthExp)&&!is(T==DollarExp)&&!is(T==AggregateDecl)&&!is(T==ReferenceAggregateDecl)&&!is(T==UnionDecl)&&!is(T==AggregateTy)&&!is(T==TmpVarExp)&&!is(T==TemporaryExp)&&!is(T==StructConsExp)&&!is(T==NewExp)&&!is(T==CurrentExp)&&!is(T:Type)){}


mixin template CTFEInterpret(T) if(is(T==Node)){
	void byteCompile(ref ByteCodeBuilder bld){
		import std.stdio; writeln(this);
		assert(0, to!string(typeid(this)));}
}

mixin template CTFEInterpret(T) if(is(T==Declaration)){
	override void byteCompile(ref ByteCodeBuilder bld){
		/+ do nothing +/
	}

}

mixin template CTFEInterpret(T) if(is(T==Expression)){
	// some expressions can be lvalues
	LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){assert(0, to!string(typeid(this))~" "~to!string(this));}

	// enable TCO for expressions that include flow control
	void byteCompileRet(ref ByteCodeBuilder bld, bool isRefReturn){
		if(isRefReturn) UnaryExp!(Tok!"&").emitAddressOf(bld,this);
		else byteCompile(bld);
		bld.emit(Instruction.ret);
	}

	final FunctionDef createCallWrapper(Scope sc){
		auto bdy = New!BlockStm(cast(Statement[])[New!ReturnStm(this)]);
		auto fty=New!FunctionTy(STC.init,cast(Expression)null,cast(Parameter[])null,VarArgs.none);
		auto dg=New!FunctionDef(STCstatic,fty,New!Identifier("__ctfeCallWrapper"),cast(BlockStm)null,cast(BlockStm)null,cast(Identifier)null,bdy);
		dg.sstate = SemState.begin;
		dg.scope_ = sc;
		dg.semantic(sc);
		mixin(Rewrite!q{dg});
		while(dg.sstate!=SemState.completed){
			dg.semantic(sc);
			mixin(Rewrite!q{dg});
			assert(dg.sstate!=SemState.error);
		}
		dg.loc = loc;
		// The following is here to make sure that inaccessible contexts are never compiled in
		// TODO: is this correct?
		static struct UpdateScopes{
			Scope sc;
			void perform(Symbol self){
				if(!self.meaning) return;
				self.scope_ = sc;
				if(self.meaning.isTmpVarDecl()){
					// note: if this tmpVarDecl was expanded from a tuple declaration
					// then the tuple declaration will not necessarily change scope
					// this can result in a somewhat counter-intuitive AST state
					// TODO: countermeasures?
					self.meaning.scope_ = sc;
				}
			}
			void perform(CurrentExp self){ self.scope_ = sc; }
		}
		runAnalysis!UpdateScopes(this,dg.fsc);
		return dg;
	}
	final void callWrapper(Scope sc, ref FunctionDef ctfeCallWrapper, Expression e){
		if(sstate == SemState.error) return;
		if(rewrite) return;
		//Scheduler().add(this,sc); //(the scheduler might already have finished off the expression) TODO: more elegant solution
		static struct MakeStrong{
			void perform(Symbol sym){
				// allow interpretation of partially analyzed functions
				// (TODO: fix implementation)
/+				if(sym.meaning &&
				   (!sym.meaning.isFunctionDecl() || sym.meaning.sstate != SemState.started)){
					sym.makeStrong();
				}+/
				sym.makeStrong();
			}
		}
		runAnalysis!MakeStrong(this);
		if(e) mixin(SemChld!q{e});
		Expression r;
		if(!ctfeCallWrapper){
			//if(args.length == 0) ctfeCallWrapper = fn;
			//else{
			ctfeCallWrapper = createCallWrapper(sc);
			//}
		}
		try{
			r = ctfeCallWrapper.interpretCall(sc.handler).toExpr();
			r.type = type;
			r.loc = this.loc;
			mixin(RewEplg!q{r});
		}catch(CTFERetryException e){
			mixin(PropRetry!(q{e.node},false));
			needRetry = true;
		}catch(UnwindException e){
			// (only show note if not totally obvious)
			// (also makes sure calls from the constant folder
			// into the interpreter are seamless.)
			if(loc.rep.ptr+loc.rep.length<=e.loc.rep.ptr||
			   loc.rep.ptr>=e.loc.rep.ptr+e.loc.rep.length)
				sc.note("during evaluation requested here", loc);
			mixin(ErrEplg);
		}catch(SilentUnwindException){
			mixin(ErrEplg);
		}
	}
}

mixin template CTFEInterpret(T) if(is(T==ExpTuple)){
	override void byteCompile(ref ByteCodeBuilder bld){
		foreach(x; exprs) x.byteCompile(bld);
	}
	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		auto lvs=new LValueStrategy[](exprs.length);
		foreach(i,x;exprs) lvs[i]=x.byteCompileLV(bld);
		assert(cast(TypeTuple)type);
		auto ty=cast(TypeTuple)cast(void*)type;
		return LVtuple(lvs,ty);
	}
}

mixin template CTFEInterpret(T) if(is(T==EmptyStm)){
	override void byteCompile(ref ByteCodeBuilder bld){ /+ ; +/ }
}

mixin template CTFEInterpret(T) if(is(T _==UnaryExp!S,TokenType S)){
	static if(is(T _==UnaryExp!S,TokenType S)):
	override void byteCompile(ref ByteCodeBuilder bld){
		alias Instruction I;
		static if(S!=Tok!"&") auto tu = e.type.getHeadUnqual();
		static if(S==Tok!"+"){
			assert(tu.isBasicType()||tu.isPointerTy());
			e.byteCompile(bld);
		}else static if(S==Tok!"-"||S==Tok!"~"||S==Tok!"!"){
			assert(tu.isBasicType());
			e.byteCompile(bld);
			if(auto bt = tu.isIntegral()){
				bld.emit(S==Tok!"-"?I.negi:S==Tok!"~"?I.noti:I.notb);
				static if(S==Tok!"!"){if(tu !is Type.get!bool()) bld.emit(I.int2bool);}
				else{
					auto size = bt.bitSize();
					if(size<63){
						bld.emit(bt.isSigned()?I.truncs:I.trunc);
						bld.emitConstant(size);
					}
				}
			}
		}else static if(S==Tok!"++" || S==Tok!"--") byteCompileHelper(bld, false);
		else static if(S==Tok!"&"){
			emitAddressOf(bld, e);
		}else static if(S==Tok!"*"){
			e.byteCompile(bld);
			if(type.isFunctionTy()) return;
			bld.emitUnsafe(I.ptrtoa, this);
			bld.emit(I.push);
			bld.emitConstant(0);
			if(LVstorea.isArrElement(type)) bld.emitUnsafe(I.loadaa, this);
			else{
				bld.emitUnsafe(I.loada, this);
				bld.emitConstant(getCTSizeof(type));
				ctToBCAdjust(bld, type);
			}
		}else static assert(0,TokChars!S);
	}

	static if(S==Tok!"&"){
		static void emitAddressOf(ref ByteCodeBuilder bld, Expression e){
			auto tu = e.type.getHeadUnqual();
			if(tu.isFunctionTy()){
				assert(cast(Symbol)e||cast(FieldExp)e);
				e.byteCompile(bld);
			}else{
				auto strat = e.byteCompileLV(bld);
				strat.emitPointer(bld);
			}
		}
	}

	static if(S==Tok!"*"){
		override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
			e.byteCompile(bld);
			auto ptr=e.type.getHeadUnqual().isPointerTy();
			return LVpointer(ptr.ty, this);
		}
	}

	static if(S==Tok!"++" || S==Tok!"--"):
	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		return byteCompileHelper(bld, true);
	}

	private final LValueStrategy byteCompileHelper(ref ByteCodeBuilder bld, bool isLvalue){
		alias Instruction I;
		auto strat = e.byteCompileLV(bld);
		strat.emitLoadKR(bld);
		if(auto bt = type.isIntegral()){
			bld.emit(I.push);
			bld.emitConstant(1);
			bld.emit(S==Tok!"++"?I.addi:I.subi);
			auto size = bt.bitSize();
			if(size < 64){
				bld.emit(bt.isSigned()?I.truncs:I.trunc);
				bld.emitConstant(size);
			}
		}else if(auto ptr = type.isPointerTy()){
			bld.emit(I.push);
			bld.emitConstant(S==Tok!"++"?1:-1);
			bld.emit(I.addp);
			bld.emitConstant(getCTSizeof(ptr.ty));
		}else assert(0);
		if(isLvalue){
			strat.emitStoreKR(bld);
			return strat;
		}else{
			strat.emitStoreKV(bld);
			return null;
		}
	}
}

mixin template CTFEInterpret(T) if(is(T _==PostfixExp!S,TokenType S)){
	static if(is(T _==PostfixExp!S,TokenType S)):
	static assert(S==Tok!"++"||S==Tok!"--");
	override void byteCompile(ref ByteCodeBuilder bld){
		alias Instruction I;
		auto strat = e.byteCompileLV(bld);
		strat.emitLoadKR(bld);
		auto tu = e.type.getHeadUnqual();
		auto siz = getBCSizeof(tu);
		bld.emitDup(siz);
		bld.emit(I.push);
		bld.emitConstant(S==Tok!"++"?1:-1);
		if(auto bt = tu.isIntegral()){
			assert(bt.getSizeof()<=8);
			bld.emit(I.addi);
			auto size = bt.bitSize();
			if(size < 64){
				bld.emit(bt.isSigned()?I.truncs:I.trunc);
				bld.emitConstant(size);
			}
		}else if(auto ptr = tu.isPointerTy()){
			bld.emit(I.addp);
			bld.emitConstant(getCTSizeof(ptr.ty));
		}else{super.byteCompile(bld); assert(0);} // TODO: fix!
		bld.emitSwap(siz);
		bld.emitTmppush(siz);
		strat.emitStore(bld);
		bld.emitTmppop(siz);
	}
}

enum byteCompileDollar = q{
	if(dollar){
		dollar.byteCompile(bld);
		bld.emitDup(getBCSizeof(e.type));
		bld.emit(Instruction.lengtha);
		bld.emitConstant(siz);

		auto bcs_t = getBCSizeof(Type.get!Size_t());
		bld.emitTmppush(bcs_t);
		auto strat = dollar.byteCompileSymbolLV(bld,this,ascope);
		bld.emitTmppop(bcs_t);
		strat.emitStore(bld);
	}
};

void ctToBCAdjust(ref ByteCodeBuilder bld, Type t){
	if(auto i=t.isIntegral()){
		if(i.isSigned()){
			auto bs=i.bitSize();
			if(bs<64){
				bld.emit(Instruction.truncs);
				bld.emitConstant(bs);
			}
		}
	}
}

// workaround for DMD bug, other part is in expression.IndexExp
mixin template CTFEInterpretIE(T) if(is(T _==IndexExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		alias Instruction I;
		void bcLeftover(){
			if(aLeftover) ExpressionStm.byteCompileIgnoreResult(bld,aLeftover);
		}
		scope(success) if(!a.length) bcLeftover();

		auto siz = getCTSizeof(a.length?type:e.type.getElementType());
		if(e.type.getHeadUnqual().isArrayTy()){ // static arrays
			// TODO: this is a little hacky
			auto lv=e.byteCompileLV(bld);
			lv.emitPointer(bld);
			bld.emitUnsafe(I.ptrtoa, this);
			if(!a.length) return;
			a[0].byteCompile(bld);
			goto Lload;
		}

		e.byteCompile(bld);
		mixin(byteCompileDollar);
		if(!a.length) return;

		assert(a.length == 1);
		a[0].byteCompile(bld);
		bcLeftover();
		static if(size_t.sizeof>uint.sizeof){
			// compiler has larger size_t than target.
			auto t_siz=getCTSizeof(a[0].type);
			if(t_siz<size_t.sizeof){
				bld.emit(I.truncs);
				bld.emitConstant(t_siz*8);
			}
		}
		if(e.type.getHeadUnqual().isPointerTy()){
			bld.emit(I.addp);
			bld.emitConstant(siz);
			bld.emitUnsafe(I.ptrtoa, this);
			bld.emit(I.push);
			bld.emitConstant(0);
		}
	Lload:
		if(LVstorea.isArrElement(type)){
			bld.emitUnsafe(I.loadaa, this);
			return;
		}
		bld.emitUnsafe(I.loada, this);
		bld.emitConstant(siz);
		ctToBCAdjust(bld, type);
	}

	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		alias Instruction I;
		// TODO: slice assign
		assert(a.length == 1);
		auto siz = getCTSizeof(type);
		if(e.type.getHeadUnqual().isArrayTy()){ // static arrays
			// TODO: this is a little hacky
			auto lv=e.byteCompileLV(bld);
			lv.emitPointer(bld);
			bld.emitUnsafe(I.ptrtoa, this);
			a[0].byteCompile(bld);
			return LVstorea(type, this);
		}
		e.byteCompile(bld);
		mixin(byteCompileDollar);

		a[0].byteCompile(bld);
		if(aLeftover) ExpressionStm.byteCompileIgnoreResult(bld,aLeftover);

		static if(size_t.sizeof>uint.sizeof){
			// compiler has larger size_t than target.
			auto t_siz=getCTSizeof(a[0].type);
			if(t_siz<size_t.sizeof){
				bld.emit(I.trunc);
				bld.emitConstant(t_siz*8);
			}
		}
		if(e.type.getHeadUnqual().isPointerTy()){
			bld.emit(I.addp);
			bld.emitConstant(siz);
			return LVpointer(type, this);
		}
		return LVstorea(type, this);
	}
}

mixin template CTFEInterpret(T) if(is(T==SliceExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		e.byteCompile(bld);

		Type elm = type.getElementType();
		auto siz = getCTSizeof(elm);
		mixin(byteCompileDollar);

		// TODO: static arrays
		l.byteCompile(bld);
		static if(size_t.sizeof>uint.sizeof){
			// compiler has larger size_t than target.
			auto t_siz=getCTSizeof(l.type);
			if(t_siz<size_t.sizeof){
				bld.emit(Instruction.trunc);
				bld.emitConstant(t_siz*8);
			}
		}
		if(auto ptr = e.type.getHeadUnqual().isPointerTy()){
			bld.emit(Instruction.dup);
			bld.emit(Instruction.tmppush);
			bld.emit(Instruction.addp);
			bld.emitConstant(siz);
			bld.emitUnsafe(Instruction.ptrtoa, this);
			bld.emit(Instruction.push);
			bld.emitConstant(0);
			r.byteCompile(bld);
			static if(size_t.sizeof>uint.sizeof){
				if(t_siz<size_t.sizeof){
					bld.emit(Instruction.truncs);
					bld.emitConstant(t_siz*8);
				}
			}
			bld.emit(Instruction.tmppop);
			bld.emit(Instruction.subi);
		}else{
			r.byteCompile(bld);
			static if(size_t.sizeof>uint.sizeof){
				if(t_siz<size_t.sizeof){
					bld.emit(Instruction.truncs);
					bld.emitConstant(t_siz*8);
				}
			}
		}
		bld.emitUnsafe(Instruction.slicea, this);
		bld.emitConstant(siz);
	}
}

mixin template CTFEInterpret(T) if(is(T==AssertExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		a[0].byteCompile(bld);
		if(aLeftover) ExpressionStm.byteCompileIgnoreResult(bld, aLeftover);
		bld.emit(Instruction.jnz);
		auto l = bld.emitLabel();
		if(a.length==1){
			if(a[0].loc.rep=="false"||a[0].loc.rep=="0")
				// don't state the obvious:
				bld.error("assertion failure", loc);
			else bld.error(format("assertion failure: %s is false",a[0].loc.rep), loc);
		}else{
			assert(a.length==2);
			assert({
				auto icd=a[1].type.implicitlyConvertsTo(Type.get!(const(char)[])());
				assert(!icd.dependee);
				return icd.value;
			}());
			a[1].byteCompile(bld);
			bld.emitUnsafe(Instruction.hltstr, this);
		}
		l.here();
	}
}

mixin template CTFEInterpret(T) if(is(T==ABinaryExp)||is(T==AssignExp)){}
mixin template CTFEInterpret(T) if(is(T _==BinaryExp!S,TokenType S)){
	static if(is(T _==BinaryExp!S,TokenType S)):
	static if(S!=Tok!"."):
	override void byteCompile(ref ByteCodeBuilder bld){
		byteCompileHelper(bld, false);
	}

	static if(isAssignOp(S) || S==Tok!",")
	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		return byteCompileHelper(bld, true);
	}

	static if(S==Tok!",")
	override void byteCompileRet(ref ByteCodeBuilder bld, bool isRefReturn){
		e1.byteCompile(bld);
		bld.ignoreResult(getBCSizeof(e1.type));
		return e2.byteCompileRet(bld, isRefReturn);
	}

	private LValueStrategy byteCompileHelper(ref ByteCodeBuilder bld, bool isLvalue) in{assert(!isLvalue || isAssignOp(S) || S==Tok!",");}body{
		import std.typetuple;
		alias Instruction I;
		static if(S==Tok!"="){
			auto strat = e1.byteCompileLV(bld);
			e2.byteCompile(bld);
			if(isLvalue){
				strat.emitStoreKR(bld);
				return strat;
			}else strat.emitStoreKV(bld);
		}else static if(S==Tok!","){
			e1.byteCompile(bld);
			bld.ignoreResult(getBCSizeof(e1.type));
			return isLvalue ? e2.byteCompileLV(bld) : (e2.byteCompile(bld),null);
		}else static if(isAssignOp(S)&&S!=Tok!"~=" || isArithmeticOp(S) || isShiftOp(S) || isBitwiseOp(S) ||isRelationalOp(S)&&S!=Tok!"in"&&S!=Tok!"!in"){
			auto ptrt=type.isPointerTy();
			if(auto ptr = ptrt?ptrt:e1.type.getHeadUnqual().isPointerTy()){
				enum op = TokChars!S;
				static if(S==Tok!"+"){
					if(e2.type.isIntegral()){
						e1.byteCompile(bld);
						e2.byteCompile(bld);
					}else{
						assert(e1.type.isIntegral());
						e2.byteCompile(bld);
						e1.byteCompile(bld);
					}
					bld.emit(I.addp);
					bld.emitConstant(getCTSizeof(ptr.ty));
					assert(!isLvalue);
					return null;
				}else static if(S==Tok!"-"){
					e1.byteCompile(bld);
					e2.byteCompile(bld);
					bld.emit(I.negi);
					bld.emit(I.addp);
					bld.emitConstant(getCTSizeof(ptr.ty));
					assert(!isLvalue);
					return null;
				}else static if(S==Tok!"+="||S==Tok!"-="){
					assert(e2.type.isIntegral());
					auto strat = e1.byteCompileLV(bld);
					strat.emitLoadKR(bld);
					e2.byteCompile(bld);
					static if(S==Tok!"-=") bld.emit(I.negi);
					bld.emit(I.addp);
					bld.emitConstant(getCTSizeof(ptr.ty));
					if(!isLvalue){ strat.emitStoreKV(bld); return null; }
					else{ strat.emitStoreKR(bld); return strat; }
				}else static if(isRelationalOp(S)){
					assert(e2.type is e1.type);
					e1.byteCompile(bld);
					e2.byteCompile(bld);
					static if(op=="=="||op=="is"||op=="!<>") bld.emit(I.cmpep);
					else static if(op=="!="||op=="!is"||op=="<>") bld.emit(I.cmpnep);
					else static if(op=="<"||op=="!>=") bld.emit(I.cmpbp);
					else static if(op=="<="||op=="!>") bld.emit(I.cmpbep);
					else static if(op==">"||op=="!<=") bld.emit(I.cmpap);
					else static if(op==">="||op=="!<") bld.emit(I.cmpaep);
					else static if(op=="<>="||op=="!<>="){
						bld.ignoreResult(getBCSizeof(e2.type));
						bld.ignoreResult(getBCSizeof(e1.type));
						bld.emit(I.push);
						bld.emitConstant(op=="<>=");
					}else static assert(0);
					return null;
				}
			}else{
				assert(type.getHeadUnqual().isBasicType(), text(type," ",this));
				static if(S!=Tok!"<<"&&S!=Tok!">>"&&S!=Tok!">>>") assert(e1.type is e2.type,text(this," ",loc));
			}

			static if(isAssignOp(S)){
				auto strat = e1.byteCompileLV(bld);
				strat.emitLoadKR(bld);
				enum op = TokChars!S[0..$-1];
			}else{
				e1.byteCompile(bld);
				enum op = TokChars!S;
			}
			e2.byteCompile(bld);

			assert(!isShiftOp(Tok!op) && !isBitwiseOp(Tok!op) || type.isIntegral());
			if(auto bt=e1.type.getHeadUnqual().isIntegral()){
				auto size = bt.bitSize(), signed = bt.isSigned();
				static if(op=="<<"||op==">>"||op==">>>"){
					bool isNarrow = size <= 32;
					assert(isNarrow || size == 64);
				}
				static if(op=="+") bld.emit(I.addi);
				else static if(op=="-") bld.emit(I.subi);
				else static if(op=="*") bld.emit(I.muli);
				else static if(op=="/") bld.emitUnsafe(signed?I.divsi:I.divi, this);
				else static if(op=="%") bld.emitUnsafe(signed?I.modsi:I.modi, this);
				else static if(op=="^^") assert(0, "TODO (?)");
				else static if(op=="<<") bld.emitUnsafe(isNarrow?I.shl32:I.shl64, this);
				else static if(op==">>"){
					if(signed) bld.emitUnsafe(isNarrow?I.sar32:I.sar64, this);
					else bld.emitUnsafe(isNarrow?I.shr32:I.shr64, this);
				}else static if(op==">>>") bld.emitUnsafe(isNarrow?I.shr32:I.shr64, this);
				else static if(op=="|") bld.emit(I.or);
				else static if(op=="^") bld.emit(I.xor);
				else static if(op=="&") bld.emit(I.and);
				else static if(op=="=="||op=="is"||op=="!<>") bld.emit(I.cmpei);
				else static if(op=="!="||op=="!is"||op=="<>") bld.emit(I.cmpnei);
				else static if(op=="<"||op=="!>=") bld.emit(signed?I.cmpli:I.cmpbi);
				else static if(op=="<="||op=="!>") bld.emit(signed?I.cmplei:I.cmpbei);
				else static if(op==">"||op=="!<=") bld.emit(signed?I.cmpgi:I.cmpai);
				else static if(op==">="||op=="!<") bld.emit(signed?I.cmpgei:I.cmpaei);
				else static if(op=="<>="||op=="!<>="){
					bld.ignoreResult(getBCSizeof(e2.type));
					bld.ignoreResult(getBCSizeof(e1.type));
					bld.emit(I.push);
					bld.emitConstant(op=="<>=");
				}else static assert(0, op);
				if(S!=Tok!"=" && !isBitwiseOp(Tok!op) && !isRelationalOp(S) && size<64){
					bld.emit(signed?I.truncs:I.trunc);
					bld.emitConstant(size);
				}
			}else static if(isArithmeticOp(Tok!op) && op!="^^"){
				if(auto bt0=e1.type.getHeadUnqual().isBasicType()){
				if(auto bt=bt0.isFloating()){
					enum which = op=="+"?"add":
						         op=="-"?"sub":
						         op=="*"?"mul":
						         op=="/"?"div":
						         op=="%"?"mod":
						    /+op=="^^"?+/"pow";
					foreach(tt; ToTuple!(["float","double","real"])){
						enum s = tt[0];
						mixin("alias "~tt~" T;");
						if(bt is Type.get!T()){
							bld.emit(mixin(`I.`~which~s));
							break;
						}
					}
				}else assert(0, "TODO: '"~op~"' for "~e1.type.toString());}	// TODO: operators for all built-in types
			}else static if(isRelationalOp(S)&&S!=Tok!"in"&&S!=Tok!"!in"){
				assert(!e1.type.getElementType()," CTFE array relational operators not implemented yet");
				if(auto bt0=e1.type.getHeadUnqual.isBasicType()){
					if(auto bt=bt0.isFloating()){
						foreach(tt; ToTuple!(["float","double","real"])){
							enum s = tt[0];
							mixin("alias "~tt~" T;");
							if(bt is Type.get!T()){
								static if(op=="is") bld.emit(mixin(`I.cmpis`~s));
								else static if(op=="!is"){
									bld.emit(mixin(`I.cmpis`~s));
									bld.emit(I.notb);
								}else static if(op=="==") bld.emit(mixin(`I.cmpe`~s));
								else static if(op=="!=") bld.emit(mixin(`I.cmpne`~s));
								else static if(op=="<") bld.emit(mixin(`I.cmpl`~s));
								else static if(op=="<=") bld.emit(mixin(`I.cmple`~s));
								else static if(op==">") bld.emit(mixin(`I.cmpg`~s));
								else static if(op==">=") bld.emit(mixin(`I.cmpge`~s));
								else static if(op=="<>"||op=="!<>"){
									bld.emitDup(2*getBCSizeof(bt));
									bld.emit(mixin(`I.cmpl`~s));
									bld.emit(I.tmppush);
									bld.emit(mixin(`I.cmpg`~s));
									bld.emit(I.tmppop);
									bld.emit(I.or);
									static if(op=="!<>") bld.emit(I.notb);
								}else static if(op=="<>="||op=="!<>="){
									auto sz = getBCSizeof(bt);
									bld.emitDup(sz);
									bld.emit(mixin(`I.cmpe`~s));
									bld.emit(I.tmppush);
									bld.emitDup(sz);
									bld.emit(mixin(`I.cmpe`~s));
									bld.emit(I.tmppop);
									bld.emit(I.and);
									static if(op == "!<>=") bld.emit(I.notb);
								}else static if(op=="!<"){
									bld.emit(mixin(`I.cmpl`~s));
									bld.emit(I.notb);
								}else static if(op=="!<="){
									bld.emit(mixin(`I.cmpl`~s));
									bld.emit(I.notb);
								}else static if(op=="!>="){
									bld.emit(mixin(`I.cmpge`~s));
									bld.emit(I.notb);
								}else static if(op=="!>"){
									bld.emit(mixin(`I.cmpg`~s));
									bld.emit(I.notb);
								}else static assert(0);
								assert(!isLvalue);
								return null;
							}
						}
					}
				}else static if(S==Tok!"is"||S==Tok!"!is"){
					if(auto at=e1.type.isAggregateTy()){
						assert(at.decl.isClassDecl(),"TODO: is for interfaces and value types");
						assert(!!e2.type.isAggregateTy());
						static if(S==Tok!"is") bld.emit(I.cmpep);
						else bld.emit(I.cmpnep);
						assert(!isLvalue);
						return null;
					}
				}
				assert(0, "TODO: '"~op~"' for "~e1.type.toString());
			}else assert(0, "TODO: '"~op~"' for "~e1.type.toString());	// TODO: operators for all built-in types
			static if(isAssignOp(S)){
				if(!isLvalue){ strat.emitStoreKV(bld); return null; }
				else{ strat.emitStoreKR(bld); return strat; }
			 }
		}else static if(S==Tok!"||"||S==Tok!"&&"){
			assert(e1.type is Type.get!bool());
			e1.byteCompile(bld);
			auto tu = type.getHeadUnqual();
			bool keepresult = tu is Type.get!bool();
			if(keepresult) bld.emit(I.dup);
			else assert(tu is Type.get!void());
			bld.emit(S==Tok!"||"?I.jnz:I.jz);
			auto end=bld.emitLabel();
			if(keepresult) bld.emit(I.pop);
			e2.byteCompile(bld);
			end.here();
		}else static if(S==Tok!"~"){
			e1.byteCompile(bld);
			if(e1.type.getUnqual() is e2.type.getUnqual().getElementType())
				emitMakeArray(bld,e2.type,1);
			e2.byteCompile(bld);
			if(e2.type.getUnqual() is e1.type.getUnqual().getElementType())
				emitMakeArray(bld,e1.type,1);
			bld.emit(I.concata);
		}else static if(S==Tok!"~="){
			auto strat = e1.byteCompileLV(bld);
			strat.emitLoadKR(bld);
			e2.byteCompile(bld);
			if(e2.type.equals(e1.type.getElementType()))
				emitMakeArray(bld,e1.type,1);
			bld.emit(I.appenda);
			if(!isLvalue){ strat.emitStoreKV(bld); return null; }
			else{ strat.emitStoreKR(bld); return strat; }
		}else super.byteCompile(bld);

		assert(!isLvalue);
		return null;
	}
}

mixin template CTFEInterpret(T) if(is(T==TupleAssignExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		auto strat = e1.byteCompileLV(bld);
		e2.byteCompile(bld);
		strat.emitStoreKV(bld);
	}
}

mixin template CTFEInterpret(T) if(is(T==TernaryExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		alias Instruction I;
		e1.byteCompile(bld);
		bld.emit(I.jz);
		auto otherwise=bld.emitLabel();
		e2.byteCompile(bld);
		bld.emit(I.jmp);
		auto end=bld.emitLabel();
		otherwise.here();
		e3.byteCompile(bld);
		end.here();
	}

	override void byteCompileRet(ref ByteCodeBuilder bld, bool isRefReturn){
		e1.byteCompile(bld);
		bld.emit(Instruction.jz);
		auto otherwise = bld.emitLabel();
		e2.byteCompileRet(bld,isRefReturn);
		otherwise.here();
		e3.byteCompileRet(bld,isRefReturn);
	}

	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		alias Instruction I;
		e1.byteCompile(bld);
		bld.emit(I.jz);
		auto otherwise=bld.emitLabel();
		auto strat1=e2.byteCompileLV(bld);
		bld.emit(I.push);
		bld.emitConstant(1);
		bld.emit(I.tmppush);
		bld.emit(I.jmp);
		auto end=bld.emitLabel();
		otherwise.here();
		auto strat2=e3.byteCompileLV(bld);
		bld.emit(I.push);
		bld.emitConstant(0);
		bld.emit(I.tmppush);
		end.here();
		return LVconditional(strat1, strat2);
	}
}

mixin template CTFEInterpret(T) if(is(T==CompoundStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		foreach(x; s) x.byteCompile(bld);
	}
}

mixin template CTFEInterpret(T) if(is(T==ILabeledStm)){
	ref ByteCodeBuilder.Label getBCLabel(ref ByteCodeBuilder bld);
}

mixin template CTFEInterpret(T) if(is(T==LabeledStm)){
	ByteCodeBuilder.Label bcLabel;

	override void byteCompile(ref ByteCodeBuilder bld){
		if(!bcLabel.initialized(bld)) bcLabel = bld.getLabel();
		bcLabel.here();
		s.byteCompile(bld);
	}
	ref ByteCodeBuilder.Label getBCLabel(ref ByteCodeBuilder bld){
		if(!bcLabel.initialized(bld)) bcLabel = bld.getLabel();
		return bcLabel;
	}
}
mixin template CTFEInterpret(T) if(is(T==ExpressionStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		byteCompileIgnoreResult(bld, e);
	}
	static void byteCompileIgnoreResult(ref ByteCodeBuilder bld, Expression e){
		e.byteCompile(bld);
		auto l = getBCSizeof(e.type);
		if(~l) bld.ignoreResult(l);
		else bld.emitUnsafe(Instruction.hlt, e); // TODO: probably redundant
	}
}
mixin template CTFEInterpret(T) if(is(T==IfStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		bld.Label otherwise, end;
		e.byteCompile(bld);
		bld.emit(Instruction.jz);
		otherwise=bld.emitLabel();
		s1.byteCompile(bld);
		if(s2){
			bld.emit(Instruction.jmp);
			end = bld.emitLabel();
			otherwise.here();
			s2.byteCompile(bld);
			end.here();
		}else otherwise.here();
	}
}

mixin template CTFEInterpret(T) if(is(T==BreakableStm)){
protected:
	final void setBCEnd(ByteCodeBuilder.Label* end){ bcend = end; }
	final void emitBCEnd(ref ByteCodeBuilder bld){bld.emitLabel(*bcend);}
	final void cleanupBCEnd(){ bcend = null; }
	enum doBCEnd = q{
		auto end = bld.getLabel();
		setBCEnd(&end);
		scope(exit){
			end.here();
			cleanupBCEnd();
		}
	};
private:
	ByteCodeBuilder.Label* bcend;
}
mixin template CTFEInterpret(T) if(is(T==LoopingStm)){
protected:
	final void setBCStart(ulong start){ bcstart = start; }
	void emitBCContinueLabel(ref ByteCodeBuilder bld){ bld.emitConstant(bcstart); }
	enum doBCStart = q{
		auto start = bld.getLocation();
		setBCStart(start);
	};
private:
	ulong bcstart;
}

mixin template CTFEInterpret(T) if(is(T==WhileStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		mixin(doBCStart~doBCEnd);
		e.byteCompile(bld);
		bld.emit(Instruction.jz);
		bld.emitLabel(end);
		s.byteCompile(bld);
		bld.emit(Instruction.jmp);
		bld.emitConstant(start);
	}
}

mixin template CTFEInterpret(T) if(is(T==DoStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		mixin(doBCStart~doBCEnd);
		s.byteCompile(bld);
		e.byteCompile(bld);
		bld.emit(Instruction.jnz);
		bld.emitConstant(start);
	}
}

mixin template CTFEInterpret(T) if(is(T==ForStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		s1.byteCompile(bld);
		mixin(doBCStart~doBCEnd);
		auto bccnt = bld.getLabel();
		bccontinue = &bccnt; scope(exit) bccontinue = null;
		if(e1){
			e1.byteCompile(bld);
			bld.emit(Instruction.jz);
			bld.emitLabel(end);
		}
		s2.byteCompile(bld);
		bccnt.here();
		if(e2) ExpressionStm.byteCompileIgnoreResult(bld, e2);
		bld.emit(Instruction.jmp);
		bld.emitConstant(start);
	}
	override void emitBCContinueLabel(ref ByteCodeBuilder bld){
		bld.emitLabel(*bccontinue);
	}
private:
	ByteCodeBuilder.Label* bccontinue;
}


mixin template CTFEInterpret(T) if(is(T==ForeachStm)||is(T==ForeachRangeStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		assert(!!lower,"TODO");
		lower.byteCompile(bld);
	}
}

mixin template CTFEInterpret(T) if(is(T==SwitchStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		mixin(doBCEnd);
		// TODO: specialized byte code instructions for switching on a value?
		tmpVarDecl.byteCompile(bld);

		// emit binary search
		static struct Expr{
			Variant exp;
			SwitchLabelStm equal;
			SwitchLabelStm smaller; // but larger than the previous one
		}

		auto expr(CaseRange c){
			static struct Only(T){ // TODO: use updated std.range
				T front;
				bool empty;
				void popFront(){ empty = true; }
			}
			auto only(T)(T arg){ return Only!T(arg); }
			if(auto cs=c.stm.isCaseStm()){
				auto e=cs.e[c.index];
				assert(e.isConstant());
				auto ee=Expr(e.interpretV(), cs, theDefault);
				return chain(only(ee),only(ee)).take(1);
			}else if(auto cs=c.stm.isCaseRangeStm()){
				assert(cs.e1.isConstant() && cs.e2.isConstant());
				return chain(only(Expr(cs.e1.interpretV(), cs, theDefault)),only(Expr(cs.e2.interpretV(), cs, cs))).take(2);
			}else assert(0);
		}
		auto exprs=casesInOrder[].map!expr.joiner.array; // TODO: get rid of temp allocation
		enum siz = 1;
		assert(e.type &&
		       (isIntegral()&&getBCSizeof(e.type)==siz
		        ||isString()&&e.type.getElementType()&&
		        getBCSizeof(e.type.getElementType())==siz));
		bool signed = kind==Kind.sintegral;
		assert(Type.get!Size_t().isIntegral()&&!Type.get!Size_t().isIntegral().isSigned());
		auto errorLabel=bld.getLabel();
		// TODO: DMD should allow this to be a template...
		// don't want to use dynamic delegates, but still want to reuse binary search code

		enum linearSearchThreshold=4;
		void binarySearch(VarDecl tmpVarDecl, Expr[] exprs, SwitchLabelStm larger, scope void delegate(size_t index, Instruction jmpInstr) found)in{assert(exprs.length);}body{
			assert(f||theDefault);

			void emitComparands(size_t i){
				assert(tmpVarDecl&&tmpVarDecl.scope_);
				tmpVarDecl.byteCompileSymbol(bld, e, tmpVarDecl.scope_);
				LiteralExp.byteCompileValue(bld, exprs[i].exp);
			}
			void emitCmpL(){ with(Instruction) return bld.emit(signed?cmpli:cmpbi); }
			void emitCmpLE(){ with(Instruction) return bld.emit(signed?cmplei:cmpbei); }
			void emitCmpE(){ return bld.emit(Instruction.cmpei); }


			void linearSearch(Expr[] range, SwitchLabelStm larger) in{
				assert(range.length<=linearSearchThreshold);
				// assert(range.isSorted())
			}body{
				// linear search
				foreach(i;0..range.length){
					if(range[i].equal.isCaseRangeStm()){
						if(range[i].smaller is range[i].equal){
							if(i) continue;
							emitComparands(&range[0]-exprs.ptr);
							emitCmpLE();
							bld.emit(Instruction.jnz);
							bld.emitLabel(range[i].equal.getBCLabel(bld));
						}else{
							emitComparands(&range[i]-exprs.ptr);
							emitCmpL();
							if(i+1<range.length){
								// (we have already excluded all smaller cases)
								bld.emit(Instruction.jnz);
								bld.emitLabel(theDefault?theDefault.getBCLabel(bld):errorLabel);
								emitComparands(&range[i+1]-exprs.ptr);
								emitCmpLE();
								found(&range[i]-exprs.ptr, Instruction.jnz);
							}else found(&range[i]-exprs.ptr, Instruction.jz);
						}
					}else{
						assert(!!range[i].equal.isCaseStm());
						emitComparands(&range[i]-exprs.ptr);
						emitCmpE();
						found(&range[i]-exprs.ptr, Instruction.jnz);
					}
				}
				bld.emit(Instruction.jmp);
				bld.emitLabel(theDefault?theDefault.getBCLabel(bld):errorLabel);
			}

			void go(Expr[] range, SwitchLabelStm larger){
				if(range.length<=linearSearchThreshold) return linearSearch(range, larger);
				emitComparands(&range[$/2]-exprs.ptr);
				emitCmpL();
				bld.emit(Instruction.jz);
				auto lbl=bld.emitLabel();
				go(range[0..$/2], range[$/2].smaller);
				lbl.here();
				go(range[$/2..$], larger);
			}
			go(exprs, larger);
		}
		void found(size_t index, Instruction jmpInstr){
			bld.emit(jmpInstr);
			bld.emitLabel(exprs[index].equal.getBCLabel(bld));
		}
		if(exprs.length){
			if(isIntegral()) binarySearch(tmpVarDecl, exprs, theDefault, &found);
			else{
				assert(isString());
				// we first search for length, then for the characters in order
				// TODO: how to determine the order the characters are compared in the
				// smartest way?
				// stable sort in 2.063 is buggy.
				// sort!((a,b)=>a.exp.length<b.exp.length, SwapStrategy.stable)(exprs);
				sort!((a,b)=>a.exp.length<b.exp.length||a.exp.length==b.exp.length&&a.exp.opBinary!"<"(b.exp))(exprs);

				// auto lenClasses=exprs.chunkBy!(a=>a.exp.length).array; // phobos should have this
				Expr[] lenClasses; // TODO: avoid temporary allocation
				size_t lengthCriterion(ref Expr a){ return a.exp.length; }
				void locateNextClass(T)(ref size_t i, scope T delegate(ref Expr) criterion){
					T c=criterion(exprs[i]);
					for(i++;i<exprs.length&&criterion(exprs[i])==c;i++){}
				}
				for(size_t i=0;i<exprs.length;locateNextClass(i, &lengthCriterion)){
					// TODO: DMD wrong-code if for-loop in increment position
					lenClasses~=exprs[i];
					(ref v){ v=Variant(v.length,Type.get!Size_t); }(lenClasses[$-1].exp);
				}
				tmpVarDeclStr.byteCompile(bld);
				size_t j=0;

				size_t ctSiz = isString()?getCTSizeof(e.type.getElementType()):0;
				void foundLength(size_t index, Instruction jmpInstr){
					with(Instruction) assert(jmpInstr==jz||jmpInstr==jnz);
					with(Instruction) bld.emit(jmpInstr==jz?jnz:jz);
					auto skipLbl = bld.emitLabel();
					scope(exit) skipLbl.here(); // continue outer binary search

					assert(j<exprs.length);
					size_t i=j;
					locateNextClass(j, &lengthCriterion);
					static struct Trie{
						union{
							SwitchLabelStm lbl;
							struct{
								Variant head;
								Trie[] children; // TODO: get rid of temporary gc allocations
							}
						}

						void insert(Variant x, SwitchLabelStm lbl){
							if(!x.length){
								Trie c;
								c.lbl = lbl;
								children~=c;
								return;
							}
							// TODO: dollar
							if(children.length&&children[$-1].head.get!size_t==x[0].get!size_t)
								return children[$-1].insert(x[1..x.length], lbl);
							assert(!children.length||children[$-1].head.get!size_t<x[0].get!size_t,text(children[$-1].head," ",x));
							Trie c;
							c.head=x[0];
							c.insert(x[1..x.length], lbl);
							children~=c;
						}

						bool isLast(){
							return children.length==1&&!children[0].children.length;
						}

						SwitchLabelStm label()in{assert(isLast());}body{
							return children[0].lbl;
						}
					}
					Trie t;
					foreach(x,ref e;exprs[i..j]){
						assert(cast(CaseStm)e.equal);
						t.insert(e.exp, e.equal);
					}

					void emitSearch(ref Trie t, size_t i){
						if(t.isLast()){
							bld.emit(Instruction.jmp);
							bld.emitLabel(t.label().getBCLabel(bld));
							return;
						}

						tmpVarDecl.byteCompileSymbol(bld,e,tmpVarDecl.scope_);
						bld.emit(Instruction.push);
						bld.emitConstant(i);
						bld.emitUnsafe(Instruction.loada,e);
						bld.emitConstant(ctSiz);

						void binarySearch(Trie[] c){
							assert(c.length);
							static assert(linearSearchThreshold>=1);
							if(c.length<=linearSearchThreshold){
								foreach(j,ref ct;c){
									if(j+1!=c.length) bld.emit(Instruction.dup);
									LiteralExp.byteCompileValue(bld, ct.head);
									bld.emit(Instruction.cmpei);
									bld.emit(Instruction.jz);
									auto lbl=bld.getLabel();
									if(j+1==c.length)
										bld.emitLabel(theDefault?theDefault.getBCLabel(bld):errorLabel);
									else bld.emitLabel(lbl);
									if(j+1!=c.length) bld.emit(Instruction.pop);
									emitSearch(ct,i+1);
									if(j+1!=c.length) lbl.here();
								}
							}else{
								bld.emit(Instruction.dup);
								LiteralExp.byteCompileValue(bld, c[$/2].head);
								bld.emit(Instruction.cmpbi);
								bld.emit(Instruction.jz);
								auto lbl=bld.emitLabel();
								binarySearch(c[0..$/2]);
								lbl.here();
								binarySearch(c[$/2..$]);
							}
						}
						binarySearch(t.children);
					}
					emitSearch(t,0);
				}
				//dw("!! ",exprs, "\nlencl: ", lenClasses,"\n",exprs.map!(a=>a.exp.length));

				binarySearch(tmpVarDeclStr, lenClasses, theDefault, &foundLength);
			}
		}else if(theDefault){
			bld.emit(Instruction.jmp);
			bld.emitLabel(theDefault.getBCLabel(bld));
		}
		if(!theDefault){
			errorLabel.here();
			assert(f);
			bld.error("final switch expression does not evaluate to one of the allowed enum values",e.loc);
		}
		s.byteCompile(bld);
	}
}

mixin template CTFEInterpret(T) if(is(T==SwitchLabelStm)){
	ByteCodeBuilder.Label bcLabel;
	final ref ByteCodeBuilder.Label getBCLabel(ref ByteCodeBuilder bld){
		if(!bcLabel.initialized(bld)) bcLabel=bld.getLabel();
		return bcLabel;
	}
}

mixin template CTFEInterpret(T) if(is(T==CaseStm)||is(T==CaseRangeStm)||is(T==DefaultStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		assert(bcLabel.outer is &bld);
		bcLabel.here();
		foreach(ss;s) ss.byteCompile(bld);
	}
}

mixin template CTFEInterpret(T) if(is(T==ReturnStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		if(e) e.byteCompileRet(bld, isRefReturn);
		else bld.emit(Instruction.ret);
	}
}

mixin template CTFEInterpret(T) if(is(T==ContinueStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		assert(sstate==SemState.completed,text(this," ",loc));
		bld.emit(Instruction.jmp);
		getLoweredEnclosingStatement().emitBCContinueLabel(bld);
	}
}
mixin template CTFEInterpret(T) if(is(T==BreakStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		bld.emit(Instruction.jmp);
		getLoweredEnclosingStatement().emitBCEnd(bld);
	}
}
mixin template CTFEInterpret(T) if(is(T==GotoStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		if(lower) return lower.byteCompile(bld);
		bld.emit(Instruction.jmp);
		bld.emitLabel(target.getBCLabel(bld));
	}
}

mixin template CTFEInterpret(T) if(is(T==WithStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		if(tmp) tmp.byteCompile(bld);
		s.byteCompile(bld);
	}
}

mixin template CTFEInterpret(T) if(is(T==LiteralExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		byteCompileValue(bld, value);
	}
	static void byteCompileValue(ref ByteCodeBuilder bld, ref Variant value){
		auto tu = value.getType().getHeadUnqual();
		if(auto et=tu.isEnumTy()){
			assert(!!et.decl.base);
			tu=et.decl.base.getHeadUnqual();
		}
		if(auto bt = tu.isBasicType()){
			if(bt.isIntegral()){
				bld.emit(Instruction.push);
				if(bt.isSigned()) bld.emitConstant(cast(long)value.get!ulong());
				else bld.emitConstant(value.get!ulong());
				return;
			}else if(tu is Type.get!float()||tu is Type.get!ifloat()){
				bld.emit(Instruction.push);
				bld.emitConstant(value.get!float());
				return;
			}else if(tu is Type.get!double()||tu is Type.get!idouble()){
				bld.emit(Instruction.push);
				bld.emitConstant(value.get!double());
				return;
			}else if(tu is Type.get!real()||tu is Type.get!ireal()){
				bld.emit(Instruction.push2);
				bld.emitConstant(value.get!real());
				return;
			}
		}else if(auto arr=tu.isArrayTy()){
			auto siz=getCTSizeof(arr);
			auto tmp=new void[siz]; // TODO: allocate deterministically
			arr.variantToMemory(value, tmp);
			bld.emitPushConstant(tmp);
			return;
		}else if(auto dyn=tu.isDynArrTy()){
			BCSlice r;
			dyn.variantToMemory(value, (cast(void*)&r)[0..BCSlice.sizeof]);

			size_t size = getBCSizeof(tu.getElementType().getDynArr());
			if(tu.getUnqual() is Type.get!(void[])()){
				bld.emit(Instruction.push);
				bld.emitConstant(cast(ulong)cast(void*)value.getType());
			}else assert(!(size&1),text(tu));
			bld.emitPushConstant(r);
			return;
		}else if(auto pt=tu.isPointerTy()){
			if(pt.getFunctionTy()){
				Symbol s;// TODO: merge?
				pt.variantToMemory(value, (cast(void*)&s)[0..Symbol.sizeof]);
				bld.emitPushConstant(s);
				return;
			}
			BCPointer r;
			pt.variantToMemory(value,(cast(void*)&r)[0..BCPointer.sizeof]);
			size_t size = getBCSizeof(tu);
			if(tu.getUnqual() is Type.get!(void*)()){
				bld.emit(Instruction.push);
				bld.emitConstant(cast(ulong)cast(void*)value.getType());
			}else assert(!(size&1),text(tu));
			bld.emitPushConstant(r);
			return;
		}else if(auto at=tu.isAggregateTy()){
			auto vars = value.get!(Variant[VarDecl])();
			if(vars is null){ assert(at.decl.isReferenceAggregateDecl()); goto Lnull; }
			// TODO: do more efficiently
			void[] tmp = new void[getCTSizeof(at)];
			value.getType().variantToMemory(value, tmp);
			bld.emitPushConstant(tmp);
		}else if(auto dgt=tu.isDelegateTy()){
			void[(bcPointerBCSize+1)*ulong.sizeof] mem=void;
			value.getType().variantToMemory(value, mem[]);
			bld.emitPushConstant(mem[]);
		}else{
		Lnull:
			assert(tu.getUnqual() is Type.get!(typeof(null))()||tu.isAggregateTy());
			// TODO: solve more elegantly
			foreach(i;0..getBCSizeof(Type.get!(typeof(null))())){
				bld.emit(Instruction.push);
				bld.emitConstant(0);
			}
			return;
		}
	}

	// for eg. top-level immutable ref parameters that have been const folded
	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		byteCompile(bld);
		emitMakeArray(bld,type.getDynArr(), 1);
		bld.emit(Instruction.ptra);
		return LVpointer(type, this);
	}
}


void emitMakeArray(ref ByteCodeBuilder bld, Type ty, ulong elems)in{
	assert(ty.getElementType());
}body{
	alias Instruction I;
	ty = ty.getElementType().getHeadUnqual();
	bld.emit(I.push);
	bld.emitConstant(elems);
	bld.emit(I.makearray);
	bld.emitConstant(getCTSizeof(ty));
}


mixin template CTFEInterpret(T) if(is(T==ArrayLiteralExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		auto tt = type;
		if(type.getUnqual() is Type.get!(void[])){
			if(lit.length) tt = lit[0].type.getDynArr();
			else tt = Type.get!EmptyArray();
			bld.emit(Instruction.push);
			static assert(Type.sizeof<=ulong.sizeof);
			bld.emitConstant(cast(ulong)cast(void*)tt);
		}
		foreach(x; lit) x.byteCompile(bld);
		if(litLeftover) ExpressionStm.byteCompileIgnoreResult(bld, litLeftover);
		emitMakeArray(bld, tt, lit.length);
		if(type.getUnqual().isArrayTy()){ // static array literal (TODO: this is a horrible kludge)
			bld.emit(Instruction.push);
			bld.emitConstant(0);
			bld.emitUnsafe(Instruction.loada,this);
			bld.emitConstant(getCTSizeof(tt));
		}
	}

	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		assert(type.isArrayTy()); // static array literal, also kludgy
		foreach(x; lit) x.byteCompile(bld);
		emitMakeArray(bld, type, lit.length);
		bld.emit(Instruction.ptra);
		return LVpointer(type, this);
	}
}

mixin template CTFEInterpret(T) if(is(T==CastExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		e.byteCompile(bld);
		import std.typetuple;
		alias Instruction I;
		auto t1 = e.type.getHeadUnqual(), t2 = type.getHeadUnqual();
		auto cvt1=t1, cvt2=t2;
		if(auto e1=t1.isEnumTy()) cvt1=e1.decl.base;
		if(auto e2=t2.isEnumTy()) cvt2=e2.decl.base;
		assert(cvt1&&cvt2);
		if(cvt1.equals(cvt2)) return;
		if(e.isUnique()) cvt1=cvt1.getUnqual(), cvt2=cvt2.getUnqual();
		if(t2.getHeadUnqual() is Type.get!void()){
			bld.ignoreResult(getBCSizeof(t1));
			return;
		}
		if(auto from=cvt1.isIntegral()){
			if(auto to=cvt2.isIntegral()){
				auto fb=from.bitSize(), tb=to.bitSize();
				if(fb<tb && from.isSigned==to.isSigned()||tb==64) return;
				if(to is Type.get!bool()){
					bld.emit(I.int2bool);
					return;
				}
				bld.emit(to.isSigned() ? I.truncs : I.trunc);
				bld.emitConstant(to.bitSize());
				return;
			}else foreach(T; TypeTuple!(float, double, real)){ // TODO: imaginary/complex
				if(cvt2 is Type.get!T()){
					bld.emit(from.isSigned() ? I.int2real : I.uint2real);
					static if(!is(T==real)) bld.emit(mixin(`I.real2`~T.stringof));
					return;
				}
			}
		}else foreach(T; TypeTuple!(float, double, real)){
			if(cvt1 is Type.get!T()){
				if(auto to=cvt2.isIntegral()){
					static if(!is(T==real)) bld.emit(mixin(`I.`~T.stringof~`2real`));
					if(to is Type.get!bool()){
						bld.emit(I.real2bool);
						return;
					}
					auto signed = to.isSigned();
					bld.emit(signed?I.real2int:I.real2uint);
					if(to.bitSize()<64){
						bld.emit(signed ? I.truncs : I.trunc);
						bld.emitConstant(to.bitSize());
					}
					return;
				}else foreach(S; TypeTuple!(float, double, real)){
					if(cvt2 is Type.get!S()){
						static if(is(S==T)) return;
						else{
							static if(!is(T==real)) bld.emit(mixin(`I.`~T.stringof~`2real`));
							static if(!is(S==real)) bld.emit(mixin(`I.real2`~S.stringof));
							return;
						}
					}
				}
				break;
			}
		}

		void castToVoidPtrOrArray(Type tt){
			auto siz=getBCSizeof(tt);
			bld.emitTmppush(siz);
			bld.emit(I.push);
			bld.emitConstant(cast(ulong)cast(void*)tt);
			bld.emitTmppop(siz);
		}

		auto varr=Type.get!(void[])();
		auto vptr=Type.get!(void*)();
		auto cvt1u=cvt1.getUnqual(), cvt2u=cvt2.getUnqual();

		if(cvt2u is varr||cvt2u is vptr){
			castToVoidPtrOrArray(t1);
			return;
		}
		if(cvt1u is varr||cvt1u is vptr){
			bld.emitUnsafe(t1 is varr ? I.castfromvarr : I.castfromvptr, this);
			static assert(Type.sizeof<=ulong.sizeof);
			bld.emitConstant(cast(ulong)cast(void*)t2);
			return;
		}

		// TODO: sanity check for reinterpreted references
		// TODO: sanity check for array cast alignment
		auto rcd = cvt1.refConvertsTo(cvt2,0);
		assert(!rcd.dependee); // must have been determined to type check the expression
		if(rcd.value){
			auto el1=t1.getElementType(), el2=t2.getElementType();
			bool ok=true;
			while(el1 && el2){
				auto el1u=el1.getHeadUnqual(), el2u=el2.getHeadUnqual();
				if(el2u is Type.get!void() && el1u !is Type.get!void())
					ok=false;
				el1=el1u.getElementType(), el2=el2u.getElementType();
			}
			if(ok) return;
		}

		if(auto dyn=t1.isDynArrTy()){
			if(auto ptr=t2.isPointerTy()){
				if(cvt2u is Type.get!(void*)()){
					bld.emit(I.ptra);
					castToVoidPtrOrArray(t1.getElementType().getPointer());
					return;
				}
				cvt1=dyn, cvt2=ptr.ty.getDynArr();
				// TODO: comprehensive treatment of unique expressions
				auto rcd2 = cvt1.refConvertsTo(cvt2, 0);
				assert(!rcd2.dependee);
				if(rcd2.value){
					bld.emit(I.ptra);
					return;
				}
			}
		}
		//if(t1.isDynArrTy() && t2.isDynArrTy()) return;
		//if(t1.isPointerTy() && t2.isPointerTy()) return;
		bld.error(format("cannot interpret cast from '%s' to '%s' at compile time", e.type,type),loc);
	}

	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		assert({
			auto rcd1=e.type.refConvertsTo(type,1);   // ref params
			auto rcd2= type.refConvertsTo(type,1); // out params
			assert(!rcd1.dependee&&!rcd2.dependee);
			return rcd1.value || rcd2.value;
		}());
		return e.byteCompileLV(bld);
	}
}

mixin template CTFEInterpret(T) if(is(T==Symbol)){
	override void byteCompile(ref ByteCodeBuilder bld){
		if(auto vd = meaning.isVarDecl()) return vd.byteCompileSymbol(bld, this, scope_);
		else if(auto fd=meaning.isFunctionDef()){
			static assert(this.sizeof<=(void*).sizeof&&(void*).sizeof<=ulong.sizeof);
			if(!(fd.stc&STCstatic) && !fd.isConstructor()){
				auto fsc=scope_.getFrameScope();
				auto mfsc=meaning.scope_.getFrameScope();
				if(fsc&&mfsc&&fsc.isNestedIn(mfsc)){
					assert(scope_.getFrameNesting() >=
					       meaning.scope_.getFrameNesting());
					auto diff = scope_.getFrameNesting() - meaning.scope_.getFrameNesting();
					
					bld.emitUnsafe(Instruction.pushcontext, this);
					bld.emitConstant(diff);
				}else if(!mfsc||fd.isInterpretableWithoutContext()){
					bld.emitNullPointer();
				}else{
					bld.error(accessError(), loc);
				}
			}
			if(!(fd.stc&STCnonvirtual)&&CurrentExp.enclosingMemberFunction(scope_))
			if(auto decl=fd.scope_.getDeclaration())
			if(auto raggr=decl.isReferenceAggregateDecl()){
				FieldExp.byteCompileVirtualCall(bld, raggr, fd, this);
				return;
			}
			bld.emit(Instruction.push);
			bld.emitConstant(cast(ulong)cast(void*)this);
			return;
		}
		bld.error(format("cannot interpret %s '%s' at compile time%s", kind, loc.rep,
			meaning.isFunctionDecl()?", because it has no available source code":""), loc);
	}

	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		assert(scope_);
		if(auto vd = meaning.isVarDecl()) return vd.byteCompileSymbolLV(bld, this, scope_);
		bld.error(format("cannot interpret symbol '%s' at compile time", toString()), loc);
		return LVpopc(Type.get!void(), this); // dummy
	}
}

mixin template CTFEInterpret(T) if(is(T==DollarExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		// dollar expression at module scope
		// this is on the boundary between const folding
		// and byte code interpretation, see Interpret!DollarExp
		// for the rest of the implementation
		if(meaning.stc & STCstatic){
			assert(getBCSizeof(Type.get!Size_t())==1);
			bld.emit(Instruction.push);
			bld.emitConstant(ivalue);
			return;
		}
		super.byteCompile(bld);
	}
}


mixin template CTFEInterpret(T) if(is(T==FieldExp)){
	// TODO: validate the 'this' pointer!
	override void byteCompile(ref ByteCodeBuilder bld){
		assert(e2.meaning);
		auto this_=e1.extractThis();
		if(e2.meaning.stc&STCstatic){
			if(this_) ExpressionStm.byteCompileIgnoreResult(bld, this_);
			return e2.byteCompile(bld);
		}
		bool nonvirtual = false;
		auto thisCompile=()=>this_.byteCompile(bld);
		auto thisCompileLV=()=>this_.byteCompileLV(bld);
		AggregateTy aggrt=null;
		if(!this_){ // TODO: would prefer not having this
			aggrt=e2.scope_.getAggregate().getType(); // TODO: qualifiers eventually needed?
			thisCompile=()=>CurrentExp.byteCompile(bld, e2.scope_, aggrt, this);
			thisCompileLV=()=>CurrentExp.byteCompileLV(bld, e2.scope_, aggrt, this);
			nonvirtual = true;
		}else{
			if(this_.isSuperExp()) nonvirtual = true;
			if(auto te=this_.isThisExp())
				if(!te.enclosingMemberFunction())
					nonvirtual = true;
			assert(!this_ || cast(AggregateTy)this_.type.getHeadUnqual());
			aggrt = cast(AggregateTy)cast(void*)this_.type.getHeadUnqual();
		}

		if(auto vd=e2.meaning.isVarDecl()){
			size_t len, off = aggrt.getBCLocOf(vd, len);
			if(aggrt.decl.isValueAggregateDecl()){
				auto lv=thisCompileLV();
				emitCheckedFieldLoad(bld, lv, aggrt, vd).emitLoad(bld);
			}else{
				thisCompile();
				LVfield(off, len, getCTSizeof(vd.type), this).emitLoad(bld);
			}
			return;
		}
		assert(e2.meaning.isFunctionDecl());
		auto fun = e2.meaning.isFunctionDef();
		if(!fun){ e2.byteCompile(bld); return; }
		if(auto raggr=aggrt.decl.isReferenceAggregateDecl()){
			// TODO: interfaces!
			if(fun.stc&STCnonvirtual) nonvirtual = true;
			auto fd = fun.isFunctionDef();
			if(nonvirtual && fd.isInterpretableWithoutContext()) bld.emitNullPointer();
			else thisCompile();
			if(!nonvirtual){
				byteCompileVirtualCall(bld, raggr, fun, this);
				return;
			}
		}else{
			auto lv=thisCompileLV();
			lv.emitPointer(bld);
		}
		bld.emit(Instruction.push);
		static assert(e2.sizeof<=(void*).sizeof&&(void*).sizeof<=ulong.sizeof);
		bld.emitConstant(cast(ulong)cast(void*)e2);
	}

	static void byteCompileVirtualCall(ref ByteCodeBuilder bld, ReferenceAggregateDecl raggr, FunctionDecl fun, Expression loader){
		// TODO: this is not permissive enough
		// ideally, virtual method calls would work like non-virtual ones
/+		if(!raggr.vtbl.has(fun)){
			raggr.semantic(raggr.scope_);
			if(raggr.needRetry){
				dw(raggr.needRetry," moo");
				throw new CTFERetryException(raggr);
			}
			if(raggr.sstate == SemState.error){
				bld.error(format("cannot perform a virtual method call on an object of invalid type '%s'", raggr.name),loader.loc);
				return;
			}
		}+/

		bld.emitDup(bcPointerBCSize); // copy the class reference
		bld.emitUnsafe(Instruction.loadf, loader);
		bld.emitConstant(ReferenceAggregateDecl.bcTypeidOffset);
		bld.emitConstant(ReferenceAggregateDecl.bcTypeidSize);

		if(raggr.vtbl.has(fun)){
			bld.emit(Instruction.fetchvtbl);
			bld.emitConstant(raggr.vtbl.vtblIndex[fun]);
		}else{
			bld.emit(Instruction.fetchoverride);
			static assert(fun.sizeof<=(void*).sizeof&&(void*).sizeof<=ulong.sizeof);
			bld.emitConstant(cast(ulong)cast(void*)fun);
		}
	}

	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		assert(e2.meaning);
		if(e2.meaning.stc&STCstatic){
			if(auto this_=e1.extractThis()) ExpressionStm.byteCompileIgnoreResult(bld, this_);
			return e2.byteCompileLV(bld);
		}
		auto this_=e1.extractThis();
		if(!this_){
			this_ = New!ThisExp(); // TODO: would prefer not having this
			this_.loc = loc;
			do this_.semantic(e2.scope_);
			while(this_.sstate != SemState.completed);
		}
		assert(!!this_ && cast(AggregateTy)this_.type.getHeadUnqual(), text(this_," ",this));
		auto aggrt = cast(AggregateTy)cast(void*)this_.type.getHeadUnqual();

		auto vd=e2.meaning.isVarDecl();
		assert(!!vd);
		LValueStrategy r;
		if(aggrt.decl.isValueAggregateDecl()){
			auto lv=this_.byteCompileLV(bld);
			return emitCheckedFieldLoad(bld, lv, aggrt, vd);
		}else{
			this_.byteCompile(bld);
			size_t len, off = aggrt.getBCLocOf(vd, len);
			return LVfield(off, len, getCTSizeof(vd.type), this);
		}
	}

	final private LValueStrategy emitCheckedFieldLoad(ref ByteCodeBuilder bld, LValueStrategy lv, AggregateTy aggrt, VarDecl vd){
		assert(aggrt.decl);
		auto ud=aggrt.decl.isUnionDecl();
		assert(~vd.stc&STCstatic);
		if(ud) return ud.emitCheckedFieldLoad(lv, vd, this);
		size_t len, off = aggrt.getBCLocOf(vd, len);
		return lv.emitFieldLV(bld, off, len, getCTSizeof(vd.type), this, vd);
	}
}

mixin template CTFEInterpret(T) if(is(T==PtrExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		if(e.type.getHeadUnqual().isDynArrTy()){
			e.byteCompile(bld);
			bld.emit(Instruction.ptra);
		}else{
			assert(e.type.getHeadUnqual().isArrayTy());
			auto lv=e.byteCompileLV(bld);
			lv.emitPointer(bld);
		}
	}
}
mixin template CTFEInterpret(T) if(is(T==LengthExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		e.byteCompile(bld);
		bld.emit(Instruction.lengtha);
		bld.emitConstant(getCTSizeof(e.type.getElementType()));
	}

	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		return LVlength(e.byteCompileLV(bld),e.type.getElementType());
	}
}


mixin template CTFEInterpret(T) if(is(T==ConditionDeclExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		decl.byteCompile(bld);
		sym.byteCompile(bld);
	}
}

interface NotifyOnLayoutChanged{
	void notifyLayoutChanged(AggregateDecl decl);
}

mixin template CTFEInterpret(T) if(is(T==AggregateDecl)){
	enum bcTypeidOffset = bcPointerBCSize;
	enum bcTypeidSize = 1;

	protected size_t initialOffset(){
		// nested aggregates have a context pointer
		return stc&STCstatic ? 0 : bcPointerBCSize;
	}

	private bool[NotifyOnLayoutChanged] subscribers;
	void subscribeForLayoutChanges(NotifyOnLayoutChanged notified){
		subscribers[notified]=true;
	}
	void notifyLayoutChanged(AggregateDecl decl){
		vmtr.flushCaches(); // TODO!
		layoutKnown = false;
		foreach(s,_;subscribers) s.notifyLayoutChanged(this);
	}

	/* Called in presemantic of fields. This allows multiple different interpretations
	   of the same aggregate type during different CTFE executions, while the layout
	   can still be cached.
	 */

	void layoutChanged(){
		updateVersion();
		notifyLayoutChanged(this);
	}

	bool isLayoutKnown(){
		return layoutKnown;
	}

	int traverseDeclaredFields(scope int delegate(VarDecl) dg){
		foreach(d;&bdy.traverseInOrder){
			int visitVarDecl(VarDecl vd){
				if(vd.sstate != SemState.completed) return 0; // TODO: ok?
				if(vd.stc&(STCstatic|STCenum)) return 0;
				return dg(vd);
			}
			if(auto vd=d.isVarDecl()){
				if(vd.tupleContext){
					foreach(tvd;vd.tupleContext.vds)
						if(auto r=visitVarDecl(tvd))
							return r;
				}else if(auto r=visitVarDecl(vd)) return r;
			}
		}
		return 0;
	}

	int traverseFields(scope int delegate(VarDecl) dg){
		return traverseDeclaredFields(dg);
	}

	final int updateLayoutTraversal(scope int delegate(VarDecl) dg){
		foreach(vd;&traverseDeclaredFields){
			if(auto aggrty=vd.type.isAggregateTy()){
				if(auto decl=aggrty.decl.isValueAggregateDecl()){
					decl.subscribeForLayoutChanges(this);
				}
			}
			assert(!!vd.type, vd.to!string);
			if(auto r=dg(vd)) return r;
		}
		return 0;
	}

	void updateLayout()in{assert(!isLayoutKnown());}body{
		size_t off=initialOffset();
		// TODO: anonymous structs/unions etc.
		foreach(vd;&updateLayoutTraversal){
			auto len = getBCSizeof(vd.type);
			vd.setBCLoc(off, len);
			off+=len;
		}
		bcSize = off;
		layoutKnown = true;
	}
	final size_t getBCSize(){
		if(!isLayoutKnown()) updateLayout();
		return bcSize?bcSize:1;
	}
	static ulong getVersion(){
		return vers;
	}
	private static void updateVersion(){
		if(vers == ulong.max) assert(0);
		vers++;
	}

	void byteCompileInit(ref ByteCodeBuilder bld, Scope sc){
		if(!isLayoutKnown()) updateLayout();
		void emitNullPtr(){
			foreach(i;0..bcPointerBCSize){
				bld.emit(Instruction.push);
				bld.emitConstant(0);
			}
		}
		if(!(stc&STCstatic)){
			if(sc is null) emitNullPtr();
			else{
				auto diff = sc.getFrameNesting() - scope_.getFrameNesting();
				assert(diff>=0);
				bld.emitUnsafe(Instruction.pushcontext, this);
				bld.emitConstant(diff);
			}
		}
		if(auto raggr=isReferenceAggregateDecl()){
			if(stc&STCstatic) emitNullPtr();
			bld.emit(Instruction.push);
			static assert(ReferenceAggregateDecl.sizeof<=(void*).sizeof &&
			              (void*).sizeof<=ulong.sizeof);
			bld.emitConstant(cast(ulong)cast(void*)this);
		}
		byteCompileFields(bld);
		if(!bcSize){
			bld.emit(Instruction.push);
			bld.emitConstant(0);
		}
	}

	protected void byteCompileFields(ref ByteCodeBuilder bld){
		foreach(vd;&traverseDeclaredFields){
			size_t len, off = vd.getBCLoc(len);
			if(len!=-1){
				if(vd.init) vd.init.byteCompile(bld);
				else foreach(i;0..len){bld.emit(Instruction.push); bld.emitConstant(0);}
			}else{
				bld.error(format("cannot interpret field '%s' of type '%s' during compile time",vd.toString(),vd.type.toString()),loc);
			}
		}
	}

private:
	size_t bcSize;
	static ulong vers;
	bool layoutKnown = false;
}

mixin template CTFEInterpret(T) if(is(T==UnionDecl)){
	enum bcTagOffset=0, bcTagLength=1;
	protected override size_t initialOffset(){
		assert(stc&STCstatic);
		assert(getBCSizeof(Type.get!ulong())==bcTagLength);
		return bcTagLength;
	}
	private int[Type] indices;
	public final int getIndex(VarDecl vd)in{assert(isLayoutKnown()&&vd&&vd.type&&vd.scope_&&vd.isField&&vd.scope_&&vd.scope_.getDeclaration() is this);}body{
		return indices[vd.type];
	}
	void updateLayout()in{assert(!isLayoutKnown());}body{
		size_t maxl=0, index=0, init=initialOffset();
		// TODO: anonymous structs/unions etc.
		indices = null;
		foreach(vd;&updateLayoutTraversal){
			if(vd.type !in indices){
				assert(index<int.max);
				indices[vd.type]=cast(int)(index++);
			}
			auto len = getBCSizeof(vd.type);
			vd.setBCLoc(init, len);
			if(maxl<len) maxl=len;
		}
		bcSize = init+maxl;
		layoutKnown = true;
	}

	LValueStrategy emitCheckedFieldLoad(LValueStrategy lv, VarDecl vd, ErrorInfo loader)in{
		assert(!!lv);
	}body{
		static class UnionFieldLV: LValueStrategy{
			LValueStrategy lv; ErrorInfo loader; size_t index; VarDecl vd;
			size_t size;
			this(LValueStrategy lv, ErrorInfo loader, size_t index, VarDecl vd){
				this.lv=lv; this.loader=loader; this.index=index; this.vd = vd;
				size=getBCSizeof(vd.type);
			}
			override @property size_t lvBCSize(){
				return lv.lvBCSize;
			}
			final LValueStrategy emitTagLV(ref ByteCodeBuilder bld){
				lv.dupR(bld);
				return lv.emitFieldLV(bld, bcTagOffset, bcTagLength, getCTSizeof(Type.get!ulong()), loader, null);
			}
			final LValueStrategy emitTheField(ref ByteCodeBuilder bld){
				size_t len, off = vd.getBCLoc(len);
				return lv.emitFieldLV(bld, off, len, getCTSizeof(vd.type), loader, vd);
			}

			void emitIndex(ref ByteCodeBuilder bld){
				bld.emit(Instruction.push);
				bld.emitConstant(index);
			}

			enum lderr = "cannot reinterpret union fields at compile time";
			final void loadCheck(ref ByteCodeBuilder bld, string error=lderr, Location loc=Location()){
				if(!loc.line) loc=loader.loc;
				emitTagLV(bld).emitLoad(bld);
				emitIndex(bld);
				bld.emit(Instruction.cmpei);
				bld.emit(Instruction.jnz);
				auto l = bld.emitLabel();
				bld.error(error, loc);
				l.here();
			}

			void storeUpdate(ref ByteCodeBuilder bld){
				auto tlv=emitTagLV(bld);
				emitIndex(bld);
				tlv.emitStore(bld);
			}
			private static _emitAll(){
				string r;
				foreach(s;["emitLoad", "emitLoadKR"]){
					r~=mixin(X!q{
						override void @(s)(ref ByteCodeBuilder bld){
							loadCheck(bld);
							emitTheField(bld).@(s)(bld);
						}
					});
				}
				foreach(s;["emitStore", "emitStoreKR", "emitStoreKV"]){
					r~=mixin(X!q{
						override void @(s)(ref ByteCodeBuilder bld){
							bld.emitTmppush(size);
							storeUpdate(bld);
							auto fld=emitTheField(bld);
							bld.emitTmppop(size);
							fld.@(s)(bld);
						}
					});
				}
				return r;
			}
			mixin(_emitAll());

			override void emitPointer(ref ByteCodeBuilder bld){
				bld.error("taking address of union fields not yet supported at compile time", loader.loc);
			}
			override LValueStrategy emitFieldLV(ref ByteCodeBuilder bld, size_t off, size_t len, size_t ctlen, ErrorInfo info, VarDecl vd){
				static bool isFullStore(VarDecl vd){
					if(!vd) return true; // union tag
					assert(!!vd&&vd.scope_&&vd.isField);
					auto decl=vd.scope_.getDeclaration();
					assert(cast(AggregateDecl)decl);
					if(auto ud=decl.isUnionDecl()) return true;
					auto aggr=cast(AggregateDecl)cast(void*)decl;
					size_t n=0;
					foreach(fld;&aggr.traverseDeclaredFields)
						if(++n>1) return false;
					return true;
				}
				static class PartialUnionAccessLV: LValueStrategy{
					UnionFieldLV outer;
					LValueStrategy delegate() r; ErrorInfo info;
					size_t size;
					bool fullstore;
					this(UnionFieldLV outer,LValueStrategy delegate() r, ErrorInfo info,size_t size,bool fullstore){
						this.outer=outer; this.r=r; this.info=info;
						this.size=size;
						this.fullstore=fullstore;
					}

					override @property size_t lvBCSize(){ return outer.lvBCSize; }
					private static _emitAll(){
						string r;
						foreach(s;["emitLoad", "emitLoadKR"]){
							r~=mixin(X!q{
								override void @(s)(ref ByteCodeBuilder bld){
									auto lv=r();
									outer.loadCheck(bld);
									lv.@(s)(bld);
								}
							});
						}
						foreach(i,s;["emitStore", "emitStoreKR", "emitStoreKV"])
							r~=mixin(X!q{ override void @(s)(ref ByteCodeBuilder bld){
								bld.emitTmppush(size);
								enum lderr="partial assignments to union fields not yet supported at compile time";
								if(fullstore) outer.storeUpdate(bld);
								else outer.loadCheck(bld, lderr, info.loc);
								auto lv=r();
								bld.emitTmppop(size);
								lv.@(s)(bld);
							} });
						return r;
					}
					mixin(_emitAll());
					override void emitPointer(ref ByteCodeBuilder bld){
						bld.error("taking address of members of union fields not yet supported at compile time", info.loc);
					}
					override LValueStrategy emitFieldLV(ref ByteCodeBuilder bld, size_t off, size_t len, size_t ctlen, ErrorInfo info2, VarDecl vd){
						auto lv=()=>r().emitFieldLV(bld, off, len, ctlen, info2, vd);
						return new PartialUnionAccessLV(outer, lv, info, len, fullstore&&isFullStore(vd));
					}
				}
				auto r=()=>emitTheField(bld).emitFieldLV(bld, off, len, ctlen, info, vd);
				return new PartialUnionAccessLV(this, r, info, len, isFullStore(vd));
			}
		}
		return new UnionFieldLV(lv, loader, getIndex(vd), vd);
	}
}


mixin template CTFEInterpret(T) if(is(T==ReferenceAggregateDecl)){
	private Symbol[] symbols;
	private FunctionDecl findFunDeclFromIndex(size_t index){
		if(vtbl.length>index) return vtbl.vtbl[index].fun;
		assert(parents.length && cast(AggregateTy)parents[0] &&
		       cast(ReferenceAggregateDecl)(cast(AggregateTy)parents[0]).decl);
		auto pdecl = cast(ReferenceAggregateDecl)cast(void*)(cast(AggregateTy)cast(void*)parents[0]).decl;
		return pdecl.findFunDeclFromIndex(index);
	}
	final Symbol bcFetchVTBL(size_t index){
		if(vtbl.length<=index) // incomplete vtbl
			return bcFetchOverride(findFunDeclFromIndex(index));
		if(!symbols.length) symbols = new Symbol[vtbl.length];
		if(!symbols[index]){
			symbols[index] = createSymbol(vtbl.vtbl[index].fun);
		}
		return symbols[index];
	}
	private Symbol createSymbol(FunctionDecl decl){
		auto sym = New!Symbol(decl);
		sym.scope_ = scope_;
		sym.accessCheck = AccessCheck.none;
		sym.willAlias();
		return sym;
	}
	private Symbol[FunctionDecl] dynSymbols;
	private Identifier[FunctionDecl] lkupIdents;
	final Symbol bcFetchOverride(FunctionDecl decl){
		if(!dynSymbols.get(decl, null)){
			if(!lkupIdents.get(decl, null)){
				auto ident = New!Identifier(decl.name.name);
				ident.loc = decl.name.loc; // TODO: improve
				lkupIdents[decl]=ident;
			}
			auto ident = lkupIdents[decl];

			if(!ident.meaning){
				Dependent!FunctionDecl traverse(Scope view, ReferenceAggregateDecl raggr){
					auto own = raggr.lookupSealedOverloadSet(view,ident);
					own.dependentCTFE();
					if(auto ovs = own.value){
						mixin(FindOverrider!q{auto fod;ovs,decl});
						if(fod) return fod.independent;
					}
					if(!raggr.parents.length) return null.independent!FunctionDecl;
					raggr.findFirstNParents(1, true);
					mixin(Rewrite!q{raggr.parents[0]});
					if(raggr.parents[0].sstate != SemState.completed){
						raggr.parents[0].needRetry = true;
						return Dependee(raggr.parents[0], raggr.scope_).dependent!FunctionDecl;
					}
					if(auto ty=raggr.parents[0].isType())
					if(auto at=ty.isAggregateTy()){
						if(auto cd=at.decl.isClassDecl())
							return traverse(view,cd);
					}
					return null.independent!FunctionDecl;
				}
				auto x = traverse(asc,this);
				x.dependentCTFE();
				//if(!x.value){ throw new UnwindException; }
				assert(x.value);
				dynSymbols[decl]=createSymbol(x.value); // TODO!
			}
		}
		return dynSymbols[decl];
	}

	override int traverseFields(scope int delegate(VarDecl) dg){
		if(auto p=parentClass()) if(auto r=p.traverseFields(dg)) return r;
		return super.traverseFields(dg);
	}

	override bool isLayoutKnown(){
		if(auto p = parentClass()) if(parentVers != getVersion()) return false;
		return super.isLayoutKnown();
	}
	override void updateLayout(){
		super.updateLayout();
		if(auto p = parentClass()) parentVers = p.getVersion();
	}

	override protected size_t initialOffset(){
		if(auto p = parentClass()) return p.getBCSize();
		// static classes have a null context pointer so that virtual method calls
		// can rely on a consistent layout
		return bcPointerBCSize+1; // space for type information
	}

	override void byteCompileFields(ref ByteCodeBuilder bld){
		if(auto p = parentClass()) p.byteCompileFields(bld);
		super.byteCompileFields(bld);
	}
private:
	ulong parentVers = 0;
}

mixin template CTFEInterpret(T) if(is(T==TmpVarExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		tmpVarDecl.byteCompile(bld);
	}
}

mixin template CTFEInterpret(T) if(is(T==TemporaryExp)){
	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		assert(tmpVarDecl);
		tmpVarDecl.inHeapContext = true; // TODO: why is this here?
		tmpVarDecl.byteCompile(bld);
		return tmpVarDecl.byteCompileSymbolLV(bld, this, tmpVarDecl.scope_);
	}
}

mixin template CTFEInterpret(T) if(is(T==StructConsExp)){

	void beginByteCompile(ref ByteCodeBuilder bld){
		if(consCall) tmpVarDecl.inHeapContext = true; // conservative, anticipating that the constructor might escape 'this'
	}

	override void byteCompile(ref ByteCodeBuilder bld){
		if(!strd.isLayoutKnown()) strd.updateLayout();
		strd.byteCompileInit(bld, contextIsNull ? null : tmpVarDecl.scope_);
		// TODO: finish temporary variables (destructors etc)
	}
	void finishByteCompile(ref ByteCodeBuilder bld){
		if(consCall){
			tmpVarDecl.byteCompileSymbolLV(bld, this, tmpVarDecl.scope_).emitPointer(bld);
			consCall.byteCompile(bld);
		}
	}
}

mixin template CTFEInterpret(T) if(is(T==NewExp)){
	void byteCompileInit(ref ByteCodeBuilder bld, Type type){
	}
	void byteCompileForType(ref ByteCodeBuilder bld, Type type){
		auto tu = type.getHeadUnqual();
		if(auto da=tu.isDynArrTy()){
			void go(Type ty, size_t index){
				if(index<a2.length){
					a2[index].byteCompile(bld);
					assert(getBCSizeof(a2[index].type)==1);
					bld.emit(Instruction.dup);
					bld.emit(Instruction.tmppush);
					bld.emit(Instruction.newarray);
					auto elt=ty.getElementType();
					assert(!!elt);
					auto elsiz=getCTSizeof(elt);
					bld.emitConstant(elsiz);
					bld.emit(Instruction.push);
					bld.emitConstant(0); // loop index
					auto start=bld.getLocation();
					bld.emit(Instruction.tmppop); // termination criterion
					bld.emit(Instruction.dup);
					bld.emit(Instruction.push);
					bld.emitConstant(1);
					bld.emit(Instruction.subi);
					bld.emit(Instruction.tmppush); // termination criterion
					bld.emit(Instruction.jz);
					auto end=bld.emitLabel();
					go(elt, index+1);
					bld.emitUnsafe(Instruction.storeakr, this); // (always safe)
					bld.emitConstant(elsiz);
					bld.emit(Instruction.push);
					bld.emitConstant(1);
					bld.emit(Instruction.addi); // increment loop index
					bld.emit(Instruction.jmp);
					bld.emitConstant(start);
					end.here();
					bld.emit(Instruction.tmppop); // discard termination criterion
					bld.emit(Instruction.pop);
					bld.emit(Instruction.pop); // discard loop index
				}else VarDecl.byteCompileDefaultInit(bld, ty, scope_);
			}
			go(type,0);
			return;
		}
		size_t siz;
		if(auto aggrty=tu.isAggregateTy()){
			aggrty.decl.byteCompileInit(bld, scope_);
			auto els=aggrty.decl.getBCSize();
			siz=els*ulong.sizeof;
		}else{
			// built-in
			if(a2.length){
				assert(a2.length==1);
				a2[0].byteCompile(bld);
			}else VarDecl.byteCompileDefaultInit(bld, tu, scope_);
			siz=getCTSizeof(tu);
		}
		bld.emit(Instruction.push); bld.emitConstant(1);
		bld.emit(Instruction.makearray);
		bld.emitConstant(siz);
		bld.emit(Instruction.ptra);

		if(consCall){
			bld.emitDup(bcPointerBCSize); // duplicate the reference
			consCall.byteCompile(bld);
		}
	}
	override void byteCompile(ref ByteCodeBuilder bld){
		assert(!!type);
		auto tt = type;
		if(auto ptr=type.isPointerTy()) tt=ptr.ty;
		byteCompileForType(bld, tt);
	}
}

mixin template CTFEInterpret(T) if(is(T==CurrentExp)){
	private static void pushContext(ref ByteCodeBuilder bld, Scope scope_, Expression loader){
		auto diff = scope_.getFrameNesting()-
			(scope_.getAggregate().scope_.getFrameNesting()+1);
		bld.emitUnsafe(Instruction.pushcontext, loader);
		bld.emitConstant(diff);
	}
	private static bool checkEnclosingMemberFunction(ref ByteCodeBuilder bld, Scope scope_, Expression loader){
		if(!enclosingMemberFunction(scope_)){
			bld.error("cannot access 'this' in an evaluation invoked at this nesting level", loader.loc);
			return false;
		}
		return true;
	}
	override void byteCompile(ref ByteCodeBuilder bld){ byteCompile(bld, scope_, type, this); }
	static void byteCompile(ref ByteCodeBuilder bld, Scope scope_, Type type, Expression loader){
		if(!checkEnclosingMemberFunction(bld, scope_, loader)) return;
		assert(cast(AggregateTy)type.getHeadUnqual()&&scope_.getAggregate());
		if((cast(AggregateTy)cast(void*)type.getHeadUnqual()).decl.isReferenceAggregateDecl()){
			return pushContext(bld, scope_, loader);
		}
		auto diff = scope_.getFrameNesting()-
			(scope_.getAggregate().scope_.getFrameNesting()+1);

		bld.emit(Instruction.push); bld.emitConstant(0);
		if(diff){bld.emit(Instruction.push); bld.emitConstant(diff);}
		auto lv=diff?LVpopcc(type, loader):LVpopc(type, loader);
		lv.emitLoad(bld);
	}
	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		return byteCompileLV(bld, scope_, type, this);
	}
	static LValueStrategy byteCompileLV(ref ByteCodeBuilder bld, Scope scope_, Type type, Expression loader){
		assert((cast(AggregateTy)type.getHeadUnqual())&&cast(ValueAggregateDecl)(cast(AggregateTy)type.getHeadUnqual()).decl);
		if(!checkEnclosingMemberFunction(bld,scope_,loader)) return LVpopc(Type.get!void(), loader); // dummy
		pushContext(bld, scope_, loader);
		return LVpointer(type, loader);
	}
}

// get compile time size of a type in bytes
size_t getCTSizeof(Type type)out(res){
	assert(res||type.isTypeTuple()&&type.isTypeTuple().length==0);
}body{
	type = type.getHeadUnqual();
	if(type.getUnqual().among(Type.get!(void*)(), Type.get!(void[])()))
		return getBCSizeof(type)*ulong.sizeof;
	if(type.isDynArrTy()) return BCSlice.sizeof;
	import std.algorithm;
	if(auto arr=type.isArrayTy()) return cast(size_t)max(1, getCTSizeof(arr.ty)*arr.length);
	if(auto ptr=type.isPointerTy()){
		if(ptr.ty.isFunctionTy()) return Symbol.sizeof;
		else return BCPointer.sizeof;
	}
	if(type is Type.get!(typeof(null))()) return BCPointer.sizeof;
	static assert(FunctionDef.sizeof<=ulong.sizeof && (void*).sizeof<=ulong.sizeof);
	if(type.isDelegateTy()) return getBCSizeof(type)*ulong.sizeof;
	if(type is Type.get!real()) return real.sizeof;
	if(auto at=type.isAggregateTy()){
		if(at.decl.isReferenceAggregateDecl()) return BCPointer.sizeof;
		return getBCSizeof(at)*ulong.sizeof;
	}
	if(auto et = type.isEnumTy()){
		assert(et.decl.base);
		return getCTSizeof(et.decl.base);
	}
	if(auto tt = type.isTypeTuple()) return getBCSizeof(tt)*ulong.sizeof;
	return cast(size_t)type.getSizeof();
}

// get size in ulongs on the bc stack
enum bcPointerBCSize = (BCPointer.sizeof+ulong.sizeof-1)/ulong.sizeof;
enum bcSliceBCSize = (BCSlice.sizeof+ulong.sizeof-1)/ulong.sizeof;
enum bcFunPointerBCSize = 1;
enum bcDelegateBCSize = bcPointerBCSize+bcFunPointerBCSize;
size_t getBCSizeof(Type type)in{ assert(!!type); }body{
	type = type.getHeadUnqual();
	if(auto bt = type.isBasicType()){
		if(bt.op == Tok!"void") return 0;
		return (bt.bitSize()+63)/64;
	}
	if(type.isDynArrTy() || type is Type.get!EmptyArray())
		return bcSliceBCSize + (type.getUnqual() is Type.get!(void[])());
	if(type.isArrayTy()) return (getCTSizeof(type)+ulong.sizeof-1)/ulong.sizeof;
	if(auto ptr=type.isPointerTy()){
		if(ptr.ty.isFunctionTy()) return bcFunPointerBCSize;
	ptr: return bcPointerBCSize+(type.getUnqual() is Type.get!(void*)());
	}else if(type is Type.get!(typeof(null))()) goto ptr;
	static assert(FunctionDef.sizeof<=ulong.sizeof && (void*).sizeof<=ulong.sizeof);
	if(type.isDelegateTy()) return bcDelegateBCSize;
	if(auto aggrty = type.isAggregateTy()){
		if(aggrty.decl.isValueAggregateDecl()){
			return aggrty.decl.getBCSize();
		}else{
			assert(!!aggrty.decl.isReferenceAggregateDecl());
			goto ptr;
		}
	}
	if(auto et = type.isEnumTy()){
		assert(et.decl.base);
		return getBCSizeof(et.decl.base);
	}
	if(auto tt = type.isTypeTuple()){
		size_t r=0;
		foreach(Type t;tt) r+=getBCSizeof(t);
		return r;
	}
	assert(0, "type "~type.toString~" not yet supported at compile time");
}

mixin template CTFEInterpret(T) if(is(T==VarDecl)){

	static void byteCompileDefaultInit(ref ByteCodeBuilder bld, Type type, Scope sc){
		auto len = getBCSizeof(type);
		if(auto aggrty=type.isAggregateTy()){
			if(auto decl=aggrty.decl.isStructDecl()){
				auto b = Declaration.isDeclAccessible(sc.getDeclaration(), decl).force;
				decl.byteCompileInit(bld, b?sc:null); // TODO: handle scope not being accessible
				return;
			}
		}
		// TODO: emit the correct inits
		foreach(i;0..len){bld.emit(Instruction.push); bld.emitConstant(0);}
	}

	size_t getBCSize(){
		if(auto tp=type.isTypeTuple()){
			size_t size=0;
			foreach(x;tupleContext.vds) size+=x.getBCSize;
			return size;
		}
		if(stc&STCbyref) return bcPointerBCSize;
		if(stc&STClazy) return bcDelegateBCSize;
		return getBCSizeof(type);
	}

	final override void byteCompile(ref ByteCodeBuilder bld){
		byteCompileOptionalInit(bld, true);
	}

	private void byteCompileOptionalInit(ref ByteCodeBuilder bld, bool initialize){
		if(init&&init.isVoidInitializerExp()) initialize=false; // TODO: catch use before write?
		if(auto tp=type.isTypeTuple()){
			assert(initialize);
			assert(tupleContext && tupleContext.vds.length == tp.length);
			auto complexInit=init&&!init.isExpTuple();
			foreach(x;tupleContext.vds) x.byteCompileOptionalInit(bld,!complexInit);
			if(complexInit){
				if(stc&STCref) UnaryExp!(Tok!"&").emitAddressOf(bld, init);
				else init.byteCompile(bld);
				size_t size=getBCSize();
				bld.emitTmppush(size);
				size_t off = 0;
				foreach(x;tupleContext.vds){
					auto lv=x.byteCompileInitLV(bld, init, x.scope_);
					size_t len; x.getBCLoc(len);
					bld.emitTmppop(len);
					lv.emitStore(bld);
					off+=len;
				}
				assert(size==off);
			}
			if(tupleContext.initLeftover)
				ExpressionStm.byteCompileIgnoreResult(bld, tupleContext.initLeftover);
			return;
		}
		size_t off, len = getBCSize();
		// dw(len," ",type);
		if(len==-1) return emitUnsupportedError(bld);
		if(initialize)if(auto ini=init?init.isStructConsExp():null){
			assert(ini.tmpVarDecl is this,text(ini.tmpVarDecl));
			ini.beginByteCompile(bld);
		}
		if(inHeapContext){
			off = bld.getContextOffset();
			setBCLoc(off, len);
			bld.addContextOffset(len);
		}else{
			off = bld.getStackOffset();
			setBCLoc(off, len);
			bld.addStackOffset(len);
		}

		if(!initialize) return;
		if(inHeapContext){
			bld.emit(Instruction.push);
			bld.emitConstant(off);
		}
		if(stc&STCref){
			assert(!!init);
			UnaryExp!(Tok!"&").emitAddressOf(bld, init);
		}else{
			if(init) init.byteCompile(bld); // TODO: in semantic, add correct 'init's
			else byteCompileDefaultInit(bld, type, scope_);
		}

		// dw(this," ",off," ",len);

		if(inHeapContext){
			bld.emitUnsafe(Instruction.popcn, this);
			bld.emitConstant(len);
		}else{
			if(len){
				bld.emitPopp(len);
				bld.emitConstant(off);
			}
		}

		if(auto ini=init?init.isStructConsExp():null){
			assert(ini.tmpVarDecl is this);
			ini.finishByteCompile(bld);
		}
	}

	final void emitUnsupportedError(ref ByteCodeBuilder bld){
		bld.error(format("cannot interpret local variable of type '%s' at compile time yet.",type.toString()),loc);
	}

	/* loads a variable, without taking into account any special storage classes
	   (loads a pointer for STCbyref, loads a delegate for STClazy)
	 */

	private void load(ref ByteCodeBuilder bld, Expression loader, Scope loadersc)in{
		assert(loader&&loadersc);
	}body{
		void accessError(){
			if(name)
				bld.error(format("cannot access variable '%s' at compile time", name.toString()), loader.loc);
			else
				bld.error("cannot access variable at compile time", loader.loc);
		}
		if(stc&STCstatic && (!(stc&(STCimmutable|STCconst)||!init))){
			accessError();
			return;
		}if(stc&STCenum){
			// TODO: this can be inefficient for immutable variables
			init.byteCompile(bld);
			return;
		}else{
			// TODO: nested functions
			size_t len, off = getBCLoc(len);
			if(!~off){
				if(stc&(STCimmutable|STCconst)&&init){
					// TODO: this should implicitly copy aggregates
					init.byteCompile(bld);
					return;
				}
				accessError();
				return;
			}
			if(!inHeapContext){
				if(len){
					bld.emitPushp(len);
					bld.emitConstant(off);
				}
				return;
			}else{
				auto diff = loadersc.getFrameNesting() - scope_.getFrameNesting();

				if(!diff){
					bld.emit(Instruction.push);
					bld.emitConstant(off);
					bld.emitUnsafe(Instruction.pushcn, loader);
					bld.emitConstant(len);
				}else{
					bld.emit(Instruction.push);
					bld.emitConstant(off);
					bld.emit(Instruction.push);
					bld.emitConstant(diff);
					bld.emitUnsafe(Instruction.pushccn, loader);
					bld.emitConstant(len);
				}
				return;
			}
		}
	}


	final void byteCompileSymbol(ref ByteCodeBuilder bld, Expression loader, Scope loadersc)in{
		assert(loader&&loadersc);
	}body{
		load(bld, loader, loadersc);
		if(stc&STCbyref){
			auto strat = LVpointer(type, loader);
			strat.emitLoad(bld);
		}else if(stc&STClazy){
			// call the delegate
			bld.emitUnsafe(Instruction.call, loader);
			bld.emitConstant(bcPointerBCSize);
		}
		assert(!(stc&STCbyref)||!(stc&STClazy));
	}

	// emit code and get the LValueStrategy to access the raw variable memory
	final LValueStrategy byteCompileInitLV(ref ByteCodeBuilder bld, Expression loader, Scope loadersc)in{
		assert(loader&&loadersc);
	}body{
		size_t len, off = getBCLoc(len);
		if(!~off){
			if(stc&(STCimmutable|STCconst)&&init){
				if(stc&STCstatic){
					static LiteralExp[VarDecl] decls;
					if(this !in decls){
						assert(cast(LiteralExp)init,text(init," ",));
						auto v=init.interpretV();
						auto s=[v]; // TODO: allocation here
						auto p=Variant([FieldAccess(s.ptr-s.ptr)], s, type.getPointer());
						auto e=p.toExpr();
						assert(cast(LiteralExp)e);
						decls[this]=cast(LiteralExp)cast(void*)e;
					}
					decls[this].byteCompile(bld);
				}else{
					// global local variables
					// TODO: aliasing
					init.byteCompile(bld);
					emitMakeArray(bld,type.getDynArr(), 1);
					bld.emit(Instruction.ptra);
				}
				return LVpointer(type, this);
			}
			bld.error(format("cannot access variable '%s' at compile time", name.toString()),loader.loc);
			return LVpopc(Type.get!void(), loader); // dummy
		}
		bld.emit(Instruction.push);
		bld.emitConstant(off);
		auto lnst = loadersc.getFrameNesting(), nst = scope_.getFrameNesting();
		assert(lnst>=nst);
		auto diff = lnst - nst;
		if(diff){bld.emit(Instruction.push); bld.emitConstant(diff);}
		return diff?LVpopcc(type, loader):inHeapContext?LVpopc(type, loader):LVpopr(len);
	}

	final LValueStrategy byteCompileSymbolLV(ref ByteCodeBuilder bld, Expression loader, Scope loadersc)in{
		assert(loader&&loadersc);
	}body{
		if(stc & STCbyref){
			load(bld, loader, loadersc);
			return LVpointer(type, this);
		}
		return byteCompileInitLV(bld, loader, loadersc);
	}


	final void setBCLoc(size_t off, size_t len){
		// import std.stdio; writeln(this," ", len," ", off);
		byteCodeStackOffset = off;
		byteCodeStackLength = len;
		// dw("yes ", this," ",off," ",len," ",cast(void*)this);

		if(tupleContext){
			size_t toff=off;
			foreach(vd;tupleContext.vds){
				assert(vd.sstate == SemState.completed);
				auto tlen=getBCSizeof(vd.type);
				vd.setBCLoc(toff, tlen);
				toff+=tlen;
			}
			assert(toff==off+len);
		}
	}
	final size_t getBCLoc(ref size_t len){
		// import std.stdio; writeln("l ",this," ",cast(void*)this," ", byteCodeStackLength," ", byteCodeStackOffset);
		if(sstate!=SemState.completed)
			throw new CTFERetryException(this); // TODO: make more efficient
		len = byteCodeStackLength;
		return byteCodeStackOffset;
	}

	bool inHeapContext = false;
private:
	size_t byteCodeStackOffset = -1;
	size_t byteCodeStackLength = 0;
}

mixin template CTFEInterpret(T) if(is(T==Declarators)){
	override void byteCompile(ref ByteCodeBuilder bld){
		foreach(x; decls) x.byteCompile(bld);
	}
}

mixin template CTFEInterpret(T) if(is(T==FunctionDef)){
	private ByteCode _byteCode;
	private ErrorInfo[] bcErrtbl; // keep references for GC

	private size_t bcnumargs=-1;
	private bool hasBCContext;

	private void bcpreanalyze(){
		static struct MarkHeapContext{
			enum manualPropagate = true;
			void perform(Symbol self){
				if(!self.meaning) return;
				if(auto vd = self.meaning.isVarDecl()){
					if(vd.stc&STCbyref) return;
					vd.inHeapContext = true;
				}
			}
			void perform(FieldExp self){
				// for value types, having one member in the heap frame
				// implies that the entire value is stored there
				if(auto this_=self.e1.extractThis())
				if(auto aggrty=this_.type.getHeadUnqual().isAggregateTy())
				if(aggrty.decl.isValueAggregateDecl()){
					runAnalysis!MarkHeapContext(this_);
				}
			}

			void perform(UnaryExp!(Tok!"++") self){
				runAnalysis!MarkHeapContext(self.e);
			}
			void perform(UnaryExp!(Tok!"--") self){
				runAnalysis!MarkHeapContext(self.e);
			}
			void perform(CommaExp self){
				runAnalysis!MarkHeapContext(self.e2);
			}
			void perform(TernaryExp self){
				runAnalysis!MarkHeapContext(self.e2);
				runAnalysis!MarkHeapContext(self.e3);
			}
			void perform(IndexExp self){
				if(self.type.isArrayTy())
					runAnalysis!MarkHeapContext(self.e);
			}
			void perform(AssignExp self){
				runAnalysis!MarkHeapContext(self.e1);
			}
			debug void perform(TupleAssignExp self){ assert(0); }
			void perform(ExpTuple self){
				foreach(x;self) runAnalysis!MarkHeapContext(x);
			}
			// can happen eg for ref arguments
			void perform(CastExp self){
				runAnalysis!MarkHeapContext(self.e);
			}
		}
		// TODO: this is quite conservative for ease of implementation
		static struct HeapContextAnalysis{
			void perform(UnaryExp!(Tok!"&") self){
				runAnalysis!MarkHeapContext(self.e);
			}
			void perform(PtrExp self){
				if(self.e.type&&self.e.type.getHeadUnqual().isArrayTy())
					runAnalysis!MarkHeapContext(self.e);
			}
			void perform(IndexExp self){
				// TODO: remove this, do not require static arrays to reside on the heap!
				if(self.e.type&&self.e.type.getHeadUnqual().isArrayTy())
					runAnalysis!MarkHeapContext(self.e);
			}
			void perform(Symbol self){
				if(self.sstate!=SemState.completed) return;
				assert(self.scope_,text(self," ",self.loc));
				if(self.scope_.getFrameNesting()       >
				   self.meaning.scope_.getFrameNesting()){
					runAnalysis!MarkHeapContext(self);
				}
			}
			void perform(CallExp self){
				if(self.tmpVarDecl) self.tmpVarDecl.inHeapContext = true; // TODO: why?
				if(!self.fun || !self.fun.type) return; // TODO: ok?
				auto tt=self.fun.type.getHeadUnqual().getFunctionTy();
				assert(!!tt,text(self.fun.type));
				foreach(i,x; self.args){
					if(tt.params[i].stc&STCbyref)
						runAnalysis!MarkHeapContext(x);
				}
			}
			void perform(VarDecl self){
				if(self.init && self.stc&STCref)
					runAnalysis!MarkHeapContext(self.init);
			}
			void perform(FieldExp self){
				// the implicit this pointer is passed by reference
				// for value types
				if(self.type) // alias declarations can contain such expressions (TODO: should they?)
				if(self.type.getHeadUnqual().getFunctionTy())
				if(auto this_=self.e1.extractThis())
				if(auto aggrty=this_.type.getHeadUnqual().isAggregateTy())
				if(aggrty.decl.isValueAggregateDecl()){
					runAnalysis!MarkHeapContext(this_);
				}
			}
			void perform(ReturnStm self){
				if(self.isRefReturn) runAnalysis!MarkHeapContext(self.e);
			}

			void perform(FunctionDef self){
				// TODO: this is very conservative
				if(!(self.stc&STCstatic)) self.resetByteCode();
			}
			void perform(TemplateInstanceDecl self){
				// TODO: maybe this is too conservative too
				if(!(self.stc&STCstatic)) self.resetByteCode();
			}
		}
		runAnalysis!HeapContextAnalysis(this);
	}

	/+final int traverseHeapContext(scope int delegate(VarDecl) dg){
		if(stc&STCstatic) return 0;
		auto decl=scope_.getDeclaration();
		if(!decl) return 0;
		if(auto fd=decl.isFunctionDef()) return fd.traverseOwnHeapContext(dg);
		else if(auto ad=decl.isAggregateDecl()) return ad.traverseFields(dg);
		else assert(0);
	}+/

	final int traverseHeapContext(scope int delegate(VarDecl) dg){
		foreach(p;type.params.filter!(p=>p.inHeapContext))
			if(auto r=dg(p)) return r;
		// TODO: collect variables more efficiently
		static struct CollectVariables{
			FunctionDef self;
			typeof(dg) found;
			int r=0;
			void perform(VarDecl vd){
				if(!vd.scope_||vd.scope_.getFunction() !is self) return;
				if(!r&&vd.inHeapContext) r = found(vd);
			}
		}
		return runAnalysis!CollectVariables(this,this,dg).r;
	}


	void resetByteCode(){
		_byteCode = null;
	}

	void resetLabels(){
		static struct Resetter{
			void perform(LabeledStm lbl){
				lbl.bcLabel=ByteCodeBuilder.Label.init;
			}
			void perform(SwitchLabelStm swl){
				swl.bcLabel=ByteCodeBuilder.Label.init;
			}
		}
		runAnalysis!Resetter(bdy);
	}

	private{
		ulong vers=0;
		bool mayBeOutdated(){
			return vers!=AggregateDecl.getVersion();
		}
		void rememberVersion(){
			vers = AggregateDecl.getVersion();
		}
	}

	private void subscribeForLayoutChanges(){
		static struct Subscribe{
			NotifyOnLayoutChanged me;
			void perform(Expression self){
				if(!self.type) return;
				if(auto aggrty=self.type.isAggregateTy())
					aggrty.decl.subscribeForLayoutChanges(me);
			}
			void perform(VarDecl self){
				if(!self.type) return;
				if(auto aggrty=self.type.isAggregateTy())
					aggrty.decl.subscribeForLayoutChanges(me);
			}
		}
		runAnalysis!Subscribe(this, this);
	}

	void notifyLayoutChanged(AggregateDecl decl){
		resetByteCode();
	}

	final bool isInterpretableWithoutContext(){
		// TODO: invalid (null) contexts should never be stored in delegates that are kept for later
		// (maybe it is best to automatically insert the right context for enum constants
		// like DMD does?)
		return canBeStatic || (a=>!a||a.isFunctionDef())(scope_.getDeclaration());
	}

	ByteCodeBuilder bld;

	@property ByteCode byteCode(){
		if(_byteCode is null){
			bld=ByteCodeBuilder.init;
			if(bcnumargs==-1) bcpreanalyze();
			size_t loc = 0, len = 0;
			if(!(stc&STCstatic)) loc+=bcPointerBCSize; // context pointer
			foreach(i,x; type.params){
				len = x.getBCSize();
				x.setBCLoc(loc, len);
				loc+=len;
			}
			bcnumargs = loc;
			bld.addStackOffset(bcnumargs); // leave room for locals
			// move arguments to context if necessary:
			alias util.any any;
			bool hasBCContext = !(stc&STCstatic) || any!(_=>_.inHeapContext)(type.params);
			auto alloca = bld.emitAlloca(); // reserve local variables
			auto allocc = bld.emitAllocc();
			if(hasBCContext){
				alias Instruction I;
				// copy parent context pointer to own context
				// TODO: this does not have to be in the context if never requested
				if(!(stc&STCstatic)){
					bld.addContextOffset(bcPointerBCSize);
					bld.emit(I.push);
					bld.emitConstant(0);
					bld.emitPushp(bcPointerBCSize);
					bld.emitConstant(0);
					bld.emitUnsafe(I.popcn, this);
					bld.emitConstant(bcPointerBCSize);
				}
				foreach(i,x; type.params){
					if(!x.inHeapContext) continue;
					size_t coff = bld.getContextOffset();
					size_t slen, soff = x.getBCLoc(slen);
					x.setBCLoc(coff, slen);
					if(slen){
						bld.addContextOffset(slen);
						bld.emit(I.push);
						bld.emitConstant(coff);
						bld.emitPushp(slen);
						bld.emitConstant(soff);
						bld.emitUnsafe(I.popcn, x);
						bld.emitConstant(slen);
					}
				}
			}

			bdy.byteCompile(bld);

			if(type.ret is Type.get!void()) bld.emit(Instruction.ret);
			allocc.done();
			alloca.done();
			_byteCode = bld.getByteCode();
			bcErrtbl = bld.getErrtbl();
			if(_displayByteCode){
				import std.stdio; writeln("byteCode for ",name," ",scope_.getDeclaration()?scope_.getDeclaration().name.name:"",":\n",_byteCode.toString());
			}

			rememberVersion();
			resetLabels();
			subscribeForLayoutChanges();
		}
		return _byteCode;
	}

	final Variant interpretCall(ErrorHandler handler)in{
		assert(sstate == SemState.completed);
		assert(type.params.length == 0);
	}body{
		ulong[100] stackst;
		auto stack=Stack(stackst[]);

		bcpreanalyze();

		byteCode.doInterpret(stack, handler);

		if(sstate != SemState.completed)
			resetByteCode();

		// TODO: this relies on the little-endianness of the host system for built-in integers!
		version(LittleEndian) enum endiannessok=true;
		static assert(endiannessok);

		auto ctsize=getCTSizeof(type.ret);
		// SliceCollection slices; // TODO?
		// type.ret.collectSlices((cast(void[])stack.stack)[0..ctsize], type.ret, slices);
		if(type.ret is Type.get!void()) return Variant(null, Type.get!void());
		assert(ctsize<=(stack.stp+1)*ulong.sizeof);
		return type.ret.variantFromMemory((cast(void[])stack.stack)[0..ctsize], type.ret);
	}
}

mixin template CTFEInterpret(T) if(is(T==CallExp)){
	private void emitCall(ref ByteCodeBuilder bld){
		bool ctx = false;
		if(auto s = fun.isSymbol())if(auto m = s.meaning)
			if(m.isFunctionDecl()&&!(m.stc&STCstatic)) ctx=true;
		if(auto f = fun.isFieldExp())if(auto m = f.e2.meaning)
			if(m.isFunctionDecl()&&!(m.stc&STCstatic)) ctx=true;
		auto tt=fun.type.getHeadUnqual();
		if(!ctx && tt.isDelegateTy()) ctx = true;

		FunctionTy ft;
		if(auto fty=tt.isFunctionTy()) ft = fty;
		else if(auto ptr=tt.isPointerTy()){
			assert(cast(FunctionTy)ptr.ty);
			ft=cast(FunctionTy)cast(void*)ptr.ty;
		}else{
			assert(cast(DelegateTy)tt);
			ft=(cast(DelegateTy)cast(void*)tt).ft;
		}

		fun.byteCompile(bld);
		ulong numargs = ctx ? bcPointerBCSize : 0;
		if(args.length){
			bld.emit(Instruction.tmppush);
			foreach(i,x;args){
				if(ft.params[i].stc & STCbyref){
					UnaryExp!(Tok!"&").emitAddressOf(bld, x);
					numargs += getBCSizeof(x.type.getPointer());
				}else if(ft.params[i].stc & STClazy){
					assert(adapted[i] && adapted[i].sstate == SemState.completed &&
					       adapted[i].type.isDelegateTy());
					adapted[i].byteCompile(bld);
					numargs += getBCSizeof(adapted[i].type);
				}else{
					x.byteCompile(bld);
					numargs += getBCSizeof(x.type);
				}
			}
			bld.emit(Instruction.tmppop);
		}
		if(argsLeftover) ExpressionStm.byteCompileIgnoreResult(bld, argsLeftover);
		bld.emitUnsafe(Instruction.call, this);
		bld.emitConstant(numargs);
	}
	override void byteCompile(ref ByteCodeBuilder bld){
		emitCall(bld);
		if(fun.type.getHeadUnqual().getFunctionTy().stc&STCref) LVpointer(type, this).emitLoad(bld);
	}
	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		if(!(fun.type.getHeadUnqual().getFunctionTy().stc&STCref)) return super.byteCompileLV(bld);
		emitCall(bld);
		return LVpointer(type, this);
	}
}

mixin template CTFEInterpret(T) if(is(T==TemplateDecl)){
	override void byteCompile(ref ByteCodeBuilder bld){
		// TODO: local templates are still a little messy!
		foreach(x; store.instances) x.byteCompile(bld);
	}
}
mixin template CTFEInterpret(T) if(is(T==TemplateInstanceDecl)){
	private bool alreadyBCCompiled = false;

	void resetByteCode(){
		alreadyBCCompiled = false;
	}

	override void byteCompile(ref ByteCodeBuilder bld){
		if(alreadyBCCompiled) return;
		bdy.byteCompile(bld);
		alreadyBCCompiled = true;
	}
}
mixin template CTFEInterpret(T) if(is(T==BlockDecl)){
	override void byteCompile(ref ByteCodeBuilder bld){
		foreach(decl; decls) decl.byteCompile(bld);
	}
}
mixin template CTFEInterpret(T) if(is(T==PragmaDecl)){
	override void byteCompile(ref ByteCodeBuilder bld){
		bdy.byteCompile(bld);
	}
}


/+// TODO: this is similar to Stack.pop
T consume(T=ulong)(ref ulong[] memory){
	static if(is(T==ulong)){
		auto res = memory[0];
		memory = memory[1..$];
		return res;
	}else{
		enum sz=(ulong.sizeof-1+T.sizeof)/ulong.sizeof;
		T c=void;
		static if(T.alignof<=ulong.alignof)
			c=*cast(T*)memory.ptr;
		else{
			import core.stdc.string;
			memcpy(&c,memory.ptr,c.sizeof);
		}
		memory=memory[sz..$];
		return c;
	}
}+/

mixin template CTFEInterpret(T) if(is(T==Type)){
	abstract void variantToMemory(Variant value, void[] mem);
	abstract Variant variantFromMemory(void[] mem, Type type);
}

mixin template NoCTFEInterpretType(){
	override void variantToMemory(Variant value, void[] mem){
		assert(0);
	}
	override Variant variantFromMemory(void[] mem, Type type){
		assert(0);
	}
}

mixin template CTFEInterpret(T) if(is(T==ErrorTy)||is(T==MatcherTy)){
	mixin NoCTFEInterpretType;
}

mixin template CTFEInterpret(T) if(is(T==ConstTy)||is(T==ImmutableTy)||is(T==SharedTy)||is(T==InoutTy)){
	override void variantToMemory(Variant value, void[] mem){
		return getHeadUnqual().variantToMemory(value, mem);
	}
	override Variant variantFromMemory(void[] mem, Type type){
		return getHeadUnqual().variantFromMemory(mem, type);
	}
}

mixin template CTFEInterpret(T) if(is(T==NullPtrTy)){
	override void variantToMemory(Variant value, void[] mem){
		assert(value.getType().getHeadUnqual() is this);
		assert(mem.length==BCPointer.sizeof);
		*(cast(BCPointer*)mem.ptr)=BCPointer([],null);
	}

	override Variant variantFromMemory(void[] mem, Type type){
		assert(type.getHeadUnqual() is this);
		assert(mem.length==BCPointer.sizeof);
		assert(*(cast(BCPointer*)mem.ptr)==BCPointer([],null));
		return Variant(null, type);
	}
}

mixin template CTFEInterpret(T) if(is(T==EmptyArrTy)){
	override void variantToMemory(Variant value, void[] mem){
		assert(value.getType().getHeadUnqual() is this);
		assert(mem.length==BCSlice.sizeof);
		*(cast(BCSlice*)mem.ptr)=BCSlice([],[]);
	}

	override Variant variantFromMemory(void[] mem, Type type){
		assert(type.getHeadUnqual() is this);
		assert(mem.length==BCSlice.sizeof);
		assert(*(cast(BCSlice*)mem.ptr)==BCSlice([],[]));
		return Variant((Variant[]).init,(Variant[]).init,type);
	}
}

mixin template CTFEInterpret(T) if(is(T==BasicType)){
	enum ctfeinterpretbody = q{
		switch(op){
			foreach(x;ToTuple!basicTypes){
				static if(x!="void")
				case Tok!x:
					mixin("alias "~x~" T;"); // workaround DMD bug
				assert(mem.length==T.sizeof);
				mixin(res);
			}
			default: assert(0);
		}
	};

	override void variantToMemory(Variant value, void[] mem){
		assert(value.getType().getHeadUnqual() is this);
		enum res=q{ *(cast(T*)mem.ptr)=value.get!T(); return; };
		mixin(ctfeinterpretbody);
	}

	override Variant variantFromMemory(void[] mem, Type type){
		assert(type.getHeadUnqual() is this);
		enum res=q{ return Variant(*cast(T*)mem.ptr, type); };
		mixin(ctfeinterpretbody);
	}
}

mixin template CTFEInterpret(T) if(is(T==FunctionTy)){
	override void variantToMemory(Variant value, void[] mem){
		assert(value.getType().getHeadUnqual() is this);
		assert(0, "TODO");
	}
	override Variant variantFromMemory(void[] mem, Type type){
		assert(type.getHeadUnqual() is this);
		assert(0, "TODO");
	}
}

mixin template CTFEInterpret(T) if(is(T==TypeofExp)||is(T==TypeofReturnExp)){
	mixin NoCTFEInterpretType;
}

mixin template CTFEInterpret(T) if(is(T==PointerTy)){
	// TODO: move common parts out instead of relying on DynArrTy implementation?
	override void variantToMemory(Variant value, void[] mem){
		assert(getUnqual() !is Type.get!(void*)()); // this case is handled elsewhere (TODO: move here?)
		assert(value.getType().getHeadUnqual() is this);
		if(ty.isFunctionTy()){
			assert(mem.length == Symbol.sizeof);
			*cast(Symbol*)mem.ptr = value.getFunctionPointer();
			return;
		}
		assert(mem.length==BCPointer.sizeof);
		auto cnt = value.getContainer();
		auto slt = ty.getDynArr();
		auto vcnt = variantArrayToContainer(cnt,slt);
		auto fa = value.getFieldAccess();
		size_t offset = parseFieldAccess(fa,slt);
		*(cast(BCPointer*)mem.ptr)=BCPointer(vcnt, vcnt.ptr+offset);
	}
	private size_t parseFieldAccess(scope FieldAccess[] fa,Type type){
		if(!fa.length) return 0;
		size_t x;
		Type nty;
		auto faf=fa.front;
		if(faf.isIndex){
			auto el=type.getElementType();
			assert(!!el);
			auto ctsize=getCTSizeof(el);
			x=ctsize*faf.index;
			nty=el;
		}else{
			assert(!!type.isAggregateTy());
			size_t len, off = faf.field.getBCLoc(len);
			x=off;
			nty=faf.field.type;
		}
		return x+parseFieldAccess(fa[1..$],nty);
	}

	override Variant variantFromMemory(void[] mem, Type type){
		assert(type.getHeadUnqual() is this);
		if(ty.isFunctionTy()){
			assert(mem.length == Symbol.sizeof);
			return Variant(*cast(Symbol*)mem.ptr,type);
		}
		if(type is Type.get!(void*)()){// TODO: merge with the respective code in
			assert(mem.length==getCTSizeof(Type.get!(void*)()));
			return voidPointerOrArrayToVariant(mem,BCPointer.sizeof);
		}
		assert(mem.length == getCTSizeof(this));
		auto ptr=*cast(BCPointer*)mem.ptr;
		auto offset = ptr.ptr-ptr.container.ptr;
		// TODO: correctly handle pointers to members
		auto cnt=variantArrayFromContainer(ptr.container, ty);
		auto ctsize=getCTSizeof(ty);
		return Variant([FieldAccess(offset/ctsize)], cnt, type);
	}
}

Variant voidPointerOrArrayToVariant(void[] mem, size_t size){
	auto ul=cast(ulong[])mem;
	auto type = cast(Type)cast(void*)ul[0];
	void[] nmem=ul[1..$];
	return type.variantFromMemory(nmem[0..size], type);
}

void variantArrayToContainer(Variant[] arr, void[] mem){
	// TODO: this is wasteful
	foreach(i;0..arr.length){
		auto el=arr[i].getType();
		auto ctsize=getCTSizeof(el);
		assert(ctsize&&mem.length==arr.length*ctsize,text(arr," ",ctsize," ",mem));
		el.variantToMemory(arr[i], mem[i*ctsize..(i+1)*ctsize]);
	}
}

void[] variantArrayToContainer(Variant[] cnt, Type tt){
	void[] vcnt;
	if(cnt.ptr in vmtr.sl_aliasing) vcnt=vmtr.sl_aliasing[cnt.ptr];
	else{
		auto ctsize = cnt.length?getCTSizeof(cnt[0].getType()):1;
		vcnt = (new void[cnt.length*ctsize+1])[0..$-1]; // prevent in-place update to make caching based on .ptr valid.
		if(vcnt !is null){
			vmtr.sl_aliasing[cnt.ptr]=vcnt;
			auto tag=q(tt.getUnqual(),vcnt.ptr);
			vmtr.sl_aliasing_rev[tag]=cnt;
			variantArrayToContainer(cnt, vcnt);
		}
	}
	return vcnt;
}

Variant[] variantArrayFromContainer(void[] mem, Type el, bool remember=true){
	auto ctsize=getCTSizeof(el);
	assert(!(mem.length%ctsize));
	auto tag=q(cast(Type)el.getUnqual().getDynArr(),mem.ptr);
	if(remember&&tag in vmtr.sl_aliasing_rev) return vmtr.sl_aliasing_rev[tag];
	auto len=mem.length/ctsize;
	auto res=new Variant[len];

	if(remember){
		vmtr.sl_aliasing_rev[tag]=res;
		vmtr.sl_aliasing[res.ptr]=mem;
	}

	foreach(i;0..len) res[i]=el.variantFromMemory(mem[i*ctsize..(i+1)*ctsize], el);
	return res;
}

mixin template CTFEInterpret(T) if(is(T==DynArrTy)){
	override void variantToMemory(Variant value, void[] mem){
		assert(getUnqual() !is Type.get!(void[])()); // this case is handled elsewhere (TODO: move here?)
		assert(value.getType().getHeadUnqual() is this);
		assert(mem.length == BCSlice.sizeof);

		if(value.getType().getHeadUnqual().isSomeString()){
			// TODO: aliasing
			foreach(T;Seq!(string,wstring,dstring)){
				if(value.getType().getHeadUnqual() is Type.get!T()){
					BCSlice slc;
					auto str=value.get!T();
					auto cnt=str~'\0';
					*cast(BCSlice*)mem.ptr=BCSlice(cast(void[])cnt,cast(void[])cnt[0..$-1]);
					return;
				}
			}
			assert(0);
		}

		auto arr = value.get!(Variant[])();
		auto cnt = value.getContainer();
		auto start = arr.ptr-cnt.ptr;
		auto end = start+arr.length;
		auto ctsize = getCTSizeof(ty);
		auto vcnt = variantArrayToContainer(cnt, this);
		*cast(BCSlice*)mem.ptr=BCSlice(vcnt, vcnt[ctsize*start..ctsize*end]);
	}
	override Variant variantFromMemory(void[] mem, Type type){
		if(type.getUnqual() is Type.get!(void[])()){
			assert(mem.length==getCTSizeof(Type.get!(void[])()));
			return voidPointerOrArrayToVariant(mem,BCSlice.sizeof);
		}
		assert(type.getHeadUnqual() is this);
		assert(mem.length == BCSlice.sizeof);
		auto slc = *cast(BCSlice*)mem.ptr;
		if(type.getHeadUnqual().isSomeString()){
			// TODO: aliasing
			foreach(T;Seq!(string,wstring,dstring)){
				if(type.getHeadUnqual() is Type.get!T())
					return Variant(cast(T)slc.slice,type);
			}
			assert(0);
		}
		auto cnt = variantArrayFromContainer(slc.container,ty);
		auto ctsize = getCTSizeof(ty);
		size_t start = slc.slice.ptr-slc.container.ptr;
		size_t end = start+slc.slice.length;
		auto rslc = cnt[start/ctsize..end/ctsize];
		return Variant(rslc, cnt, type);
	}
}

mixin template CTFEInterpret(T) if(is(T==ArrayTy)){
	override void variantToMemory(Variant value, void[] mem){
		assert(value.getType().getUnqual() is getUnqual());
		variantArrayToContainer(value.getContainer(), mem);
	}
	override Variant variantFromMemory(void[] mem, Type type){
		assert(type.getUnqual() is getUnqual());
		auto cnt=variantArrayFromContainer(mem, type.getElementType(), false);
		return Variant(cnt,cnt,type);
	}
}

mixin template CTFEInterpret(T) if(is(T==TypeTuple)){
	override void variantToMemory(Variant value, void[] mem){
		assert(value.getType().getHeadUnqual() is this);
		Variant[] vals=value.getTuple();
		size_t i=0, off=0;
		foreach(t;types){
			auto ctlen = getCTSizeof(t);
			t.variantToMemory(vals[i], mem[off..off+ctlen]);
			auto len = getBCSizeof(t);
			assert(len*ulong.sizeof>=ctlen);
			off+=len*ulong.sizeof;
			i++;
		}
	}
	override Variant variantFromMemory(void[] mem, Type type){
		assert(type.getHeadUnqual() is this);
		auto vals=new Variant[types.length];
		assert(!!cast(TypeTuple)type);
		auto tpl=cast(TypeTuple)cast(void*)type;
		auto ttypes=tpl.types;
		size_t i=0,off=0;
		foreach(t;types){
			auto ctlen = getCTSizeof(t);
			vals[i]=t.variantFromMemory(mem[off..off+ctlen], ttypes[i]);
			auto len = getBCSizeof(t);
			assert(len*ulong.sizeof>=ctlen);
			off+=len*ulong.sizeof;
			i++;
		}
		return Variant(vals, tpl);
	}
}

mixin template CTFEInterpret(T) if(is(T==AggregateTy)){
	final size_t getBCLocOf(VarDecl vd, out size_t len){
		if(!decl.isLayoutKnown()) decl.updateLayout();
		return vd.getBCLoc(len);
	}

	override void variantToMemory(Variant value, void[] mem){
		assert(value.getType().getUnqual() is this);
		assert(decl.getBCSize()!=0);

		void[] res;
		void emplacePointer(){
			assert(res.length == BCPointer.sizeof);
			*cast(BCPointer*)res.ptr=BCPointer(mem,mem.ptr);
		}

		auto vars = value.get!(Variant[VarDecl])();
		if(auto rd=decl.isReferenceAggregateDecl()){
			res=mem;
			if(vars.byid in vmtr.aggr_aliasing){
				mem = vmtr.aggr_aliasing[vars.byid];
				emplacePointer();
				return;
			}else mem = new void[decl.getBCSize()*ulong.sizeof];
			vmtr.aggr_aliasing[vars.byid]=mem;
			auto tag=q(cast(Type)this,mem.ptr);
			vmtr.aggr_aliasing_rev[tag]=Variant(vars,decl.getType());
			static assert(ReferenceAggregateDecl.sizeof<=ulong.sizeof);
			(cast(ulong[])mem)[ReferenceAggregateDecl.bcTypeidOffset]=cast(ulong)cast(void*)rd;
		}else assert(mem.length==getCTSizeof(this));

		assert(!(mem.length%ulong.sizeof));
		assert(!mem.length||mem.length==decl.getBCSize()*ulong.sizeof);

		foreach(vd;&decl.traverseFields){
			size_t len, off = vd.getBCLoc(len);
			auto ctlen=getCTSizeof(vd.type);
			assert(len != -1);
			if(vd !in vars && vd.init){
				vars[vd]=vd.init.interpretV(); // TODO: ok?
			}
			if(vd in vars){
				auto var = vars[vd];
				assert(getCTSizeof(vd.type)==getCTSizeof(var.getType()));
				var.getType().variantToMemory(var, mem[off*ulong.sizeof..off*ulong.sizeof+ctlen]);
			}
		}
		if(decl.isReferenceAggregateDecl()){
			emplacePointer();
			// discoverPointers(res, decl.getType(), false);
		}
	}

	override Variant variantFromMemory(void[] mem, Type type){
		assert(type.getHeadUnqual() is this);
		auto decl=this.decl;
		Variant[VarDecl] res;
		void initializeRes(){
			assert(type !is null);
			// (stupid built-in AAs)
			res[cast(VarDecl)cast(void*)type]=Variant(null);
			res.remove(cast(VarDecl)cast(void*)type);
		}
		if(decl.isReferenceAggregateDecl()){
			assert(mem.length==getCTSizeof(this));
			auto ptr=*cast(BCPointer*)mem.ptr;
			assert(ptr.ptr==ptr.container.ptr);
			if(ptr.ptr is null) return Variant((Variant[VarDecl]).init, type);
			mem=ptr.container;
			decl=cast(ReferenceAggregateDecl)cast(void*)(cast(ulong[])mem)[ReferenceAggregateDecl.bcTypeidOffset];
			type = decl.getType().applySTC(type.getHeadSTC());
			auto tag=q(cast(Type)decl.getType(),mem.ptr);
			// TODO: What about pointers with an offset?
			if(tag in vmtr.aggr_aliasing_rev) return vmtr.aggr_aliasing_rev[tag];
		}
		initializeRes();
		if(decl.isReferenceAggregateDecl){
			auto tag=q(cast(Type)decl.getType(),mem.ptr);
			vmtr.aggr_aliasing_rev[tag]=Variant(res,type);
		}

		assert(decl.isLayoutKnown);
		foreach(vd;&decl.traverseFields){
			size_t len, off = vd.getBCLoc(len);
			auto ctlen=getCTSizeof(vd.type);
			assert(len != -1);
			auto tt=vd.type.applySTC(type.getHeadSTC());
			res[vd]=tt.variantFromMemory(mem[off*ulong.sizeof..off*ulong.sizeof+ctlen], tt);
		}
		return Variant(res, type);
	}
}

mixin template CTFEInterpret(T) if(is(T==EnumTy)){
	override void variantToMemory(Variant value, void[] mem){
		auto tt=value.getType();
		auto ty=decl.base.applySTC(tt.getHeadSTC());
		ty.variantToMemory(value.convertTo(ty), mem);
	}
	override Variant variantFromMemory(void[] mem, Type type){
		assert(type.getHeadUnqual() is this);
		auto ty=decl.base.applySTC(type.getHeadSTC());
		auto r=ty.variantFromMemory(mem, ty);
		return r.convertTo(type);
	}
}

mixin template CTFEInterpret(T) if(is(T==DelegateTy)){
	override void variantToMemory(Variant value, void[] mem){
		assert(value.getType().getHeadUnqual() is this);
		assert(mem.length==(bcPointerBCSize+1)*ulong.sizeof);
		auto fun = value.getDelegateFunctionPointer();
		if(!fun){ (cast(byte[])mem)[]=0; return; }
		assert(cast(FunctionDef)fun.meaning);
		auto fd = cast(FunctionDef)cast(void*)fun.meaning;
		auto ctx = buildContext(value.getDelegateContext(), fd, true);
		auto ptr = BCPointer(null,null);
		if(ctx.length){
			assert(ctx.length==bcPointerBCSize*ulong.sizeof);
			ptr = *cast(BCPointer*)ctx.ptr;
		}
		mem[0..BCPointer.sizeof]=(cast(void*)&ptr)[0..BCPointer.sizeof];
		*cast(Symbol*)(mem.ptr+bcPointerBCSize*ulong.sizeof)=fun;
	}

	private static void[] buildContext(Variant[VarDecl] vars, FunctionDef fd, bool first=false){
		if(!first && vars.byid in vmtr.aggr_aliasing) return vmtr.aggr_aliasing[vars.byid];
		size_t size=0;
		foreach(vd,_;vars){
			if(vd is outerContext){
				assert(!(fd.stc&STCstatic),text(fd));
				size = max(size, bcPointerBCSize);
				continue;
			}
			size_t len, off = vd.getBCLoc(len);
			size=max(size,off+len);
		}
		void[] mem = new void[ulong.sizeof*size];
		auto tag=q(Type.init,mem.ptr);
		vmtr.aggr_aliasing[vars.byid]=mem;
		vmtr.aggr_aliasing_rev[tag]=Variant(vars);

		if(!(fd.stc&STCstatic)){
			auto decl=fd.scope_.getDeclaration();
			if(decl){
				assert(outerContext in vars);
				auto ctx=vars[outerContext];

				if(auto efd=decl.isFunctionDef()){
					auto emem = buildContext(ctx.get!(Variant[VarDecl])(), efd);
					auto ptr = BCPointer(emem, emem.ptr);
					assert(mem.length>=BCPointer.sizeof);
					*cast(BCPointer*)mem.ptr=ptr;
				}else if(auto agg=decl.isAggregateDecl()){
					assert({
							auto ty=agg.getType().applySTC(fd.stc&STCtypeconstructor);
							if(!decl.isReferenceAggregateDecl()) ty=ty.getPointer();
							return ty.getConst() is ctx.getType().getConst();
						}());
					auto ty=ctx.getType();
					auto ctsiz=getCTSizeof(ty);
					ty.variantToMemory(ctx, mem[0..ctsiz]);
				}
			}
		}
		if(first) return mem;

		foreach(vd;&fd.traverseHeapContext){
			size_t len, off = vd.getBCLoc(len);
			auto ctlen=getCTSizeof(vd.type);
			assert(len != -1);
			assert(vd in vars);
			auto var = vars[vd];
			assert(getCTSizeof(vd.type)==getCTSizeof(var.getType()));
			var.getType().variantToMemory(var, mem[off*ulong.sizeof..off*ulong.sizeof+ctlen]);
		}

		return mem;
	}

	@property static VarDecl outerContext(){
		static VarDecl outer;
		if(outer is null) outer = new VarDecl(STC.init, null, new Identifier("$__outerContext"), null);
		return outer;
	}

	private static Variant[VarDecl] parseContext(void[] mem, FunctionDef fd, bool first=false){
		auto tag=q(Type.init,mem.ptr);
		// TODO: What about pointers with an offset?
		if(!first&&tag in vmtr.aggr_aliasing_rev)
			return vmtr.aggr_aliasing_rev[tag].get!(Variant[VarDecl])();

		Variant[VarDecl] r;
		// (stupid built-in AAs)
		assert(fd !is null);
		r[cast(VarDecl)cast(void*)fd]=Variant(null);
		r.remove(cast(VarDecl)cast(void*)fd);

		if(!first) vmtr.aggr_aliasing_rev[tag]=Variant(r);

		if(!(fd.stc&STCstatic)){
			if(auto decl=fd.scope_.getDeclaration()){
				assert(mem.length>=BCPointer.sizeof);
				auto ptr=*cast(BCPointer*)mem.ptr;
				assert(ptr.ptr is ptr.container.ptr);
				if(auto efd=decl.isFunctionDef()){
					r[outerContext]=Variant(parseContext(ptr.container, efd));
				}else if(auto agg=decl.isAggregateDecl()){
					auto ty=agg.getType().applySTC(fd.stc&STCtypeconstructor);
					if(!decl.isReferenceAggregateDecl()) ty=ty.getPointer();
					r[outerContext]=ty.variantFromMemory((cast(void*)&ptr)[0..BCPointer.sizeof],ty);
				}else assert(0);
			}
		}
		if(first) return r;
		foreach(vd;&fd.traverseHeapContext){
			size_t len, off = vd.getBCLoc(len);
			auto tt=vd.type;
			auto ctlen=getCTSizeof(tt);
			assert(len != -1);
			r[vd]=tt.variantFromMemory(mem[off*ulong.sizeof..off*ulong.sizeof+ctlen], tt);
		}
		return r;
	}

	override Variant variantFromMemory(void[] mem, Type type){
		assert(type.getHeadUnqual() is this);
		assert(mem.length==(bcPointerBCSize+1)*ulong.sizeof);
		auto ul=cast(ulong[])mem;
		auto fun=cast(Symbol)cast(void*)ul[$-1];
		if(!fun) return Variant(fun, (Variant[VarDecl]).init, type);
		assert(cast(FunctionDef)fun.meaning);
		auto fd=cast(FunctionDef)cast(void*)fun.meaning;
		auto vars = parseContext(mem[0..bcPointerBCSize*ulong.sizeof], fd, true);
		return Variant(fun, vars, type);
	}
}

// TODO: this abstraction could maybe act as an arena allocator
// (usage could even be extended into CTFE, but then some form of additional GC
// during CTFE-runtime will be required.)

struct VariantMemoryTranslation{
	void[][AAbyIdentity!(VarDecl,Variant)] aggr_aliasing; // preserve aliasing
	Variant[Q!(Type,void*)] aggr_aliasing_rev; // preserve aliasing on reverse translation

	void[][Variant*] sl_aliasing; // preserve aliasing
	Variant[][Q!(Type,void*)] sl_aliasing_rev; // preserve aliasing on reverse translation

	void flushCaches(){
		aggr_aliasing=null;
		sl_aliasing=null;
		// may still need reverse translation
		// hashtables with weak keys would be neat to resolve the memory leak this causes
		// TODO: fix memory leak
	}
}
VariantMemoryTranslation vmtr; // TODO: get rid of thread-local state?
