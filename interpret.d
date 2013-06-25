// Written in the D programming language.

import lexer, expression, semantic, scope_, type;
import util;
import std.string;
import std.conv: to;

private template NotYetImplemented(T){
	static if(is(T _==BinaryExp!S,TokenType S) || is(T==ABinaryExp) || is(T==AssignExp))
		enum NotYetImplemented = false;
	else static if(is(T _==UnaryExp!S,TokenType S))
		enum NotYetImplemented = false;
		else enum NotYetImplemented = !is(T==Expression) && !is(T==ExpTuple) && !is(T:Type) && !is(T:Symbol) && !is(T==FieldExp) && !is(T:LiteralExp) && !is(T==CastExp) && !is(T==ArrayLiteralExp) && !is(T==IndexExp) && !is(T==SliceExp) && !is(T==TernaryExp) && !is(T==CallExp) && !is(T==UFCSCallExp) && !is(T==MixinExp) && !is(T==IsExp) && !is(T==AssertExp) && !is(T==LengthExp) && !is(T==DollarExp) && !is(T==ThisExp) && !is(T==SuperExp) && !is(T==TemporaryExp) && !is(T==StructConsExp);
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
mixin template Interpret(T) if(is(T:Expression) && NotYetImplemented!T || is(T==ThisExp)||is(T==SuperExp)){
	override void interpret(Scope sc){
		assert(sc, "expression "~toString()~" was assumed to be interpretable");
		sc.error(format("expression '%s' is not interpretable at compile time yet",toString()),loc);
		mixin(ErrEplg);
	}
}

mixin template Interpret(T) if(is(T==Expression)){

	final void prepareInterpret(){
		weakenAccessCheck(AccessCheck.memberFuns);
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
		auto impld = e.type.implicitlyConvertsTo(type);
		assert(!impld.dependee); // analysis has already determined this
		if(impld.value) return e.checkInterpret(sc);
		if(type.getHeadUnqual().isPointerTy()){
			sc.error(format("cannot interpret cast from '%s' to '%s' at compile time",e.type,type),loc);
			return false;
		}
		return e.checkInterpret(sc);
	}
	override Variant interpretV(){
		auto le=e.isLiteralExp(); // polysemous string literals might be cast
		auto el = type.getElementType();
		if(el&&le&&le.isPolyString()){
			auto vle=e.interpretV();
			auto typeu = type.getHeadUnqual();
			if(typeu.isSomeString()) return vle.convertTo(type);
			// TODO: allocation ok?
			Variant[] r = new Variant[vle.length];
			foreach(i,ref x;r) x = vle[i].convertTo(el);
			return Variant(r,r,type);
		}else return e.interpretV().convertTo(type);
	}

	override void _interpretFunctionCalls(Scope sc){mixin(IntFCChld!q{e});}
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
		if(this_&&this_.isConstant()) return true;
		return super.checkInterpret(sc);
	}
	
	override Variant interpretV(){
		if(e2.isConstant()) return e2.interpretV();
		auto value=e1.interpretV();
		auto aggr=value.get!(Variant[VarDecl])();
		// TODO: handle the case when the variable decl does not occur
		assert(cast(VarDecl)e2.meaning);
		return aggr[cast(VarDecl)cast(void*)e2.meaning];
	}
}
mixin template Interpret(T) if(is(T==BinaryExp!(Tok!"."))){ } // (workaround for DMD bug)

mixin template Interpret(T) if(is(T==LengthExp)){
	override bool checkInterpret(Scope sc){
		return e.checkInterpret(sc);
	}
	override Variant interpretV(){
		return Variant(e.interpretV().length, Type.get!Size_t());
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
		foreach(i,ref x;lit) x = arr[i].toExpr();
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
		bool ok = true;
		foreach(x; lit) if(!x.checkInterpret(sc)) ok=false;
		return ok;
	}

	override Variant interpretV(){
		// TODO: this GC allocation is probably justified
		Variant[] res = new Variant[lit.length];
		foreach(i, ref x; res) x = lit[i].interpretV();
		return Variant(res,res,type);
	}

	override void _interpretFunctionCalls(Scope sc){
		foreach(ref x; lit){
			x._interpretFunctionCalls(sc);
			mixin(PropRetry!q{x});
		}
		mixin(PropErr!q{lit});
		mixin(IntFCEplg);
	}
}

mixin template Interpret(T) if(is(T==IndexExp)){
	override bool checkInterpret(Scope sc){
		if(!a.length) return e.checkInterpret(sc);
		assert(a.length==1);
		return e.checkInterpret(sc)&a[0].checkInterpret(sc);
	}
	override Variant interpretV(){
		if(a.length==0) return e.interpretV();
		assert(a.length==1);
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
		if(a.length){
			if(ascope.dollar){
				mixin(SemProp!q{e});
				auto len = e.interpretV().length;
				DollarExp.resolveValue(a, len);
			}
			assert(a.length==1);
			a[0]._interpretFunctionCalls(sc);
			mixin(SemProp!q{a[0]});
		}
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
		return a[0].checkInterpret(sc) & (a.length<2 || a[1].checkInterpret(sc));
	}
	override Variant interpretV(){return Variant(toString(),Type.get!string());} // good enough

	override void _interpretFunctionCalls(Scope sc){
		a[0]._interpretFunctionCalls(sc);
		mixin(PropRetry!q{a[0]});
		if(a.length>1){
			a[1]._interpretFunctionCalls(sc);
			mixin(PropRetry!q{a[1]});
		}
		mixin(PropErr!q{a});
		auto cond = a[0].interpretV();
		if(!cond){
			if(a.length<2){
				sc.error(format("assertion failure: %s is false",a[0].loc.rep), loc);
			}else{
				auto expr = a[1];
				sc.error(expr.interpretV().get!string(), loc);
			}
			mixin(ErrEplg);
		}
		mixin(SemEplg);
	}
}

mixin template Interpret(T) if(is(T _==UnaryExp!S,TokenType S)){
	static if(is(T _==UnaryExp!S,TokenType S)):
	static if(S!=Tok!"&"&&S!=Tok!"*"): // TODO: implement where possible
	static if(S!=Tok!"++"&&S!=Tok!"--"):
	override bool checkInterpret(Scope sc){return e.checkInterpret(sc);}
	override Variant interpretV(){
		return e.interpretV().opUnary!(TokChars!S)();
	}

	override void _interpretFunctionCalls(Scope sc){mixin(IntFCChld!q{e});}
}

mixin template Interpret(T) if(is(T==ExpTuple)){
	override void interpret(Scope sc){ }
	override Variant interpretV(){ assert(0, "TODO"); }
}

mixin template Interpret(T) if(is(T==ABinaryExp)||is(T==AssignExp)){}
mixin template Interpret(T) if(is(T _==BinaryExp!S, TokenType S) && !is(T==BinaryExp!(Tok!"."))){
	static if(is(T _==BinaryExp!S, TokenType S)):
	static if(!isAssignOp(S)):
	override bool checkInterpret(Scope sc){
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
			if(e1.type.equals(e2.type)) return e1.interpretV().opBinary!"~"(e2.interpretV());
			// TODO: this might be optimized. this gc allocates
			// TODO: get rid of bulky string special casing code
			if(auto ety = e1.type.getElementType()){
				if(ety.equals(e2.type)){
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
			assert(e2.type.getElementType() &&
			       e2.type.getElementType().equals(e1.type),
			       text(e2.type," ",e1.type));
			auto ety = e1.type;
			auto lhs = e1.interpretV();
			if(ety is Type.get!(immutable(char))())
				lhs = Variant(""c~lhs.get!char(),ety);
			else if(ety is Type.get!(immutable(wchar))())
				lhs = Variant(""w~lhs.get!wchar(),ety);
			else if(ety is Type.get!(immutable(dchar))())
				lhs = Variant(""d~lhs.get!dchar(),ety);
			else{ auto l=[lhs];lhs = Variant(l,l,ety.getDynArr()); }
			return lhs.opBinary!"~"(e2.interpretV());
		}else return super.interpretV();
	}

	override void _interpretFunctionCalls(Scope sc){
		static if(S==Tok!"/"){
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

mixin template Interpret(T) if(is(T==StructConsExp)){
	override bool checkInterpret(Scope sc){
		return true; // be optimistic
	}
	override void _interpretFunctionCalls(Scope sc){
		callWrapper(sc,ctfeCallWrapper,consCall?consCall.e:null);		
	}
private:
	FunctionDef ctfeCallWrapper;
}

mixin template Interpret(T) if(is(T==CallExp)){
	//private Variant val;
	override bool checkInterpret(Scope sc){
		// TODO: ok?
		if(fun.type.getHeadUnqual().getFunctionTy().ret is Type.get!void()) return super.checkInterpret(sc);
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
class UnwindException: Exception{this(){super("");}}
class SilentUnwindException: Exception{this(){super("");}}

void dependentCTFE(T)(Dependent!T node){
	if(node.dependee){
		if(node.dependee.node.needRetry){
			throw new CTFERetryException(node.dependee.node);
		}else{
			assert(node.dependee.node.sstate == SemState.error);
			throw new UnwindException;
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
	newarray,                   // creates an array, stack top is ptr, ltop is length
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

	struct Label{
		private{
			ByteCodeBuilder* outer;
			size_t loc = -1; // no allocation if label used exactly once
			size_t[] locs;
			ulong pos = -1;
		}
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
	abstract void emitLoadKR(ref ByteCodeBuilder); // load value at address, keep address

	abstract void emitPointer(ref ByteCodeBuilder);

	LValueStrategy emitFieldLV(ref ByteCodeBuilder bld, size_t off, size_t len, size_t ctlen, ErrorInfo info){
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
	override void emitLoadKR(ref ByteCodeBuilder bld){
		bld.emitDup(iscc?2:1); // duplicate address
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

	override LValueStrategy emitFieldLV(ref ByteCodeBuilder bld, size_t off, size_t len, size_t ctlen, ErrorInfo){
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
	bool isptr;
	ErrorInfo info;
	static opCall(Type elty, ErrorInfo info){
		return new LVstorea(elty, info, false);
	}
	private this(Type elty, ErrorInfo inf, bool ptr){
		isarr = cast(bool)elty.getHeadUnqual().isDynArrTy();
		if(!isarr) els = getCTSizeof(elty);
		bcsiz = getBCSizeof(elty);
		info = inf;
		isptr=ptr;
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

	override void emitLoad(ref ByteCodeBuilder bld){
		ptrPrlg(bld,false);
		bld.emitUnsafe(isarr?Instruction.loadaa:Instruction.loada, info);
		if(!isarr) bld.emitConstant(els);
	}
	override void emitLoadKR(ref ByteCodeBuilder bld){
		ptrPrlg(bld,false);
		bld.emitUnsafe(isarr?Instruction.loadaak:Instruction.loadak, info);
		if(!isarr) bld.emitConstant(els);
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
				throw new UnwindException;
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
Ldivbyzero:
	auto info0 = obtainErrorInfo();
	handler.error("divide by zero", info0.loc);
	goto Lfail;
Loutofbounds:
	auto info1 = obtainErrorInfo();
	auto s_t = Type.get!Size_t();
	if(s_t.getSizeof()==uint.sizeof) tmp[0] = cast(uint)tmp[0];
	else assert(s_t.getSizeof()==ulong.sizeof);
	handler.error(format("array index %s%s is out of bounds [0%s..%d%s)",tmp[0],Size_t.suffix,Size_t.suffix,tmp[1],Size_t.suffix),info1.loc);
	goto Lfail;
Lshiftoutofrange:
	auto info2 = obtainErrorInfo();
	bool isSigned;
	if(auto e = cast(BinaryExp!(Tok!"<<"))info2) isSigned=(cast(BasicType)e.e2.type).isSigned();
	else if(auto e = cast(BinaryExp!(Tok!">>"))info2) isSigned=(cast(BasicType)e.e2.type).isSigned();
	else if(auto e = cast(BinaryExp!(Tok!">>>"))info2) isSigned=(cast(BasicType)e.e2.type).isSigned();
	if(isSigned) handler.error(format("shift amount of %d is outside the range 0..%d", cast(long)tmp[0], tmp[1]),info2.loc);
	else handler.error(format("shift amount of %d is outside the range 0..%d", tmp[0], tmp[1]),info2.loc);
	goto Lfail;
Linvalidpointer:
	auto info3 = obtainErrorInfo();
	bool offby1=cast(bool)tmp[1];
	if(!offby1){
		auto exp=cast(Expression)info3;
		if(!exp.type.isFunctionTy())// TODO: this should not even be reached
		if(exp && tmp[2]+getCTSizeof(exp.type)==tmp[3]) offby1 = true;
	}
	handler.error(format("%s pointer dereference%s",tmp[0]?"null":"invalid",offby1?" (off by one)":""), info3.loc);
	goto Lfail;
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
	goto Lfail;
Lnullfunction:
	auto info5 = obtainErrorInfo();
	assert(!!cast(CallExp)info5);
	auto ce = cast(CallExp)cast(void*)info5;
	handler.error(format("null %s dereference", ce.e.type.isDelegateTy?"delegate":"function pointer"),ce.loc);
	goto Lfail;
Lcastfailure:
	auto castinfo = obtainErrorInfo();
	assert(!!cast(CastExp)castinfo);
	auto cae = cast(CastExp)cast(void*)castinfo;
	auto t1 = cast(Type)cast(void*)tmp[0];
	handler.error(format("cannot interpret cast from '%s' aliasing a '%s' to '%s' at compile time", cae.e.type,t1,cae.type), cae.loc); // TODO: 'an'
	goto Lfail;
Linvfunction:
	auto info6 = obtainErrorInfo();
	handler.error("interpretation of invalid function failed", info6.loc);
	goto Lfail;
Lhlt:
	auto hltinfo = cast(HltErrorInfo)cast(void*)obtainErrorInfo();
	handler.error(hltinfo.err, hltinfo.loc);
	goto Lfail;
Lhltstr:
	auto hltsinfo = obtainErrorInfo();
	string err = cast(string)stack.pop!BCSlice().slice;
	handler.error(err, hltsinfo.loc);
Lfail:
	throw new UnwindException();
}


mixin template CTFEInterpret(T) if(!is(T==Node)&&!is(T==FunctionDef)&&!is(T==TemplateDecl)&&!is(T==TemplateInstanceDecl) && !is(T==BlockDecl) && !is(T==PragmaDecl) && !is(T==EmptyStm) && !is(T==CompoundStm) && !is(T==LabeledStm) && !is(T==ExpressionStm) && !is(T==IfStm) && !is(T==ForStm) && !is(T==WhileStm) && !is(T==DoStm) && !is(T==LiteralExp) && !is(T==ArrayLiteralExp) && !is(T==ReturnStm) && !is(T==CastExp) && !is(T==Symbol) && !is(T==FieldExp) && !is(T==ConditionDeclExp) && !is(T==VarDecl) && !is(T==Expression) && !is(T==ExpTuple) && !is(T _==BinaryExp!S,TokenType S) && !is(T==ABinaryExp) && !is(T==AssignExp) && !is(T==TernaryExp)&&!is(T _==UnaryExp!S,TokenType S) && !is(T _==PostfixExp!S,TokenType S) &&!is(T==Declarators) && !is(T==BreakStm) && !is(T==ContinueStm) && !is(T==GotoStm) && !is(T==BreakableStm) && !is(T==LoopingStm) && !is(T==SliceExp) && !is(T==AssertExp) && !is(T==CallExp) && !is(T==Declaration) && !is(T==PtrExp)&&!is(T==LengthExp)&&!is(T==DollarExp)&&!is(T==AggregateDecl)&&!is(T==ReferenceAggregateDecl)&&!is(T==AggregateTy)&&!is(T==TemporaryExp)&&!is(T==StructConsExp)&&!is(T==NewExp)&&!is(T==CurrentExp)&&!is(T==MultiReturnValueExp)){}


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
		auto dg=New!FunctionDef(STCstatic,fty,New!Identifier("__ctfeCallWrapper"),cast(BlockStm)null,cast(BlockStm)null,cast(Identifier)null,bdy, false);
		dg.sstate = SemState.begin;
		dg.scope_ = sc;
		dg.semantic(sc);
		mixin(Rewrite!q{dg});
		while(dg.sstate!=SemState.completed){
			dg.semantic(sc);
			mixin(Rewrite!q{dg});
		}
		dg.loc = loc;
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
		}catch(UnwindException){
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
			if(type.getHeadUnqual().isDynArrTy()) bld.emitUnsafe(I.loadaa, this);
			else{
				bld.emitUnsafe(I.loada, this);
				bld.emitConstant(getCTSizeof(type));
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

// workaround for DMD bug, other part is in expression.IndexExp
mixin template CTFEInterpretIE(T) if(is(T _==IndexExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		alias Instruction I;

		auto siz = getCTSizeof(type);
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
		if(!a.length) return;

		assert(a.length == 1);
		mixin(byteCompileDollar);

		a[0].byteCompile(bld);
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
		if(type.getHeadUnqual().isDynArrTy()){
			bld.emitUnsafe(I.loadaa, this);
			return;
		}
		bld.emitUnsafe(I.loada, this);
		bld.emitConstant(siz);
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
				bld.emit(Instruction.truncs);
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
		bld.emit(Instruction.jnz);
		auto l = bld.emitLabel();
		if(a.length==1){
			bld.error(format("assertion failure: %s is false", a[0].loc.rep),loc);
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

	static if(isAssignOp(S) && S!=Tok!"=" || S==Tok!",")
	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		return byteCompileHelper(bld, true);
	}

	private LValueStrategy byteCompileHelper(ref ByteCodeBuilder bld, bool isLvalue) in{assert(!isLvalue || isAssignOp(S) && S!=Tok!"=" || S==Tok!",");}body{
		import std.typetuple;
		alias Instruction I;
		static if(S==Tok!"="){
			auto strat = e1.byteCompileLV(bld);
			e2.byteCompile(bld);
			strat.emitStoreKV(bld);
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
				static if(S!=Tok!"<<"&&S!=Tok!">>"&&S!=Tok!">>>") assert(e1.type is e2.type);
			}

			if(S==Tok!"is"||S==Tok!"!is"){
				if(auto at=e1.type.isAggregateTy()){
					assert(at.decl.isClassDecl(),"TODO: is for interfaces and value types");
					assert(!!e2.type.isAggregateTy());
					static if(S==Tok!"is") bld.emit(I.cmpep);
					else bld.emit(I.cmpnep);
				}
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
			}else static if(isRelationalOp(S) && S!=Tok!"in"){

				assert(!e1.type.getElementType()," CTFE array relational operators not implemented yet");

				if(auto bt0=e1.type.getHeadUnqual.isBasicType())
					if(auto bt=bt0.isFloating()){
					string either(string op1, string op2, bool neg=false){
						return mixin(X!q{
						});
					}

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
							break;
						}
					}
				}
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
			auto exp1=e1, exp2=e2;
			// kludge: remove supposedly "unsafe" casts
			// this only allows valid code, but maybe it will have to be changed
			// eg. cast(char[])"hello"~cast(char[])"hello" is allowed by this
			// but not by conservative treatment
			void removeReinterpretCast(ref Expression exp, Expression other){
				if(exp.type is other.type.getElementType()) return;
				if(auto ce=exp.isCastExp()){
					if(ce.type.getUnqual() is ce.e.type.getUnqual())
						exp = ce.e;
				}
			}
			removeReinterpretCast(exp1, exp2);
			removeReinterpretCast(exp2, exp1);

			exp1.byteCompile(bld);
			if(e1.type is e2.type.getElementType())
				emitMakeArray(bld,e2.type,1);
			exp2.byteCompile(bld);
			if(e2.type is e1.type.getElementType())
				emitMakeArray(bld,e1.type,1);
			bld.emit(I.concata);
		}else static if(S==Tok!"~="){
			auto strat = e1.byteCompileLV(bld);
			strat.emitLoadKR(bld);
			e2.byteCompile(bld);
			if(e2.type is e1.type.getElementType())
				emitMakeArray(bld,e1.type,1);
			bld.emit(I.appenda);
			if(!isLvalue){ strat.emitStoreKV(bld); return null; }
			else{ strat.emitStoreKR(bld); return strat; }
		}else super.byteCompile(bld);

		assert(!isLvalue);
		return null;
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
		foreach(x; s){
			if(x.sstate == SemState.completed){
				x.byteCompile(bld);
			}else{
				bld.emit(Instruction.analyzeandfail);
				static assert(x.sizeof <= (void*).sizeof && (void*).sizeof<=ulong.sizeof);
				bld.emitConstant(cast(ulong)cast(void*)x);
				static struct FindScope{
					Scope result;
					void perform(Symbol self){
						if(self.meaning&&self.meaning.isFunctionDecl()&&self.meaning.sstate==SemState.started){
							if(!result) result = self.scope_; // TODO: shortcut
						}
					}
				}
				auto sc = runAnalysis!FindScope(x).result;
				assert(!!sc, x.toString());
				static assert(sc.sizeof <= (void*).sizeof && (void*).sizeof<=ulong.sizeof);
				bld.emitConstant(cast(ulong)cast(void*)sc);
				break;
			}
		}
	}
}
mixin template CTFEInterpret(T) if(is(T==LabeledStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		if(!bclabel.initialized(bld)) bclabel = bld.getLabel();
		bclabel.here();
		s.byteCompile(bld);
	}
	ref ByteCodeBuilder.Label getBCLabel(ref ByteCodeBuilder bld){
		if(!bclabel.initialized(bld)) bclabel = bld.getLabel();
		return bclabel;
	}
private:
	ByteCodeBuilder.Label bclabel;
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

mixin template CTFEInterpret(T) if(is(T==ReturnStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		if(e) e.byteCompileRet(bld, isRefReturn);
		else bld.emit(Instruction.ret);
	}
}

mixin template CTFEInterpret(T) if(is(T==ContinueStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		bld.emit(Instruction.jmp);
		theLoop.emitBCContinueLabel(bld);
	}
}
mixin template CTFEInterpret(T) if(is(T==BreakStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		bld.emit(Instruction.jmp);
		brokenOne.emitBCEnd(bld);
	}
}
mixin template CTFEInterpret(T) if(is(T==GotoStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		bld.emit(Instruction.jmp);
		bld.emitLabel(target.getBCLabel(bld));
	}
}

mixin template CTFEInterpret(T) if(is(T==LiteralExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		auto tu = type.getHeadUnqual();
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
		}else if(tu.getElementType()){
			auto r=variantToMemory.VariantToBCSlice(value);
			size_t size = getBCSizeof(tu.getElementType().getDynArr());
			if(tu.getUnqual() is Type.get!(void[])()){
				bld.emit(Instruction.push);
				bld.emitConstant(cast(ulong)cast(void*)value.getType());
			}else assert(!(size&1),text(tu));
			for(size_t i=0;i<(size&~1);i+=2){
				bld.emit(Instruction.push2);
				bld.emitConstant(*(cast(ulong*)&r+i));
				bld.emitConstant(*(cast(ulong*)&r+i+1));
			}
			if(tu.isArrayTy()){ // static array literal (TODO: this is a horrible kludge, duplicated in ArrayLiteralExp)
				bld.emit(Instruction.push);
				bld.emitConstant(0);
				bld.emitUnsafe(Instruction.loada,this);
				bld.emitConstant(getCTSizeof(tu));
			}
			return;
		}else if(auto pt=tu.isPointerTy()){
			auto r=variantToMemory.VariantToBCPointer(value);
			size_t size = getBCSizeof(tu);
			if(tu.getUnqual() is Type.get!(void*)()){
				bld.emit(Instruction.push);
				bld.emitConstant(cast(ulong)cast(void*)value.getType());
			}else assert(!(size&1),text(tu));
			for(size_t i=0;i<(size&~1);i+=2){
				bld.emit(Instruction.push2);
				bld.emitConstant(*(cast(ulong*)&r+i));
				bld.emitConstant(*(cast(ulong*)&r+i+1));
			}
			return;
		}else if(auto at=tu.isAggregateTy()){
			auto vars = value.get!(Variant[VarDecl])();
			if(vars is null) goto Lnull;
			// TODO: this is inefficient
			ulong[] memory = variantToMemory.VariantToBCMemory(value);
			foreach(v;memory){
				bld.emit(Instruction.push);
				bld.emitConstant(v);
			}
		}else{
		Lnull:
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
		if(t1.equals(t2)) return;
		if(t2.getHeadUnqual() is Type.get!void()){
			bld.ignoreResult(getBCSizeof(t1));
			return;
		}
		if(auto from=t1.isIntegral()){
			if(auto to=t2.isIntegral()){
				if(from.bitSize()<=to.bitSize()) return;
				if(to is Type.get!bool()){
					bld.emit(I.int2bool);
					return;
				}
				bld.emit(to.isSigned() ? I.truncs : I.trunc);
				bld.emitConstant(to.bitSize());
				return;
			}else foreach(T; TypeTuple!(float, double, real)){ // TODO: imaginary/complex
				if(t2 is Type.get!T()){
					bld.emit(from.isSigned() ? I.int2real : I.uint2real);
					static if(!is(T==real)) bld.emit(mixin(`I.real2`~T.stringof));
					return;
				}
			}
		}else foreach(T; TypeTuple!(float, double, real)){
			if(t1 is Type.get!T()){
				if(auto to=t2.isIntegral()){
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
					if(type is Type.get!S()){
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

		if(e.isDirectlyAllocated()) t1 = t1.getUnqual(), t2 = t2.getUnqual(); // TODO: this is not good.

		void castToVoidPtrOrArray(Type tt){
			auto siz=getBCSizeof(tt);
			bld.emitTmppush(siz);
			bld.emit(I.push);
			bld.emitConstant(cast(ulong)cast(void*)tt);
			bld.emitTmppop(siz);			
		}

		auto varr=Type.get!(void[])();
		auto vptr=Type.get!(void*)();
		auto t1u=t1.getUnqual(), t2u=t2.getUnqual();		
		if(t2u is varr||t2u is vptr){
			castToVoidPtrOrArray(t1);
			return;
		}
		if(t1u is varr||t1u is vptr){
			bld.emitUnsafe(t1 is varr ? I.castfromvarr : I.castfromvptr, this);
			static assert(Type.sizeof<=ulong.sizeof);
			bld.emitConstant(cast(ulong)cast(void*)t2);
			return;
		}

		// TODO: sanity check for reinterpreted references
		// TODO: sanity check for array cast alignment
		auto rcd = t1.refConvertsTo(t2,0);
		assert(!rcd.dependee); // must have been determined to type check the expression
		if(rcd.value) return;

		if(auto dyn=t1.isDynArrTy()){
			if(auto ptr=t2.isPointerTy()){
				if(t2 is Type.get!(void*)()){
					bld.emit(I.ptra);
					castToVoidPtrOrArray(t1.getElementType().getPointer());
					return;
				}
				auto rcd2 = dyn.refConvertsTo(ptr.ty.getDynArr(), 0);
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
			if(!(meaning.stc&STCstatic) && !fd.isConstructor()){
				assert(scope_.getFrameNesting() >=
				       meaning.scope_.getFrameNesting());

				auto diff = scope_.getFrameNesting() - meaning.scope_.getFrameNesting();

				bld.emitUnsafe(Instruction.pushcontext, this);
				bld.emitConstant(diff);
			}
			if(!(fd.stc&STCnonvirtual))
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
		if(!this_){
			this_ = New!ThisExp(); // TODO: would prefer not having this
			this_.loc = loc;
			do this_.semantic(e2.scope_);
			while(this_.sstate != SemState.completed);
			nonvirtual = true;
		}
		assert(!this_ || cast(AggregateTy)this_.type.getHeadUnqual());
		auto aggrt = cast(AggregateTy)cast(void*)this_.type.getHeadUnqual();

		if(auto vd=e2.meaning.isVarDecl()){
			size_t len, off = aggrt.getBCLocOf(vd, len);
			if(aggrt.decl.isValueAggregateDecl()){
				auto lv=this_.byteCompileLV(bld);
				lv.emitFieldLV(bld, off, len, getCTSizeof(vd.type), this).emitLoad(bld);
			}else{
				this_.byteCompile(bld);
				LVfield(off, len, getCTSizeof(vd.type), this).emitLoad(bld);
			}
			return;
		}
		auto fun = e2.meaning.isFunctionDecl();
		if(this_.isSuperExp()) nonvirtual = true;
		assert(!!fun);
		if(auto raggr=aggrt.decl.isReferenceAggregateDecl()){
			// TODO: interfaces!
			this_.byteCompile(bld);
			if(fun.stc&STCnonvirtual) nonvirtual = true;
			if(!nonvirtual){
				byteCompileVirtualCall(bld, raggr, fun, this);
				return;
			}
		}else{
			auto lv=this_.byteCompileLV(bld);
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
		size_t len, off = aggrt.getBCLocOf(vd, len);
		if(aggrt.decl.isValueAggregateDecl()){
			auto lv=this_.byteCompileLV(bld);
			return lv.emitFieldLV(bld, off, len, getCTSizeof(vd.type), this);
		}else{
			this_.byteCompile(bld);
			return LVfield(off, len, getCTSizeof(vd.type), this);
		}
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
		variantToMemory.flushCaches();
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
			if(auto vd=d.isVarDecl()){
				if(vd.sstate != SemState.completed) continue; // TODO: ok?
				if(vd.stc&(STCstatic|STCenum)) continue;
				if(auto r=dg(vd)) return r;
			}
		}
		return 0;
	}

	int traverseFields(scope int delegate(VarDecl) dg){
		return traverseDeclaredFields(dg);
	}

	void updateLayout()in{assert(!isLayoutKnown());}body{
		size_t off=initialOffset();
		// TODO: unions, anonymous structs/unions etc.
		// TODO: the traversal of vardecls is repeated below, factor out into range
		foreach(vd;&traverseDeclaredFields){
			if(auto aggrty=vd.type.isAggregateTy()){
				if(auto decl=aggrty.decl.isValueAggregateDecl()){
					decl.subscribeForLayoutChanges(this);
				}
			}
			assert(!!vd.type, vd.to!string);
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
				Dependent!FunctionDecl traverse(ReferenceAggregateDecl raggr){
					auto own = raggr.asc.lookupHere(ident, null);
					own.dependentCTFE();
					if(auto ovs = own.value.isOverloadSet()){
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
							return traverse(cd);
					}
					return null.independent!FunctionDecl;
				}
				auto x = traverse(this);
				x.dependentCTFE();
				if(!x.value){ throw new UnwindException; }
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

mixin template CTFEInterpret(T) if(is(T==AggregateTy)){
	size_t getBCLocOf(VarDecl vd, out size_t len){
		if(!decl.isLayoutKnown()) decl.updateLayout();
		return vd.getBCLoc(len);
	}
}

mixin template CTFEInterpret(T) if(is(T==TemporaryExp)){
	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		assert(tmpVarDecl);
		tmpVarDecl.inHeapContext = true;
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
			bld.error("type "~type.toString()~" not yet supported in CTFE", loc);
			return;
		}
		if(auto aggrty=tu.isAggregateTy()){
			bld.emit(Instruction.push); bld.emitConstant(1);
			bld.emit(Instruction.newarray);
			auto els=aggrty.decl.getBCSize();
			bld.emitConstant(els*ulong.sizeof);
			bld.emit(Instruction.ptra);
			bld.emitDup(bcPointerBCSize); // duplicate the reference
			aggrty.decl.byteCompileInit(bld, scope_); // TODO: context is null
			bld.emitUnsafe(Instruction.storef, this); // perfectly safe in this case
			bld.emitConstant(0);
			bld.emitConstant(els);

			if(consCall){
				bld.emitDup(bcPointerBCSize); // duplicate the reference
				consCall.byteCompile(bld);
			}
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
	private void pushContext(ref ByteCodeBuilder bld){
		auto diff = scope_.getFrameNesting()-
			(scope_.getAggregate().scope_.getFrameNesting()+1);
		bld.emitUnsafe(Instruction.pushcontext, this);
		bld.emitConstant(diff);
	}
	override void byteCompile(ref ByteCodeBuilder bld){
		assert(cast(AggregateTy)type.getHeadUnqual()&&scope_.getAggregate());
		if((cast(AggregateTy)cast(void*)type.getHeadUnqual()).decl.isReferenceAggregateDecl()){
			return pushContext(bld);
		}
		auto diff = scope_.getFrameNesting()-
			(scope_.getAggregate().scope_.getFrameNesting()+1);

		bld.emit(Instruction.push); bld.emitConstant(0);
		if(diff){bld.emit(Instruction.push); bld.emitConstant(diff);}
		auto lv=diff?LVpopcc(type, this):LVpopc(type, this);
		lv.emitLoad(bld);
	}
	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		assert((cast(AggregateTy)type.getHeadUnqual())&&cast(ValueAggregateDecl)(cast(AggregateTy)type.getHeadUnqual()).decl);
		pushContext(bld);
		return LVpointer(type, this);
	}
}

// get compile time size of a type in bytes
size_t getCTSizeof(Type type)out(res){assert(!!res);}body{
	type = type.getHeadUnqual();
	if(type.getUnqual().among(Type.get!(void*)(), Type.get!(void[])()))
		return getBCSizeof(type)*ulong.sizeof;
	if(type.isDynArrTy()) return BCSlice.sizeof;
	if(type.isPointerTy()){
		if(type.getFunctionTy()) return Symbol.sizeof;
		else return BCPointer.sizeof;
	}
	static assert(FunctionDef.sizeof<=ulong.sizeof && (void*).sizeof<=ulong.sizeof);
	if(type.isDelegateTy()) return getBCSizeof(type)*ulong.sizeof;
	if(type is Type.get!real()) return real.sizeof;
	if(type.isAggregateTy()) return getBCSizeof(type)*ulong.sizeof;
	return cast(size_t)type.getSizeof();
}

// get size in ulongs on the bc stack
enum bcPointerBCSize = (BCPointer.sizeof+ulong.sizeof-1)/ulong.sizeof;
enum bcFunPointerBCSiz = 1;
size_t getBCSizeof(Type type)in{ assert(!!type); }body{
	type = type.getHeadUnqual();
	if(auto bt = type.isBasicType()){
		if(bt.op == Tok!"void") return 0;
		return (bt.bitSize()+63)/64;
	}
	if(type.isDynArrTy() || type is Type.get!EmptyArray())
		return (BCSlice.sizeof+ulong.sizeof-1)/ulong.sizeof + (type.getUnqual() is Type.get!(void[])());
	if(type.isArrayTy()) return (getCTSizeof(type)+ulong.sizeof-1)/ulong.sizeof;
	if(auto ptr=type.isPointerTy()){
		if(ptr.ty.isFunctionTy()) return bcFunPointerBCSiz;
	ptr: return bcPointerBCSize+(type is Type.get!(void*)());
	}else if(type is Type.get!(typeof(null))()) goto ptr;
	static assert(FunctionDef.sizeof<=ulong.sizeof && (void*).sizeof<=ulong.sizeof);
	if(type.isDelegateTy()) return bcPointerBCSize+bcFunPointerBCSiz;
	if(auto aggrty = type.isAggregateTy()){
		if(aggrty.decl.isValueAggregateDecl()){
			return aggrty.decl.getBCSize();
		}else{
			assert(!!aggrty.decl.isReferenceAggregateDecl());
			goto ptr;
		}
	}
	assert(0, "type "~type.toString~" not yet supported in CTFE");
}

mixin template CTFEInterpret(T) if(is(T==VarDecl)){
	override void byteCompile(ref ByteCodeBuilder bld){
		if(auto tp=type.isTypeTuple()){
			assert(tupleContext && tupleContext.vds.length == tp.length);
			foreach(x;tupleContext.vds){
				size_t len;
				if(x.getBCLoc(len)!=-1) continue; // MultiReturnValueExp!
				x.byteCompile(bld);
			}
			return;
		}
		size_t off, len = getBCSizeof(type);
		// dw(len," ",type);
		if(len==-1) return emitUnsupportedError(bld);
		if(auto ini=init?init.isStructConsExp():null){
			assert(ini.tmpVarDecl is this);
			ini.beginByteCompile(bld);
		}

		if(inHeapContext){
			off = bld.getContextOffset();
			bld.emit(Instruction.push);
			bld.emitConstant(off);
			setBCLoc(off, len);
			bld.addContextOffset(len);
		}

		if(init) init.byteCompile(bld); // TODO: in semantic, add correct 'init's
		else foreach(i;0..len){bld.emit(Instruction.push); bld.emitConstant(0);}

		// dw(this," ",off," ",len);

		if(inHeapContext){
			bld.emitUnsafe(Instruction.popcn, this);
			bld.emitConstant(len);
		}else{
			off = bld.getStackOffset();
			if(len){
				bld.emitPopp(len);
				bld.emitConstant(off);
				bld.addStackOffset(len);
			}
			setBCLoc(off, len);
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

	private void load(ref ByteCodeBuilder bld, Expression loader, Scope loadersc){
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
			// import std.stdio; writeln(vd," ",off," ",len);

			if(!~off){
				if(stc&(STCimmutable|STCconst)&&init){
					// TODO: this can be inefficient for non-enum variables
					// and it destroys reference identity for them
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


	final void byteCompileSymbol(ref ByteCodeBuilder bld, Expression loader, Scope loadersc){
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
	final LValueStrategy byteCompileInitLV(ref ByteCodeBuilder bld, Expression loader, Scope loadersc){
		size_t len, off = getBCLoc(len);
		if(!~off){
			if(stc&(STCimmutable|STCconst)&&init){
				if(stc&STCstatic){
					static LiteralExp[VarDecl] decls;
					if(this !in decls){
						assert(cast(LiteralExp)init,text(init," ",));
						auto v=init.interpretV();
						auto s=[v]; // TODO: allocation here
						auto p=Variant(s.ptr, s, type.getPointer());
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
		auto diff = loadersc.getFrameNesting() - scope_.getFrameNesting();
		if(diff){bld.emit(Instruction.push); bld.emitConstant(diff);}
		return inHeapContext?diff?LVpopcc(type, loader):LVpopc(type, loader):LVpopr(len);
	}

	final LValueStrategy byteCompileSymbolLV(ref ByteCodeBuilder bld, Expression loader, Scope loadersc){
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
	}
	final size_t getBCLoc(ref size_t len){
		// import std.stdio; writeln("l ",this," ",cast(void*)this," ", byteCodeStackLength," ", byteCodeStackOffset);
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
				if(self.scope_.getFrameNesting()       >
				   self.meaning.scope_.getFrameNesting()){
					runAnalysis!MarkHeapContext(self);
				}
			}
			void perform(CallExp self){
				if(self.tmpVarDecl) self.tmpVarDecl.inHeapContext = true;
				if(!self.fun || !self.fun.type) return; // TODO: ok?
				auto tt=self.fun.type.getHeadUnqual().getFunctionTy();
				assert(!!tt,text(self.fun.type));
				foreach(i,x; self.args){
					if(tt.params[i].stc&STCbyref)
						runAnalysis!MarkHeapContext(x);
				}
			}
			void perform(FieldExp self){
				// the implicit this pointer is passed by reference
				// for value types
				if(self.type) // alias declarations can contain such expressions (TODO: should they?)
				if(self.type.getHeadUnqual().getFunctionTy())
				if(auto this_=self.e1.extractThis())
				if(auto aggrty=this_.type.isAggregateTy())
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

	void resetByteCode(){
		_byteCode = null;
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

	ByteCodeBuilder bld;

	@property ByteCode byteCode(){
		if(_byteCode is null){
			bld=ByteCodeBuilder.init;
			if(bcnumargs==-1) bcpreanalyze();
			size_t loc = 0, len = 0;
			if(!(stc&STCstatic)) loc+=bcPointerBCSize; // context pointer
			foreach(i,x; type.params){
				if(x.stc&STCbyref) len = getBCSizeof(x.type.getPointer());
				else if(x.stc&STClazy) len = bcPointerBCSize+bcFunPointerBCSiz; // TODO: ok?
				else len = getBCSizeof(x.type);
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

		auto supported=true, res=variantToMemory.VariantFromBCMemory(stack.stack[0..stack.stp+1], type.ret, supported);
		if(supported) return res;
		// assert(0,"unsupported return type "~type.ret.toString());
		handler.error(format("return type '%s' not yet supported in CTFE", type.ret.toString()),loc);
		throw new UnwindException();
	}
}

mixin template CTFEInterpret(T) if(is(T==CallExp)){
	private void emitCall(ref ByteCodeBuilder bld){
		bool ctx = false;
		if(auto s = fun.isSymbol())if(auto m = s.meaning)
			if(m.isFunctionDecl()&&!(m.stc&STCstatic)) ctx=true;
		if(auto f = fun.isFieldExp())if(auto m = f.e2.meaning)
			if(m.isFunctionDecl()&&!(m.stc&STCstatic)) ctx=true;
		if(!ctx && fun.type.isDelegateTy()) ctx = true;

		FunctionTy ft;
		auto tt=fun.type.getHeadUnqual();
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

mixin template CTFEInterpret(T) if(is(T==MultiReturnValueExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		byteCompileHelper(bld, true);
	}
	final void byteCompileIgnoreResult(ref ByteCodeBuilder bld){
		byteCompileHelper(bld, false);
	}
	private void byteCompileHelper(ref ByteCodeBuilder bld, bool keepv){
		auto oinit = call.tmpVarDecl.tupleContext.vds[0].init;
		//assert(call.tmpVarDecl.tupleContext.vds[0].init is this);
		if(call.tmpVarDecl.tupleContext.vds.length){
			call.tmpVarDecl.tupleContext.vds[0].init=null;
			foreach(x;call.tmpVarDecl.tupleContext.vds){
				x.byteCompile(bld);
			}
			call.tmpVarDecl.tupleContext.vds[0].init=oinit;
		}

		call.byteCompile(bld);
		assert(cast(TypeTuple)call.type);
		auto tt = cast(TypeTuple)cast(void*)call.type;
		size_t size=0, i=0;
		foreach(Type x;tt){
			auto bcs=getBCSizeof(x);
			if(bcs == -1){
				call.tmpVarDecl.tupleContext.vds[i].emitUnsupportedError(bld);
				return;
			}
			size+=bcs;
			i++;
		}
		bld.emitTmppush(size);
		size_t off = 0;
		foreach(x;call.tmpVarDecl.tupleContext.vds){
			auto lv=x.byteCompileInitLV(bld, this, call.tmpVarDecl.scope_);
			size_t len; x.getBCLoc(len);
			bld.emitTmppop(len);
			lv.emitStore(bld);
			off+=len;
		}
		assert(size==off);
		if(keepv&&call.tmpVarDecl.tupleContext.vds.length){
			call.tmpVarDecl.tupleContext.vds[0].byteCompileSymbol(bld, this, call.tmpVarDecl.scope_);
		}
	}
	// TODO: lvalues (ref return of mrv function call)
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


// TODO: this is similar to Stack.pop
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
}

// TODO: this abstraction could maybe act as an arena allocator
// (usage could even be extended into CTFE, but then some form of additional GC
// during CTFE-runtime will be required.)
struct VariantToMemoryContext{
	ulong[] VariantToBCMemory(Variant value){
		auto va = VariantToMemory(value);
		// TODO: this might be not ok!
		if(va.length%ulong.sizeof) va.length = va.length+ulong.sizeof-va.length%ulong.sizeof;
		assert(!(va.length%ulong.sizeof));
		return cast(ulong[])va;
	}

	Variant VariantFromBCMemory(ulong[] memory, Type type, ref bool supported){
		scope(exit) assert(!supported||!memory.length,memory.text);
		auto ret = type.getHeadUnqual();
		if(auto bt = ret.isBasicType()){
		swtch:switch(bt.op){
				foreach(x; ToTuple!integralTypes){
					case Tok!x: return Variant(mixin(`cast(`~x~`)memory.consume()`),type);
				}
				import std.typetuple;
				foreach(T; TypeTuple!(float, ifloat, double, idouble, real, ireal))
				case Tok!(T.stringof): return Variant(memory.consume!T(),type);
				default: break;
			}
		}
		if(ret.getUnqual().among(Type.get!(void[])(),Type.get!(void*)())){
			auto ltt = memory.consume();
			auto ty = cast(Type)cast(void*)ltt;
			auto r=VariantFromBCMemory(memory, ty, supported);
			memory=[];
			return r;
		}
		if(ret.isArrayTy){
			assert((memory.length-1)*ulong.sizeof<=getCTSizeof(ret)&&getCTSizeof(ret)<=memory.length*ulong.sizeof);
			auto slice = (cast(void*)memory.ptr)[0..getCTSizeof(ret)];
			memory=[];
			return VariantFromBCSlice(BCSlice(slice,slice),type,supported);
		}

		// TODO: preserve aliasing of pointers correctly.
		if(ret.getElementType()) return VariantFromBCSlice(memory.consume!BCSlice(),type,supported);
		if(auto pt=ret.isPointerTy()){
			auto ptr=memory.consume!BCPointer();
			if(ptr.ptr is null) return Variant(null,type);
			// TODO: proper pointer support!
			auto siz=getCTSizeof(pt.ty);
			auto slc=BCSlice(ptr.container,ptr.ptr[0..siz]);
			return VariantFromBCSlice(slc, pt, supported);
		}
		if(ret.isDelegateTy()){
			memory=[];
			return Variant(null,type); // TODO!
		}

		if(ret is Type.get!(typeof(null))){
			assert(memory.length==getBCSizeof(Type.get!(typeof(null))()));
			memory=[];
			return Variant(null);
		}
		if(auto at=ret.isAggregateTy()){
			if(at.decl.isReferenceAggregateDecl()){
				auto ptr=memory.consume!BCPointer();
				if(ptr.ptr is null) return Variant(null);
				return VariantFromAggregate(cast(ulong[])ptr.container, type, supported);
			}
			auto r=VariantFromAggregate(memory, type, supported);
			assert(memory.length==at.decl.getBCSize(),text(memory," ",at.decl," ",at.decl.getBCSize()," ",at.decl.isLayoutKnown()));
			memory=[];
			return r;
		}
		supported = false;
		return Variant(null);
	}

	void[] VariantToMemory(Variant value){ // TODO: optimize this such that it does not allocate so heavily
		auto ret = value.getType().getHeadUnqual();
		if(auto bt = ret.isBasicType()){
		swtch:switch(bt.op){
				foreach(x; ToTuple!integralTypes){
					case Tok!x: return [mixin(`cast(`~x~`)value.get!ulong()`)];
				}
				foreach(T; Seq!(float, ifloat, double, idouble, real, ireal))
				case Tok!(T.stringof): return [cast(T)value.get!T()];
				default: break;
			}
		}
		if(ret.isArrayTy){
			auto res=VariantToBCSlice(value);
			return res.slice;
		}
		if(ret.getElementType()){
			return [VariantToBCSlice(value)];
		}
		if(ret.isPointerTy()){
			return [VariantToBCPointer(value)];
		}
		if(ret.isDelegateTy()){
			return new ulong[getBCSizeof(ret)]; // TODO!
		}
		if(auto at=ret.isAggregateTy()){
			Variant[VarDecl] vars = value.get!(Variant[VarDecl])();
			if(vars is null){
				assert(!!at.decl.isReferenceAggregateDecl());
				goto Lnull;
			}
			auto memory=VariantToAggregate(vars, at.decl);
			if(at.decl.isReferenceAggregateDecl()){
				return [BCPointer(memory, memory.ptr)];
			}
			return memory;
		}
		if(ret is Type.get!(typeof(null))){
		Lnull: return [BCPointer(null,null)];
		}
		assert(0,ret.text);
	}

	Variant VariantFromBCSlice(BCSlice bc, Type type, ref bool supported)in{
		assert(type.getElementType()||type.getHeadUnqual().isPointerTy());
	}body{
		auto v = bc.container;
		auto el = type.getElementType();
		if(!el) el=type.getHeadUnqual().isPointerTy().ty;
		auto tyu=type.getHeadUnqual();
		import std.typetuple;
		foreach(T;TypeTuple!(string, wstring, dstring))
			if(tyu is Type.get!T()) return Variant(cast(T)bc.slice,type); // TODO: aliasing!

		auto ttt=type.getUnqual();
		if(auto ptr=ttt.isPointerTy()) ttt=ptr.ty.getDynArr();
		auto tag=q(ttt,v.ptr);
		auto computeContainer(){
			if(el.getHeadUnqual().isDynArrTy()){
				auto from = cast(BCSlice[])v;
				auto res = new Variant[from.length];
				sl_aliasing_rev[tag]=res;
				foreach(i,ref x; res) x = VariantFromBCSlice(from[i],el,supported);
				return res;
			}
			if(type is Type.get!EmptyArray()){
				return sl_aliasing_rev[tag]=(Variant[]).init;
			}
			if(auto bt = el.getHeadUnqual().isBasicType()){
			swtch:switch(bt.op){
					foreach(xx;ToTuple!basicTypes){
						static if(xx!="void"){
							alias typeof(mixin(xx~`.init`)) T;
							case Tok!xx:
								auto from = cast(T[])v;
								auto res = new Variant[from.length];
								foreach(i, ref x; res) x=Variant(from[i],el);
								sl_aliasing_rev[tag]=res;
								return res;
						}
					}
					default: assert(0);
				}
			}
			auto memory = cast(ulong[])v;
			auto siz=el.getBCSizeof();
			// TODO: can we assert siz!=0?
			if(!siz) return (Variant[]).init;
			assert(siz&&!(v.length%siz));
			auto res = new Variant[memory.length/siz];
			sl_aliasing_rev[tag]=res;
			foreach(i,ref x; res) x = VariantFromBCMemory(memory[siz*i..siz*i+siz],el,supported);
			return res;
		}
		Variant[] container;
		auto siz = getCTSizeof(el);
		assert(siz!=0);
		assert(!((bc.slice.ptr-bc.container.ptr)%siz));
		assert(!(bc.slice.length%siz));
		if(tag in sl_aliasing_rev){
			container=sl_aliasing_rev[tag];
		}else{
			container = computeContainer();
			assert(tag in sl_aliasing_rev);
		}
		auto start=(bc.slice.ptr-bc.container.ptr)/siz;
		auto end=start+bc.slice.length/siz;
		if(type.getHeadUnqual().isPointerTy()) return Variant(container.ptr+start, container, type);
		return Variant(container[start..end],container,type);
	}

	BCSlice VariantToBCSlice(Variant value)in{
		assert(!!value.getType().getElementType());
	}body{
		auto ret=value.getType().getHeadUnqual();
		if(ret is Type.get!(typeof(null))())
			return BCSlice(null); // TODO: necessary?
		foreach(T;Seq!(string,wstring,dstring)){ // TODO: aliasing for strings, proper zero-termination of allocated memory blocks
			if(ret is Type.get!T()){
				auto str = value.get!T();
				//return BCSlice(cast(void[])str, cast(void[])str);
				str=str~0; // duplicate payload and zero terminate
				return BCSlice(cast(void[])str, cast(void[])str[0..$-1]);
			}
		}
		auto arr = value.get!(Variant[])();
		auto cnt = value.getContainer();
		auto start = arr.ptr-cnt.ptr;
		auto end = start+arr.length;
		void[] rcnt;
		bool cached = false;
		if(cnt.ptr in sl_aliasing){
			rcnt=sl_aliasing[cnt.ptr];
			cached = true;
		}

		auto finish(size_t siz){
			if(!cached){
				sl_aliasing[cnt.ptr]=rcnt;
				sl_aliasing_rev[q(ret.getUnqual(),rcnt.ptr)]=cnt;
			}
			return BCSlice(rcnt, rcnt.ptr[start*siz..end*siz]);
		}

		assert(ret.getElementType());
		if(ret.getUnqual() is Type.get!EmptyArray()) return BCSlice([]);
		auto el = ret.getElementType().getHeadUnqual();
		if(el is Type.get!(void)()){
			el = value.getType().getElementType(); // TODO: store the actual type
		}
		assert(el);
		// this prevents in-place append of containers by allocating one element too much
		// TODO: is there a more elegant solution?
		if(auto bt=el.isBasicType()){
			if(bt.isIntegral()){
				switch(bt.getSizeof()){
					foreach(U; Seq!(ubyte, ushort, uint, ulong)){
						case U.sizeof:
							if(cached) return finish(U.sizeof);
							auto r=(new U[cnt.length+1])[0..$-1];
							foreach(i,ref x;r) x=cast(U)cnt[i].get!ulong();
							rcnt=r;
							return finish(U.sizeof);
					}
					default: assert(0);
				}
			}
			foreach(U; Seq!(float, double, real, ifloat, idouble, ireal, cfloat, cdouble, creal)){
				if(bt is Type.get!U()){
					if(cached) return finish(U.sizeof);
					auto r=(new U[cnt.length+1])[0..$-1];
					foreach(i,ref x;r) x=cast(U)cnt[i].get!U();
					rcnt=r;
					return finish(U.sizeof);
				}
			}
		}
		assert(getCTSizeof(el)==getBCSizeof(el)*ulong.sizeof);
		auto siz=getBCSizeof(el);
		if(cached) return finish(siz*ulong.sizeof);
		auto r = (new ulong[cnt.length*siz+1])[0..$-1];
		foreach(i;0..cnt.length) r[i*siz..(i+1)*siz]=VariantToBCMemory(cnt[i])[];
		rcnt=r;
		return finish(siz*ulong.sizeof);
	}

	BCPointer VariantToBCPointer(Variant value)in{
		assert(cast(PointerTy)value.getType().getHeadUnqual());
	}body{
		auto tt = cast(PointerTy)cast(void*)value.getType().getHeadUnqual();
		auto cnt = value.getContainer();
		assert(cnt.ptr<=value.getPointer());
		auto id = value.getPointer()-cnt.ptr;
		auto slc = VariantToBCSlice(Variant(cnt.ptr[id..id+1],cnt,tt.ty.getDynArr()));
		return BCPointer(slc.container, slc.slice.ptr);
	}


	Variant VariantFromAggregate(ulong[] memory, Type type, ref bool supported)in{
		assert(type.getHeadUnqual().isAggregateTy());
	}body{
		auto ret = type.getHeadUnqual();
		auto decl = (cast(AggregateTy)cast(void*)ret).decl;
		// TODO: What about pointers with an offset?
		auto tag=q(ret.getUnqual(),memory.ptr);
		if(tag in aliasing_reverse){
			// there can be structs with a first field of struct type,
			// hence multiple pieces of data may start at the same location
			return aliasing_reverse[tag];
		}
		// (stupid built-in AAs)
		Variant[VarDecl] res;
		res[cast(VarDecl)cast(void*)type]=Variant(null);
		res.remove(cast(VarDecl)cast(void*)type);
		// now 'res' is initialized
		aliasing_reverse[tag]=Variant(res, type);
		assert(decl.isLayoutKnown);
		foreach(vd;&decl.traverseFields){
			size_t len, off = vd.getBCLoc(len);
			assert(len != -1);
			res[vd]=VariantFromBCMemory(memory[off..off+len],
			                            vd.type.applySTC(type.getHeadSTC()),
			                            supported);
		}
		return Variant(res, type);
	}


	ulong[] VariantToAggregate(Variant[VarDecl] vars, AggregateDecl decl){
		if(vars.byid in aliasing_cache) return aliasing_cache[vars.byid];
		auto res = new ulong[decl.getBCSize()];
		aliasing_cache[vars.byid]=res;
		auto tag=q(cast(Type)decl.getType(),res.ptr);
		aliasing_reverse[tag]=Variant(vars,decl.getType());
		static assert(ReferenceAggregateDecl.sizeof<=ulong.sizeof);
		if(auto rd=decl.isReferenceAggregateDecl())
			res[ReferenceAggregateDecl.bcTypeidOffset]=cast(ulong)cast(void*)rd;
		foreach(vd;&decl.traverseFields){
			size_t len, off = vd.getBCLoc(len);
			assert(len != -1);
			if(vd !in vars && vd.init){
				vars[vd]=vd.init.interpretV(); // TODO: ok?
			}
			if(vd in vars){
				auto var = vars[vd];
				res[off..off+len]=VariantToBCMemory(var);
			}
		}
		return res;
	}
   
	import std.typecons : q=tuple, Q=Tuple;
	ulong[][AAbyIdentity!(VarDecl,Variant)] aliasing_cache; // preserve aliasing
	Variant[Q!(Type,ulong*)] aliasing_reverse; // preserve aliasing on reverse translation

	void[][Variant*] sl_aliasing; // preserve aliasing
	Variant[][Q!(Type,void*)] sl_aliasing_rev; // preserve aliasing on reverse translation

	void flushCaches(){
		aliasing_cache=null;
		sl_aliasing=null;
		// we still need reverse translation
		// hashtables with weak keys would be neat to resolve the memory leak this causes
		// TODO: fix memory leak
	}
}

VariantToMemoryContext variantToMemory; // TODO: is there a better way?
