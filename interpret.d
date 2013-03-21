import lexer, expression, semantic, scope_, type;
import std.string;


private template NotYetImplemented(T){
	static if(is(T _==BinaryExp!S,TokenType S) && !is(T==BinaryExp!(Tok!".")))
		enum NotYetImplemented = false;
	else static if(is(T _==UnaryExp!S,TokenType S))
		enum NotYetImplemented = false;
	else enum NotYetImplemented = !is(T==Expression) && !is(T:Type) && !is(T:Symbol) && !is(T:LiteralExp) && !is(T==CastExp);
}

mixin template Interpret(T) if(is(T:Expression) && NotYetImplemented!T){
	override Expression interpret(Scope sc){
		sc.error(format("expression '%s' is not interpretable at compile time yet",loc.rep),loc);
		sstate = SemState.error;
		return this;
	}
}

mixin template Interpret(T) if(is(T==Expression)){
	// scope may be null if it is evident that the expression can be interpreted
	Expression interpret(Scope sc)in{assert(sstate == SemState.completed);}body{
		Variant r = interpretV();
		assert(sc||!r.isEmpty());
		if(r.isEmpty()){
			sc.error(format("expression '%s' is not interpretable at compile time",loc.rep),loc);
			mixin(ErrEplg);
		}
		return r.toExpr();
	}
	Variant interpretV()in{assert(sstate == SemState.completed);}body{
		return Variant("TODO: cannot interpret "~to!string(this)~" yet");
		//return Variant.init;
	}
}

mixin template Interpret(T) if(is(T==CastExp)){
	override Variant interpretV(){return e.interpretV().convertTo(type);}
}
mixin template Interpret(T) if(is(T==Type)){
	override Expression interpret(Scope sc){return this;}
}mixin template Interpret(T) if(!is(T==Type) && is(T:Type)){}

mixin template Interpret(T) if(is(T==Symbol)){
	override Variant interpretV(){
		if(auto vd = meaning.isVarDecl()){
			assert(meaning.sstate == SemState.completed);
			if(vd.stc&STCenum) return vd.init.interpretV();
		}
		return super.interpretV();
	}
}mixin template Interpret(T) if(!is(T==Symbol) && is(T:Symbol)){}
mixin template Interpret(T) if(is(T==LiteralExp)){
	override LiteralExp interpret(Scope sc){return this;}

	private template getTokOccupied(T){
		enum vocc = to!string(getOccupied!T);
		static if(vocc == "wstr") enum occ = "str";
		else static if(vocc == "dstr") enum occ = "str";
		else static if(vocc == "fli80") enum occ = "flt80";
		else enum occ = vocc;
		enum getTokOccupied = occ;
	}

	override Variant interpretV(){
		//return Variant();
		// TODO: this might allocate. ok?
		switch(lit.type){
			foreach(x; ToTuple!literals){
				static if(x!="null"){
					alias typeof(mixin(x)) U;
					enum occ = getTokOccupied!U;
					static if(x=="``"w||x=="``"d){
						case Tok!x: return Variant(to!U(mixin(`lit.`~occ)));
					}else{
						case Tok!x: return Variant(cast(U)mixin(`lit.`~occ));
					}
				}else{
					case Tok!x: return Variant(null);
				}
			}
			default: assert(0);
		}
	}
}

mixin template Interpret(T) if(is(T _==UnaryExp!S,TokenType S)){
	static if(is(T _==UnaryExp!S,TokenType S)):
	static if(S!=Tok!"&"&&S!=Tok!"*"): // TODO: implement where possible
	static if(S!=Tok!"++"&&S!=Tok!"--"):
	override Variant interpretV(){
		return e.interpretV().opUnary!(TokChars!S)();
	}
}


mixin template Interpret(T) if(is(T _==BinaryExp!S, TokenType S) && !is(T==BinaryExp!(Tok!"."))){
	static if(is(T _==BinaryExp!S, TokenType S)):
	static if(!isAssignOp(S)):
	override Variant interpretV(){
		static if(isArithmeticOp(S)||isBitwiseOp(S)||isShiftOp(S))
			return mixin(`e1.interpretV()`~TokChars!S~`e2.interpretV()`);
		else assert(0, "TODO");
	}
}