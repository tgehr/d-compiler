import lexer, expression, semantic, scope_, type;
import std.string;


private template NotYetImplemented(T){
	static if(is(T _==BinaryExp!S,TokenType S) && !is(T==BinaryExp!(Tok!".")))
		enum NotYetImplemented = false;
	else static if(is(T _==UnaryExp!S,TokenType S))
		enum NotYetImplemented = false;
		else enum NotYetImplemented = !is(T==Expression) && !is(T:Type) && !is(T:Symbol) && !is(T:LiteralExp) && !is(T==CastExp) && !is(T==ArrayLiteralExp) && !is(T==IndexExp) && !is(T==SliceExp) && !is(T==TernaryExp);
}

mixin template Interpret(T) if(is(T:Expression) && NotYetImplemented!T){
	override Expression interpret(Scope sc){
		assert(sc, "expression "~toString()~" was assumed to be interpretable");
		sc.error(format("expression '%s' is not interpretable at compile time yet",loc.rep),loc);
		mixin(ErrEplg);
	}
}

mixin template Interpret(T) if(is(T==Expression)){
	// scope may be null if it is evident that the expression can be interpreted
	bool checkInterpret(Scope sc)in{assert(sstate == SemState.completed);}body{
		assert(sc, loc.rep);
		sc.error(format("expression '%s' is not interpretable at compile time",loc.rep),loc);
		return false;
	}
	Expression interpret(Scope sc)in{assert(sstate == SemState.completed);}body{
		if(!checkInterpret(sc)) mixin(ErrEplg);
		auto r = interpretV().toExpr();
		r.loc=loc;
		return r; 
	}
	Variant interpretV()in{assert(sstate == SemState.completed);}body{
		//return Variant.error(format("expression '%s' is not interpretable at compile time"),loc.rep);
		return Variant("TODO: cannot interpret "~to!string(this)~" yet");
		//return Variant.init;
	}
}

mixin template Interpret(T) if(is(T==CastExp)){
	override bool checkInterpret(Scope sc){return e.checkInterpret(sc);}
	override Variant interpretV(){
		auto le=e.isLiteralExp(); // polysemous string literals might be cast
		if(e.isArrayLiteralExp()||le&&le.isPolyString()){
			auto vle=e.interpretV();
			// TODO: factor this out into a final member function of Type?
			auto el = type.getElementType();
			assert(!!el, "cannot convert");
			auto typeu = type.getHeadUnqual();
			if(typeu is Type.get!string()
			|| typeu is Type.get!wstring()
			|| typeu is Type.get!dstring())
				return e.interpretV().convertTo(type);
			// TODO: allocation ok?
			Variant[] r = new Variant[vle.length];
			foreach(i,ref x;r) x = vle[i].convertTo(el);
			return Variant(r);
		}else return e.interpretV().convertTo(type);
	}
}
mixin template Interpret(T) if(is(T==Type)){
	override bool checkInterpret(Scope sc){return true;}
	override Expression interpret(Scope sc){return this;}
}mixin template Interpret(T) if(!is(T==Type) && is(T:Type)){}

mixin template Interpret(T) if(is(T==Symbol)){
	override bool checkInterpret(Scope sc){
		if(auto vd = meaning.isVarDecl()){
			if(vd.stc&STCenum
			|| vd.stc&STCimmutable && vd.init.isConstant())
				return true;
		}
		return super.checkInterpret(sc);
	}
	override Variant interpretV(){
		if(auto vd = meaning.isVarDecl()){
			assert(meaning.sstate == SemState.completed);
			/+if(vd.stc&STCenum|STCimmutable) +/
			return vd.init.interpretV();
		}
		assert(0);
	}
}mixin template Interpret(T) if(!is(T==Symbol) && is(T:Symbol)){}
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
						case Tok!x: value=Variant(to!U(mixin(`lit.`~occ))); break swtch;
					}else{
						case Tok!x: value=Variant(cast(U)mixin(`lit.`~occ)); break swtch;
					}
				}else{
					case Tok!x: value=Variant(null); break swtch;
				}
			}
			default: assert(0, to!string(lit.type));
		}
	}
	this(Variant value){ this.value = value; }

	static LiteralExp create(alias New=New,T)(T val){//workaround for long standing bug
		// TODO: get rid of most of this logic
		/+Token lit;

		static if(is(T==bool)){
			lit.type = val?Tok!"true":Tok!"false";
			lit.int64 = val;
		}else{
			// TODO: this sometimes allocates.
			foreach(x; ToTuple!literals){
				static if(is(typeof(mixin(x))==T)){
					lit.type = Tok!x;
					alias typeof(mixin(`lit.`~getTokOccupied!T)) U;
					static if(x=="``"w||x=="``"d)
						mixin(`lit.`~getTokOccupied!T) = to!U(val);
					else mixin(`lit.`~getTokOccupied!T) = cast(U)val;

				}
			}
			static if(is(T==dchar)||is(T==wchar)){
				lit.type = Tok!"' '";
				lit.int64 = val;
			}
		}+/
		//return New!LiteralExp(lit).semantic(null);
		return New!LiteralExp(Variant(val)).semantic(null);
		//lit.type = Tok!"``";
		//lit.str = str;
	}


	override bool checkInterpret(Scope sc){ return true; }
	override LiteralExp interpret(Scope sc){ return this; }
	override Variant interpretV(){ return value; }
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
		foreach(i, ref x; res) res[i] = lit[i].interpretV();
		return Variant(res);
	}
}

mixin template Interpret(T) if(is(T==IndexExp)){
	override bool checkInterpret(Scope sc){
		if(a.length==0) return e.checkInterpret(sc);
		assert(a.length==1);
		return e.checkInterpret(sc)&a[0].checkInterpret(sc);
	}
	override Variant interpretV(){
		if(a.length==0) return e.interpretV();
		assert(a.length==1);
		assert(e.isConstant());
		auto lit = e.interpretV();
		auto ind = a[0].interpretV();
		if(lit.isEmpty() || ind.isEmpty()) return Variant.init;
		return lit[ind];
	}
}

mixin template Interpret(T) if(is(T==SliceExp)){
	override bool checkInterpret(Scope sc){
		return e.checkInterpret(sc) & l.checkInterpret(sc) & r.checkInterpret(sc);
	}
	override Variant interpretV(){
		return e.interpretV()[l.interpretV()..r.interpretV()];
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
}


mixin template Interpret(T) if(is(T _==BinaryExp!S, TokenType S) && !is(T==BinaryExp!(Tok!"."))){
	static if(is(T _==BinaryExp!S, TokenType S)):
	static if(!isAssignOp(S)):
	override bool checkInterpret(Scope sc){
		return e1.checkInterpret(sc)&e2.checkInterpret(sc);
	}
	override Variant interpretV(){
		static if(isRelationalOp(S)&&S!=Tok!"is"&&S!=Tok!"in"||isArithmeticOp(S)||isBitwiseOp(S)||isShiftOp(S)||isLogicalOp(S))
			return e1.interpretV().opBinary!(TokChars!S)(e2.interpretV());
		else static if(S==Tok!"~"){
			if(e1.type.equals(e2.type)) return e1.interpretV().opBinary!"~"(e2.interpretV());
			// TODO: this might be optimized. this gc allocates
			if(auto ety = e1.type.getElementType()){
				if(ety.equals(e2.type))
					return e1.interpretV().opBinary!"~"(Variant([e2.interpretV()]));
			}
			assert(e2.type.getElementType() &&
			       e2.type.getElementType().equals(e1.type));
			return Variant([e1.interpretV()]).opBinary!"~"(e2.interpretV());
		}else return super.interpretV();
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
}

/+mixin template Interpret(T) if(is(T==CallExp)){
	private Variant val;
	final override bool checkInterpret(Scope sc){
		// TODO: interpret
		// TODO: 
		assert(0);
	}
	override 
}+/
