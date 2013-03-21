
import std.array, std.conv, std.algorithm, std.string;

import lexer, parser, expression, statement, declaration, scope_, util;

public import operators;

string uniqueIdent(string base){
	shared static id=0;
	return base~to!string(id++);
}
// helper macros

template PropErr(string s){ // propagate the 'error' semantic state TODO: maybe exceptions?
	enum PropErr={
		string r;
		auto ss=s.split(",");
		foreach(t;ss){
			r~="static if(is(typeof("~t~"): Node)){if("~t~".sstate==SemState.error){sstate=SemState.error;return this;};}\n";
			r~="else{foreach(x;"~t~") if(x.sstate==SemState.error){sstate=SemState.error;return this;};}\n";
		}
	return r;
	}();
}

template SemChld(string s){ // perform semantic analysis on child node, propagate all errors
	enum SemChld={
		string r;
		auto ss=s.split(",");
		foreach(t;ss){
			r~="static if(is(typeof("~t~"): Node)) "~t~"="~t~".semantic(sc);\n";
			r~="else foreach(ref x;"~t~"){x=x.semantic(sc);}\n";
		}
		return r~PropErr!s;
	}();
}


enum SemState{
	pre,
	begin,
	started,
	fwdRefs,
	completed,
	error,
}

enum SemPrlg=q{
	if(sstate >= SemState.completed) return this;
	//if(sstate>SemState.begin){sc.error("cyclic dependency",loc);sstate=SemState.error;return this;}
};
enum SemEplg=q{
	sstate = SemState.completed;
	return this;
};
enum ErrEplg=q{
	sstate=SemState.error;
	return this;
};
template Semantic(T) if(is(T==Node)){
	Node semantic(Scope s)in{assert(sstate>=SemState.begin);}body{
		s.error("unimplemented feature",loc);
		sstate = SemState.error;
		return this;
	}
}

// error nodes (TODO: file bug against covariance error)

mixin template Semantic(T) if(is(T==ErrorDecl)||is(T==ErrorExp)||is(T==ErrorStm)||is(T==ErrorTy)){
	override T semantic(Scope sc){ return this; } // DMD compiler bug: T is required
}


// expressions
mixin template Semantic(T) if(is(T==Expression)){
	Type type;
	override Expression semantic(Scope sc){ sc.error("unimplemented feature",loc); sstate = SemState.error; return this; }

	Type typeSemantic(Scope sc){
		Expression me;
		if(sstate<SemState.started){ // TODO: is this ok?
			sstate = SemState.started;
			me = semantic(sc);
			if(me.sstate == SemState.error) return New!ErrorTy;
			if(auto ty=me.isType()) return ty;
		}else me=this;
		sc.error(format("%s '%s' is used as a type",me.kind,me.loc.rep),me.loc);
		return New!ErrorTy;
	}

	Expression isLvalue(){return null;}
	Expression implicitlyConvertTo(Type to){ // TODO: assert(to.sstate == SemState.completed);
		if(type is to) return this;
		return New!ImplicitCastExp(to,this);
	}
	bool implicitlyConvertsTo(Type rhs){
		if(type.implicitlyConvertsTo(rhs)) return true;
		auto l = type.isIntegral(), r = rhs.type.isIntegral();
		if(l && r){
			if(l.op == Tok!"long" || l.op == Tok!"ulong") return r.getLongRange().contains(getLongRange());
			return r.getIntRange().contains(this.getIntRange());
		}
		return false;
	}
	IntRange getIntRange(){return type.getIntRange();}
	LongRange getLongRange(){return type.getLongRange();}
}

mixin template Semantic(T) if(is(T==LiteralExp)){
	override Expression semantic(Scope sc){
		switch(lit.type){ // TODO: remove some boilerplate
			case Tok!"``": //TODO: this needs to have a polysemous type
				type=Type.get!(immutable(char)[])(); break;
			case Tok!"``c":
				type=Type.get!(immutable(char)[])(); break;
			case Tok!"``w":
				type=Type.get!(immutable(wchar)[])(); break;
			case Tok!"``d":
				type=Type.get!(immutable(dchar)[])(); break;
			case Tok!"''":
				if(lit.int64<128) type=Type.get!char();
				else type=Type.get!dchar(); break;
			case Tok!"0":
				type=Type.get!int(); break;
			case Tok!"0U":
				type=Type.get!uint(); break;
			case Tok!"0L":
				type=Type.get!long(); break;
			case Tok!"0LU":
				type=Type.get!ulong(); break;
			case Tok!".0f":
				type=Type.get!float(); break;
			case Tok!".0":
				type=Type.get!double(); break;
			case Tok!".0L":
				type=Type.get!real(); break;
			case Tok!".0fi":
				type=Type.get!ifloat(); break;
			case Tok!".0i":
				type=Type.get!idouble(); break;
			case Tok!".0Li":
				type=Type.get!ireal(); break;
			case Tok!"null":
				type=Type.get!Null(); break;
			case Tok!"true", Tok!"false":
				type=Type.get!bool(); break;
				lit.int64=lit.type == Tok!"true";
			default: return super.semantic(sc); // TODO: verify
		}
		mixin(SemEplg);
	}
	override IntRange getIntRange(){
		switch(lit.type){
			case Tok!"''":
				if(lit.int64<128) goto case Tok!"0";
				goto case Tok!"0U";
			case Tok!"0", Tok!"true", Tok!"false":
				return IntRange(cast(int)lit.int64,cast(int)lit.int64,true);
			case Tok!"0U":
				return IntRange(cast(uint)lit.int64,cast(uint)lit.int64,false);
			default: return super.getIntRange();
		}
	}
	override LongRange getLongRange(){
		bool signed=true;
		switch(lit.type){
			case Tok!"0LU": signed=false; goto case;
			case Tok!"''", Tok!"0", Tok!"0U", Tok!"0L":
			case Tok!"true", Tok!"false":
				return LongRange(lit.int64,lit.int64,signed);
			default: return super.getLongRange();
		}
	}
}

template Semantic(T) if(is(T==ArrayLiteralExp)){
	override Expression semantic(Scope sc){
		if(!lit.length){type=Type.get!EmptyArray(); sstate=SemState.completed; return this;}
		mixin(SemChld!q{lit});
		auto ty=lit[0].type;
		foreach(x;lit[1..$]){
			// TODO: implicit casts
			if(auto newty=ty.combine(x.type)) ty=newty;
			else{sc.error(format("incompatible type '%s' in array of '%s'",x.type,ty),x.loc); sstate=SemState.error; return this;}
		}
		type=ty.getDynArr();
		mixin(SemEplg);
	}
}

template Semantic(T) if(is(T X==PostfixExp!S,TokenType S)){
	override Expression semantic(Scope sc){ // TODO: rewrite to (auto x=e, op e, e)
		mixin(SemPrlg);
		mixin(SemChld!q{e});
		if(auto bt=cast(BasicType)e.type){
			type=e.type;
			mixin(SemEplg);
		}
		sc.error(format("type '%s' does not support postfix "~TokChars!op,e.type),loc);
		mixin(ErrEplg);
	}
}

template Semantic(T) if(is(T==IndexExp)){
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e}); // TODO: add 'a'.
		if(auto ty=e.isType()){
			if(!a.length) return ty.getDynArr();
			return super.semantic(sc); // TODO: implement
		}
		return super.semantic(sc); // TODO: implement
	}
	
	override Type typeSemantic(Scope sc){
		//mixin(SemPrlg);
		Type ty;
		e=ty=e.typeSemantic(sc);
		if(ty.sstate == SemState.error) return New!ErrorTy;
		if(!a.length) return ty.getDynArr().semantic(sc);
		return super.typeSemantic(sc); // TODO: implement
	}
}

template Semantic(T) if(is(T==CallExp)){
	override Expression semantic(Scope sc){ // TODO: type checking
		mixin(SemPrlg);
		mixin(SemChld!q{e,args});
		sc.error("unimplemented feature", loc);
		mixin(ErrEplg);
		//mixin(SemEplg);
	}
}

template Semantic(T) if(is(T==BinaryExp!(Tok!"."))){}

template Semantic(T) if(is(T X==BinaryExp!S,TokenType S) && !is(T==BinaryExp!(Tok!"."))){
	static if(is(T X==BinaryExp!S,TokenType S)):
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e1,e2});
		
		static if(isAssignOp(S)){
			if(auto lv=e1.isLvalue()){
				type = e1.type;
				e2=e2.implicitlyConvertTo(type).semantic(sc);
				if(e2.sstate == SemState.error) sstate=SemState.error;
				return this;
			}else{
				sc.error("expression is not assignable",loc);
				mixin(ErrEplg);
			}
		}else{
			auto bt1=e1.type.getHeadUnqual().isBasicType();
			auto bt2=e2.type.getHeadUnqual().isBasicType();
			static if(isArithmeticOp(S) || isBitwiseOp(S)){
				auto v = Type.get!void();
				if(bt1 && bt2 && bt1 !is v && bt2 !is v){
					bt1=bt1.intPromote(); bt2=bt2.intPromote();
					if(auto ty=bt1.combine(bt2)){
						e1 = e1.implicitlyConvertTo(ty).semantic(sc);
						e2 = e2.implicitlyConvertTo(ty).semantic(sc);
						type = ty;
						mixin(SemEplg);
					}
				}
			}else static if(isRelationalOp(S)){
				auto v = Type.get!void();
				if(bt1 && bt2 && bt1 !is v && bt2 !is v){
					if(auto ty=bt1.combine(bt2)){
						e1 = e1.implicitlyConvertTo(ty).semantic(sc);
						e2 = e2.implicitlyConvertTo(ty).semantic(sc);
						type = Type.get!bool();
						if(ty.op!=Tok!"cfloat"&&ty.op!=Tok!"cdouble"&&ty.op!=Tok!"creal"){
							mixin(SemEplg);
						}else{
							sc.error("cannot compare complex operands",loc);
							mixin(ErrEplg);
						}
					}
				}
			}
		}
		static if(S==Tok!","){
			type=e2.type;
			mixin(SemEplg);
		}else{
			sc.error(format("incompatible types for binary "~TokChars!S~": '%s' and '%s'",e1.type,e2.type),loc);
			mixin(ErrEplg);
		}
	}
	override IntRange getIntRange(){
		static if(isArithmeticOp(S) || isBitwiseOp(S)){
			return mixin(`e1.getIntRange()`~TokChars!S~`e2.getIntRange()`);
		}else static if(S==Tok!"," || isAssignOp(S)){
			return e2.getIntRange(); 
		}else static if(isRelationalOp(S)){
			// TODO: relational operators
			return super.getIntRange();
		}else static if(isLogicalOp(S)){
			// TODO: logical operators
			return super.getIntRange();
		}else return super.getIntRange(); // '~'
	}
	override LongRange getLongRange(){
		static if(isArithmeticOp(S) || isBitwiseOp(S)){
			return mixin(`e1.getLongRange()`~TokChars!S~`e2.getLongRange()`);
		}else static if(S==Tok!"," || isAssignOp(S)){
			return e2.getLongRange(); 
		}else static if(isRelationalOp(S)){
			// TODO: relational operators
			return super.getLongRange();
		}else static if(isLogicalOp(S)){
			// TODO: logical operators
			return super.getLongRange();
		}else return super.getLongRange(); // '~'
	}
}

template Semantic(T) if(is(T X==TernaryExp)){
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		e1=e1.semantic(sc);
		mixin(SemChld!q{e2,e3});
		auto ty1=cast(Type)e2.type, ty2=cast(Type)e3.type;
		assert(ty1 && ty2);
		auto ty=ty1.combine(ty2);
		if(!ty){
			sc.error(format("incompatible types for ternary operator: '%s' and '%s'",e2.type,e3.type),loc);
			mixin(ErrEplg);
		}
		mixin(PropErr!q{e1});
		type=ty;
		mixin(SemEplg);
	}
}
class Symbol: Expression{ // semantic node
	Declaration meaning;
	override Symbol semantic(Scope sc){
		mixin(SemPrlg);
		if(sstate<SemState.started){
			sstate = SemState.started;
			mixin(SemChld!q{meaning});
		}else{mixin(PropErr!q{meaning});}

		if(auto vd=meaning.isVarDecl()){
			type=vd.type.typeSemantic(sc);
			mixin(PropErr!q{type});
		}
		else type=Type.get!void(); // same as DMD

		sstate = SemState.completed;
		return this;
	}
	override string toString(){return meaning.name;}
	override @property string kind(){return meaning.kind;}

	// override Type isType(){...} // TODO.
}

mixin template Semantic(T) if(is(T==CastExp)){
	override Expression semantic(Scope sc){
		// TODO: sanity checks etc.
		mixin(SemPrlg);
		mixin(SemChld!q{e});
		if(!ty) {
			if(!stc) type = e.type.getHeadUnqual(); // TODO: works differently for classes...
			else type = e.type.applySTC(stc);
		}else{
			type=ty.typeSemantic(sc);
			mixin(PropErr!q{type});
		}
		mixin(SemEplg);
	}
	IntRange getIntRange(){
		auto ty = e.type.getHeadUnqual().isIntegral();
		auto nt = type.getHeadUnqual().isIntegral();
		int size=nt.bitSize();
		if(!ty||!nt) return type.getIntRange();
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
			auto or=e.getIntRange();
			r=LongRange(or.min, or.max, true);
		}
		if(signed) r=r.toSigned();
		else r=r.toUnsigned();
		return r;
	}
}

class ImplicitCastExp: CastExp{ // semantic node
	this(Expression tt, Expression exp){super(STC.init, tt, exp);}
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e});
		ty=type=ty.semantic(sc).isType();
		assert(type && 1); // if not a type the program is in error
		if(type.sstate == SemState.error){sstate = SemState.error; return this;}
		if(e.implicitlyConvertsTo(type)) return this;
		sstate = SemState.error;
		sc.error(format("cannot implicitly convert expression '%s' of type '%s' to '%s'",e,e.type,type),e.loc); // TODO: replace toString with actual representation
		//error(format("no viable conversion from type '%s' to '%s'",e.type,type),e.loc);
		return this;
	}
	override string toString(){return e.toString();}
}



mixin template Semantic(T) if(is(T==Identifier)){
	override Symbol semantic(Scope sc){
		mixin(SemPrlg);
		meaning=sc.lookup(this);
		return super.semantic(sc);
	}
}

mixin template Semantic(T) if(is(T==FunctionLiteralExp)){
	override Symbol semantic(Scope sc){
		assert(sstate != SemState.completed);
		if(!type) type=New!FunctionType(STCauto,cast(Expression)null,cast(Parameter[])null,VarArgs.none);
		auto dg=New!FunctionDef(fty,New!Identifier(uniqueIdent("__dgliteral")),cast(BlockStm)null,cast(BlockStm)null,cast(Identifier)null,bdy);
		dg.sstate = SemState.begin;
		dg=dg.semantic(sc);
		auto e=New!Symbol;
		e.meaning=dg; // TODO: dg.addressOf();
		e.loc=loc;
		return e.semantic(sc);
	}
}

// types
mixin template Semantic(T) if(is(T==Type)){
	override Type semantic(Scope sc){return this;}
	override Type typeSemantic(Scope sc){return semantic(sc);}
	Type checkVarDecl(Scope, VarDecl){return this;}

	Type getArray(long size){
		if(auto r=arrType.get(size,null)) return r;
		return arrType[size]=ArrayTy.create(this,size);
	}

	private static auto __funcliteralTQ(){string r;
		foreach(x; typeQualifiers~["pointer","dynArr"]){ // getConst, getImmutable, getShared, getInout, getPointer, getDynArr. remember to keep getArray in sync.
			r ~= 
`			private Type `~x~`Type;
			final Type get`~upperf(x)~`(){
				if(`~x~`Type) return `~x~`Type;
				return `~x~`Type=get`~upperf(x)~`Impl();
			}
			protected Type get`~upperf(x)~`Impl(){return `~upperf(x)~`Ty.create(this);}
			Type getTail`~upperf(x)~`(){return this;}
			Type in`~upperf(x)~`Context(){return this;}
`;		}
		return r;
	}mixin(__funcliteralTQ());

	final Type applySTC(STC stc){
		auto r = this;
		r = r.applySTC(stc);
		if(stc&STCconst)     r = r.getConst();
		if(stc&STCimmutable) r = r.getImmutable();
		if(stc&STCshared)    r = r.getShared();
		if(stc&STCinout)     r = r.getInout();
		return r;
	}

	Type getHeadUnqual(){return this;} // TODO: make lazy

	override bool implicitlyConvertsTo(Type rhs){
		return this.refConvertsTo(rhs.getHeadUnqual(),0);
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
		bool l2r=this.implicitlyConvertsTo(rhs);
		bool r2l=rhs.implicitlyConvertsTo(this);
		if(l2r ^ r2l){
			if(l2r) return rhs;
			return this;
		}
		return null;
	}

	final protected Type refMostGeneral(Type rhs, int num){ // TODO: merge with above
		if(rhs is this) return this;
		bool l2r=this.refConvertsTo(rhs, num);
		bool r2l=rhs.refConvertsTo(this, num);
		if(l2r ^ r2l){
			if(l2r) return rhs;
			return this;
		}
		return null;
	}

	/* common type computation. TDPL p60
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
			// TODO: more efficient if rhs.getConst() instead of rhs?
			if(num) return getConst().refCombine(rhs.getConst(), 0);
			auto tconst = getTailConst();
			if(this !is tconst) return tconst.refCombine(rhs.getTailConst(), 0);
		}
		return null;
	}

	override IntRange getIntRange(){return IntRange.full(true);}
	override LongRange getLongRange(){return LongRange.full(true);}
}

mixin template Semantic(T) if(is(T==BasicType)){
	override BasicType semantic(Scope sc){
		mixin({
			string r=`switch(op){`;
			foreach(x; basicTypes) r~=`case Tok!"`~x~`": return Type.get!`~x~`();`;
			return r~`default: assert(0);}`;
		}());
	}
	override Type checkVarDecl(Scope sc, VarDecl me){
		if(op!=Tok!"void") return this;
		sc.error(format("%s '%s' has invalid type '%s'", me.kind, me.name, this), me.loc);
		return New!ErrorTy;
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
		 Tok!"ifloat":-1,Tok!"idouble":-1,Tok!"ireal":-1,Tok!"cfloat":-2,Tok!"cdouble":-2,Tok!"creal":-2];

	override BasicType isIntegral(){return strength[op]>=0 && strength[op]<=5 ? this : null;}
	final int bitSize()in{assert(!!isIntegral());}body{
		switch(op){
			case Tok!"bool", Tok!"char", Tok!"byte", Tok!"ubyte":
				return 8;
			case Tok!"wchar", Tok!"short", Tok!"ushort":
				return 16;
			case Tok!"dchar", Tok!"int", Tok!"uint":
				return 32;
			case Tok!"long", Tok!"ulong":
				return 64;
			default: return -1;
		}
	}
	final bool isSigned()in{assert(!!isIntegral());}body{
		switch(op){
			case Tok!"bool", Tok!"ubyte", Tok!"ushort", Tok!"dchar", Tok!"uint", Tok!"ulong":
				return false;
			default: return true;
		}
	}

	override bool implicitlyConvertsTo(Type rhs){
		if(auto bt=rhs.getHeadUnqual().isBasicType()){ // transitive closure of TDPL p44
			if(op == Tok!"void") return false;
			if(strength[op]>=0 && strength[bt.op]>=0) return strength[op]<=strength[bt.op];
			if(strength[bt.op]==-2) return true;
			return strength[op] == -1 && strength[bt.op] == -1; // both must be imaginary
		}
		return false;
	}

	override BasicType combine(Type rhs){
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
			else if(op!=Tok!"creal" && bt.op!=Tok!"creal") return Type.get!idouble();
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
					r~=`case Tok!"`~x~`": return IntRange(`~x~`.min,`~x~`.max,false);`;
				foreach(x;["bool","byte","ubyte","char","short","ushort","wchar","int"])
					r~=`case Tok!"`~x~`": return IntRange(`~x~`.min,`~x~`.max,true);`;
				return r;
			}()~`default: return super.getIntRange();`);
		}
	}
	override LongRange getLongRange(){
		switch(op){
			case Tok!"ulong": return LongRange(ulong.min,ulong.max,false);
			mixin({
				string r;
				foreach(x;["bool","byte","ubyte", "char","short","ushort","wchar","int","dchar","uint","long"])
					r~=`case Tok!"`~x~`": return LongRange(`~x~`.min,`~x~`.max,true);`;
				return r;
			}()~`default: return super.getLongRange();`);
		}
	}
	
}

mixin template Semantic(T) if(is(T==ConstTy)||is(T==ImmutableTy)||is(T==SharedTy)||is(T==InoutTy)){

	private enum qual = T.stringof[0..$-2];

	static Type create(Type next)in{
		assert(next.sstate == SemState.completed);
	}body{
		auto tt = mixin(`next.in`~qual~`Context()`);
		if(tt==next){
			assert(!mixin(`next.`~lowerf(qual)~`Type`));
			auto r = New!T(tt);
			r.ty = tt;
			r.sstate = SemState.completed;
			return r;
		}else return mixin(`tt.get`~qual)();
	}

	invariant(){assert(sstate < SemState.started || ty);}
	Type ty;
	override Type semantic(Scope sc){
		mixin(SemPrlg);
		e=ty=e.typeSemantic(sc);
		sstate = SemState.started;
		Type r;
		mixin(PropErr!q{e});
		static if(is(T==ConstTy)) r=ty.getConst();
		else static if(is(T==ImmutableTy)) r=ty.getImmutable();
		else static if(is(T==SharedTy)) r=ty.getShared();
		else static if(is(T==InoutTy)) r=ty.getInout();
		else static assert(0);
		sstate = SemState.completed;
		return r.semantic(sc);
	}

	override bool implicitlyConvertsTo(Type rhs){
		return getHeadUnqual().implicitlyConvertsTo(rhs.getHeadUnqual());
	}

	override bool refConvertsTo(Type rhs, int num){
		if(this is rhs) return true;
		if(auto d=mixin(`rhs.is`~T.stringof)())
			// const and immutable imply covariance
			static if(is(T==ConstTy) || is(T==ImmutableTy)){
				return mixin(`ty.getTail`~qual)().refConvertsTo(mixin(`d.ty.getTail`~qual)(), 0);
			}else{
				// shared and inout do not imply covariance unless they are also const:
				auto nn = this is getConst() ? 0 : num;
				return mixin(`ty.getTail`~qual)().refConvertsTo(mixin(`d.ty.getTail`~qual)(),nn);
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
		static if(is(T==ConstTy)||is(T==ImmutableTy)){
			auto r = rhs.getConst();
			if(rhs is r) return null;
			return refCombine(r,num);
		}else{
			auto l=getConst(), r=rhs.getConst();
			if(this is l && rhs is r) return null; // avoid infinite recursion
			return l.refCombine(r,num);
		}
	}

	override IntRange getIntRange(){return ty.getIntRange();}
	override LongRange getLongRange(){return ty.getLongRange();}


	override protected Type getConstImpl() {
		static if(is(T==ConstTy)||is(T==ImmutableTy)) return this;
		else{ // (must be SharedTy)
			static if(is(T==SharedTy)) return ty.getConst().getShared();
			else static if(is(T==InoutTy)) return ty.getConst().getInout();
		}
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
			else return ty.getInout().getShared(); // (must be SharedTy)
		}
	}

	override Type getHeadUnqual(){
		if(hunqualType) return hunqualType;
		return hunqualType=mixin(`ty.getHeadUnqual().getTail`~qual~`()`);
	}

	private static string __dgliteralTail(){ // TODO: maybe memoize this?
		string r;
		foreach(q;typeQualifiers){
			r~=
`			override Type getTail`~upperf(q)~`(){
				return ty.getTail`~upperf(q)~`().get`~qual~`();
			}
`;		}
		return r;
	}
	mixin(__dgliteralTail());

	// TODO: maybe memoize this?
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
}

mixin template GetTailOperations(string tail, string puthead){
	static string __dgliteralTailQualified(){// "delegate literals cannot be class members..."
		string r;
		foreach(q;typeQualifiers){
			r~=
`				Type tail`~upperf(q)~`Type;
				override Type getTail`~upperf(q)~`(){
					if(tail`~upperf(q)~`Type) return tail`~upperf(q)~`Type;
					return tail`~upperf(q)~`Type=`~tail~`.get`~upperf(q)~`().`~puthead~`;
			    }
				override Type in`~upperf(q)~`Context(){ // TODO: memoize
					assert(`~tail~`&&1);
					return `~tail~`.in`~upperf(q)~`Context().`~puthead~`;
				}
`;
		}
		return r;
	}
	mixin(__dgliteralTailQualified());
}


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
	override Type semantic(Scope sc){
		mixin(SemPrlg);
		e=ty=e.typeSemantic(sc);
		Type r;
		mixin(PropErr!q{e});
		static if(is(T==ArrayTy)) r=ty.getArray(length);
		else r = mixin("ty.get"~T.stringof[0..$-2]~"()");
		sstate = SemState.completed;
		return r;
	}

	static if(is(T==ArrayTy)){ // static arrays are value types
		// TODO: implement this
	}else{
		// this adds one indirection for pointers and arrays
		override bool refConvertsTo(Type rhs, int num){
			if(auto c=mixin(`rhs.is`~T.stringof)())
				return ty.refConvertsTo(c.ty,num+!is(T==ArrayTy));
			return super.refConvertsTo(rhs,num);
		}
		override Type combine(Type rhs){
			if(auto r = mostGeneral(rhs)) return r;
			auto unqual = rhs.getHeadUnqual();
			return unqual.refCombine(this, 0);
			return null;
		}
		override Type refCombine(Type rhs, int num){
			if(auto c=mixin(`rhs.is`~T.stringof)())
				if(auto d=ty.refCombine(c.ty,num+!is(T==ArrayTy)))
					return mixin(`d.`~puthead);
			return super.refCombine(rhs,num);
		}
	}
	private enum puthead = "get"~(is(T==ArrayTy)?"Array(length)":typeof(this).stringof[0..$-2]~"()");
	mixin GetTailOperations!("ty", puthead);
}

mixin template Semantic(T) if(is(T==NullPtrTy)||is(T==EmptyArrTy)){
	override bool implicitlyConvertsTo(Type rhs){
		rhs = rhs.getHeadUnqual();
		static if(is(T==NullPtrTy)){
			// TODO: add || rhs.isClassTy()
			if(rhs.isPointerTy() || rhs.isDynArrTy()) return true;
		}else{ // EmptyArrTy
			if(rhs.isDynArrTy()) return true;
		}
		if(auto arr = rhs.isArrayTy()) return arr.length == 0;
		return false;
	}
}


mixin template Semantic(T) if(is(T==TypeofExp)){
	override Type semantic(Scope sc){
		mixin(SemPrlg);
		if(sstate == SemState.started){
			sc.error("recursive typeof declaration",loc);
			mixin(ErrEplg);
		}
		sstate = SemState.started;
		e = e.semantic(sc);
		sstate = e.sstate;
		if(sstate == SemState.completed){
			if(!e.type) return Type.get!void(); // TODO: make this unecessary
			return e.type.semantic(sc);
		}
		return this;
	}
}

// statements

mixin template Semantic(T) if(is(T==Statement)){
	override Statement semantic(Scope sc){
		sc.error("unimplemented feature",loc);
		sstate = SemState.error;
		return this;
	}
}

mixin template Semantic(T) if(is(T==EmptyStm)){
	override EmptyStm semantic(Scope sc){
		sstate = SemState.completed;
		return this;
	}
}

mixin template Semantic(T) if(is(T==BlockStm)){
	BlockStm semanticNoScope(Scope sc){
		mixin(SemPrlg);
		auto newstate = SemState.max;
		foreach(ref x;s){
			x=x.semantic(sc);
			newstate = min(newstate, x.sstate);
		}
		sstate = newstate;
		return this;
	}
	
	override BlockStm semantic(Scope sc){
		if(!mysc) mysc = New!BlockScope(sc);
		return semanticNoScope(mysc);
	}
private:
	FunctionScope mysc = null;	
}

mixin template Semantic(T) if(is(T==ForStm)){
	override ForStm semantic(Scope sc){
		mixin(SemPrlg);
		if(!lsc) lsc = New!BlockScope(sc);
		s1=s1.semantic(lsc); e1=e1.semantic(lsc);
		e2=e2.semantic(lsc); s2=s2.semantic(lsc);
		sstate=min(min(s1.sstate,e1.sstate),min(e2.sstate,s2.sstate));
		return this;
	}
private:
	BlockScope lsc;
}

mixin template Semantic(T) if(is(T==ReturnStm)){
	override ReturnStm semantic(Scope sc){
		mixin(SemPrlg);
		e=e.semantic(sc);
		sstate = e.sstate;
		// TODO: match with function return type
		return this;
	}
}

// declarations
mixin template Semantic(T) if(is(T==EmptyDecl)){
	override EmptyDecl presemantic(Scope sc){
		if(sstate == SemState.pre) sstate = SemState.begin;
		return this;
	}
	override EmptyDecl semantic(Scope sc){
		sstate = SemState.completed;
		return this;
	}
}

mixin template Semantic(T) if(is(T==Declaration)){
	Declaration presemantic(Scope sc){ // insert into symbol table, but don't do the heavy processing yet
		if(sstate != SemState.pre) return this;
		sstate = SemState.begin;
		if(!name){sc.error("unimplemented feature",loc); sstate = SemState.error; return this;} // TODO: obvious
		sc.insert(this);
		return this;
	}
	override Declaration semantic(Scope sc){
		mixin(SemPrlg);
		if(sstate==SemState.pre){
			auto ps=presemantic(sc);
			if(ps!is this) return ps.semantic(sc);
		}
		mixin(SemEplg);
	}

}
mixin template Semantic(T) if(is(T==VarDecl)){
	override VarDecl presemantic(Scope sc){return cast(VarDecl)cast(void*)super.presemantic(sc);}

	override VarDecl semantic(Scope sc){
		mixin(SemPrlg);
		if(type){
			type=type.typeSemantic(sc).checkVarDecl(sc,this);
		}else if(init){ // deduce type
			init=init.semantic(sc);
			type=init.type;
			if(type is Type.get!Null()) type = Type.get!(void*)();
			else if(type is Type.get!EmptyArray()) type = Type.get!(void[])();
		}
		if(sstate == SemState.pre) sc.insert(this);
		if(!type||type.sstate==SemState.error)mixin(ErrEplg); // deliberately don't propagate init's semantic 'error' state if possible

		if(auto ty=cast(Type)type){ // TODO: remove cast
			// TODO: quick hack, make prettier
			if(init) init=init.implicitlyConvertTo(ty).semantic(sc);
			type = ty; // TODO: check validity (eg. inout)
		}else assert(0, "type is not a Type!");

		mixin(SemEplg);
	}
}

mixin template Semantic(T) if(is(T==CArrayDecl)){ // TODO: should CArrayDecl inherit VarDecl?
	override VarDecl presemantic(Scope sc){return cast(VarDecl)cast(void*)super.presemantic(sc);}
	override VarDecl semantic(Scope sc){
		mixin(SemPrlg);
		while(postfix !is name){
			assert(!!cast(IndexExp)postfix);
			auto id = cast(IndexExp)cast(void*)postfix;
			postfix = id.e;
			id.e = type;
			type = id;
		}
		sstate = SemState.completed;
		return New!VarDecl(stc, type, name, init).semantic(sc);
	}
}


mixin template Semantic(T) if(is(T==Declarators)){
	override Declaration presemantic(Scope sc){
		if(sstate>SemState.pre) return this;
		foreach(ref x; decls) x=x.presemantic(sc);
		sstate=SemState.begin;
		return this;
	}
	override Declaration semantic(Scope sc){
		if(sstate==SemState.pre) return presemantic(sc).semantic(sc);
		mixin(SemPrlg);
		super.semantic(sc);
		auto newstate=SemState.max;
		foreach(ref x; decls){
			x=x.semantic(sc);
			newstate = min(newstate, x.sstate);
		}
		sstate = newstate;
		return this;
	}
}

abstract class OverloadableDecl: Declaration{ // semantic node
	this(STC stc,Identifier name){super(stc,name);}
	override OverloadableDecl isOverloadableDecl(){return this;}
}

class OverloadSet: Declaration{ // purely semantic node
	this(OverloadableDecl[] args...)in{assert(args.length);}body{
		super(STC.init,args[0].name);
		foreach(d;args) add(d);
		sstate = SemState.begin; // do not insert
	}
	this(Identifier name){super(STC.init,name);}
	void add(OverloadableDecl decl){decls~=decl;}
	override string toString(){return join(map!(to!string)(decls),"\n");}
	override OverloadSet isOverloadSet(){return this;}
private:
	OverloadableDecl[] decls; // TODO: use more efficient data structure
}

mixin template Semantic(T) if(is(T==FunctionDef)){
	FunctionScope fsc;
	override FunctionDef semantic(Scope sc){
		mixin(SemPrlg);
		if(!fsc) fsc = New!FunctionScope(sc);
		if(sstate == SemState.pre) presemantic(sc); // add self to parent scope
		foreach(p; type.params) p.presemantic(fsc); // add parameters to function scope
		foreach(p; type.params){
			p.semantic(fsc);
			sstate = min(sstate, p.sstate);
		}
		bdy.semanticNoScope(fsc);
		sstate = min(sstate, bdy.sstate);
		return this;
	}
}

mixin template Semantic(T) if(is(T==PragmaDecl)){
	override Declaration presemantic(Scope sc){
		if(auto b=bdy.isDeclaration()) bdy=b.presemantic(sc);
		return this;
	}
	override Declaration semantic(Scope sc){
		mixin(SemPrlg);
		sstate = SemState.max;
		if(args.length<1){sc.error("missing arguments to pragma",loc); sstate=SemState.error; return this;}
		if(auto id=args[0].isIdentifier()){
			switch(id.name){
				case "msg":
					if(args.length<2){sstate=SemState.completed; return this;}
					foreach(ref x; args[1..$]){
						x = x.semantic(sc);
						sstate = min(sstate, x.sstate);
					}
					if(sstate == SemState.completed){
						// TODO: interpret!
						import std.stdio;
						foreach(x; args[1..$]){
							if(x.type !is Type.get!string()) stderr.write(x);
							else stderr.write(x);
						}
						stderr.writeln();
						if(bdy){mixin(SemChld!q{bdy});}
						return this;
					}
					if(bdy){mixin(SemChld!q{bdy});}
					return this;
				default: break;

				// for debugging. TODO: remove
				case "__range":
					if(args.length!=2) break;
					args[1]=args[1].semantic(sc);
					import std.stdio;
					auto ty=args[1].type.isIntegral();
					if(ty&&ty.bitSize()<=32) stderr.writeln(args[1].getIntRange());
					stderr.writeln(args[1].getLongRange());
					return this;
			}
		}
		sc.error(format("unrecognized pragma '%s'",args[0].loc.rep),args[0].loc); // TODO: maybe remove this
		return New!EmptyDecl().semantic(sc);
	}
}
