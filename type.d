import std.array, std.algorithm, std.range, std.conv, std.string;

import lexer, parser, util;
import semantic, scope_, visitors;

class Type: Expression{ //Types can be part of Expressions and vice-versa
	override string toString(){return "Type";}

	static BasicType get(T)() if(isBasicType!T){
		if(uniqueType!T) return uniqueType!T;
		return uniqueType!T=New!BasicType(Tok!(T.stringof));
	}

	static Type get(T: T[])(){
		if(uniqueType!(T[])) return uniqueType!(T[]);
		return uniqueType!(T[])=get!T.getDynArr();
	}

	static Type get(T: const(T))() if(!is(typeof({T x; x=T.init;}))&&!isBasicType!T){
		if(uniqueType!(const(T))) return uniqueType!(const(T));
		return uniqueType!(const(T))=get!T.getConst();		
	}
	static Type get(T: immutable(T))(){
		if(uniqueType!(immutable(T))) return uniqueType!(immutable(T));
		return uniqueType!(immutable(T))=get!T.getImmutable();		
	}
	static Type get(T: shared(T))(){
		if(uniqueType!(shared(T))) return uniqueType!(shared(T));
		return uniqueType!(shared(T))=get!T.getShared();		
	}

	static Type get(T)() if(!isBasicType!T){
		if(uniqueType!T) return uniqueType!T;
		pragma(msg,"TODO: fix. do not know how to get type "~T.stringof);
		return uniqueType!T=New!BasicType(Tok!"void"); // TODO: improve		
	}

	static Type get(T:Null)(){ // typeof(null)
		if(uniqueType!T) return uniqueType!T;
		return uniqueType!T=New!NullPtrTy();
	}

	static Type get(T:EmptyArray)(){ // typeof([])
		if(uniqueType!T) return uniqueType!T;
		return uniqueType!T=New!EmptyArrTy();
	}

	final{
	Type getPointer(){
		if(ptrType) return ptrType;
		return ptrType=New!PointerTy(this);
	}

	Type getDynArr(){
		if(darrType) return darrType;
		return darrType=New!DynArrTy(this);
	}

	Type getArray(long size){
		if(auto r=arrType.get(size,null)) return r;
		return arrType[size]=New!ArrayTy(this,size);
	}

	Type getConst(){
		if(constType) return constType;
		return constType=New!ConstTy(this);
	}
	Type getImmutable(){
		if(immutableType) return immutableType;
		return immutableType=New!ImmutableTy(this);
	}
	Type getShared(){
		if(sharedType) return sharedType;
		return sharedType=New!SharedTy(this);
	}
	Type getInout(){
		if(inoutType) return inoutType;
		return inoutType=New!InoutTy(this);
	}
	}

	override Type isType(){return this;}

	mixin DownCastMethods!(
	    DynArrTy,
	);

	BasicType isIntegral(){return null;}
	
	bool implicitlyConvertsTo(Type){
		return false;
	}
	Type combine(Type rhs){
		if(rhs is this) return this;
		bool l2r=implicitlyConvertsTo(rhs);
		bool r2l=rhs.implicitlyConvertsTo(this);
		if(l2r ^ r2l){
			if(l2r) return rhs;
			return this;
		}
		return null;
	}

	mixin Visitors;

private:
	static template uniqueType(T){
		static if(isBasicType!T) BasicType uniqueType;
		else Type uniqueType;
	}
	PointerTy ptrType;
	DynArrTy darrType;
	ArrayTy[long] arrType;
	ConstTy constType;
	ImmutableTy immutableType;
	SharedTy sharedType;
	InoutTy inoutType;
}

class ErrorTy: Type{
	this(){ sstate = SemState.error; }
	override string toString(){return _brk("__error");}

	mixin Visitors;
}


struct Null{} // dummy type. TODO: make Type.get accept a null literal
struct EmptyArray{}
struct Struct{}
struct Class{}

class NullPtrTy: Type{ // typeof(null)
	this(){sstate = SemState.completed;}
	override string toString(){return "nullptr_t";}
}

class EmptyArrTy: Type{ // typeof([])
	this(){sstate = SemState.completed;}
	override string toString(){return "emptyarr_t";} // TODO: fix name for this type
}


enum VarArgs{
	none,
	cStyle,
	dStyle,
}
class FunctionType: Type{
	STC stc;
	Expression ret;
	Parameter[] params;
	VarArgs vararg;
	this(STC stc, Expression retn,Parameter[] plist,VarArgs va){this.stc=stc; ret=retn; params=plist; vararg=va;}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~(ret?ret.toString():"")~pListToString();}
	string pListToString(){
		return "("~join(map!(to!string)(params),",")~(vararg==VarArgs.cStyle?(params.length?",":"")~"...)":vararg==VarArgs.dStyle?"...)":")");
	}
}

class FunctionPtr: Type{
	FunctionType ft;
	this(FunctionType ft)in{assert(ft !is null&&ft.ret !is null);}body{this.ft=ft;}
	override string toString(){return ft.ret.toString()~" function"~ft.pListToString()~(ft.stc?" "~STCtoString(ft.stc):"");}
}

class DelegateType: Type{
	FunctionType ft;
	this(FunctionType ft)in{assert(ft !is null&&ft.ret !is null);}body{this.ft=ft;}
	override string toString(){return ft.ret.toString()~" delegate"~ft.pListToString()~(ft.stc?" "~STCtoString(ft.stc):"");}
}

class TypeofExp: Type{
	Expression e;
	this(Expression exp){e=exp;}
	override string toString(){return _brk("typeof("~e.toString()~")");}

	mixin Visitors;
}
class TypeofReturnExp: Type{
	override string toString(){return _brk("typeof(return)");}
}

enum basicTypes=["bool","byte","ubyte","short","ushort","int","uint","long","ulong","char","wchar","dchar","float","double","real","ifloat","idouble","ireal","cfloat","cdouble","creal","void"];

template isBasicType(T){
	enum isBasicType=canFind(basicTypes,T.stringof);
}

final class BasicType: Type{
	TokenType op;
	this(TokenType op)in{assert(strength[op]||op==Tok!"void");}body{this.op=op; sstate=SemState.completed;}
	override string toString(){return _brk(TokenTypeToString(op));}
	
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

	override bool implicitlyConvertsTo(Type rhs){ // like TDPL p. 44 but transitive.
		if(auto bt=cast(BasicType)rhs){
			if(strength[op]>=0 && strength[bt.op]>=0) return strength[op]<=strength[bt.op];
			if(strength[bt.op]==-2) return true;
		}
		return false;
	}

	override BasicType combine(Type rhs){
		if(this is rhs) return this;
		if(auto bt=cast(BasicType)rhs){
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

	mixin Visitors;
}

class PointerTy: Type{
	Expression e;
	this(Expression next)in{assert(next&&1);}body{e=next;}
	override string toString(){return _brk(e.toString()~'*');}

	mixin Visitors;
}

class DynArrTy: Type{ //purely semantic node
	Expression e;
	this(Expression next)in{assert(next&&1);}body{e=next;}
	override string toString(){return _brk(e.toString()~"[]");}
	override DynArrTy isDynArrTy(){return this;}

	mixin Visitors;
}

// class SliceTy: DynArrTy{ //purely semantic node
// 	this(Expression next)in{assert(next&&1);}body{super(next);}
// 	override SliceTy isSliceTy(){return this;}

// 	mixin Visitors;
// }

class ArrayTy: Type{ //purely semantic node
	Expression e;
	long size;
	this(Expression next, long siz)in{assert(next&&1);}body{e=next; size=siz;}
	override string toString(){return _brk(e.toString()~'['~to!string(size)~']');}

	mixin Visitors;
}


template QualifiedType(TokenType op){
	static if(op==Tok!"const") alias ConstTy QualifiedType;
	else static if(op==Tok!"immutable") alias ImmutableTy QualifiedType;
	else static if(op==Tok!"shared") alias SharedTy QualifiedType;
	else static if(op==Tok!"inout") alias SharedTy QualifiedType;
}

class ConstTy: Type{
	Expression e;
	this(Expression type){e=type;}
	//override string toString(){return _brk(TokChars!op~(!type.brackets?" ":"")~type.toString());}
	override string toString(){return _brk("const("~e.toString()~')');}

	mixin Visitors;	
}

class ImmutableTy: Type{
	Expression e;
	this(Expression type){e=type;}
	//override string toString(){return _brk(TokChars!op~(!type.brackets?" ":"")~type.toString());}
	override string toString(){return _brk("immutable("~e.toString()~')');}

	mixin Visitors;	
}

class SharedTy: Type{
	Expression e;
	this(Expression type){e=type;}
	//override string toString(){return _brk(TokChars!op~(!type.brackets?" ":"")~type.toString());}
	override string toString(){return _brk("shared("~e.toString()~')');}

	mixin Visitors;	
}

class InoutTy: Type{
	Expression e;
	this(Expression type){e=type;}
	//override string toString(){return _brk(TokChars!op~(!type.brackets?" ":"")~type.toString());}
	override string toString(){return _brk("inout("~e.toString()~')');}

	mixin Visitors;	
}

//-----------------

class PolysemousType: Type{} // TODO: Implement