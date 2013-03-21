import std.array, std.algorithm, std.range, std.conv, std.string;

import lexer, parser, util;
import semantic, scope_, visitors;


class Type: Expression{ //Types can be part of Expressions and vice-versa
	this(){type = this;}

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

	override Type isType(){return this;}

	mixin DownCastMethods!(
		ConstTy,
		ImmutableTy,
		SharedTy,
		InoutTy,
		PointerTy,
		DynArrTy,
		ArrayTy,
	);

	BasicType isIntegral(){return null;}
	

	mixin Visitors;

protected:
	static template uniqueType(T){
		static if(isBasicType!T) BasicType uniqueType;
		else Type uniqueType;
	}
	Type[long] arrType;
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
	override string toString(){return "null_t";}
}

class EmptyArrTy: Type{ // typeof([])
	this(){sstate = SemState.completed;}
	override string toString(){return "emptyarray_t";}
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

	mixin Visitors;
}

class PointerTy: Type{
	Expression e;
	this(Expression next)in{assert(next&&1);}body{e=next;}
	override string toString(){return _brk(e.toString()~'*');}
	override PointerTy isPointerTy(){return this;}

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
	override ArrayTy isArrayTy(){return this;}

	mixin Visitors;
}


template QualifiedType(TokenType op){
	static if(op==Tok!"const") alias ConstTy QualifiedType;
	else static if(op==Tok!"immutable") alias ImmutableTy QualifiedType;
	else static if(op==Tok!"shared") alias SharedTy QualifiedType;
	else static if(op==Tok!"inout") alias InoutTy QualifiedType;
}

class QualifiedTy: Type{
	Expression e;
}

class ConstTy: QualifiedTy{
	this(Expression type){e=type;}
	override string toString(){return _brk("const("~e.toString()~')');}
	override ConstTy isConstTy(){return this;}

	mixin Visitors;	
}

class ImmutableTy: QualifiedTy{
	this(Expression type){e=type;}
	override string toString(){return _brk("immutable("~e.toString()~')');}
	override ImmutableTy isImmutableTy(){return this;}

	mixin Visitors;	
}

class SharedTy: QualifiedTy{
	this(Expression type){e=type;}
	override string toString(){return _brk("shared("~e.toString()~')');}
	override SharedTy isSharedTy(){return this;}

	mixin Visitors;	
}

class InoutTy: QualifiedTy{
	this(Expression type){e=type;}
	override string toString(){return _brk("inout("~e.toString()~')');}
	override InoutTy isInoutTy(){return this;}

	mixin Visitors;	
}

//-----------------

class PolysemousType: Type{} // TODO: Implement