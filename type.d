import std.array, std.algorithm, std.range, std.conv, std.string;

import lexer, parser, util;
import semantic, scope_, vrange, visitors;


class Type: Expression{ //Types can be part of Expressions and vice-versa
	this(){type = get!void();}
	private this(int){type = this;}

	override string toString(){return "Type";}
	override @property string kind(){return "type";}

	static BasicType get(T)() if(.isBasicType!T){
		if(uniqueType!T) return uniqueType!T;
		return uniqueType!T=New!BasicType(Tok!(T.stringof));
	}

	static Type get(T: T*)(){
		if(uniqueType!(T*)) return uniqueType!(T*);
		return uniqueType!(T*)=get!T().getPointer();
	}

	static Type get(T: T[])(){
		if(uniqueType!(T[])) return uniqueType!(T[]);
		return uniqueType!(T[])=get!T().getDynArr();
	}

	static Type get(T: T[N], ulong N)(){
		if(uniqueType!(T[N])) return uniqueType!(T[N]);
		return uniqueType!(T[N])=get!T().getArray(N);
	}

	static Type get(T: const(T))() if(!is(typeof({T x; x=T.init;}))&&!.isBasicType!T){
		if(uniqueType!(const(T))) return uniqueType!(const(T));
		return uniqueType!(const(T))=get!T().getConst();		
	}
	static Type get(T: immutable(T))(){
		if(uniqueType!(immutable(T))) return uniqueType!(immutable(T));
		return uniqueType!(immutable(T))=get!T().getImmutable();
	}
	static Type get(T: shared(T))(){
		if(uniqueType!(shared(T))) return uniqueType!(shared(T));
		return uniqueType!(shared(T))=get!T().getShared();
	}
	static Type get(T: inout(T))(){
		if(uniqueType!(inout(T))) return uniqueType!(inout(T));
		return uniqueType!(inout(T))=get!T().getInout();
	}

	static Type get(T)() if(!.isBasicType!T){
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

	static Type get(T:Size_t)(){ // typeof((new int[]).length)
		enum _32bit = true; // TODO: make parameterizable
		if(_32bit) return get!uint();
		else return get!ulong();
	}


	mixin DownCastMethod;
	mixin DownCastMethods!(
		BasicType,
		QualifiedTy,
		ConstTy,
		ImmutableTy,
		SharedTy,
		InoutTy,
		PointerTy,
		DynArrTy,
		ArrayTy,
		FunctionTy,
	);
	
	mixin Visitors;

protected:
	static template uniqueType(T){
		static if(.isBasicType!T) BasicType uniqueType;
		else Type uniqueType;
	}
	Type[long] arrType;
}

class ErrorTy: Type{
	this(){ sstate = SemState.error; }
	override string toString(){return _brk("__error");}

	mixin Visitors;
}


// dummy types:
struct Null{}
struct EmptyArray{}
struct Struct{}
struct Class{}

struct Size_t{}

class NullPtrTy: Type{ // typeof(null)
	this(){sstate = SemState.completed;}
	override string toString(){return "typeof(null)";}

	mixin Visitors;
}

class EmptyArrTy: Type{ // typeof([])
	this(){sstate = SemState.completed;}
	override string toString(){return "typeof([])";}
}


enum VarArgs{
	none,
	cStyle,
	dStyle,
}
class FunctionTy: Type{
	STC stc;
	Expression ret;
	Type retTy;
	Parameter[] params;
	VarArgs vararg;
	this(STC stc, Expression retn,Parameter[] plist,VarArgs va){this.stc=stc; ret=retn; params=plist; vararg=va;}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~(ret?ret.toString():"")~pListToString();}
	string pListToString(){
		return "("~join(map!(to!string)(params),",")~(vararg==VarArgs.cStyle?(params.length?",":"")~"...)":vararg==VarArgs.dStyle?"...)":")");
	}

	mixin DownCastMethod;
	mixin Visitors;
}

class FunctionPtr: Type{
	FunctionTy ft;
	this(FunctionTy ft)in{assert(ft !is null&&ft.ret !is null);}body{this.ft=ft;}
	override string toString(){return ft.ret.toString()~" function"~ft.pListToString()~(ft.stc?" "~STCtoString(ft.stc):"");}

	mixin Visitors;
}

class DelegateTy: Type{
	FunctionTy ft;
	this(FunctionTy ft)in{assert(ft !is null&&ft.ret !is null);}body{this.ft=ft;}
	override string toString(){return ft.ret.toString()~" delegate"~ft.pListToString()~(ft.stc?" "~STCtoString(ft.stc):"");}

	mixin Visitors;

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
	this(TokenType op)in{assert(strength[op]||op==Tok!"void");}body{
		this.op=op; sstate=SemState.completed;
		if(op==Tok!"void") super(0);
		else super();
	}
	override string toString(){return _brk(TokenTypeToString(op));}

	mixin DownCastMethod;
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
	ulong length;
	this(Expression next, long len)in{assert(next&&1);}body{e=next; length=len;}
	override string toString(){return _brk(e.toString()~'['~to!string(length)~']');}
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

	mixin DownCastMethod;
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

