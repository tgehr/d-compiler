import std.array, std.algorithm, std.range, std.conv, std.string;

import lexer, parser, util;
import semantic, scope_, visitors;

enum basicTypes=["bool","byte","ubyte","short","ushort","int","uint","long","ulong","char","wchar","dchar","float","double","real","ifloat","idouble","ireal","cfloat","cdouble","creal","void"];

template isBasicType(T){
	enum isBasicType=canFind(basicTypes,T.stringof);
}

class Type: Expression{ //Types can be part of Expressions and vice-versa
	override string toString(){return "Type";}

	static Type get(T)() if(isBasicType!T){
		if(uniqueType!T) return uniqueType!T;
		return uniqueType!T=New!BasicType(Tok!(T.stringof));
	}

	static Type get(T: T[])(){
		if(uniqueType!(T[])) return uniqueType!(T[]);
		return uniqueType!(T[])=get!T.getSlice();
	}

	static Type get(T: const(T))() if(!is(typeof({T x; x=T.init;}))&&!isBasicType!T){
		import std.stdio;writeln(T.stringof);
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
		import std.stdio;writeln("TODO: fix. do not know how to get type "~T.stringof);
		return uniqueType!T=New!BasicType(Tok!"void"); // TODO: improve		
	}

	final{
	Type getPointer(){
		if(ptrType) return ptrType;
		return ptrType=New!PointerTy(this);
	}

	Type getSlice(){
		if(slcType) return slcType;
		return slcType=New!SliceTy(this);
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

	//bool implicitlyConvertsTo(){...}
	Type combine(Type rhs){
		if(rhs is this) return this;
		return null;
	}

	Type intPromote(){
		return this;
	}

	mixin Visitors;

private:
	static template uniqueType(T){Type uniqueType;}
	PointerTy ptrType;
	SliceTy slcType;
	ArrayTy[long] arrType;
	ConstTy constType;
	ImmutableTy immutableType;
	SharedTy sharedType;
	InoutTy inoutType;
}

struct Null{} // dummy type. TODO: make Type.get accept a null literal
struct Struct{}
struct Class{}

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
final class BasicType: Type{
	TokenType type;
	this(TokenType type){this.type=type; sstate=SemState.completed;}
	override string toString(){return _brk(TokenTypeToString(type));}

	override BasicType intPromote(){
		switch(type){
			case Tok!"bool", Tok!"byte", Tok!"char":
			case Tok!"short", Tok!"wchar":
			case Tok!"ubyte", Tok!"ushort":
				return Type.get!int();
			case Tok!"dchar":
				return Type.get!uint();
			default:
				return this;
		}
	}

	mixin Visitors;
}

class PointerTy: Type{
	Expression e;
	this(Expression next)in{assert(next&&1);}body{e=next;}
	override string toString(){return _brk(e.toString()~'*');}

	mixin Visitors;
}

class SliceTy: Type{ //purely semantic node
	Expression e;
	this(Expression next)in{assert(next&&1);}body{e=next;}
	override string toString(){return _brk(e.toString()~"[]");}

	mixin Visitors;
}

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