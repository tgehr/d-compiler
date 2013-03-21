// Written in the D programming language.

import std.array, std.algorithm, std.range, std.conv, std.string;

import lexer, parser, util;
import semantic, scope_, vrange, visitors;

import analyze;

import std.traits : Unqual;

class Type: Expression{ //Types can be part of Expressions and vice-versa
	this(){type = get!void();}
	private this(int){type = this;} // break infinite recursion for 'void'

	override string toString(){return "Type";}
	override @property string kind(){return "type";}

	static BasicType get(T)() if(.isBasicType!T){
		if(uniqueType!T) return uniqueType!T;
		uniqueType!T=New!BasicType(Tok!(T.stringof));
		uniqueType!T.sstate = SemState.completed;
		return uniqueType!T;
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

	static Type get(T: const(U),U)()if(!is(T==U)){
		if(uniqueType!T) return uniqueType!T;
		return uniqueType!T=get!U().getConst();		
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

	static Type get(T:typeof(null))(){
		if(uniqueType!T) return uniqueType!T;
		return uniqueType!T=New!NullPtrTy();
	}

	static Type get(T:EmptyArray)(){ // typeof([])
		if(uniqueType!T) return uniqueType!T;
		return uniqueType!T=New!EmptyArrTy();
	}

	static Type get(T:Size_t)(){ // typeof((new int[]).length)
		if(Size_t.size==4) return get!uint();
		else if(Size_t.size==8) return get!ulong();
		else assert(0,"TODO: gracefully melt down");
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
		DelegateTy,
		AggregateTy,
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
//struct Null{}
struct EmptyArray{}
struct Struct{}
struct Class{}

struct Size_t{
	static int size = 8;
	static @property string suffix(){
		return size==4?"U":size==8?"LU":"";
	}
}

class NullPtrTy: Type{ // typeof(null)
	this(){sstate = SemState.completed;}
	override string toString(){return "typeof(null)";}

	mixin Visitors;
}

class EmptyArrTy: Type{ // typeof([])
	this(){sstate = SemState.completed;}
	override string toString(){return "typeof([])";}

	mixin Visitors;
}


enum VarArgs{
	none,
	cStyle,
	dStyle,
}
class FunctionTy: Type{
	STC stc;
	Expression rret;
	Type ret;
	Parameter[] params;
	VarArgs vararg;
	this(STC stc, Expression retn,Parameter[] plist,VarArgs va){this.stc=stc; rret=retn; params=plist; vararg=va;}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~(rret&&!ret?rret.toString():ret?ret.toString():"")~pListToString();}
	string pListToString(){
		return "("~join(map!(to!string)(params),",")~(vararg==VarArgs.cStyle?(params.length?",":"")~"...)":vararg==VarArgs.dStyle?"...)":")")~STCtoString(stc);
	}

	mixin DownCastMethod;
	mixin Visitors;
}

/+class FunctionPtr: Type{ // merged into PointerTy. TODO: invariant ft.rret !is null
	FunctionTy ft;
	this(FunctionTy ft)in{assert(ft !is null&&ft.rret !is null);}body{this.ft=ft;}
	override string toString(){return ft.rret.toString()~" function"~ft.pListToString()~(ft.stc?" "~STCtoString(ft.stc):"");}

	mixin Visitors;
}+/

class DelegateTy: Type{
	FunctionTy ft;
	this(FunctionTy ft)in{assert(ft !is null&&(ft.ret !is null||ft.rret !is null));}body{this.ft=ft;}
	override string toString(){return (ft.rret&&!ft.ret?ft.rret.toString():ft.ret?ft.ret.toString:"auto")~" delegate"~ft.pListToString();}

	mixin DownCastMethod;
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

enum integralTypes = ["bool","byte","ubyte","short","ushort","int","uint","long","ulong","char","wchar","dchar"];
enum basicTypes = integralTypes~["float","double","real","ifloat","idouble","ireal","cfloat","cdouble","creal","void"];


template isBasicType(T){
	enum isBasicType=canFind(basicTypes,T.stringof);
}

int basicTypeBitSize(TokenType op){
	switch(op){
		case Tok!"void":
		case Tok!"bool", Tok!"char", Tok!"byte", Tok!"ubyte":
			return 8;
		case Tok!"wchar", Tok!"short", Tok!"ushort":
			return 16;
		case Tok!"dchar", Tok!"int", Tok!"uint":
			return 32;
		case Tok!"long", Tok!"ulong":
			return 64;
		case Tok!"float", Tok!"ifloat":
			return 32;
		case Tok!"double", Tok!"idouble":
			return 64;
		case Tok!"real", Tok!"ireal":
			return 96; // TODO: this is architecture-dependent
		case Tok!"cfloat": return 64;
		case Tok!"cdouble": return 128;
		case Tok!"creal": return 192; // TODO: verify
		default: return -1;
	}
}
bool basicTypeIsSigned(TokenType op){
	switch(op){
		case Tok!"bool", Tok!"ubyte", Tok!"ushort", Tok!"dchar", Tok!"uint", Tok!"ulong":
				return false;
		default: return true;
	}
}


final class BasicType: Type{
	TokenType op;
	this(TokenType op)in{assert(strength[op]||op==Tok!"void");}body{
		this.op=op;
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
	override string toString(){
		if(auto tt=e.isType())if(auto ft=tt.isFunctionTy()) return (ft.rret&&!ft.ret?ft.rret.toString():ft.ret?ft.ret.toString():"auto")~" function"~ft.pListToString();
		return _brk(e.toString()~'*');
	}
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

class AggregateTy: Type{
	AggregateDecl decl;
	this(AggregateDecl decl){ this.decl = decl; sstate = SemState.completed; }

	mixin DownCastMethod;
	mixin Visitors;
}