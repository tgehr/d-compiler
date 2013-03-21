import std.array, std.algorithm, std.range, std.conv;

import lexer, parser, util;

alias GCAlloc.New New;

class Type: Expression{ //Types can be part of Expressions and vice-versa
	override string toString(){return "Type";}

	static Type get(T)(){return New!BasicType(Tok!"void");} // TODO: improve
}

struct Null{} // dummy type. TODO: make Type.get accept a null literal

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
}
class TypeofReturnExp: Type{
	override string toString(){return _brk("typeof(return)");}
}
class BasicType: Type{
	TokenType type;
	this(TokenType type){this.type=type;}
	override string toString(){return _brk(TokenTypeToString(type));}
}

class Pointer: Type{
	Expression e;
	this(Expression next)in{assert(next&&1);}body{e=next;}
	override string toString(){return _brk(e.toString()~'*');}
}

class QualifiedType(TokenType op): Type{
	Expression type;
	this(Expression type){this.type=type;}
	override string toString(){return _brk(TokChars!op~(!type.brackets?" ":"")~type.toString());}
}


//-----------------

class PolysemousType: Type{} // TODO: Implement