import std.array, std.algorithm, std.range, std.conv;

import lexer, parser, declaration, statement, type;
import scope_, semantic;


enum SemState{
	pre,
	begin,
	fwdRefs,
	completed,
}


abstract class Node{
	Location loc;
	SemState sstate = SemState.begin;
	Node semantic(Scope s)in{assert(sstate>=SemState.begin);}body{ s.error("unimplemented feature",loc); sstate = SemState.completed; return this;}
}

class Expression: Node{ // empty expression if instanced
	int brackets=0;
	override string toString(){return _brk("{}()");}
	protected string _brk(string s){return std.array.replicate("(",brackets)~s~std.array.replicate(")",brackets); return s;}

	Type type;
	Expression semantic(Scope sc){ sc.error("unimplemented feature",loc); sstate = SemState.completed; return this; }
}

class ErrorExp: Expression{
	override string toString(){return _brk("__error");}
}


class LiteralExp: Expression{
	Token lit;
	this(Token literal){lit=literal;} // TODO: suitable contract
	override string toString(){return _brk(lit.toString());}
	Expression semantic(Scope sc){
		sstate = SemState.completed;
		switch(lit.type){ // TODO: remove some boilerplate
			case Tok!"``": //TODO: this needs to have a polysemous type
				type=Type.get!(immutable(char)[])(); break;
			case Tok!"``c":
				type=Type.get!(immutable(char)[])(); break;
				return this;
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
			default: return Expression.semantic(sc);
		}
		return this;
	}
}

class ArrayAssocExp: Expression{
	Expression key;
	Expression value;
	this(Expression k, Expression v){key=k; value=v;}
	override string toString(){return key.toString()~":"~value.toString();}
}

class ArrayLiteralExp: Expression{
	Expression[] lit;
	this(Expression[] literal){lit=literal;}
	override string toString(){return _brk("["~join(map!(to!string)(lit),",")~"]");}
}

class FunctionLiteralExp: Expression{
	FunctionType type;
	BlockStm bdy;
	bool isStatic;
	this(FunctionType ft, BlockStm b, bool s=false){ type=ft; bdy=b; isStatic=s;}
	override string toString(){return _brk((isStatic?"function"~(type&&type.ret?" ":""):type&&type.ret?"delegate ":"")~(type?type.toString():"")~bdy.toString());}
}

class Identifier: Symbol{
	string name;
	alias name this;
	this(string name){ // TODO: make more efficient, this is a bottleneck!
		static string[string] uniq;
		auto n=uniq.get(name,null);
		if(n !is null) this.name = n;
		else this.name = uniq[name] = name;
	}
	override string toString(){return _brk(name);}
	override Symbol semantic(Scope sc){
		meaning=sc.lookup(this);
		return super.semantic(sc);
	}
}

// special symbols that can be used like identifiers in some contexts
class ThisExp: Identifier{
	this(){ super(q{this}); }
}
class SuperExp: Identifier{
	this(){ super(q{super}); }
}
class TildeThisExp: Identifier{
	this(){ super(q{~this}); }
}
class InvariantExp: Identifier{
	this(){ super(q{invariant}); }
}
class DollarExp: Identifier{
	this(){ super(q{$}); }
}

class CastExp: Expression{
	STC stc;
	Expression type,e;
	this(STC ss,Expression tt,Expression exp){stc=ss; type=tt; e=exp;}
	override string toString(){return _brk("cast("~(stc?STCtoString(stc)~(type?" ":""):"")~(type?type.toString():"")~")"~e.toString());}
}
class NewExp: Expression{
	Expression[] a1;
	Expression type;
	Expression[] a2;
	this(Expression[] args1,Expression type,Expression[] args2){a1=args1; this.type=type; a2=args2;}
	override string toString(){
		return _brk("new"~(a1?"("~join(map!(to!string)(a1),",")~") ":" ")~type.toString()~(a2?"("~join(map!(to!string)(a2),",")~")":""));
	}
}
class NewClassExp: Expression{
	Expression[] args;
	ClassDecl class_;
	this(Expression[] a, ClassDecl c)in{assert(c&&c.bdy);}body{args=a; class_=c;}
	override string toString(){
		return "new class("~join(map!(to!string)(args),",")~")"~(class_.parents?" "~join(map!(to!string)(class_.parents),","):"")~class_.bdy.toString();
	}
}
class MixinExp: Expression{
	Expression e;
	this(Expression exp){e=exp;}
	override string toString(){return _brk("mixin("~e.toString()~")");}
}
class ImportExp: Expression{
	Expression e;
	this(Expression exp){e=exp;}
	override string toString(){return _brk("import("~e.toString()~")");}
}
class AssertExp: Expression{
	Expression[] a;
	this(Expression[] args){a = args;}
	override string toString(){return _brk("assert("~join(map!(to!string)(a),",")~")");}
}

class UnaryExp(TokenType op): Expression{
	Expression e;
	this(Expression next){e = next;}
	override string toString(){return _brk(TokChars!op~e.toString());}
}
class PostfixExp(TokenType op): Expression{
	Expression e;
	this(Expression next){e = next;}
	override string toString(){return _brk(e.toString()~TokChars!op);}
}
class IndexExp: Expression{ //e[a...]
	Expression e;
	Expression[] a;
	this(Expression exp, Expression[] args){e=exp; a=args;}
	override string toString(){return _brk(e.toString()~(a.length?'['~join(map!(to!string)(a),",")~']':"[]"));}
}
class SliceExp: Expression{//e[l..r]
	Expression e;
	Expression l,r;
	this(Expression exp, Expression left, Expression right){e=exp; l=left; r=right;}
	override string toString(){return _brk(e.toString()~'['~l.toString()~".."~r.toString()~']');}
}
class CallExp: Expression{
	Expression e;
	Expression[] args;
	this(Expression exp, Expression[] args){e=exp; this.args=args;}
	override string toString(){return _brk(e.toString()~(args.length?'('~join(map!(to!string)(args),",")~')':"()"));}

	override Expression semantic(Scope sc){
		if(sstate == SemState.completed) return this;
		e.semantic(sc); // semantically analyze the left part
		auto newstate = e.sstate;
		foreach(ref x;args){
			x = x.semantic(sc);
			newstate = min(newstate, x.sstate);
		}
		sstate = newstate;
		return this;
	}
}
class TemplateInstanceExp: Expression{
	Expression e;
	Expression[] args;
	this(Expression exp, Expression[] a){e=exp; args=a;}
	override string toString(){return _brk(e.toString()~"!"~(args.length!=1?"(":"")~join(map!(to!string)(args),",")~(args.length!=1?")":""));}
}
class BinaryExp(TokenType op): Expression{
	Expression e1, e2;
	this(Expression left, Expression right){e1=left; e2=right;}
	override string toString(){
		static if(op==Tok!"in"||op==Tok!"is"||op==Tok!"!in"||op==Tok!"!is") return _brk(e1.toString() ~ " "~TokChars!op~" "~e2.toString());
		else return _brk(e1.toString() ~ TokChars!op ~ e2.toString());
	}
	//override string toString(){return e1.toString() ~ " "~ e2.toString~TokChars!op;} // RPN
}

class TernaryExp: Expression{
	Expression e1, e2, e3;
	this(Expression cond, Expression left, Expression right){e1=cond; e2=left; e3=right;}
	override string toString(){return _brk(e1.toString() ~ '?' ~ e2.toString() ~ ':' ~ e3.toString());}
}

enum WhichIsExp{
	type,
	implicitlyConverts,
	isEqual
}
class IsExp: Expression{
	WhichIsExp which;
	Expression type;
	Identifier ident;
	Expression typeSpec;
	TokenType typeSpec2;
	TemplateParameter[] tparams;
	this(WhichIsExp w, Expression t, Identifier i, Expression ts, TokenType ts2, TemplateParameter[] tp)
		in{assert(t&&(which==WhichIsExp.type||typeSpec||typeSpec2!=Tok!"")); assert(which!=WhichIsExp.type||!tparams);}body{
		which=w; type=t; ident=i; typeSpec=ts;
		typeSpec2=ts2; tparams=tp;
	}
	override string toString(){
		return "is("~type.toString()~(ident?" "~ident.toString():"")~(which!=WhichIsExp.type?(which==WhichIsExp.isEqual?"==":": ")~
			(typeSpec?typeSpec.toString():TokenTypeToString(typeSpec2))~(tparams?","~join(map!(to!string)(tparams),","):""):"")~")";
	}
}

class TypeidExp: Expression{
	Expression e;
	this(Expression exp)in{assert(exp&&1);}body{e=exp;}
	override string toString(){return "typeid("~e.toString~")";}
}

class TraitsExp: Expression{
	Expression[] args;
	this(Expression[] a){args=a;}
	override string toString(){return "__traits("~join(map!(to!string)(args),",")~")";}
}
class DeleteExp: Expression{ // why is this an expression and throw a statement? wtf...
	Expression e;
	this(Expression exp)in{assert(exp&&1);}body{e=exp;}
	override string toString(){return "delete "~e.toString();}
}

abstract class InitializerExp: Expression{}
class VoidInitializerExp: InitializerExp{
	override string toString(){return "void";}
}

class StructAssocExp: Expression{
	Identifier key;
	Expression value;
	this(Identifier k, Expression v){key=k; value=v;}
	override string toString(){return key.toString()~":"~value.toString();}
}
class ArrayInitAssocExp: Expression{
	Expression key;
	Expression value;
	this(Expression k, Expression v){key=k; value=v;}
	override string toString(){return key.toString()~":"~value.toString();}
}
class StructLiteralExp: InitializerExp{
	Expression[] args;
	this(Expression[] a){args=a;}
	override string toString(){return "{"~join(map!(to!string)(args),",")~"}";}
}

// for if(auto x=foo()){} etc
class ConditionDeclExp: Expression{
	STC stc;
	Expression type;
	Identifier name;
	Expression init;
	this(STC s, Expression t, Identifier n, Expression i){stc=s; type=t; name=n; init=i;}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~(type?type.toString()~" ":"")~name.toString()~(init?"="~init.toString():"");}
}
