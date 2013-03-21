import std.array, std.algorithm, std.range, std.conv, std.string;

import lexer, parser, declaration, statement, type;
import scope_, semantic, visitors, vrange, util;


abstract class Node{
	Location loc;

	abstract @property string kind();

	mixin DownCastMethods!(
		Declaration,
		//Statement,
		//Expression,
	);

	mixin Visitors;
}


abstract class Expression: Node{
	int brackets=0;
	override string toString(){return _brk("{}()");}
	protected string _brk(string s){return std.array.replicate("(",brackets)~s~std.array.replicate(")",brackets); return s;}

	override @property string kind(){return "expression";}

	mixin DownCastMethods!(
		Identifier,
		Type,
	);

	mixin Visitors;
}

class ErrorExp: Expression{
	this(){sstate = SemState.error;}
	override string toString(){return _brk("__error");}

	mixin Visitors;
}

class StubExp: Expression{
	this(Type type)in{assert(type.sstate==SemState.completed);}body{this.type = type;}
}


class LiteralExp: Expression{
	Token lit;
	this(Token literal){lit=literal;} // TODO: suitable contract
	override string toString(){return _brk(lit.toString());}
	override @property string kind(){return "constant";}

	mixin Visitors;
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

	mixin Visitors;
}

class FunctionLiteralExp: Expression{
	FunctionTy fty;
	BlockStm bdy;
	bool isStatic;
	this(FunctionTy ft, BlockStm b, bool s=false){ fty=ft; bdy=b; isStatic=s;}
	override string toString(){return _brk((isStatic?"function"~(fty&&fty.rret?" ":""):fty&&fty.rret?"delegate ":"")~(fty?fty.toString():"")~bdy.toString());}

	mixin Visitors;
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
	override @property string kind(){return meaning?super.kind:"identifier";}

	override Identifier isIdentifier(){return this;}

	mixin Visitors;
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
	Expression e; Expression ty;
	this(STC ss,Expression tt,Expression exp){stc=ss; ty=tt; e=exp;}
	override string toString(){return _brk("cast("~(stc?STCtoString(stc)~(ty?" ":""):"")~(ty?ty.toString():"")~")"~e.toString());}

	mixin Visitors;
}
class NewExp: Expression{
	Expression[] a1;
	Expression ty;
	Expression[] a2;
	this(Expression[] args1,Expression type,Expression[] args2){a1=args1; ty=type; a2=args2;}
	override string toString(){
		return _brk("new"~(a1?"("~join(map!(to!string)(a1),",")~") ":" ")~ty.toString()~(a2?"("~join(map!(to!string)(a2),",")~")":""));
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
class InstanceNewExp: Expression{
	Expression inst;
	Expression nexp;
	this(Expression instance, Expression newexp)in{assert(instance&&newexp);}body{
		inst=instance, nexp=newexp;
	}
	override string toString(){return inst.toString()~'.'~nexp.toString();}
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
	static if(op==Tok!"&") override @property string kind(){return "address";}
	
	mixin Visitors;
}
class PostfixExp(TokenType op): Expression{
	Expression e;
	this(Expression next){e = next;}
	override string toString(){return _brk(e.toString()~TokChars!op);}

	mixin Visitors;
}
class IndexExp: Expression{ //e[a...]
	Expression e;
	Expression[] a;
	this(Expression exp, Expression[] args){e=exp; a=args;}
	override string toString(){return _brk(e.toString()~(a.length?'['~join(map!(to!string)(a),",")~']':"[]"));}

	mixin Visitors;
}
class SliceExp: Expression{//e[l..r]
	Expression e;
	Expression l,r;
	this(Expression exp, Expression left, Expression right){e=exp; l=left; r=right;}
	override string toString(){return _brk(e.toString()~'['~l.toString()~".."~r.toString()~']');}

	mixin Visitors;
}
class CallExp: Expression{
	Expression e;
	Expression[] args;
	this(Expression exp, Expression[] args){e=exp; this.args=args;}
	override string toString(){return _brk(e.toString()~(args.length?'('~join(map!(to!string)(args),",")~')':"()"));}

	override @property string kind(){return "function call";} // TODO: 'struct literal'

	mixin Visitors;
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

	mixin Visitors;
}

class TernaryExp: Expression{
	Expression e1, e2, e3;
	this(Expression cond, Expression left, Expression right){e1=cond; e2=left; e3=right;}
	override string toString(){return _brk(e1.toString() ~ '?' ~ e2.toString() ~ ':' ~ e3.toString());}

	mixin Visitors;
}

enum WhichIsExp{
	type,
	implicitlyConverts,
	isEqual
}
class IsExp: Expression{
	WhichIsExp which;
	Expression ty;
	Identifier ident;
	Expression tySpec;
	TokenType tySpec2;
	TemplateParameter[] tparams;
	this(WhichIsExp w, Expression t, Identifier i, Expression ts, TokenType ts2, TemplateParameter[] tp)
		in{assert(t&&(which==WhichIsExp.type||tySpec||tySpec2!=Tok!"")); assert(which!=WhichIsExp.type||!tparams);}body{
		which=w; ty=t; ident=i; tySpec=ts;
		tySpec2=ts2; tparams=tp;
	}
	override string toString(){
		return "is("~ty.toString()~(ident?" "~ident.toString():"")~(which!=WhichIsExp.type?(which==WhichIsExp.isEqual?"==":": ")~
			(tySpec?tySpec.toString():TokenTypeToString(tySpec2))~(tparams?","~join(map!(to!string)(tparams),","):""):"")~")";
	}
}

class TypeidExp: Expression{
	Expression e;
	this(Expression exp)in{assert(exp&&1);}body{e=exp;}
	override string toString(){return "typeid("~e.toString()~")";}
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
	Expression ty;
	Identifier name;
	Expression init;
	this(STC s, Expression t, Identifier n, Expression i){stc=s; ty=t; name=n; init=i;}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~(ty?ty.toString()~" ":"")~name.toString()~(init?"="~init.toString():"");}

	mixin Visitors;
}
