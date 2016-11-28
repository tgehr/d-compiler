// Written in the D programming language
// Author: Timon Gehr
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.array, std.algorithm, std.range, std.conv, std.string;

import lexer, parser, expression, scope_, semantic, visitors, util;
import variant;

import analyze;

import rope_;

abstract class Statement: Node{
	override @property string kind(){return "statement";}

	mixin DownCastMethods!(
		BreakableStm,
		LoopingStm,
		CompoundStm,
	);

	mixin Visitors;
}

class EmptyStm: Statement{
	override string toString(){return ";";}
	override void semantic(Scope sc){mixin(SemPrlg); mixin(SemEplg);}
	
	mixin Visitors;
}

class ErrorStm: Statement{
	override string toString(){return "__error;";}

	mixin Visitors;
}

class CompoundStm: Statement{
	Statement[] s;
	this(Statement[] ss){s=ss;}

	override string toString(){return "{\n"~indent(join(map!(to!string)(s),"\n"))~"\n}";}

	mixin DownCastMethod;
	mixin Visitors;
}

class BlockStm: CompoundStm{
	this(Statement[] ss){super(ss);}

	mixin Visitors;
}
interface ILabeledStm{
	mixin CTFEInterpret!ILabeledStm;
}
class LabeledStm: Statement,ILabeledStm{
	Identifier l;
	Statement s;
	this(Identifier label, Statement statement){l=label; s=statement; sstate = SemState.pre;}
	override string toString(){return l.toString()~": "~s.toString();}

	mixin Visitors;
}

class ExpressionStm: Statement{
	Expression e;
	this(Expression next){e=next;}
	override string toString(){return e.toString() ~ ';';}

	mixin Visitors;
}


class IfStm: Statement{
	Expression e; Statement s1,s2;
	this(Expression cond, Statement left, Statement right){e=cond, s1=left, s2=right;}
	override string toString(){return "if(" ~ e.toString() ~ ") "~s1.toString()~(s2!is null?(cast(BlockStm)s1?"":"\n")~"else "~s2.toString():"");}

	mixin Visitors;
}

abstract class BreakableStm: Statement{
	mixin DownCastMethod;
	mixin DownCastMethods!(ForeachStm,ForeachRangeStm);
	mixin Visitors;
}
abstract class LoopingStm: BreakableStm{
	mixin DownCastMethod;
	mixin Visitors;
}

class WhileStm: LoopingStm{
	Expression e; Statement s;
	this(Expression cond, Statement statement){e=cond; s=statement;}
	override string toString(){return "while(" ~ e.toString() ~ ") "~s.toString();}

	mixin Visitors;
}
class DoStm: LoopingStm{
	Statement s; Expression e;
	this(Statement statement, Expression cond){s=statement;e=cond;}
	override string toString(){return "do "~s.toString()~"while("~e.toString()~");";}

	mixin Visitors;
}
class ForStm: LoopingStm{
	Statement s1; Expression e1, e2;
	Statement s2;
	this(Statement init, Expression cond, Expression next, Statement statement){s1=init; e1=cond; e2=next; s2=statement;}
	override string toString(){return "for("~s1.toString()~(e1?e1.toString():"")~";"~(e2?e2.toString():"")~") "~s2.toString();}

	mixin Visitors;
}
class ForeachStm: LoopingStm{
	ForeachVarDecl[] vars;
	Expression aggregate;
	Statement bdy;
	bool isReverse;
	this(ForeachVarDecl[] v,Expression a,Statement b, bool isr=false){ vars = v; aggregate = a; bdy = b; isReverse=isr; }
	override string toString(){
		if(lower) return "/+lowered foreach+/ "~lower.toString();
		return "foreach"~(isReverse?"_reverse":"")~"("~join(map!(to!string)(vars),",")~";"~aggregate.toString()~") "~bdy.toString();
	}

	mixin DownCastMethod;
	mixin Visitors;
}
class ForeachRangeStm: LoopingStm{
	ForeachVarDecl var;
	Expression left,right;
	Statement bdy;
	bool isReverse;
	this(ForeachVarDecl v,Expression l,Expression r,Statement b, bool isr=false){ var = v; left = l; right=r; bdy = b; isReverse=isr; }
	override string toString(){return "foreach"~(isReverse?"_reverse":"")~"("~var.toString()~";"~left.toString()~".."~right.toString()~") "~bdy.toString();}

	mixin DownCastMethod;
	mixin Visitors;
}
class SwitchStm: BreakableStm{
	bool f; Expression e; Statement s;
	this(bool isfinal, Expression exp, Statement statement){f=isfinal; e=exp; s=statement;}
	this(Expression exp, Statement statement){f=false; e=exp; s=statement;}
	override string toString(){return (f?"final ":"")~"switch("~e.toString()~") "~s.toString();}

	mixin Visitors;
}

abstract class SwitchLabelStm: Statement,ILabeledStm{
	mixin DownCastMethods!(
		CaseStm,
		CaseRangeStm,
		DefaultStm,
	);

	mixin Visitors;
}

class CaseStm: SwitchLabelStm{
	Expression[] e; Statement[] s;
	this(Expression[] es, Statement[] ss){e=es; s=ss;}
	override string toString(){return "case "~join(map!(to!string)(e),",")~":"~(s?"\n":"")~indent(join(map!(to!string)(s),"\n"));}

	mixin DownCastMethod;
	mixin Visitors;
}
class CaseRangeStm: SwitchLabelStm{
	Expression e1,e2; Statement[] s;
	this(Expression first, Expression last, Statement[] ss){e1=first; e2=last; s=ss;}
	override string toString(){return "case "~e1.toString()~": .. case "~e2.toString()~":"~(s?"\n":"")~indent(join(map!(to!string)(s),"\n"));}

	mixin DownCastMethod;
	mixin Visitors;
}
class DefaultStm: SwitchLabelStm{
	Statement[] s;
	this(Statement[] ss){s=ss;}
	override string toString(){return "default:"~(s?"\n":"")~indent(join(map!(to!string)(s),"\n"));}

	mixin DownCastMethod;
	mixin Visitors;
}
class ContinueStm: Statement{
	Identifier e;
	this(Identifier identifier){e=identifier;}
	override string toString(){return "continue"~(e?" "~e.name:"")~";";}

	mixin Visitors;
}
class BreakStm: Statement{
	Identifier e;
	this(Identifier identifier){e=identifier;}
	override string toString(){return "break"~(e?" "~e.name:"")~";";}

	mixin Visitors;
}
class ReturnStm: Statement{
	Expression e;
	this(Expression exp){e=exp;}
	override string toString(){return "return"~(e?" "~e.toString():"")~";";}

	mixin Visitors;
}
enum WhichGoto{
	identifier,
	default_,
	case_,
	caseExp,
}
class GotoStm: Statement{
	WhichGoto t; Expression e;
	this(WhichGoto type,Expression exp){t=type; e=exp;}
	override string toString(){
		if(lower) return "/+lowered goto+/ "~lower.toString();
		final switch(t){
			case WhichGoto.identifier: return "goto "~e.toString()~";";
			case WhichGoto.default_: return "goto default;";
			case WhichGoto.case_: return "goto case;";
			case WhichGoto.caseExp: return "goto case "~e.toString()~";";
		}
	}

	mixin Visitors;
}
class WithStm: Statement{
	Expression e; Statement s;
	this(Expression exp, Statement statement){e=exp; s=statement;}
	override string toString(){return "with("~e.toString()~") "~s.toString();}

	mixin Visitors;
}
class SynchronizedStm: Statement{
	Expression e; Statement s;
	this(Expression exp, Statement statement){e=exp; s=statement;}
	override string toString(){return "synchronized"~(e?"("~e.toString()~")":"")~" "~s.toString();}
}
class CatchStm: Statement{
	Expression type;
	Identifier ident;
	Statement statement;
	this(Expression t, Identifier i, Statement s)in{assert(s);}body{type=t; ident=i; statement=s;}
	override string toString(){return "catch"~(type?"("~type.toString()~(ident?" "~ident.toString():"")~")":" ")~statement.toString();}

	mixin Visitors;
}
class TryStm: Statement{
	Statement statement;
	CatchStm[] catches;
	Statement finally_;
	this(Statement s,CatchStm[] c, Statement f)in{assert(s&&1);if(c.length)foreach(x;c[0..$-1]) assert(x.type&&1);}body{
		statement=s;
		catches=c;
		finally_=f;
	}
	override string toString(){return "try "~statement.toString()~join(map!(to!string)(catches),"\n")~(finally_?"\nfinally "~finally_.toString():"");}

	mixin Visitors;
}
class ThrowStm: Statement{
	Expression e;
	this(Expression exp){e=exp;}
	override string toString(){return "throw "~e.toString()~";";}
}
enum WhichScopeGuard{
	exit,
	success,
	failure,
}
class ScopeGuardStm: Statement{
	WhichScopeGuard w; Statement s;
	this(WhichScopeGuard which, Statement statement){w=which; s=statement;}
	override string toString(){
		string r;
		switch(w){
			case WhichScopeGuard.exit: r="scope(exit) "; break;
			case WhichScopeGuard.success: r="scope(success) "; break;
			case WhichScopeGuard.failure: r="scope(failure) "; break;
			default: assert(0);
		}
		return r~s.toString();
	}
}
class AsmStm: Statement{
	Code asmcode; // TODO: Implement inline assembler parsing
	this(Code ac){asmcode=ac;}
	//override string toString(){return "asm{ "~join(map!(to!string)(asmcode)," ")~" } /* TODO: fix this */";}
}
class MixinStm: Statement{
	Expression[] a;
	this(Expression[] arg){a=arg;}
	override string toString(){return "mixin("~join(map!(to!string)(a),",")~");";}

	mixin Visitors;
}
