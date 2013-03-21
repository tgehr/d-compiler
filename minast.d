// this file contains the minimal (non-semantic) AST definition that works with the parser

import std.array, std.algorithm, std.range, std.conv;

import lexer, parser;

abstract class Node{
	Location loc;
}

class Expression: Node{ // empty expression if instanced
	int brackets=0;
	override string toString(){return _brk("{}()");}
	private string _brk(string s){return std.array.replicate("(",brackets)~s~std.array.replicate(")",brackets); return s;}
}
class Statement: Node{ // empty statement if instanced
	override string toString(){return ";";}
}
class Declaration: Statement{ // empty declaration if instanced
	STC stc;
	Identifier name;
	this(STC stc,Identifier name){this.stc=stc; this.name=name;}
	override string toString(){return ";";}
}

class ErrorDecl: Declaration{
	this(){super(STC.init, null);}
	override string toString(){return "__error ;";}
}

class ModuleDecl: Declaration{
	Expression symbol;
	this(STC stc, Expression sym){symbol=sym; super(stc, null);}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"module "~symbol.toString()~";";}
}

class ImportBindingsExp: Expression{
	Expression symbol;
	Expression[] bindings;
	this(Expression sym, Expression[] bind){symbol=sym; bindings=bind;}
	override string toString(){return symbol.toString()~": "~join(map!(to!string)(bindings),", ");}
}
class ImportDecl: Declaration{
	Expression[] symbols;
	this(STC stc, Expression[] sym){symbols=sym; super(stc,null);}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"import "~join(map!(to!string)(symbols),", ")~";";}
}
class EnumDecl: Declaration{
	Expression base;
	Expression[2][] members;
	this(STC stc,Identifier name, Expression base, Expression[2][] mem){this.base=base; members=mem; super(stc,name);}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"enum"~(name?" "~name.toString():"")~(base?":"~base.toString():"")~
			"{"~join(map!((a){return a[0].toString()~(a[1]?"="~a[1].toString():"");})(members),",")~"}";}
}

abstract class ConditionalDecl: Declaration{
	Statement bdy;
	Statement els;
	this(STC stc,Statement b,Statement e)in{assert(b&&1);}body{bdy=b; els=e; super(stc,null);}
}
class VersionSpecDecl: Declaration{
	Expression spec;
	this(STC stc,Expression s)in{assert(s!is null);}body{spec=s; super(stc,null);}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"version="~spec.toString()~";";}
}
class VersionDecl: ConditionalDecl{
	Expression cond;
	this(STC stc,Expression c,Statement b, Statement e)in{assert(c!is null);}body{cond=c; super(stc,b,e);}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"version("~cond.toString()~") "~bdy.toString()~
			(els?(cast(BlockStm)bdy||cast(BlockDecl)bdy?"":"\n")~"else "~els.toString():"");}
}
class DebugSpecDecl: Declaration{
	Expression spec;
	this(STC stc,Expression s)in{assert(s!is null);}body{spec=s; super(stc,null);}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"debug="~spec.toString()~";";}
}
class DebugDecl: ConditionalDecl{
	Expression cond;
	this(STC stc,Expression c,Statement b, Statement e){cond=c; super(stc,b,e);}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"debug"~(cond?"("~cond.toString()~") ":"")~bdy.toString()~
			(els?(cast(BlockStm)bdy||cast(BlockDecl)bdy?"":"\n")~"else "~els.toString():"");}
}
class StaticIfDecl: ConditionalDecl{
	Expression cond;
	this(STC stc,Expression c,Statement b,Statement e)in{assert(c&&b);}body{cond=c; super(stc,b,e);}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"static if("~cond.toString()~") "~bdy.toString()~
			(els?(cast(BlockStm)bdy||cast(BlockDecl)bdy?"":"\n")~"else "~els.toString():"");}
}
class StaticAssertDecl: Declaration{
	Expression[] a;
	this(STC stc,Expression[] args){a = args; super(stc,null);}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"static assert("~join(map!(to!string)(a),",")~");";}
}

class MixinDecl: Declaration{
	Expression e;
	this(STC stc, Expression exp){e=exp; super(stc,null);}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"mixin("~e.toString()~");";}
}
class AliasDecl: Declaration{
	Declaration decl;
	this(STC stc, Declaration declaration){decl=declaration; super(stc, declaration.name);}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"alias "~decl.toString();}
}
class TypedefDecl: Declaration{
	Declaration decl;
	this(STC stc, Declaration declaration){decl=declaration; super(stc, declaration.name);}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"typedef "~decl.toString();}
}
class BlockDecl: Declaration{
	Declaration[] decls;
	this(STC s,Declaration[] declarations){stc=s; decls=declarations; super(stc,null);}
	override string toString(){return STCtoString(stc)~"{\n"~(stc?join(map!(to!string)(decls),"\n")~"\n}":indent(join(map!(to!string)(decls),"\n"))~"\n}");}
}
class AttributeDecl: Declaration{
	Declaration[] decls;
	this(STC stc,Declaration[] declarations){decls=declarations; super(stc,null);}
	override string toString(){return STCtoString(stc)~":\n"~join(map!(to!string)(decls),"\n");}
}

class TemplateParameter: Node{
	Identifier name;
	Expression type, spec, init;
	bool isAlias, isTuple;
	this(bool isa, bool ist, Expression tt, Identifier name, Expression specialization, Expression deflt){
		isAlias=isa, isTuple=ist; this.name = name;
		type=tt; spec=specialization; init=deflt;
	}
	override string toString(){
		return (isAlias?"alias ":"")~(type?type.toString()~" ":"")~(name?name.toString():"")~
			(isTuple?"...":"")~(spec?":"~spec.toString():"")~(init?"="~init.toString():"");
	}
}

class TemplateDecl: Declaration{
	bool ismixin;
	TemplateParameter[] params;
	Expression constraint;
	BlockDecl bdy;
	this(bool m,STC stc,Identifier name, TemplateParameter[] prm, Expression c, BlockDecl b){
		ismixin=m; params=prm; constraint=c; bdy=b; super(stc,name);
	}
	override string toString(){
		return (stc?STCtoString(stc)~" ":"")~"template "~name.toString()~"("~join(map!(to!string)(params),",")~")"~
			(constraint?" if("~constraint.toString()~")":"")~bdy.toString();
	}
}

class TemplateMixinDecl: Declaration{
	Expression inst;
	this(STC stc, Expression i, Identifier name)in{assert(i&&1);}body{inst=i; super(stc,name);}
	override string toString(){return "mixin "~inst.toString()~(name?" "~name.toString():"")~";";}
}

abstract class AggregateDecl: Declaration{
	BlockDecl bdy;
	this(STC stc, Identifier name, BlockDecl b){bdy=b; super(stc,name);}
}
class StructDecl: AggregateDecl{
	this(STC stc,Identifier name, BlockDecl b){super(stc,name,b);}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"struct"~(name?" "~name.toString():"")~(bdy?bdy.toString():";");}
}
class UnionDecl: AggregateDecl{
	this(STC stc,Identifier name, BlockDecl b){super(stc,name,b);}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"union"~(name?" "~name.toString():"")~(bdy?bdy.toString():";");}
}
struct ParentListEntry{
	STC protection;
	Expression symbol;
	string toString(){return (protection?STCtoString(protection)~" ":"")~symbol.toString();}
}
class ClassDecl: AggregateDecl{
	ParentListEntry[] parents;
	this(STC stc,Identifier name, ParentListEntry[] p, BlockDecl b){ parents=p; super(stc,name,b); }
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"class"~(name?" "~name.toString():"")~
			(parents?": "~join(map!(to!string)(parents),","):"")~(bdy?bdy.toString():"");}
}
class InterfaceDecl: AggregateDecl{
	ParentListEntry[] parents;
	this(STC stc,Identifier name, ParentListEntry[] p, BlockDecl b){ parents=p; super(stc,name,b); }
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"interface"~(name?" "~name.toString():"")~
			(parents?": "~join(map!(to!string)(parents),","):"")~(bdy?bdy.toString():";");}
}
class TemplateAggregateDecl: Declaration{
	TemplateParameter[] params;
	Expression constraint;
	AggregateDecl decl;
	this(STC stc,TemplateParameter[] p, Expression c, AggregateDecl ad){ params=p; constraint=c; decl=ad; super(stc,decl.name); }
	override string toString(){
		auto s=cast(StructDecl)decl, u=cast(UnionDecl)decl, c=cast(ClassDecl)decl, i=cast(InterfaceDecl)decl;
		string r=(stc?STCtoString(stc)~" ":"");
		r~=(s?"struct":u?"union":c?"class":"interface")~(decl.name?" "~name.toString():"")~"("~join(map!(to!string)(params),",")~")";
		if(c && c.parents) r~=": "~join(map!(to!string)(c.parents),",");
		if(i && i.parents) r~=": "~join(map!(to!string)(i.parents),",");
		auto bdy=s?s.bdy:u?u.bdy:c?c.bdy:i.bdy;
		return r~(constraint?" if("~constraint.toString()~")":"")~(bdy?bdy.toString():";");
	}
}

class TemplateFunctionDecl: Declaration{
	TemplateParameter[] params;
	Expression constraint;
	FunctionDecl fdecl;
	this(STC stc, TemplateParameter[] tp, Expression c, FunctionDecl fd){params=tp; constraint=c;fdecl=fd; super(stc, fdecl.name);}
	override string toString(){
		auto fd=cast(FunctionDef)fdecl;
		return (fdecl.type.stc?STCtoString(fdecl.type.stc)~" ":"")~(fdecl.type.ret?fdecl.type.ret.toString()~" ":"")~name.toString()~
			"("~join(map!(to!string)(params),",")~")"~fdecl.type.pListToString()~(constraint?" if("~constraint.toString()~")":"")
			~(fdecl.pre?"in"~fdecl.pre.toString():"")~(fdecl.post?"out"~(fdecl.postres?"("~fdecl.postres.toString()~")":"")~fdecl.post.toString():"")~
			(fd?(fd.pre||fd.post?"body":"")~fd.bdy.toString():!fdecl.pre&&!fdecl.post?";":"");
	}
}

class CArrayDecl: Declaration{
	Expression type;
	Expression init;
	Expression postfix; // reverse order
	this(STC stc, Expression type, Identifier name, Expression pfix, Expression initializer)in{assert(type&&name&&pfix);}body{
		this.stc=stc; this.type=type; postfix=pfix; init=initializer; super(stc,name);
	}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~type.toString()~" "~postfix.toString()~(init?"="~init.toString():"")~";";}
}

class VarDecl: Declaration{
	Expression type;
	Expression init;
	this(STC stc, Expression type, Identifier name, Expression initializer){this.stc=stc; this.type=type; init=initializer; super(stc,name);}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~(type?type.toString()~" ":"")~name.toString()~(init?"="~init.toString():"")~";";}
}
class Declarators: Declaration{
	VarDecl[] decls;
	this(VarDecl[] declarations)in{assert(declarations.length>1);foreach(x;declarations) assert(x.type is declarations[0].type);}body{
		decls=declarations;super(STC.init,null);
	}
	override string toString(){
		string r=(decls[0].stc?STCtoString(decls[0].stc)~" ":"")~(decls[0].type?decls[0].type.toString()~" ":"");
		//return r~join(map!((a){return a.name.toString();})(decls),","); // WTF???
		foreach(x;decls[0..$-1]) r~=x.name.toString()~(x.init?"="~x.init.toString():"")~",";
		return r~decls[$-1].name.toString()~(decls[$-1].init?"="~decls[$-1].init.toString():"")~";";
	}
}

class Parameter: VarDecl{ // for functions, foreach etc
	this(STC stc, Expression type, Identifier name, Expression initializer){super(stc,type,name,initializer);}
	override string toString(){return STCtoString(stc)~(stc&&type?" ":"")~(type?type.toString():"")~
			(name?(stc||type?" ":"")~name.toString():"")~(init?"="~init.toString():"");}
}
class PostblitParameter: Parameter{
	this(){super(STC.init,null,null,null);}
	override string toString(){return "this";}
}
class FunctionDecl: Declaration{
	FunctionType type;
	BlockStm pre,post;
	Identifier postres;
	this(FunctionType type,Identifier name,BlockStm pr,BlockStm po,Identifier pres){
		this.type=type; pre=pr, post=po; postres=pres; super(type.stc, name);
	}
	override string toString(){
		return (type.stc?STCtoString(type.stc)~" ":"")~(type.ret?type.ret.toString()~" ":"")~name.toString()~type.pListToString()~
			(pre?"in"~pre.toString():"")~(post?"out"~(postres?"("~postres.toString()~")":"")~post.toString():"")~(!pre&&!post?";":"");
	}
}

class FunctionDef: FunctionDecl{
	BlockStm bdy;
	this(FunctionType type,Identifier name, BlockStm precondition,BlockStm postcondition,Identifier pres,BlockStm fbody){
		super(type,name, precondition, postcondition, pres); bdy=fbody;}
	override string toString(){
		return (type.stc?STCtoString(type.stc)~" ":"")~(type.ret?type.ret.toString()~" ":"")~name.toString()~type.pListToString()~
			(pre?"in"~pre.toString():"")~(post?"out"~(postres?"("~postres.toString()~")":"")~post.toString():"")~(pre||post?"body":"")~bdy.toString();
	}
}

class UnitTestDecl: Declaration{
	BlockStm bdy;
	this(STC stc,BlockStm b)in{assert(b!is null);}body{ bdy=b; super(stc,null); }
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"unittest"~bdy.toString();}
}

class PragmaDecl: Declaration{
	Expression[] args;
	Statement bdy;
	this(STC stc,Expression[] a, Statement b)in{assert(b&&1);}body{args=a; bdy=b; super(stc,null);}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~"pragma("~join(map!(to!string)(args),",")~")"~bdy.toString();}
}

enum LinkageType{
	D,
	C,
	CPP,
	Pascal,
	System,
	Windows,
}

class ExternDecl: Declaration{
	LinkageType linktype;
	Declaration decl;
	this(STC stc,LinkageType l,Declaration d)in{assert(d&&1);}body{
		linktype=l; decl=d;
		super(stc,d.name);
	}
	override string toString(){
		return (stc?STCtoString(stc)~" ":"")~"extern("~(linktype==LinkageType.CPP?"C++":to!string(linktype))~") "~decl.toString();
	}
}
class AlignDecl: Declaration{
	ulong alignment;
	Declaration decl;
	this(STC stc,ulong a,Declaration d)in{assert(d&&1);}body{
		alignment=a; decl=d;
		super(stc,d.name);
	}
	override string toString(){
		return (stc?STCtoString(stc)~" ":"")~"align("~to!string(alignment)~") "~decl.toString();
	}
}

class Type: Expression{ //Types can be part of Expressions and vice-versa
  override string toString(){return "Type";}
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

class ErrorExp: Expression{
	override string toString(){return _brk("__error");}
}

class Identifier: Expression{
	string name;
	this(string name){this.name = name;}
	override string toString(){return _brk(name);}
}

class LiteralExp: Expression{
	Token lit;
	this(Token literal){lit=literal;}
	override string toString(){return _brk(lit.toString());}
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
	Expression[] a;
	this(Expression exp, Expression[] args){e=exp; a=args;}
	override string toString(){return _brk(e.toString()~(a.length?'('~join(map!(to!string)(a),",")~')':"()"));}
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

private string indent(string code){
	import std.string;
	auto sl=splitLines(code);if(!sl.length) return "";
	string r="    "~sl[0];
	foreach(x;sl[1..$]) r~="\n    "~x;
	return r;
}
class ErrorStm: Statement{
	override string toString(){return "__error;";}
}

class BlockStm: Statement{
	Statement[] s;
	this(Statement[] ss){s=ss;}
	override string toString(){return "{\n"~indent(join(map!(to!string)(s),"\n"))~"\n}";}
}

class LabeledStm: Statement{
	Identifier l;
	Statement s;
	this(Identifier label, Statement statement){l=label; s=statement;}
	override string toString(){return l.toString()~": "~s.toString();}
}

class ExpressionStm: Statement{
	Expression e;
	this(Expression next){e=next;}
	override string toString(){return e.toString() ~ ';';}
}

class ConditionDeclExp: Expression{
	STC stc;
	Expression type;
	Identifier name;
	Expression init;
	this(STC s, Expression t, Identifier n, Expression i){stc=s; type=t; name=n; init=i;}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~(type?type.toString()~" ":"")~name.toString()~(init?"="~init.toString():"");}
}


class IfStm: Statement{
	Expression e; Statement s1,s2;
	this(Expression cond, Statement left, Statement right){e=cond, s1=left, s2=right;}
	override string toString(){return "if(" ~ e.toString ~ ") "~s1.toString()~(s2!is null?(cast(BlockStm)s1?"":"\n")~"else "~s2.toString:"");}
}
class WhileStm: Statement{
	Expression e; Statement s;
	this(Expression cond, Statement statement){e=cond; s=statement;}
	override string toString(){return "while(" ~ e.toString ~ ") "~s.toString();}
}
class DoStm: Statement{
	Statement s; Expression e;
	this(Statement statement, Expression cond){s=statement;e=cond;}
	override string toString(){return "do "~s.toString()~"while("~e.toString()~");";}
}
class ForStm: Statement{
	Statement s1; Expression e1, e2;
	Statement s2;
	this(Statement init, Expression cond, Expression next, Statement statement){s1=init; e1=cond; e2=next; s2=statement;}
	override string toString(){return "for("~s1.toString()~(e1?e1.toString():"")~";"~(e2?e2.toString:"")~") "~s2.toString();}
}
class ForeachStm: Statement{
	Parameter[] vars;
	Expression aggregate;
	Statement bdy;
	bool isReverse;
	this(Parameter[] v,Expression a,Statement b, bool isr=false){ vars = v; aggregate = a; bdy = b; isReverse=isr; }
	override string toString(){return "foreach"~(isReverse?"_reverse":"")~"("~join(map!(to!string)(vars),",")~";"~aggregate.toString()~") "~bdy.toString();}
}
class ForeachRangeStm: Statement{
	Parameter var;
	Expression left,right;
	Statement bdy;
	bool isReverse;
	this(Parameter v,Expression l,Expression r,Statement b, bool isr=false){ var = v; left = l; right=r; bdy = b; isReverse=isr; }
	override string toString(){return "foreach"~(isReverse?"_reverse":"")~"("~var.toString()~";"~left.toString()~".."~right.toString()~") "~bdy.toString();}
}
class SwitchStm: Statement{
	bool f; Expression e; Statement s;
	this(bool isfinal, Expression exp, Statement statement){f=isfinal; e=exp; s=statement;}
	this(Expression exp, Statement statement){f=false; e=exp; s=statement;}
	override string toString(){return (f?"final ":"")~"switch("~e.toString()~") "~s.toString();}
}
class CaseStm: Statement{
	Expression[] e; Statement[] s;
	this(Expression[] es, Statement[] ss){e=es; s=ss;}
	override string toString(){return "case "~join(map!(to!string)(e),",")~":"~(s?"\n":"")~indent(join(map!(to!string)(s),"\n"));}
}
class CaseRangeStm: Statement{
	Expression e1,e2; Statement[] s;
	this(Expression first, Expression last, Statement[] ss){e1=first; e2=last; s=ss;}
	override string toString(){return "case "~e1.toString()~": .. case "~e2.toString()~":"~(s?"\n":"")~indent(join(map!(to!string)(s),"\n"));}
}
class DefaultStm: Statement{
	Statement[] s;
	this(Statement[] ss){s=ss;}
	override string toString(){return "default:"~(s?"\n":"")~indent(join(map!(to!string)(s),"\n"));}
}
class ContinueStm: Statement{
	Identifier e;
	this(Identifier identifier){e=identifier;}
	override string toString(){return "continue"~(e?" "~e.name:"")~";";}
}
class BreakStm: Statement{
	Identifier e;
	this(Identifier identifier){e=identifier;}
	override string toString(){return "break"~(e?" "~e.name:"")~";";}
}
class ReturnStm: Statement{
	Expression e;
	this(Expression exp){e=exp;}
	override string toString(){return "return"~(e?" "~e.toString():"")~";";}
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
		final switch(t){
			case WhichGoto.identifier: return "goto "~e.toString()~";";
			case WhichGoto.default_: return "goto default;";
			case WhichGoto.case_: return "goto case;";
			case WhichGoto.caseExp: return "goto case "~e.toString()~";";
		}
	}
}
class WithStm: Statement{
	Expression e; Statement s;
	this(Expression exp, Statement statement){e=exp; s=statement;}
	override string toString(){return "with("~e.toString()~") "~s.toString();}
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
}
class TryStm: Statement{
	Statement statement;
	CatchStm[] catches;
	Statement finally_;
	this(Statement s,CatchStm[] c, Statement f)in{assert(s&&1);foreach(x;c[0..$-1]) assert(x.type&&1);}body{
		statement=s;
		catches=c;
		finally_=f;
	}
	override string toString(){return "try "~statement.toString()~join(map!(to!string)(catches),"\n")~(finally_?"\nfinally "~finally_.toString():"");}
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
	Expression e;
	this(Expression exp){e=exp;}
	override string toString(){return "mixin("~e.toString()~");";}
}
