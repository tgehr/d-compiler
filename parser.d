module parser;

import std.array, std.range, std.algorithm, std.traits, std.conv: to;
import std.typetuple;

import lexer;

class Expression{ // empty expression if instanced
	Location loc;
	bool brackets=false;
	override string toString(){return _brk("{}()");}
	private string _brk(string s){if(brackets) return "("~s~")"; return s;}
}
class Statement{ // empty statement if instanced
	Location loc;
	override string toString(){return ";";}
}
class Declaration: Statement{
	Location loc;
	IdentifierExp name;
	this(IdentifierExp name){this.name=name;}
	override string toString(){return "Declaration";}
}

class ImportDecl: Declaration{
	Expression[] symbols;
	bool isStatic;
	this(bool st, Expression[] sym){isStatic=st;symbols=sym; super(null);}
	override string toString(){return (isStatic?"static ":"")~"import "~join(map!(to!string)(symbols),",")~";";}
}
class ImportBindingsDecl: Declaration{
	Expression symbol;
	Expression[] bindings;
	bool isStatic;
	this(bool st, Expression sym, Expression[] bind){isStatic=st; symbol=sym; bindings=bind; super(null);}
	override string toString(){return (isStatic?"static ":"")~"import "~symbol.toString()~" : "~join(map!(to!string)(bindings),",")~";";}
}
class EnumDecl: Declaration{
	Expression base;
	Expression[2][] members;
	this(IdentifierExp name, Expression base, Expression[2][] mem){this.base=base; members=mem; super(name);}
	override string toString(){return "enum"~(name?" "~name.toString():"")~(base?":"~base.toString():"")~"{"~join(map!((a){return a[0].toString()~(a[1]?"="~a[1].toString():"");})(members),",")~"}";}
}


class AliasDecl: Declaration{
	Declaration decl;
	this(Declaration declaration){decl=declaration; super(declaration.name);}
	override string toString(){return "alias "~decl.toString();}
}
class VarDecl: Declaration{
	STC stc; Expression type;
	Expression init;
	this(STC stc, Expression type, IdentifierExp name, Expression initializer){this.stc=stc; this.type=type; init=initializer; super(name);}
	override string toString(){return STCtoString(stc)~(stc?" ":"")~(type?type.toString()~" ":"")~name.toString()~(init?"="~init.toString():"")~";";}
}
class Declarators: Declaration{
	VarDecl[] decls;
	this(VarDecl[] declarations)in{assert(declarations.length>1);foreach(x;declarations) assert(x.type is declarations[0].type);}body{decls=declarations;super(null);}
	override string toString(){
		string r=STCtoString(decls[0].stc)~(decls[0].stc?" ":"")~(decls[0].type?decls[0].type.toString()~" ":"");
		//return r~join(map!((a){return a.name.toString();})(decls),","); // WTF???
		foreach(x;decls[0..$-1]) r~=x.name.toString()~(x.init?"="~x.init.toString():"")~",";
		return r~decls[$-1].name.toString()~(decls[$-1].init?"="~decls[$-1].init.toString():"")~";";
	}
}

class Parameter: VarDecl{
	this(STC stc, Expression type, IdentifierExp name, Expression initializer){super(stc,type,name,initializer);}
	override string toString(){return STCtoString(stc)~(stc?" ":"")~(type?type.toString():"")~(name?" "~name.toString():"")~(init?"="~init.toString():"");}
}

class FunctionDecl: Declaration{
	FunctionType type;
	CompoundStm pre,post;
	IdentifierExp postres;
	this(FunctionType type,IdentifierExp name,CompoundStm pr,CompoundStm po,IdentifierExp pres){this.type=type; pre=pr, post=po; postres=pres; super(name);}
	override string toString(){
		return STCtoString(type.stc)~(type.stc?" ":"")~(type.ret?type.ret.toString()~" ":"")~name.toString()~type.pListToString()~(pre?"in"~pre.toString():"")~(post?"out"~(postres?"("~postres.toString()~")":"")~post.toString():"")~(!pre&&!post?";":"");
	}
}

class FunctionDef: FunctionDecl{
	CompoundStm bdy;
	this(FunctionType type,IdentifierExp name, CompoundStm precondition,CompoundStm postcondition,IdentifierExp pres,CompoundStm fbody){
		super(type,name, precondition, postcondition, pres); bdy=fbody;}
	override string toString(){
		return STCtoString(type.stc)~(type.stc?" ":"")~(type.ret?type.ret.toString()~" ":"")~name.toString()~type.pListToString()~(pre?"in"~pre.toString():"")~(post?"out"~(postres?"("~postres.toString()~")":"")~post.toString()~"body":"")~bdy.toString();
	}
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
	override string toString(){return STCtoString(stc)~(stc?" ":"")~(ret?ret.toString():"")~pListToString();}
	string pListToString(){
		return "("~join(map!(to!string)(params),",")~(vararg==VarArgs.cStyle?(params.length?",":"")~"...)":vararg==VarArgs.dStyle?"...)":")");
	}
}

class FunctionPtr: Type{
	FunctionType ft;
	this(FunctionType ft)in{assert(ft&&ft.ret);}body{this.ft=ft;}
	override string toString(){return ft.ret.toString()~" function"~ft.pListToString()~(ft.stc?" ":"")~STCtoString(ft.stc);}
}

class DelegateType: Type{
	FunctionType ft;
	this(FunctionType ft)in{assert(ft&&ft.ret);}body{this.ft=ft;}
	override string toString(){return ft.ret.toString()~" delegate"~ft.pListToString()~(ft.stc?" ":"")~STCtoString(ft.stc);}
}


class Type: Expression{ //Types can be part of Expressions and vice-versa
  Location loc;
  override string toString(){return "Type";}
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
	override string toString(){return _brk(Token(type).toString());}
}

class Pointer: Type{
	Expression e;
	this(Expression next){e=next;}
	override string toString(){return _brk(e.toString()~'*');}
}

class QualifiedType(string stc): Type{
	Expression type;
	this(Expression type){this.type=type;}
	override string toString(){return _brk(stc~"("~type.toString()~")");}
}

class ErrorExp: Expression{
	this(){}
	override string toString(){return _brk("__error");}
}

class IdentifierExp: Expression{
	string name;
	this(string name){this.name = name;}
	override string toString(){return _brk(name);}
}

class LiteralExp: Expression{
	Token lit;
	this(Token literal){lit=literal;}
	override string toString(){return _brk(lit.toString());}
}

class ArrayLiteralExp: Expression{
	Expression[] lit;
	this(Expression[] literal){lit=literal;}
	override string toString(){return _brk("["~join(map!(to!string)(lit),",")~"]");}
}

class AssocArrayLiteralExp: Expression{
	Expression[2][] lit;
	this(Expression[2][] literal){lit=literal;}
	override string toString(){return _brk("["~join(map!q{a[0].toString()~":"~a[1].toString()}(lit),",")~"]");}
}

class ThisExp: Expression{
	override string toString(){return _brk("this");}
}

class SuperExp: Expression{
	override string toString(){return _brk("super");}
}

class NewExp: Expression{
	Expression[] a1;
	Expression type;
	Expression[] a2;
	this(Expression[] args1,Expression type,Expression[] args2){a1=args1; this.type=type; a2=args2;}
	override string toString(){return _brk("new"~(a1?"("~join(map!(to!string)(a1),",")~") ":" ")~type.toString()~(a2?"("~join(map!(to!string)(a2),",")~")":""));}
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
	Expression[] a;
	this(Expression exp, Expression[] args){e=exp; a=args;}
	override string toString(){return _brk(e.toString()~"!("~join(map!(to!string)(a),",")~')');}
}
class BinaryExp(TokenType op): Expression{
	Expression e1, e2;
	this(Expression left, Expression right){e1=left; e2=right;}
	override string toString(){return _brk(e1.toString() ~ TokChars!op ~ e2.toString());}
	//override string toString(){return e1.toString() ~ " "~ e2.toString~TokChars!op;} // RPN
}

class TernaryExp: Expression{
	Expression e1, e2, e3;
	this(Expression cond, Expression left, Expression right){e1=cond; e2=left; e3=right;}
	override string toString(){return _brk(e1.toString() ~ '?' ~ e2.toString() ~ ':' ~ e3.toString());}
}

class ErrorStm: Statement{
	this(){}
	override string toString(){return "__error;";}
}

class CompoundStm: Statement{
	Statement[] s; bool news;
	this(Statement[] ss, bool newscope=true){s=ss; news=newscope;}
	override string toString(){return "{"~join(map!(to!string)(s))~"}";}
}

class LabeledStm: Statement{
	IdentifierExp l;
	Statement s;
	this(IdentifierExp label, Statement statement){l=label; s=statement;}
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
	IdentifierExp name;
	Expression init;
	this(STC s, Expression t, IdentifierExp n, Expression i){stc=s; type=t; name=n; init=i;}
	override string toString(){return STCtoString(stc)~(stc?" ":"")~(type?type.toString()~" ":"")~name.toString()~(init?"="~init.toString():"");}
}


class IfStm: Statement{
	Expression e; Statement s1,s2;
	this(Expression cond, Statement left, Statement right){e=cond, s1=left, s2=right;}
	override string toString(){return "if(" ~ e.toString ~ ") "~s1.toString()~(s2!is null?"else "~s2.toString:"");}
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
class ForeachStm: Statement{} // TODO: implement
class ForeachRangeStm: Statement{} // TODO: implement
class SwitchStm: Statement{
	bool f; Expression e; Statement s;
	this(bool isfinal, Expression exp, Statement statement){f=isfinal; e=exp; s=statement;}
	this(Expression exp, Statement statement){f=false; e=exp; s=statement;}
	override string toString(){return (f?"final ":"")~"switch("~e.toString()~") "~s.toString();}
}
class CaseStm: Statement{
	Expression[] e; Statement[] s;
	this(Expression[] es, Statement[] ss){e=es; s=ss;}
	override string toString(){return "case "~join(map!(to!string)(e),",")~": "~join(map!(to!string)(s));}
}
class CaseRangeStm: Statement{
	Expression e1,e2; Statement[] s;
	this(Expression first, Expression last, Statement[] ss){e1=first; e2=last; s=ss;}
	override string toString(){return "case "~e1.toString()~": .. case "~e2.toString()~": "~join(map!(to!string)(s));}
}
class DefaultStm: Statement{
	Statement[] s;
	this(Statement[] ss){s=ss;}
	override string toString(){return "default: "~join(map!(to!string)(s));}
}
class ContinueStm: Statement{
	IdentifierExp e;
	this(IdentifierExp identifier){e=identifier;}
	override string toString(){return "continue"~(e?" "~e.name:"")~";";}
}
class BreakStm: Statement{
	IdentifierExp e;
	this(IdentifierExp identifier){e=identifier;}
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
class TryStm: Statement{} // TODO: implement TryStm
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
class AsmStm: Statement{} // TODO: Implement inline assembler parsing
class PragmaStm: Statement{} // TODO: Implement compiler pragma parsing
class MixinStm: Statement{
	Expression e;
	this(Expression exp){e=exp;}
	override string toString(){return "mixin("~e.toString()~");";}
}
// expression parser:
// left binding power
template lbp(TokenType type){enum lbp=getLbp(type);}
// right binding power
template rbp(TokenType type){enum rbp=type==Tok!"."?180:lbp!type-(type==Tok!"^^"||lbp!type==30);} // ^^, (op)= bind weaker to the right than to the left, '.' binds only primaryExpressions

int getLbp(TokenType type) pure{ // operator precedence
	switch(type){
	//case Tok!"..": return 10; // range operator
	case Tok!",":  return 20; // comma operator
	// assignment operators
	case Tok!"/=",Tok!"&=",Tok!"|=",Tok!"-=":
	case Tok!"+=",Tok!"<<=",Tok!">>=", Tok!">>>=":
	case Tok!"=",Tok!"*=",Tok!"%=",Tok!"^=":
	case Tok!"^^=",Tok!"~=": 
		return 30;
	case Tok!"?":  return 40; // conditional operator
	case Tok!"||": return 50; // logical OR
	case Tok!"&&": return 60; // logical AND
	case Tok!"|":  return 70; // bitwise OR
	case Tok!"^":  return 80; // bitwise XOR
	case Tok!"&":  return 90; // bitwise AND
	// relational operators
	// TODO: add in !in is !is
	case Tok!"==",Tok!"!=",Tok!">",Tok!"<":
	case Tok!">=",Tok!"<=",Tok!"!>",Tok!"!<":
	case Tok!"!>=",Tok!"!<=",Tok!"<>",Tok!"!<>":
	case Tok!"<>=", Tok!"!<>=":
		return 100;
	// bitwise shift operators
	case Tok!">>": return 110;
	case Tok!"<<": return 110;
	case Tok!">>>":return 110;
	// additive operators
	case Tok!"+",Tok!"-",Tok!"~": 
		return 120;
	// multiplicative operators
	case Tok!"*",Tok!"/",Tok!"%":
		return 130;
	/*/ prefix operators
	case Tok!"&",Tok!"++",Tok!"--",Tok!"*":
	case Tok!"-",Tok!"+",Tok!"!",Tok!"~":
		return 140;  */
	case Tok!"^^": return 150; // power
	// postfix operators
	case Tok!".",Tok!"++",Tok!"--":
	case Tok!"(", Tok!"[": // function call and indexing
		return 160;
	// template instantiation
	case Tok!"!":  return 170;
	//case Tok!"i": return 45; //infix
	default: return -1;
	}
}

template isLiteral(TokenType type){
	enum isLiteral = canFind(["``","''","0","0U","0L","0LU",".0f",".0",".0L","null","true","false","$"],TokChars!type);
}
// unary exp binding power
enum nbp=140;
template isUnaryOp(TokenType type){
	enum isUnaryOp = canFind(["&", "*", "-", "++", "--", "+", "!", "~"],TokChars!type);
}
template isSimplePostfixOp(TokenType type){
	enum bool isSimplePostfixOp = canFind([/*".",*/ "++", "--"],TokChars!type);
}
template isPostfixOp(TokenType type){
	enum bool isPostfixOp = isSimplePostfixOp!type || canFind(["(", "["],TokChars!type);
}
template isBinaryOp(TokenType type){
	enum bool isBinaryOp = lbp!type!=-1 && !isPostfixOp!type;
}

enum basicTypes=["bool","byte","ubyte","short","ushort","int","uint","long","ulong","char","wchar","dchar","float","double","real","ifloat","idouble","ireal","cfloat","cdouble","creal","void"];

enum storageClasses=["abstract","auto","auto ref","const","deprecated","enum","extern","final","immutable","in","inout","lazy","nothrow","out","override","pure","__gshared","ref","scope","shared","static","synchronized"];

immutable toplevelSTC=["abstract","auto","auto ref","const","deprecated","enum","extern","final","immutable","inout","shared","nothrow","override","pure","__gshared","scope","static","synchronized"];

immutable attributeSTC=["property","safe","trusted","system","disable"];

immutable functionSTC=["const","immutable","inout","nothrow","pure","shared"];

immutable parameterSTC=["auto","const","final","immutable","in","inout","lazy","out","ref","scope","shared"];

enum typeQualifiers=["const","immutable","shared","inout"];


private string STCEnum(){
	string r="enum{";
	foreach(i,s;storageClasses~attributeSTC) r~="STC"~(s=="auto ref"?"autoref":s)~"="~to!string(1<<i)~",";
	return r~"}";
}
//enum{STC...}; Solved this way because most storage classes are keywords and composition will be sane
mixin(STCEnum());
static assert(storageClasses.length+attributeSTC.length<32);
alias int STC;
string STCtoString(STC stc){
	if(!stc) return "";
	STC fstc=stc&-stc;
	stc-=fstc;
	int n=0; while(1<<n<fstc) n++; 
	string r=storageClasses[n]; 
	foreach(i,s;storageClasses) if(stc&(1<<i)) r~=" "~s;
	foreach(i,s;attributeSTC) if(stc&(1<<(storageClasses.length+i))) r~=" @"~s;
	return r;
}



private string getTTCases(string[] s){
	string r="case ";
	foreach(x;s) r~="Tok!\""~x~"\",";
	return r[0..$-1]~":";
}

template isBasicType(TokenType type){
	enum bool isBasicType = canFind(basicTypes,TokChars!type);
}

immutable leftDelimiters=["(","{","["];

template isLeftDelimiter(TokenType type){
	enum bool isLeftDelimiter = canFind(leftDelimiters,TokChars!type) !=null;
}
template matchingDelimiter(TokenType left) if(isLeftDelimiter){
	enum matchingDelimiter = {
		switch(left){
			case Tok!"(": return Tok!")";
			case Tok!"{": return Tok!"}";
			case Tok!"[": return Tok!"]";
			default: assert(0);
		}
	}();
}
//Private template isCode(R){enum isCode=isForwardRange!R && is(Unqual!(ElementType!R) == Token);}


private template getParseProc(T...){
	static if(is(T[0]==AssignExp)) enum prc=`parseExpression(rbp!(Tok!","))`, off=2;
	else static if(is(T[0]==ArgumentList)||is(T[0]==AssocArgumentList)){ // ArgumentList, AssocArgumentList can take optional parameters
		static if(T[2][0]=='('&&T[2][$-1]==')')
			enum prc=`parse`~T[0].stringof~`!`~T[3].stringof~T[2], off=3;
		else enum prc=`parse`~T[0].stringof~`!`~T[2].stringof~"()", off=2;
	}else enum prc="parse"~T[0].stringof~"()", off=2;
}
//dummy structs for some of the parsing procedures:
private struct ArgumentList{}
private struct AssocArgumentList{}
private struct IdentifierList{}
private struct AssignExp{}
private struct Condition{}
private struct Existing{}

private template TTfromStr(string arg){ // turns "a,b,c,..." into TypeTuple(a,b,c,...)
	alias TypeTuple!(mixin("TypeTuple!("~arg~")")) TTfromStr;
}

private template doParseImpl(bool d,T...){
	static if(T.length==0) enum doParseImpl="";
	else static if(is(typeof(T[0]):string)) enum doParseImpl={
			static if(T[0].length>3 && T[0][0..3]=="OPT") return doOptParse!(TTfromStr!(T[0][3..$]))~doParseImpl!(d,T[1..$]);
			else switch(T[0]){
				case "_": return "nextToken();\n"~doParseImpl!(d,T[1..$]);
				case "NonEmpty": return "nonEmpty();\n"~doParseImpl!(d,T[1..$]);
				case "OPT":
				static if(T[0]=="OPT")
					return (d?"auto ":"")~T[2]~" = tok.type==Tok!\""~T[3]~"\" ? null : "~"parse"~T[1].stringof~"();\n"~doParseImpl!(d,T[3..$]);
				default: return "expect(Tok!\""~T[0]~"\");\n"~doParseImpl!(d,T[1..$]);;
			}
		}();
	else static if(is(T[0]==Existing)) alias doParseImpl!(d,T[2..$]) doParseImpl;
	else enum doParseImpl=(d?"auto ":"")~T[1]~" = "~getParseProc!T.prc~";\n"~doParseImpl!(d,T[getParseProc!T.off..$]);
}

private template doParse(T...){
	alias doParseImpl!(true,T) doParse;
}

private template parseDefOnly(T...){
	static if(T.length==0) enum parseDefOnly="";
	else static if(is(typeof(T[0]):string)){
		static if(T[0]=="OPT") alias parseDefOnly!(T[1..$]) parseDefOnly;
		else alias parseDefOnly!(T[1..$]) parseDefOnly;
	}else static if(is(T[0]==Existing)) alias parseDefOnly!(T[2..$]) parseDefOnly;
	else enum parseDefOnly=typeof(mixin("Parser."~getParseProc!T.prc)).stringof~" "~T[1]~" = null;\n"~parseDefOnly!(T[2..$]);
}
private template doOptParse(T...){
	static assert(is(typeof(T[0]):string));
	enum doOptParse=parseDefOnly!T~"if(tok.type==Tok!\""~T[0]~"\"){\n"~doParseImpl!(false,"_",T[1..$])~"}\n";
}

private template fillParseNamesImpl(int n,string b,T...){
	static if(T.length==0){alias T val; enum off=0;}
	else static if(is(typeof(T[0])==string)){
		static if(T[0].length>3 && T[0][0..3]=="OPT"){
			private alias fillParseNamesImpl!(n,b,TTfromStr!(T[0][3..$])) a;
			static assert(a.val.stringof[0..6]=="tuple(", "apparently something has finally been fixed");
			alias TypeTuple!("OPT"~a.val.stringof[6..$-1],fillParseNamesImpl!(n+a.off,b,T[1..$]).val) val;
			alias a.off off;
		}else{
			private alias fillParseNamesImpl!(n,b,T[1..$]) rest;
			alias TypeTuple!(T[0],rest.val) val;enum off=rest.off;
		}
	}else static if(is(T[0]==Existing)){
		private alias fillParseNamesImpl!(n,b,T[2..$]) rest;
		alias TypeTuple!(T[0],T[1],rest.val) val; enum off=rest.off;
	}else{
		private alias fillParseNamesImpl!(n+1,b,T[1..$]) rest;
		alias TypeTuple!(T[0],b~to!string(n),rest.val) val;enum off=rest.off+1;
	}
}

private template fillParseNames(string base,T...){
	alias fillParseNamesImpl!(0,base,T).val fillParseNames;
}
private template getParseNames(T...){
	static if(T.length==0) enum getParseNames=""; // next line: ':' instead of '==' is workaround
	else static if(!is(typeof(T[0]):string)) enum getParseNames=T[1]~","~getParseNames!(T[2..$]);
	else{
		static if(T[0].length>3 && T[0][0..3]=="OPT") enum getParseNames=getParseNames!(TTfromStr!(T[0][3..$]))~getParseNames!(T[1..$]);
		else enum getParseNames=getParseNames!(T[1..$]);
	}
}

private template rule(T...){ // applies a grammar rule and returns the result
	enum rule={
		alias fillParseNames!("e",T[1..$]) a;
		return doParse!(a)~"return new "~T[0].stringof~"("~getParseNames!a~");";
	}();
}


alias immutable(Token)[] Code;

private struct Parser{
	enum filename = "tt.d";
	Code code;
	Token tok;
	Location loc;
	this(Code code){
		this.code = code;
		this.loc = Location(filename,1);
		nextToken();
	}
	void nextToken(){
	tryagain:
		if(code.empty) return tok=token!"EOF";
		tok = code.front();
		code.popFront();
		if(tok.type==Tok!"\n"){loc.line++; goto tryagain;}
		else if(tok.type==Tok!"Error"){loc.error(tok.str); goto tryagain;}
	}
	Token peek(int x=1){
		auto save = code.save, tt=tok, sloc=loc;
		foreach(i;0..x) nextToken();
		auto t=tok;
		code = save, tok=tt, loc=sloc;
		return t;
	}
	static class ParseErrorException: Exception{this(string s){super(s);}} alias ParseErrorException PEE;
	void error(string msg){loc.error(msg);}
	void expect(TokenType type){
		if(tok.type!=type) error("found '" ~ tok.toString() ~ "' when expecting '" ~ Token(type).toString() ~"'");
		else nextToken();
	}
	void expectErr(string what)(){
		error("found '" ~ tok.toString() ~ "' when expecting " ~ what);
	}
	bool skip(TokenType type){
		if(tok.type != type) return false;
		nextToken(); return true;
	}
	bool skip(){nextToken(); return true;}
	auto dp(alias a, T...)(T args,ref Token t){ // dynamic dispatch based on token type (TODO: redesign, too much code replication)
		final switch(t.type){
			mixin({
				string r;
				foreach(t;__traits(allMembers, TokenType)) r~=`case TokenType.` ~ t ~ `:  return a!(TokenType.` ~ t ~ `)(args,t);`;
				return r;
			}());
		}
	}
	Expression parseIdentifierList(T...)(T args){
		void errori(){expectErr!"identifier following '.'"();}
		static if(T.length==0){
			if(tok.type!=Tok!"i"){expectErr!"identifier"(); return new ErrorExp;}
			Expression e = new IdentifierExp(tok.str); nextToken();
		}else{Expression e=args[0]; goto middle;}
		for(;;){
			if(tok.type==Tok!"."){
				nextToken(); 
			middle:
				if(tok.type!=Tok!"i"){errori(); return new BinaryExp!(Tok!".")(e,new ErrorExp);}
				e = new BinaryExp!(Tok!".")(e,new IdentifierExp(tok.str));
				nextToken();
			}else if(tok.type==Tok!"!"){auto t=tok; nextToken(); e=led!(Tok!"!")(e,t);}
			else break;
		}
		return e;
	}
	bool skipIdentifierList(){
		if(!skip(Tok!"i")) return false;
		for(;;){
			if(skip(Tok!".")){if(!skip(Tok!"i")) return false;}
			else if(skip(Tok!"!")){
				if(tok.type==Tok!"("){
					nextToken();
					if(!skipToUnmatched()||!skip(Tok!")")) return false;
				}else skip();
			}else return true;
		}
	}
	Expression[] parseArgumentList(string delim, bool nonempty=false,T...)(T args){
		Expression[] e;
		foreach(x;args) e~=x; // static foreach
		static if(args.length) if(tok.type==Tok!",") nextToken(); else return e;
		static if(!nonempty) if(tok.type==Tok!delim) return e;
		do{
			e~=parseExpression(rbp!(Tok!","));
			if(tok.type==Tok!",") nextToken();
			else break;
		}while(tok.type!=Tok!delim && tok.type!=Tok!"EOF");
		return e;
	}
	Expression[2][] parseAssocArgumentList(string delim, bool nonempty=false,T...)(T args) if(T.length%2==0){
		Expression[2][] e;
		e.length=args.length/2;
		foreach(i,x;args) e[i/2][i%2]=x; // static foreach
		static if(args.length) if(tok.type==Tok!",") nextToken();
		static if(!nonempty) if(tok.type==Tok!delim) return e;
		do{
			mixin(doParse!(AssignExp,"e1",":",AssignExp,"e2"));
			e.length=e.length+1; e[$-1][0]=e1, e[$-1][1]=e2;
			if(tok.type==Tok!",") nextToken();
			else break;
		}while(tok.type!=Tok!delim && tok.type!=Tok!"EOF");
		return e;
	}
	// Operator precedence expression parser
	// null denotation
	Expression nud(TokenType type)(ref Token self) {
		static if(type==Tok!"i") return new IdentifierExp(self.name);
		else static if(isBasicType!type){expect(Tok!".");return parseIdentifierList(new BasicType(type));}
		else static if(type == Tok!"this") return new ThisExp();
		else static if(type == Tok!"super") return new SuperExp();
		else static if(type == Tok!"__error") return new ErrorExp();
		else static if(isLiteral!type) return new LiteralExp(self);
		else static if(type==Tok!"("){ //TODO: (Type).identifierList
			mixin(doParse!(Expression,"e",")")); e.brackets=true;
			return e;
		}else static if(type==Tok!"["){
			mixin(doParse!(AssignExp,"e"));
			if(tok.type!=Tok!":"){
				mixin(rule!(ArrayLiteralExp,ArgumentList,"(e)","]"));
			}else{
				mixin(doParse!(":",AssignExp,"e2"));
				mixin(rule!(AssocArrayLiteralExp,AssocArgumentList,"(e,e2)","]"));
			}
		}else static if(isUnaryOp!type) return new UnaryExp!type(parseExpression(nbp));
		else static if(type == Tok!"new"){mixin(rule!(NewExp,"OPT"q{"(",ArgumentList,")"},Type,"OPT"q{"(",ArgumentList,")"}));}
		else static if(type == Tok!"assert"){mixin(rule!(AssertExp,"(",ArgumentList,")"));}
		else static if(type == Tok!"mixin"){mixin(rule!(MixinExp,"(",AssignExp,")"));}
		else static if(type == Tok!"import"){mixin(rule!(ImportExp,"(",AssignExp,")"));}
		else static if(type==Tok!"typeof"){
			expect(Tok!"(");
			if(tok.type==Tok!"return"){nextToken(); expect(Tok!")"); return new TypeofReturnExp();}
			mixin(doParse!(Expression,"e1",")"));
			Expression e2=new TypeofExp(e1);
			if(tok.type==Tok!"."){nextToken(); e2=parseIdentifierList(e2);}
			return e2;
		}else static if(type == Tok!".") return parseIdentifierList(new IdentifierExp(""));
		else throw new PEE("invalid unary operator '"~self.toString()~"'");
	}
	// left denotation
	Expression led(TokenType type)(Expression left, ref Token self){
		//static if(type == Tok!"i") return new CallExp(new BinaryExp!(Tok!".")(left,new IdentifierExp(self.name)),parseExpression(45));else // infix
		static if(type == Tok!"?"){mixin(rule!(TernaryExp,Existing,"left",Expression,":",Expression));}
		else static if(type == Tok!"["){
			if(tok.type==Tok!"]"){nextToken(); return new IndexExp(left,[]);}
			auto l=parseExpression(rbp!(Tok!","));
			if(tok.type==Tok!".."){nextToken(); auto r=parseExpression(rbp!(Tok!",")); expect(Tok!"]"); return new SliceExp(left, l,r);}
			else{auto e=new IndexExp(left,parseArgumentList!"]"(l)); expect(Tok!"]"); return e;}
		}
		else static if(type == Tok!"("){mixin(rule!(CallExp,Existing,"left",ArgumentList,")"));}
		else static if(type == Tok!"!"){
			// TODO: replace parseArgumentList with parseTypeTuple
			if(tok.type==Tok!"("){nextToken();auto e=new TemplateInstanceExp(left,parseArgumentList!")"); expect(Tok!")"); return e;}
			return new TemplateInstanceExp(left,[parseExpression(.rbp!type)]);
		}
		else static if(type == Tok!".") return parseIdentifierList(left);
		else static if(isBinaryOp!type) return new BinaryExp!type(left,parseExpression(rbp!type));
		else static if(isPostfixOp!type) return new PostfixExp!type(left);
		else throw new PEE("invalid binary operator '"~TokChars!type~"'");
	}
	Expression parseExpression(int rbp = 0){
		auto t = tok;
		nextToken();
		Expression left;
		try left = dp!nud(t);catch(PEE err){error("found '"~t.toString()~"' when expecting expression");return new ErrorExp();}
		while(rbp < getLbp(tok.type)){ // TODO: replace with array lookup
			t = tok;
			nextToken();
			try left = dp!led(left,t); catch(PEE err){error(err.msg);}
		}
		return left;
	}
	Expression parseExpression2(Expression left, int rbp = 0){ // already know what left is
		while(rbp < getLbp(tok.type)){ // TODO: replace with array lookup
			auto t = tok;
			nextToken();
			try left = dp!led(left,t); catch(PEE err){error(err.msg);}
		}
		return left;
	}
	bool skipToUnmatched(bool skipcomma=true)(){
		int pnest=0, cnest=0, bnest=0; // no local templates >:(
		for(;;nextToken()){
			switch(tok.type){
				case Tok!"(": pnest++; continue;
				case Tok!"{": cnest++; continue;
				case Tok!"[": bnest++; continue;
				case Tok!")": if(pnest--) continue; break;
				case Tok!"}": if(cnest--) continue; break;
				case Tok!"]": if(bnest--) continue; break;
				static if(!skipcomma) case Tok!",": if(pnest) continue; break;
				case Tok!";": if(cnest) continue; break;
				case Tok!"EOF": return false;
				//case Tok!"..": if(bnest) continue; break;
				default: continue;
			}
			break;
		}
		return true;
	}
	void nonEmpty(){if(tok.type==Tok!";") error("use '{}' for an empty statement, not ';'");}
	Statement parseStmError(){
		while(tok.type != Tok!";" && tok.type != Tok!"}" && tok.type != Tok!"EOF") nextToken();
		if(tok.type == Tok!";") nextToken();
		return new ErrorStm;
	}
	private static template pStm(T...){
		enum pStm="case Tok!\""~T[0]~"\":\n"~rule!(mixin(T[0][0]+('A'-'a')~T[0][1..$]~"Stm"),"_",T[1..$]);
	}
	Statement parseStatement(){ // TODO: parse DeclarationStm
		bool isfinal = false; //for final switch
		if(tok.type == Tok!"i" && peek().type == Tok!":"){
			auto l = new IdentifierExp(tok.name);
			nextToken(); nextToken();
			return new LabeledStm(l,parseStatement());
		}
		switch(tok.type){
		    case Tok!";":
			    nextToken();
				return new Statement;
		    case Tok!"{":
				return parseCompoundStm();
			mixin(pStm!("if","(",Condition,")","NonEmpty",Statement,"OPT"q{"else","NonEmpty",Statement}));
			mixin(pStm!("while","(",Condition,")","NonEmpty",Statement));
			mixin(pStm!("do","NonEmpty",Statement,"while","(",Expression,")",";"));
			mixin(pStm!("for","(",Statement,"OPT",Condition,";","OPT",Expression,")","NonEmpty",Statement));
			case Tok!"foreach":
				error("foreach not implemented yet!");
				return parseStmError();
			case Tok!"final":
				if(peek().type != Tok!"switch") goto default;
				nextToken();
				isfinal=true;
			case Tok!"switch":
				mixin(doParse!("_","(",Expression,"e",")","NonEmpty",Statement,"s"));
				return new SwitchStm(isfinal,e,s);
			case Tok!"case":
				Expression[] e;
				Statement[] s;
				bool isrange=false;
				nextToken();
				e = parseArgumentList!(":",true)(); // non-empty!
				expect(Tok!":");				
				
				if(tok.type == Tok!".."){ // CaseRange
					isrange=true;
					if(e.length>1) error("only one case allowed for start of case range");
					e.length=2;
					nextToken();
					expect(Tok!"case");
					e[1]=parseExpression(lbp!(Tok!","));
					expect(Tok!":");
				}
				
				do s~=parseStatement();while(tok.type!=Tok!"case" && tok.type!=Tok!"default" && tok.type!=Tok!"}"&&tok.type!=Tok!"EOF");
				return isrange?new CaseRangeStm(e[0],e[1],s):new CaseStm(e,s);
			case Tok!"default":
				mixin(doParse!("_",":"));
				Statement[] s;
				do s~=parseStatement();while(tok.type!=Tok!"case" && tok.type!=Tok!"default" && tok.type!=Tok!"}"&&tok.type!=Tok!"EOF");
				return new DefaultStm(s);
			case Tok!"continue":
				nextToken();
				Statement r;
				if(tok.type==Tok!"i") r=new ContinueStm(new IdentifierExp(tok.name)), nextToken();
				else r=new ContinueStm(null);
				expect(Tok!";");
				return r;
			//mixin(pStm!("break", "OPT", Identifier, ";");
			case Tok!"break":
				nextToken();
				Statement r;
				if(tok.type==Tok!"i") r=new BreakStm(new IdentifierExp(tok.name)), nextToken();
				else r=new BreakStm(null);
				expect(Tok!";");
				return r;
			mixin(pStm!("return","OPT",Expression,";"));
			case Tok!"goto":
				nextToken();
				switch(tok.type){
					case Tok!"i":
						auto r=new GotoStm(WhichGoto.identifier,new IdentifierExp(tok.name));
						nextToken(); expect(Tok!";");
						return r;
					case Tok!"default":
						nextToken();
						expect(Tok!";");
						return new GotoStm(WhichGoto.default_,null);
					case Tok!"case":
						nextToken();
						if(tok.type == Tok!";"){nextToken(); return new GotoStm(WhichGoto.case_,null);}
						auto e = parseExpression();
						expect(Tok!";");
						return new GotoStm(WhichGoto.caseExp,e);
					default:
						expectErr!"location following goto"();
						return parseStmError();
				}
			mixin(pStm!("with","(",Expression,")","NonEmpty",Statement));
			mixin(pStm!("synchronized","OPT"q{"(",Expression,")"},Statement));
			case Tok!"try":
				error("try not implemented yet!");
				return parseStmError();
			mixin(pStm!("throw",Expression,";"));
			case Tok!"scope":
				if(peek().type != Tok!"(") goto default;
				nextToken(); nextToken();
				WhichScopeGuard w;
				if(tok.type != Tok!"i"){expectErr!"scope identifier"(); return parseStmError();}
				switch(tok.name){
					case "exit": w=WhichScopeGuard.exit; break;
					case "success": w=WhichScopeGuard.success; break;
					case "failure": w=WhichScopeGuard.failure; break;
					default: error("valid scope identifiers are exit, success, or failure, not "~tok.name); return parseStmError();
				}
				nextToken();
				expect(Tok!")");
				return new ScopeGuardStm(w,parseStatement());
			case Tok!"asm":
				nextToken();
				expect(Tok!"{");
				error("inline assembler not implemented yet!");
				expect(Tok!"}");
				return new ErrorStm;
			case Tok!"mixin":
				if(peek().type!=Tok!"(") goto default; // mixin template declaration
				mixin(doParse!("_","_",AssignExp,"e",")"));
				if(tok.type != Tok!";"){// is mixin expression, not mixin statement
					auto e2=parseExpression2(new MixinExp(e));
					expect(Tok!";");
					return new ExpressionStm(e2);
				}
				nextToken();
				return new MixinStm(e);
			default:
				if(auto d=tryParseDeclDef()) return d;
				auto e = parseExpression(); // note: some other cases may invoke parseExpression2 and return an ExpressionStm!
				expect(Tok!";");
				return new ExpressionStm(e);
		}
	}
	//auto parse(){return parseStatement();}
	Expression parseType(){
		Expression tt;
		switch(tok.type){
			mixin(getTTCases(basicTypes)); tt = new BasicType(tok.type); nextToken(); break;
			case Tok!".": nextToken(); tt=parseIdentifierList(new IdentifierExp("")); break;
			case Tok!"i": tt=parseIdentifierList(); break;
			mixin({string r;
					foreach(x;typeQualifiers) r~=`case Tok!"`~x~`": nextToken(); expect(Tok!"(");tt=new QualifiedType!"`~x~`"(parseType());expect(Tok!")"); break;`;
					return r;}());
			case Tok!"typeof": auto t=tok; nextToken(); tt=nud!(Tok!"typeof")(t); break;
			default: error("expected type, not '"~tok.toString()~"'"); nextToken(); return new ErrorExp;
		}
		for(;;){
			switch(tok.type){
				case Tok!"*": nextToken(); tt=new Pointer(tt); continue;
				case Tok!"[": auto t=tok; nextToken(); //TODO: skipType, if(tok.type==Tok!"]") etc;else
				tt=led!(Tok!"[")(tt,t); continue; //'Bug': allows int[1,2].
				case Tok!"function":
					nextToken();
					VarArgs vararg;
					auto params=parseParameterList(vararg);
					STC stc=parseSTC!functionSTC();
					tt=new FunctionPtr(new FunctionType(stc,tt,params,vararg));
					continue;
				case Tok!"delegate":
					nextToken();
					VarArgs vararg;
					auto params=parseParameterList(vararg);
					STC stc=parseSTC!functionSTC();
					tt=new DelegateType(new FunctionType(stc,tt,params,vararg));
					continue;
				default: break;
			}
			break;
		}
		return tt;
	}
	bool skipType(){
		switch(tok.type){
			mixin(getTTCases(basicTypes)); nextToken(); break;
			case Tok!".": nextToken(); case Tok!"i": 
				if(!skipIdentifierList()) goto Lfalse; break;
			mixin({string r;
					foreach(x;typeQualifiers) r~=`case Tok!"`~x~`": nextToken(); if(!skip(Tok!"(")||!skipType()||!skip(Tok!")")) return false; break;`;
					return r;}());
			case Tok!"typeof":
				nextToken();
				if(!skip(Tok!"(")||!skipToUnmatched()||!skip(Tok!")")) goto Lfalse;
				if(tok.type==Tok!"."){
					nextToken();
					if(!skipIdentifierList()) goto Lfalse;
				}
				break;
			default: goto Lfalse;
		}
	skipbt2: for(;;){
			switch(tok.type){
				case Tok!"*": nextToken(); continue;
				case Tok!"[": 
					nextToken(); 
					if(!skipToUnmatched()||!skip(Tok!"]")) goto Lfalse;
					continue;
				case Tok!"function", Tok!"delegate":
					nextToken();
					if(!skip(Tok!"(")||!skipToUnmatched()||!skip(Tok!")")) goto Lfalse;
					skipSTC!functionSTC();
					continue;
				default: return true;
			}
		}
	Lfalse: return false;
	}
	Expression parseInitializer(){return parseExpression(rbp!(Tok!","));}
	STC parseSTC(alias which,bool properties=true)(){
		STC stc,cstc;
	readstc: for(;;){
			switch(tok.type){
				mixin({string r;
						foreach(x;which){
							if(x=="auto ref") continue;
							else r~="case Tok!\""~x~"\": "~(typeQualifiers.canFind(x)?"if(peek().type==Tok!\"(\") break readstc;":"")~
								     (x=="auto"&&(cast(immutable(char[])[])which).canFind("auto ref")?
								      "if(peek().type!=Tok!\"ref\") cstc=STCauto;else{nextToken();cstc=STCautoref;}":
								      "cstc=STC"~x)~";"~"goto Lstc;";
						}
						return r;}());
				static if(properties){
					case Tok!"@":
						nextToken();
						if(tok.type!=Tok!"i"){expectErr!"attribute identifier after '@'"(); nextToken(); continue;}
						switch(tok.name){
							mixin({string r;foreach(x;attributeSTC) r~="case \""~x~"\": cstc=STC"~x~"; goto Lstc;";return r;}());
							default: error("unknown attribute identifier '"~tok.name~"'");
						}
				}
				Lstc:
					if(stc&cstc) error("redundant storage class "~tok.name);
					stc|=cstc;
					nextToken();
					break;
				default:
					break readstc;
			}
		}
		return stc;
	}
	bool skipSTC(alias which,bool properties=true)(){
		bool ret=false;
		for(;;nextToken()){
			switch(tok.type){
				mixin({string r;
						foreach(x;which){
							if(x=="auto ref") continue;
							r~="case Tok!\""~x~"\": "~(typeQualifiers.canFind(x)?"if(peek().type==Tok!\"(\") break;":"")~"ret=true; continue;";
						}
						return r;}());
				case Tok!"@": nextToken(); ret=true; continue;
				default: return ret;
			}
			break;
		}
		return ret;
	}
	CompoundStm parseCompoundStm(){
		expect(Tok!"{");
		Statement[] s;
		while(tok.type!=Tok!"}" && tok.type!=Tok!"EOF"){
			s~=parseStatement();
		}
		expect(Tok!"}");
		return new CompoundStm(s);
	}
	Declaration parseDeclaration(){
		Expression type;
		Declaration d;
		STC stc;
		bool isAlias=tok.type==Tok!"alias";
		if(isAlias) nextToken();
		stc=parseSTC!toplevelSTC();
		TokenType p;
		if(!stc||(tok.type!=Tok!"i" || (p=peek().type)!=Tok!"=" && p!=Tok!"(")) type=parseType();
		if(peek.type==Tok!"(") d=parseFunctionDeclaration(stc,type);
		else d=parseDeclarators(stc,type);
		if(isAlias) d=new AliasDecl(d);
		return d;
	}
	Expression parseCondition(){
		if(!isDeclaration()) return parseExpression(rbp!(Tok!","));
		else{
			Expression type,init;
			auto stc=parseSTC!toplevelSTC();
			if(!stc||tok.type!=Tok!"i") type=parseType();
			if(tok.type!=Tok!"i"){expectErr!"identifier"; skipToUnmatched(); return new ErrorExp;}
			auto name=new IdentifierExp(tok.name); nextToken();
			if(tok.type!=Tok!"="){expectErr!"initializer for condition"(); skipToUnmatched(); return new ErrorExp;}
			nextToken();
			init=parseInitializer();
			return new ConditionDeclExp(stc,type,name,init);
		}
	}
	bool skipDeclaration(){
		TokenType p;
		if(tok.type==Tok!"alias") nextToken();
		if(skipSTC!toplevelSTC()){
			if(tok.type!=Tok!"i" || (p=peek().type)!=Tok!"=" && p!=Tok!"(" && !skipType()) return false;
		}else if(!skipType()) return false;
		return peek().type==Tok!"(" && skipFunctionDeclaration() || skipDeclarators();
	}
	bool isDeclaration(){ // is the parser sitting on the beginning of a Declaration?
		auto save=code.save, tt=tok, sloc=loc; // save current position
		bool res=skipDeclaration();
		code=save, tok=tt, loc=sloc;
		return res;
	}
	Parameter[] parseParameterList(out VarArgs vararg){
		vararg=VarArgs.none;
		Parameter[] params;
		expect(Tok!"(");
		for(;;){
			STC stc;
			Expression type;
			IdentifierExp name;
			Expression init;
			if(tok.type==Tok!")") break;
			else if(tok.type==Tok!"..."){vararg=VarArgs.cStyle; nextToken(); break;}
			stc=parseSTC!(parameterSTC, false)(); // false means no @attributes allowed
			type=parseType();
			if(tok.type==Tok!"i"){name=new IdentifierExp(tok.name); nextToken();}
			if(tok.type==Tok!"="){nextToken();init=parseInitializer();}
			params~=new Parameter(stc,type,name,init);
			if(tok.type==Tok!",") nextToken();
			else{
				if(tok.type==Tok!"..."){vararg=VarArgs.dStyle; nextToken();}
				break;
			}
		}
		expect(Tok!")");
		return params;
	}
	void parsePostcondition(out CompoundStm post,out IdentifierExp pres){ // out(pres){...}
		expect(Tok!"out");
		if(tok.type==Tok!"("){
			nextToken();
			if(tok.type==Tok!"i"){
				pres=new IdentifierExp(tok.name);
				nextToken();
			}else expect(Tok!"i");
			expect(Tok!")");
		}
		post=parseCompoundStm();
	}
	FunctionDecl parseFunctionDeclaration(STC stc, Expression ret){// BUG: Does not yet parse template functions
		string name;
		if(tok.type!=Tok!"i") expectErr!"function name"();
		else{name=tok.name;nextToken();}
		VarArgs vararg;
		auto params=parseParameterList(vararg);
		stc|=parseSTC!functionSTC();
		CompoundStm pre, post, bdy;
		IdentifierExp pres;
		if(tok.type==Tok!"in"){
			nextToken(); pre=parseCompoundStm();
			if(tok.type==Tok!"out") parsePostcondition(post,pres);
		}else if(tok.type==Tok!"out"){
			parsePostcondition(post,pres);
			if(tok.type==Tok!"in"){nextToken();pre=parseCompoundStm();}
		}
		if(tok.type==Tok!"{"||tok.type==Tok!"body"){
			if(pre||post) expect(Tok!"body");
			bdy=parseCompoundStm();
			return new FunctionDef(new FunctionType(stc,ret,params,vararg),new IdentifierExp(name),pre,post,pres,bdy);
		}else{
			if(!pre&&!post) expect(Tok!";");
			return new FunctionDecl(new FunctionType(stc,ret,params,vararg),new IdentifierExp(name),pre,post,pres);
		}
	}
	bool skipFunctionDeclaration(){ // does not skip Parameters, STC contracts or body. I think it does not have to.
		return skip(Tok!"i") && skip(Tok!"(");// && skipToUnmatched() && skip(Tok!")");//skipSTC!functionSTC();
	}
	Declaration parseDeclarators(STC stc, Expression type){
		VarDecl[] r;
		do{
			string name;
			Expression init;
			if(tok.type==Tok!"i") name = tok.name, nextToken();
			else expectErr!"identifier"();
			if(tok.type==Tok!"=") nextToken(), init=parseInitializer();
			r~=new VarDecl(stc,type,new IdentifierExp(name),init);
			if(tok.type==Tok!",") nextToken();else break;
		}while(tok.type != Tok!";" && tok.type != Tok!"EOF"); 
		expect(Tok!";");
		return r.length>1?new Declarators(r):r[0];
	}
	bool skipDeclarators(){ // only makes sure there is at least one declarator
		return skip(Tok!"i");// && (skip(Tok!"=")||skip(Tok!",")||skip(Tok!";"));
	}
	Declaration parseImportDecl(bool isStatic=false){
		expect(Tok!"import");
		Expression[] symbols;
		bool isBindings=false;
		for(;;){
			Expression s=parseIdentifierList();
			if(tok.type==Tok!"=") nextToken(), s=new BinaryExp!(Tok!"=")(s,parseIdentifierList());
			else if(!symbols.length&&tok.type==Tok!":"){nextToken(); isBindings=true; symbols~=s; continue;}
			symbols~=s;
			if(tok.type==Tok!",") nextToken();
			else break;
		}
		expect(Tok!";");
		return isBindings ? new ImportBindingsDecl(isStatic,symbols[0],symbols[1..$]) : new ImportDecl(isStatic, symbols);
	}
	EnumDecl parseEnumDecl(){
		expect(Tok!"enum");
		IdentifierExp tag;
		Expression base;
		Expression[2][] members;
		if(tok.type==Tok!"i") tag=new IdentifierExp(tok.name), nextToken();
		if(tok.type==Tok!":") nextToken(), base = parseType();
		expect(Tok!"{");
		for(;tok.type!=Tok!"}" && tok.type!=Tok!"EOF";){ // BUG: only uniform type allowed
			Expression e,i;
			if(tok.type==Tok!"i") e=new IdentifierExp(tok.name), nextToken();
			else break;
			if(tok.type==Tok!"=") nextToken(), i=parseInitializer();
			members.length=members.length+1;
			members[$-1][0]=e;
			members[$-1][1]=i;
			if(tok.type==Tok!",") nextToken();
			else break;
		}
		expect(Tok!"}");
		return new EnumDecl(tag,base,members);
	}
	Declaration tryParseDeclDef(){
		// TODO: Add attributes
		bool isStatic=false;
		switch(tok.type){
			case Tok!"static":
				isStatic=true;
				auto x=peek();
				if(x.type==Tok!"import"){nextToken(); goto case Tok!"import";}
				goto default;
			case Tok!"import": return parseImportDecl(isStatic);
			case Tok!"enum":
				auto x=peek(), y=peek(2);
				if(x.type!=Tok!"{" && x.type!=Tok!":" && x.type!=Tok!"i" || x.type==Tok!"i" && y.type!=Tok!"{" && y.type!=Tok!":") goto default;
				return parseEnumDecl();
			default: return isDeclaration() ? parseDeclaration() : null;
		}
	}

	auto parse(){return parseStatement();}
	//auto parse(){return skipDeclarations()?"wee, declarations":"boring statement";}
}

auto parse(Code code){
	return Parser(code).parse();
}



