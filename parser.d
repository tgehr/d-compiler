module parser;

import std.array, std.range, std.algorithm, std.traits, std.conv: to;

import lexer;

template numClasses(T...){
	static if(T.length == 0) enum numClasses = 0;
	else enum numClasses = is(T[0] == class) + numClasses!(T[1..$]);
}

private template finalParse(string name,int p){
	enum finalParse = {string r=name~"(";foreach(t;0..p) r~="_"~to!string(t)~","; return r~");\n";};
}

private template getParseImpl(string name,int p,T...){
	static if(T.length == 0) enum getParseImpl = "return "~finalParse!(name,p)();
	else static if(is(typeof(T[0]==string))) enum getParseImpl = "expect(Tok!\""~T[0]~"\");\n" ~ getParseImpl!(name,p,T[1..$]);
	else static if(is(T[0] == class)) enum getParseImpl = "auto _"~to!string(p)~"="~T[0].parse~";\n"~getParseImpl!(name,p+1,T[1..$]);
	else enum getParse = "parse"~T[0].stringof~"()";
}

mixin template getParse(T...){enum parse = "{\n"~getParseImpl!(this.stringof,0,T)~"}()";}

class Expression{
	Location loc;
	this(){}
	override string toString(){assert(0,"unknown expression.");}
	enum parse = "parseExpression()";
}
class Statement{enum parse = "parseStatement()";}
class DefinitionStm: Statement{}
class TypeAST{}


class ErrorExp: Expression{
	this(){}
	override string toString(){return "__error";}
}

class IdentifierExp: Expression{
	string name;
	this(string name){this.name = name;}
	override string toString(){return name;}
}

class LiteralExp: Expression{
	Token lit;
	this(Token literal){lit=literal;}
	override string toString(){return lit.toString();}
}

class UnaryExp(TokenType op): Expression{
	Expression e;
	this(Expression next){e = next;}
	override string toString(){return '('~TokChars!op~e.toString()~')';}
}
class PostfixExp(TokenType op): Expression{
	Expression e;
	this(Expression next){e = next;}
	override string toString(){return '('~e.toString()~TokChars!op~')';}
}
//TODO: Add ParameterList
//TODO: Merge IndexExp and CallExp
class IndexExp: Expression{
	Expression e;
	Expression a;
	this(Expression exp, Expression args){e=exp; a=args;}
	override string toString(){return e.toString()~'['~a.toString()~']';}
}
class CallExp: Expression{
	Expression e;
	Expression a;
	this(Expression exp, Expression args){e=exp; a=args;}
	override string toString(){return e.toString()~'('~a.toString()~')';}
}
class BinaryExp(TokenType op): Expression{
	Expression e1, e2;
	this(Expression left, Expression right){e1=left; e2=right;}
	override string toString(){return '(' ~ e1.toString() ~ TokChars!op ~ e2.toString() ~ ')';}
	//override string toString(){return e1.toString() ~ " "~ e2.toString~TokChars!op;} // RPN
}
class TernaryExp: Expression{
	Expression e1, e2, e3;
	this(Expression cond, Expression left, Expression right){e1=cond; e2=left; e3=right;}
	override string toString(){return '(' ~ e1.toString() ~ '?' ~ e2.toString() ~ ':' ~ e3.toString() ~ ')';}
}

class ExpressionStm: Statement{
	Expression e;
	this(Expression next){e=next;}
	override string toString(){return e.toString() ~ ';';}
}

class IfStm : Statement{
	mixin getParse!("if","(",Expression,")",Statement,"<?","else",Statement,"?>");
	pragma(msg,parse);
}
class ForStm : Statement{}
class WhileStm : Statement{}
class DoWhileStm : Statement{}


// expression parser:
// left binding power
template lbp(TokenType type){enum lbp=getLbp(type);}
// right binding power
template rbp(TokenType type){enum rbp=lbp!type-(type==Tok!"^^");} // ^^ binds weaker to the right than to the left

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
	/*/ prefix operator(ref Token self)s
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
	default: return -1;
	}
}

// unary exp binding power
template isLiteral(TokenType type){
	enum isLiteral = canFind(["``","''","0","0U","0L","0LU",".0f",".0",".0L"],TokChars!type);
}
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

template isLeftDelimiter(TokenType type){
	enum bool isLeftDelimiter = canFind(["(","{","["],TokChars!type) !=null;
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
//private template isCode(R){enum isCode=isForwardRange!R && is(Unqual!(ElementType!R) == Token);}

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
	static class ParseErrorException: Exception{this(string s){super(s);}} alias ParseErrorException PEE;
	void error(string msg){loc.error(msg);}
	void expect(TokenType type){
		if(tok.type!=type) error("found '" ~ tok.toString() ~ "' when expecting '" ~ Token(type).toString() ~"'");
		else nextToken();
	}
	auto dp(alias a, T...)(T args,ref Token t){ // dynamic dispatch based on token type
		final switch(t.type){
			mixin({
				string r;
				foreach(t;__traits(allMembers, TokenType)) r~=`case TokenType.` ~ t ~ `:  return a!(TokenType.` ~ t ~ `)(args,t);`;
				return r;
			}());
		}
	}
	// Operator precedence expression parser
	// null denotation
	Expression nud(TokenType type)(ref Token self) {
		static if(type==Tok!"i") return new IdentifierExp(self.name);
		else static if(type == Tok!"__error") return new ErrorExp();
		else static if(isLiteral!type) return new LiteralExp(self);
		else static if(type==Tok!"("){
			auto e=parseExpression(0);
			expect(Tok!")");
			return e;
		}else static if(isUnaryOp!type) return new UnaryExp!type(parseExpression(nbp));
		else throw new PEE("invalid unary operator '"~tok.toString()~"'");
	}
	// left denotation
	Expression led(TokenType type)(Expression left, ref Token self){
		static if(type == Tok!"?"){
			auto e=parseExpression(0);
			expect(Tok!":");
			return new TernaryExp(left,e,parseExpression(0));
		}else static if(type == Tok!"["){auto e=new IndexExp(left,parseExpression(0)); expect(Tok!"]"); return e;}
		else static if(type == Tok!"("){auto e=new CallExp(left,parseExpression(0)); expect(Tok!")"); return e;} //TODO: Merge with preceding
		else static if(isBinaryOp!type) return new BinaryExp!type(left,parseExpression(.rbp!type));
		else static if(isPostfixOp!type) return new PostfixExp!type(left);
		else throw new PEE("invalid binary operator '"~TokChars!type~"'");
	}
	Expression parseExpression(int rbp = 0){
		retry:
		auto t = tok;
		nextToken();
		Expression left;
		try left = dp!nud(t); catch(PEE err){error(err.msg); if(tok.type==Tok!"EOF") return new ErrorExp(); goto retry;}
		while(rbp < getLbp(tok.type)){ // TODO: replace with array lookup
			t = tok;
			nextToken();
			try left = dp!led(left,t); catch(PEE err){error(err.msg);}
		}
		return left;
	}
	Statement parseStatement(){
		switch(tok.type){
			case Tok!"if":
				nextToken();
				expect(Tok!"(");
				Expression e = parseExpression(0);
				expect(Tok!")");
				//if(tok.type==Tok!";") error
			default:
				error("found '" ~ tok.toString() ~ "' instead of statement");
				return null; // error?
		}
	}
	auto parse(){return parseExpression();}
}

auto parse(Code code){
	return Parser(code).parse();
}

import std.stdio;
/*auto parseo(Code code) {
	if(code.empty) throw new Exception("code is empty");
	enum filename = "tt.d";
	auto loc = Location(filename,1);
	Token tok;
	void nextToken(){
		tryagain:
		if(code.empty) return tok=token!"EOF";
		tok = code.front();
		code.popFront();
		if(tok.type==Tok!"\n"){loc.line++; goto tryagain;}
		else if(tok.type==Tok!"Error"){loc.error(tok.str); goto tryagain;}
	}
	nextToken();
	static class ParseErrorException: Exception{this(string s){super(s);}} alias ParseErrorException PEE;
	static void delegate(TokenType) expectDG;
	static Expression delegate(int) tryParseTypeDG;
	static Expression delegate(int) parseExpressionDG;
	static Expression delegate() parseStatementDG;
	void expect(TokenType type){
		if(tok.type!=type) loc.error("found '" ~ tok.toString() ~ "' when expecting '" ~ Token(type).toString() ~"'");
		else nextToken();
	}
	expectDG = &expect;
	static auto tryParseType(bool skip=false,R...)(R args){ // returns null and leaves 'code' untouched if input is not a type
		
	}
	Expression parseExpression(int rbp = 0){
		// null denotation
		static Expression nud(TokenType type)(ref Token self) {
			static if(type==Tok!"i") return new IdentifierExp(self.name);
			else static if(type == Tok!"__error") return new ErrorExp();
			else static if(isLiteral!type) return new LiteralExp(self);
			else static if(type==Tok!"("){
				auto e=parseExpressionDG(0);
				expectDG(Tok!")");
				return e;
			}else static if(isUnaryOp!type) return new UnaryExp!type(parseExpressionDG(nbp));
			else throw new PEE("invalid unary operator '"~self.toString()~"'");
		}
		// left denotation
		static Expression led(TokenType type)(Expression left){
			static if(type == Tok!"?"){
				auto e=parseExpressionDG(0);
				expectDG(Tok!":");
				return new TernaryExp(left,e,parseExpressionDG(0));
			}else static if(type == Tok!"["){auto e=new IndexExp(left,parseExpressionDG(0)); expectDG(Tok!"]"); return e;}
			else static if(type == Tok!"("){auto e=new CallExp(left,parseExpressionDG(0)); expectDG(Tok!")"); return e;} //TODO: Merge with preceding
			else static if(isBinaryOp!type) return new BinaryExp!type(left,parseExpressionDG(.rbp!type));
			else static if(isPostfixOp!type) return new PostfixExp!type(left);
			else throw new PEE("invalid binary operator '"~TokChars!type~"'");
		}
		retry:
		auto t = tok;
		nextToken();
		Expression left;
		try left = t.dp!nud(); catch(PEE err){loc.error(err.msg); if(tok.type==Tok!"EOF") return new ErrorExp(); goto retry;}
		while(rbp < getLbp(tok.type)){ // TODO: replace with array lookup
			t = tok;
			nextToken();
			try left = t.dp!led(left); catch(PEE err){loc.error(err.msg);}
		}
		return left;
	}
	Statement parseStatement(){
		switch(tok.type){
			case Tok!"if":
				expect(Tok!"(");
				Expression e = parseExpression(0);
			default:
				loc.error("found '" ~ tok.toString() ~ "' instead of statement");
				return null; // error?
		}
	}
 	parseExpressionDG = &parseExpression;
	return parseExpression();//parseStatement();
}*/



