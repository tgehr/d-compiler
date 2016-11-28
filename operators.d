// Written in the D programming language
// Author: Timon Gehr
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.conv, std.traits;
import lexer;

import std.algorithm : canFind;

enum unaryOps = ["&", "*", "-", "++", "--", "+", "!", "~"];
enum postfixOps=[/*".",*/"++", "--","(","["];
//alias canFind!("a==b",TokenType[],TokenType) _canFind;
enum binaryOps=mixin({string r="[";
		foreach(x;EnumMembers!TokenType)if(getLbp(x)!=-1&&!canFind([Tok!"++",Tok!"--",Tok!"(",Tok!"["],x)) r~=`"`~TokenTypeToString(x)~`",`;
		return r~"]";
	}());


enum overloadableUnary = ["-","+","~","*","++","--"];
enum overloadableBinary = ["+","-","*","/","%","^^","&","|","^","<<",">>",">>>","~","in"];

// expression parser:

// left binding power
template lbp(TokenType type){enum lbp=getLbp(type);}
// right binding power: ^^, (op)=, ? bind weaker to the right than to the left, '.' binds only primaryExpressions
template rbp(TokenType type){enum rbp=type==Tok!"."?180:lbp!type-(type==Tok!"^^"||lbp!type==30||type==Tok!"?");}

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
	// logical operators
	case Tok!"?":  return 40; // conditional operator
	case Tok!"||": return 50; // logical OR
	case Tok!"&&": return 60; // logical AND
	// bitwise operators
	case Tok!"|":  return 70; // bitwise OR
	case Tok!"^":  return 80; // bitwise XOR
	case Tok!"&":  return 90; // bitwise AND
	// relational operators
	case Tok!"==",Tok!"!=",Tok!">",Tok!"<":
	case Tok!">=",Tok!"<=",Tok!"!>",Tok!"!<":
	case Tok!"!>=",Tok!"!<=",Tok!"<>",Tok!"!<>":
	case Tok!"<>=", Tok!"!<>=":
	case Tok!"in", Tok!"!in" ,Tok!"is",Tok!"!is":
		return 100;
	// shift operators
	case Tok!">>", Tok!"<<":
	case Tok!">>>": return 110;
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
	case Tok!"=>": return 165; // goesto
	case Tok!"!":  return 170;
	//case Tok!"i": return 45; //infix
	default: return -1;
	}
}
// unary exp binding power
enum nbp=140;


bool isAssignOp(TokenType op){
	switch(op){
		// assignment operators
		case Tok!"/=",Tok!"&=",Tok!"|=",Tok!"-=":
		case Tok!"+=",Tok!"<<=",Tok!">>=", Tok!">>>=":
		case Tok!"=",Tok!"*=",Tok!"%=",Tok!"^=":
		case Tok!"^^=",Tok!"~=":
			return true;
		default:
			return false;
	}
}

bool isIntRelationalOp(TokenType op){
	switch(op){
		// relational operators
		case Tok!"==",Tok!"!=",Tok!"is",Tok!"!is":
		case Tok!">",Tok!"<", Tok!">=",Tok!"<=":
			return true;
		default: return false;
	}
}

bool isRelationalOp(TokenType op){
	switch(op){
		// relational operators
		case Tok!"==",Tok!"!=",Tok!">",Tok!"<":
		case Tok!">=",Tok!"<=",Tok!"!>",Tok!"!<":
		case Tok!"!>=",Tok!"!<=",Tok!"<>",Tok!"!<>":
		case Tok!"<>=", Tok!"!<>=":
		case Tok!"in", Tok!"!in" ,Tok!"is",Tok!"!is":
			return true;
		default: return false;
	}
}

TokenType toIntegerRelationalOp(TokenType op){
	switch(op){
		// convert relational float operators to integer operators
		case Tok!"!>": return Tok!"<=";
		case Tok!"!<": return Tok!">=";
		case Tok!"!>=": return Tok!"<";
		case Tok!"!<=": return Tok!">";
		case Tok!"<>": return Tok!"!=";
		case Tok!"!<>": return Tok!"==";
		case Tok!"<>=": return Tok!"<>="; // cannot translate, always true
		case Tok!"!<>=": return Tok!"!<>="; // cannot translate, always false
		default: return op;
	}
}

bool isLogicalOp(TokenType op){
	switch(op){
		case Tok!"||": // logical OR
		case Tok!"&&": // logical AND
			return true;
		default:
			return false;
	}
}

bool isBitwiseOp(TokenType op){
	switch(op){
		case Tok!"|": // bitwise OR
		case Tok!"^": // bitwise XOR
		case Tok!"&": // bitwise AND
			return true;
		default:
			return false;
	}
}

bool isShiftOp(TokenType op){
	switch(op){
		// shift operators
		case Tok!">>": return true;
		case Tok!"<<": return true;
		case Tok!">>>":return true;
			return true;
		default:
			return false;
	}

}

bool isArithmeticOp(TokenType op){
	switch(op){
			// additive operators
		case Tok!"+",Tok!"-":
			return true;
			// multiplicative operators
		case Tok!"*",Tok!"/",Tok!"%":
		case Tok!"^^": // power
			return true;
		default:
			return false;
	}
}

