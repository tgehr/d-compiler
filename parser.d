module parser;

import std.algorithm, std.range, std.conv;
import std.typetuple;

import lexer, error, util;

public import expression, statement, declaration, type;

// expression parser:
// left binding power
template lbp(TokenType type){enum lbp=getLbp(type);}
// right binding power: ^^, (op)= bind weaker to the right than to the left, '.' binds only primaryExpressions
template rbp(TokenType type){enum rbp=type==Tok!"."?180:lbp!type-(type==Tok!"^^"||lbp!type==30);}

auto arrLbp=mixin({string r="[";foreach(t;EnumMembers!TokenType) r~=to!string(getLbp(t))~",";return r~"]";}());

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
	case Tok!"==",Tok!"!=",Tok!">",Tok!"<":
	case Tok!">=",Tok!"<=",Tok!"!>",Tok!"!<":
	case Tok!"!>=",Tok!"!<=",Tok!"<>",Tok!"!<>":
	case Tok!"<>=", Tok!"!<>=":
	case Tok!"in", Tok!"!in" ,Tok!"is",Tok!"!is":
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
// unary exp binding power
enum nbp=140;

enum literals=["``","``c","``w","``d","''","0","0U","0L","0LU",".0f",".0",".0L",".0fi",".0i",".0Li","null","true","false"];
enum unaryOps = ["&", "*", "-", "++", "--", "+", "!", "~"];
enum postfixOps=[/*".",*/"++", "--","(","["];
enum binaryOps=mixin({string r="[";
        foreach(x;EnumMembers!TokenType)if(getLbp(x)!=-1&&!canFind([Tok!"++",Tok!"--",Tok!"(",Tok!"["],x)) r~=`"`~TokenTypeToString(x)~`",`;
        return r~"]";
	}());

enum basicTypes=["bool","byte","ubyte","short","ushort","int","uint","long","ulong","char","wchar","dchar","float","double","real","ifloat","idouble","ireal","cfloat","cdouble","creal","void"];

enum storageClasses=protectionAttributes~["ref","auto ref","abstract","align","auto",/*"auto ref",*/"const","deprecated","enum","extern","final","immutable","in","inout","lazy","nothrow","out","override","pure","__gshared",/*"ref",*/"scope","shared","static","synchronized"]; // ref and auto ref taken to the front for easier handling by STCtoString

immutable toplevelSTC=protectionAttributes~["abstract","align","auto","auto ref","const","deprecated","enum","extern","final","immutable","inout","shared","nothrow","override","pure","__gshared","ref","scope","static","synchronized"]; // TODO: protection attributes must always come first!

immutable protectionAttributes=["export","package","private","protected","public"];

immutable attributeSTC=["property","safe","trusted","system","disable"];

immutable functionSTC=["const","immutable","inout","nothrow","pure","shared"];

immutable parameterSTC=["auto","const","final","immutable","in","inout","lazy","out","ref","scope","shared"];

enum typeQualifiers=["const","immutable","shared","inout"];

private string STCEnum(){
	string r="enum{";
	foreach(i,s;storageClasses~attributeSTC) r~="STC"~(s=="auto ref"?"autoref":s)~"="~to!string(1L<<i)~",";
	return r~"}";
}
//enum{STC...}; Solved this way because most storage classes are keywords and composition will be sane
mixin(STCEnum());
static assert(storageClasses.length+attributeSTC.length<64);
alias long STC;
string STCtoString(STC stc){
	if(!stc) return "";
	/*STC fstc=stc&-stc;
	stc-=fstc;
	int n=0; while(1<<n<fstc) n++;
	string r=n>=storageClasses.length?"@"~attributeSTC[n-storageClasses.length]:storageClasses[n]; */
	string r;
	foreach(i,s;storageClasses) if(stc&(1L<<i)) r~=" "~s;
	foreach(i,s;attributeSTC) if(stc&(1L<<(storageClasses.length+i))) r~=" @"~s;
	return r[1..$];
}

private string getTTCases(string[] s,string[] excl = []){
	string r="case ";
	foreach(x;s) if(!excl.canFind(x)) r~="Tok!\""~x~"\",";
	return r[0..$-1]~":";
}

bool isClosingToken(TokenType type){
	return type==Tok!")" || type==Tok!"}" || type==Tok!"]" || type==Tok!";";
}

//private template isCode(R){enum isCode=isForwardRange!R && is(Unqual!(ElementType!R) == Token);}
private template GetStringOf(T){enum GetStringOf=T.stringof;} // Workaround for strange compiler limitations
private template GetStringOf(S: UnaryExp!Y,TokenType Y){enum GetStringOf=S.stringof~"!("~Y.stringof~")";}
private template GetStringOf(S: BinaryExp!Y,TokenType Y){enum GetStringOf=S.stringof~"!("~Y.stringof~")";}
private template GetStringOf(S: PostfixExp!Y,TokenType Y){enum GetStringOf=S.stringof~"!("~Y.stringof~")";}
private template GetStringOf(S: QualifiedType!Y,TokenType Y){enum GetStringOf=S.stringof~"!("~Y.stringof~")";}
//private template GetStringOf(S: S!Y,Y...){enum GetStringOf=S.stringof~"!("~Y.stringof[6..$-1]~")";} // why doesn't that work?


private template getParseProc(T...){
	static if(is(T[0]==AssignExp)) enum prc=`parseExpression(rbp!(Tok!","))`, off=2;
	else static if(is(T[0]==OrOrExp)) enum prc=`parseExpression(rbp!(Tok!"?"))`, off=2;
	else static if(is(T[0]==ArgumentList)||is(T[0]==AssocArgumentList)||is(T[0]==Tuple)){ // ArgumentList, AssocArgumentList can take optional parameters
		static if(T[2][0]=='('&&T[2][$-1]==')')
			enum prc=`parse`~T[0].stringof~`!`~T[3].stringof~T[2], off=3;
		else enum prc=`parse`~T[0].stringof~`!`~T[2].stringof~"()", off=2;
	}else static if(is(T[0]==StorageClass)) enum prc="parseSTC!toplevelSTC()", off=2;
	else static if(is(T[0]==CondDeclBody)) enum prc="parseCondDeclBody(flags)", off=2; // flags is a variable in parseDeclDef
	else enum prc="parse"~T[0].stringof~"()", off=2;
}
//dummy structs for some of the parsing procedures:
private{
	struct StorageClass{}   struct ArgumentList{}          struct AssocArgumentList{}
	struct IdentifierList{} struct AssignExp{}             struct OrOrExp{}
	struct Existing{}       struct DebugCondition{}        struct VersionCondition{}
	struct CondDeclBody{}   struct OptTemplateConstraint{} struct TemplateParameterList{}
	struct Tuple{}          struct TypeOrExpression{}      struct Initializer{}
	struct DeclDef{}        struct Condition{}
}
private template TTfromStr(string arg){ // turns "a,b,c,..." into TypeTuple(a,b,c,...)
	alias TypeTuple!(mixin("TypeTuple!("~arg~")")) TTfromStr;
}

private template doParseImpl(bool d,T...){
	static if(T.length==0) enum doParseImpl="";
	else static if(is(typeof(T[0]):string)) enum doParseImpl={
			static if(T[0].length>3 && T[0][0..3]=="OPT") return doOptParse!(TTfromStr!(T[0][3..$]))~doParseImpl!(d,T[1..$]);
			else switch(T[0]){
				case "_": return "nextToken();\n"~doParseImpl!(d,T[1..$]);
				case "NonEmpty":
					enum what=is(T[1]==CondDeclBody)?"declaration":"statement";
					return `nonEmpty!"`~what~`"();`"\n"~doParseImpl!(d,T[1..$]);
				case "OPT":
				static if(T[0]=="OPT")
						return (d?"auto ":"")~T[2]~" = "~(T[3]!=")"?"ttype==Tok!\""~T[3]~"\" || ":"")~"ttype==Tok!\")\" ? null : "~
						getParseProc!(T[1..$]).prc~";\n"~doParseImpl!(d,T[1+getParseProc!T.off..$]);
				default: return "expect(Tok!\""~T[0]~"\");\n"~doParseImpl!(d,T[1..$]);;
			}
		}();
	else static if(is(T[0]==Existing)) alias doParseImpl!(d,T[2..$]) doParseImpl;
	else enum doParseImpl=(d?"auto ":"")~T[1]~" = "~getParseProc!T.prc~";\n"~doParseImpl!(d,T[getParseProc!T.off..$]);
}

private template doParse(T...){ alias doParseImpl!(true,T) doParse; }
private template doParseNoDef(T...){ alias doParseImpl!(false,T) doParseNoDef; }

private template parseDefOnly(T...){
	static if(T.length==0) enum parseDefOnly="";
	else static if(is(typeof(T[0]):string)){
		static if(T[0]=="OPT") alias parseDefOnly!(T[1..$]) parseDefOnly;
		else alias parseDefOnly!(T[1..$]) parseDefOnly;
	}else static if(is(T[0]==Existing)) alias parseDefOnly!(T[2..$]) parseDefOnly;
	else enum parseDefOnly="typeof("~getParseProc!T.prc~") "~T[1]~"=cast(typeof("~getParseProc!T.prc~"))null;\n"~parseDefOnly!(T[2..$]);
}
private template doOptParse(T...){
	static assert(is(typeof(T[0]):string));
	enum doOptParse=parseDefOnly!T~"if(ttype==Tok!\""~T[0]~"\"){\n"~doParseImpl!(false,"_",T[1..$])~"}\n";
}

private template fillParseNamesImpl(int n,string b,T...){ // val: new TypeTuple, off: that many names have been filled in
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
		return doParse!(a)~"return res=New!("~GetStringOf!(T[0])~")("~getParseNames!a~");";
	}();
}

private template SetLoc(T: Node){
	enum SetLoc=T.stringof~q{
		res=null;
		Location begin=tok.loc;
		scope(exit){
			if(res) res.loc=begin.to(code.buffer[code.n-1&code.buffer.length-1].loc);
		}
	};
}


alias Lexer Code;
private alias ChunkGCAlloc Alloc;
//private alias GCAlloc Alloc;

private struct Parser{
	alias Alloc.New New;
	alias Alloc.appender appender;
	enum filename = "tt.d";
	Code code;
	ErrorHandler handler;
	int muteerr=0;
	this(Code code, ErrorHandler handler){
		this.code = code;
		//_tok=&code.front();
		ttype=tok.type;
		this.handler = handler;
	}
	@property ref const(Token) tok(){return code.buffer[code.n];};
	@property ref const(Token) ptok(){return code.buffer[code.n-1&code.buffer.length-1];};
	TokenType ttype;
	void nextToken(){
		if(ttype==Tok!"EOF") return;
		code.popFront();
		ttype=tok.type;
		if(!code.errors.length || muteerr) return;
		while(code.errors.length&&code.errors[0].loc.rep.ptr<tok.loc.rep.ptr){
			handler.error(code.errors[0].str,code.errors[0].loc);
			code.errors.popFront();
		}
	}
	void error(string err, Location loc=Location.init){
		if(code.errors.length&&code.errors[0].loc.rep.ptr==loc.rep.ptr) return; // don't re-report lexer errors
		if(!loc.line) loc=tok.loc;
		handler.error(err,loc);
	}
	auto saveState(){muteerr++; return code.pushAnchor();} // saves the state and mutes all error messages until the state is restored
	void restoreState(Anchor state){
		muteerr--; code.popAnchor(state);
		ttype=tok.type;
	}
	Token peek(int x=1){
		if(x<code.e-code.s) return code.buffer[code.n+x & code.buffer.length-1]; // breaking encapsulation for efficiency
		auto save = saveState();
		foreach(i;0..x) nextToken();
		auto t=tok;
		restoreState(save);
		return t;
	}
	Token peekPastParen(){
		auto save = saveState();
		nextToken();
		skipToUnmatched();
		nextToken();
		auto t=tok;
		restoreState(save);
		return t;

	}
	static class ParseErrorException: Exception{this(string s){super(s);}} alias ParseErrorException PEE;
	void expect(TokenType type){
		if(ttype==type){nextToken(); return;}
		// employ some bad heuristics to avoid cascading error messages. TODO: make this better
		bool rd=isClosingToken(type);
		Location loc=tok.loc;
		import utf=std.utf;
		if(rd){
			loc=code.buffer[code.n-1&code.buffer.length-1].loc;
			loc.rep=(loc.rep.ptr+loc.rep.length)[0..utf.stride(loc.rep.ptr[loc.rep.length..loc.rep.length+4],0)];
		}
		if(!isClosingToken(ttype) || isClosingToken(type)){
			auto tt=peek().type;
			if(tt!=Tok!"i"&&tt==type){
				error("stray '"~tok.toString()~"' in program",tok.loc);
				nextToken(); nextToken();
				return;
			}
		}
		if(rd||ttype==Tok!"__error") error("expected '"~TokenTypeToString(type)~"'",loc);
		else error("found '" ~ tok.toString() ~ "' when expecting '" ~ TokenTypeToString(type) ~"'",loc);
		if(type!=Tok!";" && type!=Tok!"}"){
			while(ttype != Tok!";" && ttype != Tok!"}" && ttype != Tok!"EOF") nextToken();
			if(ttype == Tok!";") nextToken();
		}
	}
	void expectErr(string what)(){
		if(ttype==Tok!"__error") error("expected "~what,tok.loc);
		else error("found '" ~ tok.toString() ~ "' when expecting " ~ what,tok.loc);
		if(ttype!=Tok!")" && ttype!=Tok!"}" && ttype!=Tok!"]" && ttype!=Tok!";") nextToken();
	}
	bool skip(TokenType type){
		if(ttype != type) return false;
		nextToken(); return true;
	}
	bool skip(){nextToken(); return true;}
	Identifier parseIdentifier(){ // Identifier(null) is the error value
		string name;
		if(ttype==Tok!"i") name=tok.name;
		else{expectErr!"identifier"(); auto e=New!Identifier(cast(string)null); e.loc=tok.loc; return e;}
		auto e=New!Identifier(name);
		e.loc=tok.loc;
		nextToken();
		return e;
	}
	Expression parseIdentifierList(T...)(T args){
		TokenType tt;
		Expression e;
		void errori(){expectErr!"identifier following '.'"();}
		static if(T.length==0){
			if(ttype==Tok!"."){e = New!Identifier(""); e.loc=tok.loc; nextToken();}
			else if(ttype!=Tok!"i"){expectErr!"identifier"(); return New!ErrorExp;}
			else e = New!Identifier(tok.name); e.loc = tok.loc; nextToken();
		}else{e=args[0];}
		for(bool multerr=0;;){
			if(ttype==Tok!"."){
				auto loc=tok.loc;
				nextToken();
				if(ttype!=Tok!"i"){errori(); return e;}
				auto i = New!Identifier(tok.name); i.loc=tok.loc;
				e = New!(BinaryExp!(Tok!"."))(e,i); e.loc=loc;
				nextToken();
			}else if(ttype==Tok!"!" && (tt=peek().type)!=Tok!"in" && tt!=Tok!"is"){
				e=led(e);
				if(ttype==Tok!"!"&&!multerr && (tt=peek().type)!=Tok!"in" && tt!=Tok!"is"){
					error("multiple '!' arguments are disallowed"), multerr=1;
				}
			}
			else break;
		}
		return e;
	}
	bool skipIdentifierList(){
		TokenType tt;
		skip(Tok!".");
		if(!skip(Tok!"i")) return false;
		for(;;){
			if(skip(Tok!".")){if(!skip(Tok!"i")) return false;}
			else if(ttype==Tok!"!" && (tt=peek().type)!=Tok!"in" && tt!=Tok!"is"){
				nextToken();
				if(ttype==Tok!"("){
					nextToken();
					if(!skipToUnmatched()||!skip(Tok!")")) return false;
				}else skip();
			}else return true;
		}
	}
	// allows only non-associative expressions
	Expression[] parseArgumentList(string delim, bool nonempty=false, Entry=AssignExp, T...)(T args){
		auto e=appender!(Expression[])();
		foreach(x;args) e.put(x); // static foreach
		static if(args.length){if(ttype==Tok!",") nextToken(); else return e.data;}
		static if(!nonempty) if(ttype==Tok!delim) return e.data;
		do{
			mixin(doParse!(Entry,"e1")); e.put(e1);
			if(ttype==Tok!",") nextToken();
			else break;
		}while(ttype!=Tok!delim && ttype!=Tok!"EOF");
		return e.data;
	}
	// allows interspersed associative and non-associative expressions. Entry.key must be a subset of Entry.value
	Expression[] parseAssocArgumentList(string delim, bool nonempty=false, Entry=ArrayAssocExp, T...)() if(T.length%2==0){
		alias typeof({Entry x; return x.key;}()) Key;
		alias typeof({Entry x; return x.value;}()) ValueType;
		static if(is(Entry==ArrayInitAssocExp)||is(Entry==StructAssocExp)) alias InitializerExp Value;
		else static if(is(ValueType==Expression)) alias AssignExp Value;
		else alias ValueType Value;
		auto e=appender!(Expression[])();
		static if(!nonempty) if(ttype==Tok!delim) return e.data;
		do{
			mixin(doParse!(Value,"e1"));
			auto e2=cast(Key)e1;
			if(ttype==Tok!":" && e2){
				mixin(doParse!("_",Value,"e3"));
				e.put(New!Entry(e2,e3));
			}else e.put(e1);
			if(ttype==Tok!",") nextToken();
			else break;
		}while(ttype!=Tok!delim && ttype!=Tok!"EOF");
		return e.data;
	}
	Expression parseTypeOrExpression(){
		Expression e;
		auto save=saveState();
		auto ist=skipType()&&(ttype==Tok!","||ttype==Tok!")");
		restoreState(save);
		e=ist?parseType():parseExpression(rbp!(Tok!","));
		return e;
	}
	Expression[] parseTuple(string delim, bool nonempty=false)(){
		auto e=appender!(Expression[])();
		static if(!nonempty) if(ttype==Tok!delim) return e.data;
		do{
			e.put(parseTypeOrExpression());
			if(ttype==Tok!",") nextToken();
			else break;
		}while(ttype!=Tok!delim && ttype!=Tok!"EOF");
		return e.data;
	}
	Expression parseTemplateSingleArg(){
		Expression e;
		switch(ttype){
			case Tok!"i":
				e = New!Identifier(tok.name); break;
			mixin(getTTCases(basicTypes));
				e = New!BasicType(ttype); break;
			mixin(getTTCases(literals));
				e = New!LiteralExp(tok); break;
			default:
				expectErr!"template argument"(); return New!ErrorExp;
		}
		e.loc = tok.loc;
		nextToken();
		return e;
	}
	// Operator precedence expression parser
	// null denotation
	Expression nud() {
		mixin(SetLoc!Expression);
		switch(ttype){
			case Tok!"i",Tok!".": return parseIdentifierList(); // TODO: instance.new Class(...);
			case Tok!"``", Tok!"``c", Tok!"``w", Tok!"``d": // adjacent string tokens get concatenated
				Token t=tok;
				for(nextToken();ttype==t.type||ttype==Tok!"``";nextToken()){
					if(t.type==Tok!"``" && Tok!"``c"<=ttype && ttype<=Tok!"``d") t.type=ttype; // ENHANCEMENT
					t.str~=tok.str; // TODO: make more efficient than simple append
				}
				mixin(rule!(LiteralExp,Existing,"t"));
			mixin(getTTCases(literals,["``","``c","``w","``d"])); {auto e=New!LiteralExp(tok); e.loc=tok.loc; nextToken(); return e;}
			case Tok!"this": mixin(rule!(ThisExp,"_"));  // TODO: location could be captured more efficiently. Change 'rule' to reflect that
			case Tok!"super": mixin(rule!(SuperExp,"_"));
			case Tok!"$": mixin(rule!(DollarExp,"_"));
			case Tok!"cast":
				nextToken(); expect(Tok!"(");
				STC stc;
				Expression tt=null;
				if(ttype!=Tok!")"){
					stc=parseSTC!toplevelSTC();
					if(ttype!=Tok!")") tt=parseType();
				}
				expect(Tok!")");
				auto e=nud();
				mixin(rule!(CastExp,Existing,q{stc,tt,e}));
			case Tok!"is":
				mixin(doParse!("_","(",Type,"type"));
				Identifier ident; // optional
				if(ttype==Tok!"i") ident=New!Identifier(tok.name), nextToken();
				auto which = WhichIsExp.type;
				if(ttype==Tok!":") which = WhichIsExp.implicitlyConverts;
				else if(ttype==Tok!"==") which = WhichIsExp.isEqual;
				else if(ttype==Tok!"*=" && peek().type==Tok!"=") type = New!Pointer(type), nextToken(), which=WhichIsExp.isEqual; // EXTENSION
				else{expect(Tok!")");return New!IsExp(which,type,ident,cast(Expression)null,Tok!"",cast(TemplateParameter[])null);}
				nextToken();
				Expression typespec=null;
				TokenType typespec2=Tok!"";
				if(which==WhichIsExp.isEqual){
					switch(ttype){
						case Tok!"const", Tok!"immutable", Tok!"inout", Tok!"shared":
							auto tt=peek().type; if(tt==Tok!","||tt==Tok!")") goto case; goto default;
						case Tok!"struct", Tok!"union", Tok!"class", Tok!"interface", Tok!"enum", Tok!"function", Tok!"delegate",
							Tok!"super", Tok!"return", Tok!"typedef":
							typespec2=ttype; nextToken(); break;
						default: goto parsetype;
					}
				}else parsetype: typespec=parseType();
				TemplateParameter[] tparams = null;
				if(ttype==Tok!","){
					nextToken();
					if(ident&&ttype!=Tok!")") tparams = parseTemplateParameterList();
				}
				expect(Tok!")");
				mixin(rule!(IsExp,Existing,q{which,type,ident,typespec,typespec2,tparams}));
			case Tok!"__traits": mixin(rule!(TraitsExp,"_","(",Tuple,")"));
			case Tok!"delete": mixin(rule!(DeleteExp,"_",Expression));
			case Tok!"(":
				if(peekPastParen().type==Tok!"{") return parseFunctionLiteralExp();
				nextToken();
				auto save=saveState();
				bool isType=skipType() && ttype==Tok!")";
				restoreState(save);
				if(isType){mixin(doParseNoDef!(Type,"res",")"));} // does not necessarily parse a type, eg arr[10]
				else{mixin(doParseNoDef!(Expression,"res",")"));}
				res.brackets++;
				return res;
			case Tok!"__error": mixin(rule!(ErrorExp,"_"));
			mixin(getTTCases(basicTypes)); {
				auto e=New!BasicType(ttype);
				e.loc=tok.loc;
				nextToken();
				return parseIdentifierList(e);
			} // int.max etc
			mixin({string r; // immutable(int).max etc
				foreach(type;typeQualifiers){
					r~=q{case Tok!}`"`~type~`":`q{
						nextToken(); expect(Tok!"(");
						auto e=parseType(); e.brackets++;
						expect(Tok!")");
						return res=New!(QualifiedType!(Tok!}"`"~type~"`"q{))(e);
					};
				}
				return r;
			}());
			case Tok!"{", Tok!"delegate", Tok!"function": return parseFunctionLiteralExp();
			case Tok!"[": mixin(rule!(ArrayLiteralExp,"_","OPT",AssocArgumentList,"]"));
			case Tok!"new":
				nextToken();
				if(ttype==Tok!"class"){
					mixin(doParse!("_","OPT"q{"(",ArgumentList,"args",")"}));
					auto aggr=cast(ClassDecl)cast(void*)parseAggregateDecl(STC.init,true); // it is an anonymous class, static cast is safe
					mixin(rule!(NewClassExp,Existing,q{args,aggr}));
				}else{mixin(rule!(NewExp,"OPT"q{"(",ArgumentList,")"},Type,"OPT"q{"(",ArgumentList,")"}));}
			case Tok!"assert": mixin(rule!(AssertExp,"_","(",ArgumentList,")"));
			case Tok!"mixin": mixin(rule!(MixinExp,"_","(",AssignExp,")"));
			case Tok!"import": mixin(rule!(ImportExp,"_","(",AssignExp,")"));
			case Tok!"typeid": mixin(rule!(TypeidExp,"_","(",TypeOrExpression,")"));
			case Tok!"typeof":
				nextToken(); expect(Tok!"(");
				if(ttype==Tok!"return"){nextToken(); expect(Tok!")"); return New!TypeofReturnExp();}
				mixin(doParse!(Expression,"e1",")"));
				return res=New!TypeofExp(e1);
			mixin({string r;
				foreach(x;unaryOps) r~=q{case Tok!}`"`~x~`":`q{nextToken(); return res=New!(UnaryExp!(Tok!}`"`~x~`"`q{))(parseExpression(nbp));};
				return r;
			}());
			default: throw new PEE("invalid unary operator '"~tok.toString()~"'");
		}
	}
	// left denotation
	Expression led(Expression left){
		Expression res=null;
		Location loc=tok.loc;
		scope(exit) if(res) res.loc=loc;
		switch(ttype){
			//case Tok!"i": return New!CallExp(New!BinaryExp!(Tok!".")(left,New!Identifier(self.name)),parseExpression(45));// infix
			case Tok!"?": mixin(rule!(TernaryExp,"_",Existing,"left",Expression,":",OrOrExp));
			case Tok!"[":
				nextToken();
				if(ttype==Tok!"]"){loc=loc.to(tok.loc); nextToken(); mixin(rule!(IndexExp,Existing,q{left,cast(Expression[])null}));}
				auto l=parseExpression(rbp!(Tok!","));
				if(ttype==Tok!".."){
					mixin(doParse!("_",AssignExp,"r"));
					loc=loc.to(tok.loc); expect(Tok!"]");
					mixin(rule!(SliceExp,Existing,q{left,l,r}));
				}
				else{
					res=New!IndexExp(left,parseArgumentList!"]"(l));
					loc=loc.to(tok.loc); expect(Tok!"]");
					return res;
				}
			case Tok!"(":
				nextToken();
				auto a=parseArgumentList!")"();
				loc=loc.to(tok.loc); expect(Tok!")");
				mixin(rule!(CallExp,Existing,"left,a"));
			case Tok!"!":
				nextToken();
				if(ttype==Tok!"is"){loc=loc.to(tok.loc); goto case Tok!"!is";}
				else if(ttype==Tok!"in"){loc=loc.to(tok.loc); goto case Tok!"!in";}
				if(ttype==Tok!"("){
					nextToken(); auto e=New!TemplateInstanceExp(left,parseTuple!")");
					if(e.args.length==1) e.args[0].brackets++; expect(Tok!")"); return res=e;
				}
				mixin(rule!(TemplateInstanceExp,Existing,q{left,[parseTemplateSingleArg()]}));
			case Tok!".": return parseIdentifierList(left);
			mixin({string r;
				foreach(x;binaryOps)
					if(x!="." && x!="!" && x!="?")
						r~=q{case Tok!}`"`~x~`":`q{
							nextToken();
							return res=New!(BinaryExp!(Tok!}`"`~x~`"`q{))(left,parseExpression(rbp!(Tok!}`"`~x~`"`q{)));
						};
				return r;
			}());
			//pragma(msg,TokenTypeToString(cast(TokenType)61));
			mixin({string r;
				foreach(x;postfixOps)
					if(x!="(" && x!="[")
						r~=q{case Tok!}`"`~x~`":`q{nextToken();return res=New!(PostfixExp!(Tok!}`"`~x~`"`q{))(left);};
				return r;
			}());
			default: throw new PEE("invalid binary operator '"~tok.toString()~"'");
		}
	}
	Expression parseExpression(int rbp = 0){
		Expression left;
		try left = nud();catch(PEE err){error("found '"~tok.toString()~"' when expecting expression");nextToken();return new ErrorExp();}
		while(rbp < arrLbp[ttype]){
			try left = led(left); catch(PEE err){error(err.msg);}
		}
		return left;
	}
	Expression parseExpression2(Expression left, int rbp = 0){ // left is already known
		while(rbp < arrLbp[ttype]){
			try left = led(left); catch(PEE err){error(err.msg);}
		}
		return left;
	}
	bool skipToUnmatched(bool skipcomma=true)(){
		int pnest=0, cnest=0, bnest=0; // no local templates >:(
		for(;;nextToken()){
			switch(ttype){
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
	void nonEmpty(string what="statement")(){if(ttype==Tok!";") error("use '{}' for an empty "~what~", not ';'");}
	Statement parseStmError(){
		while(ttype != Tok!";" && ttype != Tok!"}" && ttype != Tok!"EOF") nextToken();
		if(ttype == Tok!";") nextToken();
		return New!ErrorStm;
	}
	private static template pStm(T...){
		enum pStm="case Tok!\""~T[0]~"\":\n"~rule!(mixin(T[0][0]+('A'-'a')~T[0][1..$]~"Stm"),"_",T[1..$]);
	}
	Statement parseStatement(){
		mixin(SetLoc!Statement);
		bool isfinal = false; //for final switch
		bool isreverse = false; //for foreach_reverse
		if(ttype == Tok!"i" && peek().type == Tok!":"){
			auto l = New!Identifier(tok.name); // TODO: location
			nextToken(); nextToken();
			mixin(rule!(LabeledStm,Existing,"l",Statement));
		}
		switch(ttype){
			case Tok!";": mixin(rule!(Statement,"_"));
		    case Tok!"{":
				auto r=parseBlockStm();
				if(ttype!=Tok!"(") return r;
				else{
					auto e=parseExpression2(New!FunctionLiteralExp(cast(FunctionType)null,r));
					expect(Tok!";");
					mixin(rule!(ExpressionStm,Existing,"e"));
				}
			mixin(pStm!("if","(",Condition,")","NonEmpty",Statement,"OPT"q{"else","NonEmpty",Statement}));
			mixin(pStm!("while","(",Condition,")","NonEmpty",Statement));
			mixin(pStm!("do","NonEmpty",Statement,"while","(",Expression,")",";"));
			mixin(pStm!("for","(",Statement,"OPT",Condition,";","OPT",Expression,")","NonEmpty",Statement));
			case Tok!"foreach_reverse":
				isreverse=true;
			case Tok!"foreach":
				nextToken();
				expect(Tok!"(");
				auto vars=appender!(Parameter[])();
				do{
					auto stc=STC.init;
					if(ttype==Tok!"ref") stc=STCref;
					stc|=parseSTC!toplevelSTC();
					Expression type;
					TokenType tt;
					Location loc=tok.loc;
					if(ttype!=Tok!"i" || (tt=peek().type)!=Tok!"," && tt!=Tok!";") type=parseType();
					auto name=parseIdentifier();
					auto p=New!Parameter(stc,type,name,cast(Expression)null); p.loc=loc.to(ptok.loc);
					vars.put(p);
					if(ttype==Tok!",") nextToken();
					else break;
				}while(ttype!=Tok!";" && ttype!=Tok!"EOF");
				expect(Tok!";");
				auto e=parseExpression();
				if(vars.length==1&&ttype==Tok!".."){
					mixin(rule!(ForeachRangeStm,Existing,q{vars.data[0],e},"_",Expression,")","NonEmpty",Statement,Existing,"isreverse"));
				}
				expect(Tok!")"); nonEmpty();
				mixin(rule!(ForeachStm,Existing,q{vars.data,e},Statement,Existing,"isreverse"));
			case Tok!"final":
				if(peek().type != Tok!"switch") goto default;
				nextToken();
				isfinal=true;
			case Tok!"switch": mixin(rule!(SwitchStm,Existing,"isfinal","_","(",Expression,")","NonEmpty",Statement));
			case Tok!"case":
				Expression[] e;
				auto s=appender!(Statement[])();
				bool isrange=false;
				nextToken();
				e = parseArgumentList!(":",true)(); // non-empty!
				expect(Tok!":");

				if(ttype == Tok!".."){ // CaseRange
					isrange=true;
					if(e.length>1) error("only one case allowed for start of case range",e[1].loc); // TODO: better error report for Binary and Postfix Exp
					e.length=2;
					nextToken();
					expect(Tok!"case");
					e[1]=parseExpression(lbp!(Tok!","));
					expect(Tok!":");
				}

				while(ttype!=Tok!"case" && ttype!=Tok!"default" && ttype!=Tok!"}"&&ttype!=Tok!"EOF") s.put(parseStatement());
				return res=isrange?New!CaseRangeStm(e[0],e[1],s.data):New!CaseStm(e,s.data);
			case Tok!"default":
				mixin(doParse!("_",":"));
				auto s=appender!(Statement[])();
				while(ttype!=Tok!"case" && ttype!=Tok!"default" && ttype!=Tok!"}"&&ttype!=Tok!"EOF") s.put(parseStatement());
				mixin(rule!(DefaultStm,Existing,"s.data"));
			case Tok!"continue":
				nextToken();
				if(ttype==Tok!"i") res=New!ContinueStm(New!Identifier(tok.name)), nextToken();
				else res=New!ContinueStm(cast(Identifier)null);
				expect(Tok!";");
				return res;
			//mixin(pStm!("break", "OPT", Identifier, ";");
			case Tok!"break":
				nextToken();
				if(ttype==Tok!"i") res=New!BreakStm(New!Identifier(tok.name)), nextToken();
				else res=New!BreakStm(cast(Identifier)null);
				expect(Tok!";");
				return res; // TODO: location
			mixin(pStm!("return","OPT",Expression,";"));
			case Tok!"goto":
				nextToken();
				switch(ttype){
					case Tok!"i":
						res=New!GotoStm(WhichGoto.identifier,New!Identifier(tok.name));
						nextToken(); expect(Tok!";");
						return res;
					case Tok!"default": mixin(rule!(GotoStm,Existing,q{WhichGoto.default_,cast(Expression)null},"_",";"));
					case Tok!"case":
						nextToken();
						if(ttype == Tok!";"){mixin(rule!(GotoStm,Existing,q{WhichGoto.case_,cast(Expression)null},"_"));}
						auto e = parseExpression();
						mixin(rule!(GotoStm,Existing,q{WhichGoto.caseExp,e},";"));
					default:
						expectErr!"location following goto"();
						return parseStmError();
				}
			mixin(pStm!("with","(",Expression,")","NonEmpty",Statement));
			mixin(pStm!("synchronized","OPT"q{"(",Expression,")"},Statement));
			case Tok!"try":
				mixin(doParse!("_",Statement,"ss"));
				auto catches=appender!(CatchStm[])();
				do{ // TODO: abstract loop away, as soon as compile memory usage is better
					Location loc=tok.loc;
					//mixin(doParse!("catch","OPT"q{"(",Type,"type","OPT",Identifier,"ident",")"},"NonEmpty",Statement,"s"));
					//pragma(msg,doParse!("catch","OPT"q{"(",Type,"type","OPT",Identifier,"ident",")"},"NonEmpty",Statement,"s"));
					expect(Tok!"catch");
					typeof(parseType()) type=null;
					typeof(parseIdentifier()) ident;//=null; //DMD BUG: if the initializer is specified, DMD generates wrong code that results in segfault
					if(ttype==Tok!"("){
						nextToken();
						type = parseType();
						ident = ttype==Tok!")" || ttype==Tok!")" ? null : parseIdentifier();
						expect(Tok!")");
					}
					nonEmpty!"statement"();
					auto s = parseStatement();
					auto c=New!CatchStm(type,ident,s); c.loc=loc.to(ptok.loc);
					catches.put(c);
					if(!type) break; // this really should work as loop condition!
				}while(ttype==Tok!"catch");
				mixin(doParse!("OPT"q{"finally",Statement,"finally_"}));
				mixin(rule!(TryStm,Existing,q{ss,catches.data,finally_}));
			mixin(pStm!("throw",Expression,";"));
			case Tok!"scope":
				if(peek().type != Tok!"(") goto default;
				mixin(doParse!("_","_"));
				WhichScopeGuard w;
				if(ttype != Tok!"i"){expectErr!"scope identifier"(); return parseStmError();}
				switch(tok.name){
					case "exit": w=WhichScopeGuard.exit; break;
					case "success": w=WhichScopeGuard.success; break;
					case "failure": w=WhichScopeGuard.failure; break;
					default: error("valid scope identifiers are exit, success, or failure, not "~tok.name);
				}
				mixin(rule!(ScopeGuardStm,Existing,"w","_",")","NonEmpty",Statement));
			case Tok!"asm":
				nextToken();
				expect(Tok!"{");
				//error("inline assembly not implemented yet!");
				//auto start = code.ptr;
				for(int nest=1;ttype!=Tok!"EOF";nextToken()) if(!(ttype==Tok!"{"?++nest:ttype==Tok!"}"?--nest:nest)) break;
				//auto asmcode=start[0..code.ptr-start];
				Code asmcode; // TODO: fix
				expect(Tok!"}");
				mixin(rule!(AsmStm,Existing,"asmcode"));
			case Tok!"mixin":
				if(peek().type!=Tok!"(") goto default; // mixin template declaration
				Location loc=tok.loc;
				mixin(doParse!("_","_",AssignExp,"e",")"));
				if(ttype != Tok!";"){// is a mixin expression, not a mixin statement
					auto m=New!MixinExp(e); m.loc=loc.to(ptok.loc);
					auto e2=parseExpression2(m);
					mixin(rule!(ExpressionStm,Existing,"e2",";"));
				}
				mixin(rule!(MixinStm,Existing,"e","_"));
			default: // TODO: replace by case list
				if(auto d=parseDeclDef(tryonly|allowstm)) return d;
				mixin(rule!(ExpressionStm,Expression,";")); // note: some other cases may invoke parseExpression2 and return an ExpressionStm!
			case Tok!")", Tok!"}", Tok!":": // this will be default
				expectErr!"statement"; return parseStmError();
		}
	}
	Expression parseType(string expectwhat="type"){
		mixin(SetLoc!Expression);
		Expression tt;
		bool brk=false;
		switch(ttype){
			mixin(getTTCases(basicTypes)); tt = New!BasicType(ttype); nextToken(); break;
			case Tok!".": goto case;
			case Tok!"i": tt=parseIdentifierList(); break;
			mixin({string r;
				foreach(x;typeQualifiers) r~=q{
					case Tok!}`"`~x~`":`q{nextToken();
						if(ttype==Tok!"(") brk=true, nextToken();
						auto e=parseType(); e.brackets+=brk; tt=New!(QualifiedType!(Tok!}`"`~x~`"`q{))(e);if(brk) expect(Tok!")");
						if(ttype==Tok!".") tt=parseIdentifierList(tt); // ENHANCEMENT
						break;
				};
				return r;
			}());
			case Tok!"typeof": tt=nud(); if(ttype==Tok!".") tt=parseIdentifierList(tt); break;
			default: error("found '"~tok.toString()~"' when expecting "~expectwhat); nextToken(); return New!ErrorExp;
		}
		for(;;){
			switch(ttype){
				case Tok!"*": nextToken(); tt=New!Pointer(tt); continue;
				case Tok!"[":
					auto save = saveState();
					bool isAA=skip()&&skipType()&&ttype==Tok!"]";
					restoreState(save);
					if(isAA){
						Location loc=tok.loc;
						mixin(doParse!("_",Type,"e","]"));
						tt=New!IndexExp(tt,[e]); tt.loc=loc.to(ptok.loc);
					}else tt=led(tt); continue; //'Bug': allows int[1,2].
				case Tok!"function":
					auto loc=tt.loc;
					nextToken();
					VarArgs vararg;
					auto params=parseParameterList(vararg);
					STC stc=parseSTC!functionSTC();
					tt=New!FunctionPtr(New!FunctionType(stc,tt,params,vararg)); tt.loc=loc.to(ptok.loc);
					continue;
				case Tok!"delegate":
					auto loc=tt.loc;
					nextToken();
					VarArgs vararg;
					auto params=parseParameterList(vararg);
					STC stc=parseSTC!functionSTC();
					tt=New!DelegateType(New!FunctionType(stc,tt,params,vararg)); tt.loc=loc.to(ptok.loc);
					continue;
				default: break;
			}
			break;
		}
		return res=tt;
	}
	bool skipType(){
		switch(ttype){
			mixin(getTTCases(basicTypes)); nextToken(); break;
			case Tok!".": nextToken(); case Tok!"i":
				if(!skipIdentifierList()) goto Lfalse; break;
			mixin({string r;
				foreach(x;typeQualifiers) r~=q{
					case Tok!}`"`~x~`":`q{
						nextToken(); bool brk=skip(Tok!"("); if(!skipType()||brk&&!skip(Tok!")")) return false;
						if(ttype==Tok!"." && !skipIdentifierList()) goto Lfalse; break; // ENHANCEMENT
				};
				return r;
			}());
			case Tok!"typeof":
				nextToken();
				if(!skip(Tok!"(")||!skipToUnmatched()||!skip(Tok!")")) goto Lfalse;
				if(ttype==Tok!"."){
					nextToken();
					if(!skipIdentifierList()) goto Lfalse;
				}
				break;
			default: goto Lfalse;
		}
	skipbt2: for(;;){
			switch(ttype){
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
	Expression parseInitializerExp(bool recursive=true){
		mixin(SetLoc!Expression);
		if(!recursive&&ttype==Tok!"void"){nextToken(); return res=New!VoidInitializerExp();}
		else if(ttype==Tok!"["&&(recursive||peekPastParen().type==Tok!";")){
			nextToken();
			auto e=parseAssocArgumentList!("]",false,ArrayInitAssocExp)();
			expect(Tok!"]");
			return res=New!ArrayLiteralExp(e);
		}else if(ttype!=Tok!"{") return parseExpression(rbp!(Tok!","));
		else{
			auto save=saveState();
			nextToken();
			for(int nest=1;nest;nextToken()){
				switch(ttype){
					case Tok!"{": nest++; continue;
					case Tok!"}": nest--; continue;
					case Tok!";", Tok!"return", Tok!"if", Tok!"while", Tok!"do", Tok!"for", Tok!"foreach",
						 Tok!"switch", Tok!"with", Tok!"synchronized", Tok!"try", Tok!"scope", Tok!"asm", Tok!"pragma": // TODO: complete!
						if(nest!=1) continue; // EXTENSION: This is a DMD bug
						restoreState(save); // if it contains return or ;, it is a delegate literal
						return parseExpression(rbp!(Tok!","));
					case Tok!"EOF": break;
					default: continue;
				}
				break;
			}
			restoreState(save);
			nextToken();
			auto e=parseAssocArgumentList!("}",false,StructAssocExp)();
			expect(Tok!"}");
			return res=New!StructLiteralExp(e);
		}
	}
	STC parseSTC(alias which,bool properties=true)(){
		STC stc,cstc;
	readstc: for(;;){
			switch(ttype){
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
						if(ttype!=Tok!"i"){expectErr!"attribute identifier after '@'"(); nextToken(); continue;}
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
			switch(ttype){
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
	BlockStm parseBlockStm(){
		mixin(SetLoc!BlockStm);
		expect(Tok!"{");
		auto s=appender!(Statement[])();
		while(ttype!=Tok!"}" && ttype!=Tok!"EOF"){
			s.put(parseStatement());
		}
		expect(Tok!"}");
		return res=New!BlockStm(s.data);
	}
	Declaration parseDeclaration(STC stc=STC.init){ // Helper function for parseDeclDef.
		Expression type;
		Declaration d;
		bool isAlias=ttype==Tok!"alias";
		if(isAlias) nextToken();
		STC nstc, ostc=stc; // hack to make alias this parsing easy. TODO: refactor a little
		stc|=nstc=parseSTC!toplevelSTC();
		bool needtype=true;
		if(ttype==Tok!"this" || ttype==Tok!"~"&&peek().type==Tok!"this" || ttype==Tok!"invariant") needtype=false;
		TokenType p;
		if(needtype&&(!stc||(ttype!=Tok!"i" || (p=peek().type)!=Tok!"=" && p!=Tok!"("))) type=parseType("declaration");
		if(cast(ErrorExp)type) return New!ErrorDecl;
		if(isAlias){
			if(ttype==Tok!"this"){
				nextToken();
				d=New!AliasDecl(ostc,New!VarDecl(nstc,type,New!ThisExp,cast(Expression)null)); expect(Tok!";"); // alias this
			}else d=New!AliasDecl(ostc,parseDeclarators(nstc,type));
		}else if(!needtype||peek.type==Tok!"(") d=parseFunctionDeclaration(stc,type);
		else d=parseDeclarators(stc,type);
		return d;
	}
	bool skipDeclaration(){
		TokenType p;
		if(ttype==Tok!"alias") nextToken();
		if(skipSTC!toplevelSTC()){
			if((ttype!=Tok!"i"||(p=peek().type)!=Tok!"=") && p!=Tok!"(" && !skipType()) return false;
		}else if(!skipType()) return false;
		return peek().type==Tok!"(" && skipFunctionDeclaration() || skipDeclarators();
	}
	bool isDeclaration(){ // is the parser sitting on the beginning of a Declaration?
		if(ttype==Tok!"alias") return true;
		auto save=saveState();
		bool res=skipDeclaration();
		restoreState(save);
		return res;
	}
	Expression parseCondition(){
		if(!isDeclaration()) return parseExpression(rbp!(Tok!","));
		else{
			Location loc=tok.loc;
			Expression type,init;
			auto stc=parseSTC!toplevelSTC();
			if(!stc||ttype!=Tok!"i") type=parseType();
			auto name=parseIdentifier();
			if(ttype!=Tok!"="){expectErr!"initializer for condition"(); skipToUnmatched(); return New!ErrorExp;}
			nextToken();
			init=parseExpression(rbp!(Tok!","));
			auto e=New!ConditionDeclExp(stc,type,name,init); e.loc=loc.to(init.loc);
			return e;
		}
	}
	Parameter[] parseParameterList(out VarArgs vararg){
		vararg=VarArgs.none;
		auto params=appender!(Parameter[])();
		expect(Tok!"(");
		for(;;){
			STC stc;
			Expression type;
			Identifier name;
			Expression init;
			if(ttype==Tok!")") break;
			else if(ttype==Tok!"..."){vararg=VarArgs.cStyle; nextToken(); break;}
			Location loc=tok.loc;
			stc=parseSTC!(parameterSTC, false)(); // false means no @attributes allowed
			type=parseType();
			if(ttype==Tok!"i"){name=New!Identifier(tok.name); name.loc=tok.loc; nextToken();}
			if(ttype==Tok!"="){nextToken();init=parseExpression(rbp!(Tok!","));}
			auto p=New!Parameter(stc,type,name,init); p.loc=loc.to(ptok.loc);
			params.put(p);
			if(ttype==Tok!",") nextToken();
			else{
				if(ttype==Tok!"..."){vararg=VarArgs.dStyle; nextToken();}
				break;
			}
		}
		expect(Tok!")");
		return params.data;
	}
	void parsePostcondition(out BlockStm post,out Identifier pres){ // out(pres){...}
		Location loc=tok.loc;
		expect(Tok!"out");
		if(ttype==Tok!"("){
			nextToken();
			pres=parseIdentifier();
			expect(Tok!")");
		}
		post=parseBlockStm(); post.loc=loc.to(post.loc);
	}
	Declaration parseFunctionDeclaration(STC stc, Expression ret){
		Identifier name;
		VarArgs vararg;
		Expression constr;
		TemplateParameter[] tparam; bool isTemplate=false;
		Parameter[] params;
		if(ret) goto notspecial; // so that I don't have to test for ret multiple times
		if(ttype==Tok!"this"){
			name=New!ThisExp, name.loc=tok.loc; nextToken();
			if(ttype==Tok!"("&&peek().type==Tok!"this"){
				nextToken(), nextToken(), expect(Tok!")");
				params = [New!PostblitParameter()]; // TODO: avoid heap allocation. TODO: location
				goto isspecial;
			}
		}else if(ttype==Tok!"~" && peek().type==Tok!"this"){name=New!TildeThisExp; Location loc=tok.loc; nextToken(), name.loc=loc.to(tok.loc); nextToken();}
		else if(ttype==Tok!"invariant"){Location loc=tok.loc; mixin(doParse!("_","(",")")); name=New!InvariantExp; name.loc=loc; params=[]; goto isspecial;}
		else{
			notspecial:
			if(ttype!=Tok!"i") expectErr!"function name"(), name=New!Identifier(cast(string)null);
			else{name=New!Identifier(tok.name); name.loc=tok.loc; nextToken();}
		}
		if(ttype==Tok!"(" && peekPastParen().type==Tok!"(") nextToken(), tparam=parseTemplateParameterList(), expect(Tok!")"), isTemplate=true;
		params=parseParameterList(vararg);
		isspecial:
		stc|=parseSTC!functionSTC();
		if(isTemplate) constr=parseOptTemplateConstraint();
		BlockStm pre, post, bdy;
		Identifier pres;
		if(ttype==Tok!"in"){
			Location loc=tok.loc; nextToken(); pre=parseBlockStm(); pre.loc=loc.to(pre.loc);
			if(ttype==Tok!"out") parsePostcondition(post,pres);
		}else if(ttype==Tok!"out"){
			parsePostcondition(post,pres);
			if(ttype==Tok!"in"){Location loc=tok.loc; nextToken(); pre=parseBlockStm(); pre.loc=loc.to(pre.loc);}
		}
		FunctionDecl r;
		if(ttype==Tok!"{"||ttype==Tok!"body"){
			if(pre||post) expect(Tok!"body");
			else if(ttype==Tok!"body") nextToken();
			bdy=parseBlockStm();
			r=New!FunctionDef(New!FunctionType(stc,ret,params,vararg),name,pre,post,pres,bdy);
		}else{
			if(!pre&&!post) expect(Tok!";");
			r=New!FunctionDecl(New!FunctionType(stc,ret,params,vararg),name,pre,post,pres);
		}
		return isTemplate ? New!TemplateFunctionDecl(stc,tparam,constr,r) : r;
	}
	bool skipFunctionDeclaration(){ // does not skip Parameters, STC contracts or body. I think it does not have to.
		return skip(Tok!"i") && skip(Tok!"(");// && skipToUnmatched() && skip(Tok!")");//skipSTC!functionSTC();
	}
	Expression parseFunctionLiteralExp(){
		mixin(SetLoc!Expression);
		STC stc;
		Expression ret;
		bool isStatic = ttype==Tok!"function";
		VarArgs vararg;
		Parameter[] params;
		bool hastype=false;
		if(isStatic || ttype==Tok!"delegate"){
			nextToken();
			if(ttype!=Tok!"(") stc=parseSTC!toplevelSTC(), ret=parseType();
			goto readp;
		}
		if(ttype==Tok!"(") readp: params=parseParameterList(vararg), stc|=parseSTC!functionSTC(), hastype=true;
		auto bdy=parseBlockStm();
		return res=New!FunctionLiteralExp(hastype?New!FunctionType(stc,ret,params,vararg):null,bdy,isStatic);
	}
	Declaration parseDeclarators(STC stc, Expression type){
		if(peek().type==Tok!"[") return parseCArrayDecl(stc,type);
		auto r=appender!(VarDecl[])();
		do{
			Location loc=tok.loc;
			auto name=parseIdentifier();
			Expression init;
			if(ttype==Tok!"=") nextToken(), init=parseInitializerExp(false);
			auto v=New!VarDecl(stc,type,name,init); v.loc=loc.to(ptok.loc);
			r.put(v);
			if(ttype==Tok!",") nextToken();else break;
		}while(ttype != Tok!";" && ttype != Tok!"EOF");
		expect(Tok!";");
		return r.length>1?New!Declarators(r.data):r.data[0];
	}
	bool skipDeclarators(){ // only makes sure there is at least one declarator
		return skip(Tok!"i");// && (skip(Tok!"=")||skip(Tok!",")||skip(Tok!";"));
	}
	Declaration parseCArrayDecl(STC stc, Expression type){ // support stupid C syntax
		Identifier name=parseIdentifier();
		Expression pfix=name, init=null;
		while(ttype==Tok!"["){ // kludgy way of parsing, semantic will reverse the order
			auto save = saveState();
			bool isAA=skip()&&skipType()&&ttype==Tok!"]";
			restoreState(save);
			if(isAA){mixin(doParse!("_",Type,"e","]")); pfix=New!IndexExp(pfix,[e]);}
			else pfix=led(pfix);//'Bug': allows int[1,2].
		}
		if(ttype==Tok!"=") nextToken(), init=parseInitializerExp(false);
		expect(Tok!";");
		return New!CArrayDecl(stc,type,name,pfix,init);
	}
	Declaration parseImportDecl(STC stc=STC.init){ // TODO: IdentifierList is not restictive enough
		expect(Tok!"import");
		auto symbols=appender!(Expression[])();
		auto bind=appender!(Expression[])();
		bool isBindings=false;
		for(;;){
			Expression s=parseIdentifierList();
			if(ttype==Tok!"=") nextToken(), s=New!(BinaryExp!(Tok!"="))(s,parseIdentifierList());
			else if(!isBindings&&ttype==Tok!":"){nextToken(); isBindings=true; symbols.put(s); continue;}
			if(isBindings) bind.put(s); 			//(isBindings?bind:symbols).put(s); TODO: report bug!
			else symbols.put(s);
			if(ttype==Tok!",") nextToken();
			else break;
		}
		expect(Tok!";");
		auto sym=symbols.data;
		if(isBindings) sym[$-1]=New!ImportBindingsExp(sym[$-1],bind.data);
		return New!ImportDecl(stc, sym);
	}
	EnumDecl parseEnumDecl(STC stc=STC.init){
		expect(Tok!"enum");
		Identifier tag;
		Expression base;
		auto members=appender!(Expression[2][])();
		if(ttype==Tok!"i") tag=New!Identifier(tok.name), tag.loc=tok.loc, nextToken();
		if(ttype==Tok!":") nextToken(), base = parseType();
		expect(Tok!"{");
		for(;ttype!=Tok!"}" && ttype!=Tok!"EOF";){ // BUG: only uniform type allowed
			Expression e,i;
			if(ttype==Tok!"i") e=New!Identifier(tok.name), e.loc=tok.loc, nextToken();
			else break;
			if(ttype==Tok!"=") nextToken(), i=parseExpression(rbp!(Tok!","));
			Expression[2] sarr; sarr[0]=e; sarr[1]=i;
			members.put(sarr);
			if(ttype!=Tok!"}") expect(Tok!",");
		}
		expect(Tok!"}");
		return New!EnumDecl(stc,tag,base,members.data);
	}
	TemplateParameter[] parseTemplateParameterList(){
		auto r=appender!(TemplateParameter[])();
		while(ttype!=Tok!")" && ttype!=Tok!"EOF"){
			Location loc=tok.loc;
			Expression type;
			bool isAlias=ttype==Tok!"alias", isTuple=false;
			if(isAlias) nextToken();
			else{
				auto tt=peek().type;
				if(tt!=Tok!"," && tt!=Tok!":" && tt!=Tok!"=" && tt!=Tok!")" && tt!=Tok!"...") type=parseType();
			}
			auto name=parseIdentifier();
			if(!type && ttype==Tok!"...") isTuple=true, nextToken();
			Expression spec, init;
			if(!isTuple){
				if(ttype==Tok!":"){
					nextToken(); spec=isAlias ? parseTypeOrExpression() : type?parseExpression(rbp!(Tok!",")):parseType();}
				if(ttype==Tok!"=") {parseinit: nextToken(); init=isAlias ? parseTypeOrExpression() : type?parseExpression(rbp!(Tok!",")):parseType();}
				else if(ttype==Tok!"*=" && spec){spec = New!Pointer(spec); goto parseinit;} // EXTENSION
			}
			auto p=New!TemplateParameter(isAlias,isTuple,type,name,spec,init); p.loc=loc.to(ptok.loc);
			r.put(p);
			if(ttype==Tok!",") nextToken();
			else break;
		}
		return r.data;
	}
	Expression parseOptTemplateConstraint(){ // returns null if no template constraint
		if(ttype!=Tok!"if") return null;
		mixin(doParse!("_","(",Expression,"e",")"));
		return e;
	}
	Declaration parseAggregateDecl(STC stc=STC.init, bool anonclass=false)in{assert(anonclass||ttype==Tok!"struct"||ttype==Tok!"union"||ttype==Tok!"class"||ttype==Tok!"interface");}body{
		enum{Struct,Union,Class,Interface}
		int type;
		Identifier name;
		TemplateParameter[] params; Expression constraint; bool isTemplate=false;
		auto parents=appender!(ParentListEntry[])();
		if(!anonclass){
			switch(ttype){
				case Tok!"struct": type=Struct; break;
				case Tok!"union": type=Union; break;
				case Tok!"class": type=Class; break;
				case Tok!"interface": type=Interface; break;
				default: assert(0);
			}
			nextToken();
			if(ttype==Tok!"i") name=New!Identifier(tok.name), name.loc=tok.loc, nextToken();
			if(ttype==Tok!"(") nextToken(),params=parseTemplateParameterList(),expect(Tok!")"),constraint=parseOptTemplateConstraint(),isTemplate=true;
		}else type=Class;
		if(type>=Class && (!anonclass&&ttype==Tok!":")||(anonclass&&ttype!=Tok!"{")){
			if(!anonclass) nextToken();
		readparents: for(;;){
				auto s=STC.init, nonefound=false;
				switch(ttype){
					mixin({string r; foreach(x;protectionAttributes) r~=`case Tok!"`~x~`": s=STC`~x~`; nextToken(); goto case Tok!"i";`;return r;}());
					case Tok!".", Tok!"i": parents.put(ParentListEntry(s,parseIdentifierList())); break;
					default: break readparents;
				}
				if(ttype==Tok!",") nextToken();
				else break;
			}
			if(!parents.length) expectErr!"base class or interface"();
		}
		auto bdy=anonclass||ttype!=Tok!";" ? parseBlockDecl() : (nextToken(),null);
		auto r=
			type==Struct    ? New!StructDecl(stc,name,bdy)           :
			type==Union     ? New!UnionDecl(stc,name,bdy)            :
			type==Class     ? New!ClassDecl(stc,name,parents.data,bdy)    :
			                  New!InterfaceDecl(stc,name,parents.data,bdy);
		return isTemplate ? New!TemplateAggregateDecl(stc,params,constraint,r) : r;
	}
	Expression parseVersionCondition(bool allowunittest=true){
		if(ttype==Tok!"i"){auto e=New!Identifier(tok.name); e.loc=tok.loc; nextToken(); return e;}
		if(ttype==Tok!"0"||ttype==Tok!"0L"||ttype==Tok!"0U"||ttype==Tok!"0LU"){auto e=New!LiteralExp(tok); e.loc=tok.loc; nextToken(); return e;}
		if(ttype==Tok!"unittest"&&allowunittest) return nextToken(), New!Identifier("unittest");
		expectErr!"condition";
		return New!ErrorExp;
	}
	Expression parseDebugCondition(){return parseVersionCondition(false);}
	Statement parseCondDeclBody(int flags){ // getParseProc fills in an argument called 'flags'
		if(flags&allowstm) return parseStatement();
		else return parseDeclDef(allowcompound);
	}
	enum{tryonly=1, allowcompound=2, allowstm=4}
	Declaration parseDeclDef(int flags=0){ // tryonly: return null if not start of decldef. allowcompound: allow { Decls }
		mixin(SetLoc!Declaration);
		bool isStatic=false;
		bool isMix=false;
		STC stc=STC.init;
		alias CondDeclBody Body;
	    dispatch:
		switch(ttype){
			case Tok!";": nextToken(); return res=New!Declaration(STC.init,cast(Identifier)null);
			case Tok!"module":
				mixin(rule!(ModuleDecl,Existing,"stc","_",IdentifierList,";")); // TODO: disallow ! operator
			case Tok!"static":
				nextToken();
				auto tt=ttype;
				if(tt==Tok!"assert"){mixin(rule!(StaticAssertDecl,Existing,"stc","_","(",ArgumentList,")",";"));}
				if(tt==Tok!"if"){mixin(rule!(StaticIfDecl,Existing,"stc","_","(",AssignExp,")","NonEmpty",Body,"OPT"q{"else","NonEmpty",CondDeclBody}));}
				stc|=STCstatic;
				goto dispatch;
			case Tok!"debug":
				nextToken();
				if(ttype==Tok!"="){mixin(rule!(DebugSpecDecl,Existing,"stc","_",DebugCondition,";"));}
				mixin(rule!(DebugDecl,Existing,"stc","OPT"q{"(",DebugCondition,")"},"NonEmpty",Body,"OPT"q{"else","NonEmpty",CondDeclBody}));
			case Tok!"version":
				nextToken();
				if(ttype==Tok!"="){mixin(rule!(VersionSpecDecl,Existing,"stc","_",DebugCondition,";"));}
				mixin(rule!(VersionDecl,Existing,"stc","(",VersionCondition,")","NonEmpty",Body,"OPT"q{"else","NonEmpty",CondDeclBody}));
			case Tok!"pragma":
				mixin(rule!(PragmaDecl,Existing,"stc","_","(",ArgumentList,")",CondDeclBody)); // Body can be empty
			case Tok!"import": return res=parseImportDecl(stc);
			case Tok!"enum":
				auto x=peek(), y=peek(2);
				if(x.type!=Tok!"{" && x.type!=Tok!":" && x.type!=Tok!"i" || x.type==Tok!"i" && y.type!=Tok!"{" && y.type!=Tok!":") goto default;
				return res=parseEnumDecl(stc);
			case Tok!"mixin":
				nextToken(); if(ttype==Tok!"("){mixin(rule!(MixinDecl,Existing,"stc","_",AssignExp,")",";"));}
				if(ttype==Tok!"template"){isMix=true; goto case;}
				mixin(rule!(TemplateMixinDecl,Existing,"stc",IdentifierList,"OPT",Identifier,";"));
			case Tok!"template":
				mixin(rule!(TemplateDecl,Existing,"isMix",Existing,"stc","_",Identifier,"(",TemplateParameterList,")",OptTemplateConstraint,BlockDecl));
			case Tok!"struct", Tok!"union", Tok!"class", Tok!"interface": return res=parseAggregateDecl(stc);
			case Tok!"unittest": return nextToken(), res=New!UnitTestDecl(stc,parseBlockStm());
			case Tok!"align":
				nextToken();
				if(ttype!=Tok!"("){stc|=STCalign;goto dispatch;}
				nextToken();
				if(ttype!=Tok!"0"&&ttype!=Tok!"0U"&&ttype!=Tok!"0L"&&ttype!=Tok!"0LU") expectErr!"positive integer"(); // ENHANCEMENT: U,L,LU
				auto i=tok.int64;
				mixin(rule!(AlignDecl,Existing,"stc",Existing,"i","_",")",DeclDef));
			case Tok!"extern":
				LinkageType lt;
				nextToken();
				if(ttype!=Tok!"("){stc|=STCextern; goto dispatch;}
				nextToken();
				if(ttype!=Tok!"i") expectErr!"linkage type"();
				else{
					switch(tok.name){
						case "C": nextToken();
							if(ttype==Tok!"++") lt=LinkageType.CPP, nextToken();
							else lt=LinkageType.C; break;
						case "D": nextToken(); lt=LinkageType.D; break;
						case "Windows": nextToken(); lt=LinkageType.Windows; break;
						case "Pascal": nextToken(); lt=LinkageType.Pascal; break;
						case "System": nextToken(); lt=LinkageType.System; break;
						default: error("unsupported linkage type "~tok.name); nextToken(); break;
					}
				}
				expect(Tok!")");
				return res=New!ExternDecl(stc,lt,cast(Declaration)cast(void*)parseCondDeclBody(flags));
			case Tok!"typedef": nextToken(); return res=New!TypedefDecl(stc,parseDeclaration());
			case Tok!"@": goto case;
			mixin(getTTCases(cast(string[])toplevelSTC,["align", "enum", "extern","static"]));
				STC nstc; // parseSTC might parse nothing in case it is actually a type constructor
				enum STCs={string[] r; foreach(x;toplevelSTC) if(x!="align"&&x!="enum"&&x!="extern"&&x!="static") r~=x;return r;}();
				stc|=nstc=parseSTC!STCs();
				if(ttype==Tok!"{") return res=parseBlockDecl(stc);
				else if(nstc) goto dispatch;
				else goto default;
			case Tok!"{": if(!stc&&!(flags&allowcompound)) goto default; return res=parseBlockDecl(stc);
			case Tok!":": if(!stc&&!(flags&allowcompound)) goto default; nextToken(); return res=New!AttributeDecl(stc,parseDeclDefs());
			default:
				if(!(flags&tryonly)) return res=parseDeclaration(stc);
				else return stc || isDeclaration() ? res=parseDeclaration(stc) : null;
		}
	}

	BlockDecl parseBlockDecl(STC stc=STC.init){
		expect(Tok!"{");
		auto r=appender!(Declaration[])();
		while(ttype!=Tok!"}" && ttype!=Tok!"EOF"){
			r.put(parseDeclDef());
		}
		expect(Tok!"}");
		return New!BlockDecl(stc,r.data);
	}

	Declaration[] parseDeclDefs(){
		auto x=appender!(Declaration[])();
		while(ttype!=Tok!"}" && ttype!=Tok!"EOF") x.put(parseDeclDef());
		return x.data;
	}

	auto parse(){
		//auto r=appender!(Declaration[])();
		Declaration[] r;
		while(ttype!=Tok!"EOF"){
			if(ttype==Tok!"}") expectErr!"declaration"(), nextToken();
			r~=parseDeclDefs();
		}
		return r;
	}
}

Declaration[] parse(string code, ErrorHandler handler){
	return Parser(lex(code),handler).parse();
}

