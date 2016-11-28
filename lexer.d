// Written in the D programming language
// Author: Timon Gehr
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.string, utf = std.utf, std.uni;
import std.stdio, std.conv;
import std.algorithm : startsWith, swap;
import std.traits : EnumMembers;

import core.memory;

import util : lowerf, escape, mallocAppender, toEngNum;

mixin("enum TokenType{"~TokenNames()~"}");

template Tok(string type){mixin(TokImpl());}
template TokChars(TokenType type){mixin(TokCharsImpl());}


private immutable {
string[2][] complexTokens =
	[["i",     "Identifier"                ],
	 ["``",    "StringLiteral"             ],
	 ["``c",   "StringLiteralC"            ],
	 ["``w",   "StringLiteralW"            ],
	 ["``d",   "StringLiteralD"            ],
	 ["' '",   "CharacterLiteral"          ],
	 ["0",     "IntLiteral"                ],
	 ["0U",    "UintLiteral"               ],
	 ["0L",    "LongLiteral"               ],
	 ["0LU",   "UlongLiteral"              ],
	 [".0f",   "FloatLiteral"              ],
	 [".0",    "DoubleLiteral"             ],
	 [".0L",   "RealLiteral"               ],
	 [".0fi",  "ImaginaryFloatLiteral"     ],
	 [".0i",   "ImaginaryDoubleLiteral"    ],
	 [".0Li",  "ImaginaryLiteral"          ]];
string[2][] simpleTokens = 
	[["/",     "Divide"                    ],
	 ["/=",    "DivideAssign"              ],
	 [".",     "Dot"                       ],
	 ["..",    "DotDot"                    ],
	 ["...",   "DotDotDot"                 ],
	 ["&",     "And"                       ],
	 ["&=",    "AndAssign"                 ],
	 ["&&",    "AndAnd"                    ],
	 ["|",     "Or"                        ],
	 ["|=",    "OrAssign"                  ],
	 ["||",    "OrOr"                      ],
	 ["-",     "Minus"                     ],
	 ["-=",    "MinusAssign"               ],
	 ["--",    "MinusMinus"                ],
	 ["+",     "Plus"                      ],
	 ["+=",    "PlusAssign"                ],
	 ["++",    "PlusPlus"                  ],
	 ["<",     "Less"                      ],
	 ["<=",    "LessEqual"                 ],
	 ["<<",    "LeftShift"                 ],
	 ["<<=",   "LeftShiftAssign"           ],
	 ["<>",    "LessGreater"               ],
	 ["<>=",   "LessGreaterEqual"          ],
	 [">",     "Greater"                   ],
	 [">=",    "GreaterEqual"              ],
	 [">>=",   "RightShiftAssign"          ],
	 [">>>=",  "LogicalRightShiftAssign"   ],
	 [">>",    "RightShift"                ],
	 [">>>",   "LogicalRightShift"         ],
	 ["!",     "ExclamationMark"           ],
	 ["!=",    "NotEqual"                  ],
	 ["!<>",   "NotLessGreater"            ],
	 ["!<>=",  "Unordered"                 ],
	 ["!<",    "NotLess"                   ],
	 ["!<=",   "NotLessEqual"              ],
	 ["!>",    "NotGreater"                ],
	 ["!>=",   "NotGreaterEqual"           ],
	 ["(",     "LeftParen"                 ],
	 [")",     "RightParen"                ],
	 ["[",     "LeftBracket"               ],
	 ["]",     "RightBracket"              ],
	 ["{",     "LeftCurly"                 ],
	 ["}",     "RightCurly"                ],
	 ["?",     "QuestionMark"              ],
	 [",",     "Comma"                     ],
	 [";",     "Semicolon"                 ],
	 [":",     "Colon"                     ],
	 ["$",     "Dollar"                    ],
	 ["=",     "Assign"                    ],
	 ["=>",    "GoesTo"                    ],
	 ["==",    "Equal"                     ],
	 ["*",     "Star"                      ],
	 ["*=",    "MultiplyAssign"            ],
	 ["%",     "Modulo"                    ],
	 ["%=",    "ModuloAssign"              ],
	 ["^",     "Xor"                       ],
	 ["^=",    "XorAssign"                 ],
	 ["^^",    "Pow"                       ],
	 ["^^=",   "PowAssign"                 ],
	 ["~",     "Concat"                    ],
	 ["~=",    "ConcatAssign"              ],
	 ["@",     "At"                        ]];
string[2][] specialTokens = 
	[["",      "None",                     ],
	 [" ",     "Whitespace",               ],
	 ["//",    "Comment",                  ],
	 ["///",   "DokComment",               ],
	 ["\n",    "NewLine",                  ], // TODO: incorporate unicode new line support
	 ["Error", "Error"                     ],
	 ["__error","ErrorLiteral"             ],
	 ["EOF",   "Eof"                       ]];
string[2][] compoundTokens =
	[["auto ref", "AutoRef"                ],
	 ["!is"     , "NotIs"                  ],
	 ["!in"     , "NotIn"                  ]];

string[] keywords = ["abstract", "alias", "align", "asm", "assert", "auto", "body", "bool", "break", "byte", "case", "cast", "catch", "cdouble", "cent", "cfloat", "char", "class", "const", "continue", "creal", "dchar", "debug", "default", "delegate", "delete", "deprecated", "do", "double", "else", "enum", "export", "extern", "false", "final", "finally", "float", "for", "foreach", "foreach_reverse", "function", "goto", "idouble", "if", "ifloat", "immutable", "import", "in", "inout", "int", "interface", "invariant", "ireal", "is", "lazy", "long", "macro", "mixin", "module", "new", "nothrow", "null", "out", "override", "package", "pragma", "private", "protected", "public", "pure", "real", "ref", "return", "scope", "shared", "short", "static", "struct", "super", "switch", "synchronized", "template", "this", "throw", "true", "try", "typedef", "typeid", "typeof", "ubyte", "ucent", "uint", "ulong", "union", "unittest", "ushort", "version", "void", "volatile", "wchar", "while", "with", /*"__FILE__", "__LINE__",*/ "__gshared", "__thread", "__traits"];


string[2][] tokens = specialTokens ~ complexTokens ~ simpleTokens ~ compoundTokens ~ keywordTokens();
}

private{
auto keywordTokens(){
	immutable(string[2])[] r;
	foreach(i,kw;keywords) r~=[kw,kw~"_"];
	return r;
}

string TokenNames(){
	string r;
	foreach(t;tokens) r~=lowerf(t[1])~",";
	return r;
}

string TokImpl(){
	string r="static if(type==\""~tokens[0][0]~"\") alias TokenType."~lowerf(tokens[0][1])~" Tok;";
	foreach(t;tokens) r~="else static if(type==\""~t[0]~"\") alias TokenType."~lowerf(t[1])~" Tok;";
	r~="else static assert(0,\"unknown Token '\"~type~\"'\");";
	return r;
}

string TokCharsImpl(){
	string r="static if(type==TokenType."~lowerf(tokens[0][1])~") enum TokChars=\""~tokens[0][0]~"\";";
	foreach(t;tokens) r~="else static if(type==TokenType."~lowerf(t[1])~") enum TokChars=\""~t[0]~"\";";
	r~="else static assert(0,\"invalid TokenType \"~to!string(type));";
	return r;
}
}
string TokenTypeToString(TokenType type){
	return tokens[cast(int)type][0];
}

string toString(immutable(Token)[] a){string r;foreach(t;a) r~='['~t.toString()~']'; return r;}

class Source{
	immutable{
		string name;
		string code;
	}
	this(string name, string code)in{auto c=code;assert(c.length>=4&&!c[$-4]&&!c[$-3]&&!c[$-2]&&!c[$-1]);}body{ // four padding zero bytes required because of UTF{
		this.name = name;
		this.code = code[0..$-4]; // don't expose the padding zeros
		sources ~= this;
	}
	string getLineOf(string rep)in{assert(this is get(rep));}body{
		//if(!code.length) return code;
		string before=code.ptr[0..code.length+4][0..rep.ptr-code.ptr];
		string after =code.ptr[0..code.length+4][rep.ptr-code.ptr..$];
		immutable(char)* start=code.ptr, end=code.ptr+code.length;
		foreach_reverse(ref c; before) if(c=='\n'||c=='\r'){start = &c+1; break;}
		foreach(ref c; after) if(c=='\n'||c=='\r'){end = &c; break;}
		return start[0..end-start];
	}
	static Source get(string rep){
		foreach(x; sources) if(rep.ptr>=x.code.ptr && rep.ptr+rep.length<=x.code.ptr+x.code.length+4) return x;
		return null;
	}
	void dispose(){
		foreach(i,x; sources) if(x is this){
			swap(sources[i], sources[$-1]);
			sources=sources[0..$-1];
			sources.assumeSafeAppend();
		}
		assert(0);
	}
	private static Source[] sources;
}

struct Location{
	string rep;    // slice of the code representing the Location
	int line;      // line number at start of location

	// reference to the source the code belongs to
	@property Source source()const{
		auto src = Source.get(rep);
		assert(src, "source for '"~rep~"' not found!");
		return src;
	}
	Location to(const(Location) end)const{// in{assert(end.source is source);}body{
		// in{assert(rep.ptr<=end.rep.ptr);}body{ // requiring that is not robust enough
		if(rep.ptr>end.rep.ptr+end.rep.length) return cast()this;
		return Location(rep.ptr[0..end.rep.ptr-rep.ptr+end.rep.length],line);
	}
}
import std.array;
int getColumn(Location loc, int tabsize){
	int res=0;
	auto l=loc.source.getLineOf(loc.rep);
	for(;!l.empty&&l[0]&&l.ptr<loc.rep.ptr; l.popFront()){
		if(l.front=='\t') res=res-res%tabsize+tabsize;
		else res++;
	}
	return res+1;
}

struct Token{
	TokenType type;
	string toString() const{
		if(type == Tok!"EOF") return "EOF";
		if(loc.rep.length) return loc.rep;
		// TODO: remove boilerplate
		// TODO: get better representations
		switch(type){
			case Tok!"i":
				return name;
			case Tok!"``":
				return '"'~escape(str)~'"';
			case Tok!"``c":
				return '"'~escape(str)~`"c`;
			case Tok!"``w":
				return '"'~escape(str)~`"w`;
			case Tok!"``d":
				return '"'~escape(str)~`"d`;
			case Tok!"' '":
				return '\''~escape(to!string(cast(dchar)int64),false)~'\'';
			case Tok!"0":
				return to!string(cast(int)int64);
			case Tok!"0U":
				return to!string(cast(uint)int64)~'U';
			case Tok!"0L":
				return to!string(cast(long)int64)~'L';
			case Tok!"0LU":
				return to!string(int64)~"LU";
			case Tok!".0f":
				return to!string(flt80)~'f';
			case Tok!".0":
				return to!string(flt80);
			case Tok!".0L":
				return to!string(flt80)~'L';
			case Tok!".0i":
				return to!string(flt80)~'i';
			case Tok!".0fi":
				return to!string(flt80)~"fi";
			case Tok!".0Li":
				return to!string(flt80)~"Li";
			case Tok!"Error":
				return "error: "~str;
			default:
				return tokens[cast(int)type][0];case Tok!"true": return "true";
		}
	}
	union{
		string str, name;  // string literals, identifiers
		ulong int64;       // integer literals
		real flt80;        // float, double, real literals
	}
	Location loc;
}
template token(string t){enum token=Token(Tok!t);} // unions not yet supported

unittest{
static assert({
	foreach(i;simpleTokens){
		string s=i[0];
		bool found = s.length==1;
		foreach(j;simpleTokens) if(j[0] == s[0..$-1]) found = true;
		if(!found) return false;
	}return true;
}(),"Every non-empty prefix of simpleTokens must be a valid token.");
}
string caseSimpleToken(string prefix="", bool needs = false)pure{
	string r;
	int c=0,d=0;
	foreach(i;simpleTokens){string s=i[0]; if(s.startsWith(prefix)) c++;}
	if(c==1) r~=`res[0].type = Tok!"`~prefix~'"'~";\nbreak;\n";
	else{
		if(needs) r~="switch(*p){\n";
		foreach(i;simpleTokens){
			string s = i[0]; if(s[0]=='/' || s[0] == '.') continue; // / can be the start of a comment, . could be the start of a float literal
			if(s.startsWith(prefix) && s.length==prefix.length+1){
				r~=`case '`~s[$-1]~"':\n"~(needs?"p++;\n":"");
				r~=caseSimpleToken(s,true);
			}
		}
		if(prefix=="!") r~="default: mixin(lexNotAndNotIsAndNotIn);\nbreak;\n}\nbreak;\n";
		else if(needs) r~=`default: res[0].type = Tok!"`~prefix~`"`~";\nbreak;\n}\nbreak;\n";
	}
	return r;
}


auto lex(Source source){ // pure
	return Lexer(source);
}

struct Anchor{
	size_t index;
}

struct Lexer{
	string code; // Manually allocated!
	Token[] buffer;
	Token[] errors;
	Source source;
	size_t n,m; // start and end index in buffer
	size_t s,e; // global start and end index
	size_t numAnchors;  // number of existing anchors for this lexer
	size_t firstAnchor; // first local index that has to remain in buffer
	int line;
	/+invariant(){ // useless because DMD does not test the invariant at the proper time...
		assert(e-s == (m-n+buffer.length)%buffer.length); // relation between (s,e) and (n,m)
		assert(!(buffer.length&buffer.length-1)); // buffer size is always a power of two
		assert(numAnchors||firstAnchor==size_t.max);
	}+/
	//pure: phobos ...
	this(Source src){
		source = src;
		code = src.code.ptr[0..src.code.length+4]; // rely on 4 padding zero bytes
		enum initsize=4096;//685438;//
		buffer = new Token[](initsize);//
		//buffer = (cast(Token*)malloc(Token.sizeof*initsize))[0..initsize];//
		numAnchors=0;
		firstAnchor=size_t.max;
		line=1;
		n=s=0;
		e=lexTo(buffer);
		m=e&buffer.length-1;
		if(src.code.length > int.max) errors~=tokError("no support for sources exceeding 2GB",null),code.length=int.max;
	}
	@property ref const(Token) front()const{return buffer[n];}
	@property bool empty(){return buffer[n].type==Tok!"EOF";}
	void popFront(){
		assert(!empty,"attempted to popFront empty lexer.");
		n = n+1 & buffer.length-1; s++;
		if(s<e) return; // if the buffer still contains elements
		assert(s==e && n==m);
		if(!numAnchors){// no anchors, that is easy, just reuse the whole buffer
			buffer[0]=buffer[n-1&buffer.length-1]; // we want at least one token of lookback, for nice error reporting
			e+=m=lexTo(buffer[n=1..$]);
			m=m+1&buffer.length-1;
			return;
		}
		assert(firstAnchor<buffer.length);
		size_t num;
		if(m < firstAnchor){ // there is an anchor but still space
			num=lexTo(buffer[n..firstAnchor]);
			e+=num; m=m+num&buffer.length-1;
			return;
		}else if(m > firstAnchor){ // ditto
			num=lexTo(buffer[m..$]);
			if(firstAnchor) num+=lexTo(buffer[0..firstAnchor]);
			e+=num; m=m+num&buffer.length-1;
			return;
		}
		auto len=buffer.length;
		buffer.length=len<<1; // double buffer size
		//buffer=(cast(Token*)realloc(buffer.ptr,(len<<1)*Token.sizeof))[0..len<<1];
		n=len+firstAnchor; // move start and firstAnchor
		buffer[len..n]=buffer[0..firstAnchor]; // move tokens to respect the new buffer topology
		num=0;
		if(n<buffer.length){
			num=lexTo(buffer[n..$]);
			e+=num; m=n+num&buffer.length-1;
		}	
		if(!m&&firstAnchor){
			num=lexTo(buffer[0..firstAnchor]);
			e+=num; m=num&buffer.length-1;
		}
	}
	Anchor pushAnchor(){
		if(!numAnchors) firstAnchor=n;
		numAnchors++;
		return Anchor(s);
	}
	void popAnchor(Anchor anchor){
		numAnchors--;
		if(!numAnchors) firstAnchor=size_t.max;
		n=n+anchor.index-s&buffer.length-1;
		s=anchor.index;
	}

private:
	Token tokError(string s, string rep, int l=0){
		auto r = token!"Error";
		r.str = s;
		r.loc = Location(rep, l?l:line);
		return r;
	}

	size_t lexTo(Token[] res)in{assert(res.length);}body{
		alias mallocAppender appender;
		if(!code.length) return 0;
		auto p=code.ptr;
		auto s=p;    // used if the input has to be sliced
		auto sl=line;// ditto
		char del;    // used if a delimiter of some sort needs to be remembered
		size_t len;  // used as a temporary that stores the length of the last UTF sequence
		size_t num=0;// number of tokens lexed, return value
		typeof(p) invCharSeq_l=null;
		void invCharSeq(){
			if(p>invCharSeq_l+1) errors~=tokError("unsupported character",p[0..1]);
			else errors[$-1].loc.rep=errors[$-1].loc.rep.ptr[0..errors[$-1].loc.rep.length+1];
			invCharSeq_l=p; p++;
		}
		// text macros:
		enum skipUnicode = q{if(*p<0x80){p++;break;} len=0; try utf.decode(p[0..4],len), p+=len; catch{invCharSeq();}};
		enum skipUnicodeCont = q{if(*p<0x80){p++;continue;} len=0; try utf.decode(p[0..4],len), p+=len; catch{invCharSeq();}}; // don't break, continue
		enum caseNl = q{case '\r':  if(p[1]=='\n') p++; goto case; case '\n': line++; p++; continue;};
		loop: while(res.length) { // breaks on EOF or buffer full
			auto begin=p; // start of a token's representation
			auto sline=line;
			switch(*p++){
				// whitespace
				case 0, 0x1A:
					res[0].type = Tok!"EOF";
					res[0].loc.rep=p[0..1];
					res[0].loc.line = line; // TODO: Why is this necessary?
					res=res[1..$];
					num++;
					break loop;
				case ' ', '\t', '\v':
					continue;   // ignore whitespace
				case '\r': if(*p=='\n') p++; goto case;
				case '\n': line++;
					continue;

				// ! can be the start of !is or !in tokens
				enum lexNotAndNotIsAndNotIn=q{
					s = p; int cline = line; // save p and line in case we will NOT find in or is
					findnotinnotis: for(;;){
						switch(*p){
							case 'i': p++;
								if(*p == 's') res[0].type = Tok!"!is";
								else if(*p == 'n') res[0].type = Tok!"!in";
								else goto default;
								p++;
								// make sure the identifier stops here:
								if('a' <= *p && *p <='z') goto default;
								if('A' <= *p && *p <='Z') goto default;
								if('0' <= *p && *p <='9') goto default;
								if(*p&0x80){
									try{
										auto ch=utf.decode(p[0..4],len);
										if(isAlpha(ch)) goto default;
									}catch{} goto default;
								}
								break findnotinnotis;
							case ' ', '\t', '\v': 
								p++; continue; // ignore whitespace
							case '\r': if(*++p=='\n') p++; goto case;
							case '\n': line++;
								p++; continue;
							case 0x80: .. case 0xFF:
								len=0;
								try{
									auto ch=utf.decode(p[0..4],len);
									if(isWhite(ch)) p+=len; continue;
								}catch{} goto default;
							default:
								res[0].type = Tok!"!";
								p = s;
								line = cline;
								break findnotinnotis;
						}
					}
				};
			
				// simple tokens
				mixin(caseSimpleToken());
				
				// slash is special
				case '/':
					switch(*p){
						case '=': res[0].type = Tok!"/="; p++;
							break;
						case '/': p++;
							while(((*p!='\n') & (*p!='\r')) & ((*p!=0) & (*p!=0x1A))) mixin(skipUnicodeCont);
							continue; // ignore comment
						case '*':
							s=p++-1;
							sl=line;
							consumecom2: for(;;){
								switch(*p){
									mixin(caseNl); // handle newlines
									case '*': p++; if(*p=='/'){p++; break consumecom2;} break;
									case 0, 0x1A: errors~=tokError("unterminated /* */ comment",s[0..p-s],sl); break consumecom2;
									default: mixin(skipUnicode);
								}
							}
							continue; // ignore comment
						case '+':
							int d=1;
							s=p++-1;
							sl=line;
							consumecom3: while(d){
								switch(*p){
									mixin(caseNl); // handle newlines
									case '+':  p++; if(*p=='/') d--, p++; break;
									case '/':  p++; if(*p=='+') d++, p++; break;
									case 0, 0x1A: errors~=tokError("unterminated /+ +/ comment",s[0..p-s],sl); break consumecom3;
									default: mixin(skipUnicode);
								}
							}
							continue; // ignore comment
						default: res[0].type = Tok!"/"; break;
					}
					break;
				// dot is special
				case '.':
					if('0' > *p || *p > '9'){
						if(*p != '.')      res[0].type = Tok!".";
						else if(*++p!='.') res[0].type = Tok!"..";
						else               res[0].type = Tok!"...", p++;
						break;
					}
					goto case;
				// numeric literals
				case '0': .. case '9':
					res[0] = lexNumber(--p);
					if(res[0].type == Tok!"Error") errors~=res[0], res[0].type=Tok!"__error";
					break;
				// character literals
				case '\'':
					s = p; sl = line;
					res[0].type = Tok!"' '";
					if(*p=='\\'){
						try p++, res[0].int64 = cast(ulong)readEscapeSeq(p);
						catch(EscapeSeqException e) if(e.msg) errors~=tokError(e.msg,e.loc); else invCharSeq();
					}else{
						try{
							len=0;
							res[0].int64 = utf.decode(p[0..4],len);
							p+=len;
						}catch{invCharSeq();}
					}
					if(*p!='\''){
						//while((*p!='\''||(p++,0)) && *p && *p!=0x1A) mixin(skipUnicodeCont);
						errors~=tokError("unterminated character constant",(s-1)[0..p-s+1],sl);
					}else p++;
					break;
				// string literals
				// WYSIWYG string/AWYSIWYG string
				case 'r':
					if(*p!='"') goto case 'R';
					p++; del='"';
					goto skipdel;
				case '`':
					del = '`'; skipdel:
					s = p; sl = line;
					readwysiwyg: for(;;){
						if(*p==del){p++; break;} 
						switch(*p){
							mixin(caseNl); // handle newlines
							case 0, 0x1A:
								errors~=tokError("unterminated string literal", (s-1)[0..1],sl);
								break readwysiwyg;
							default: mixin(skipUnicode);
						}
					}
					res[0].type = Tok!"``";
					res[0].str = s[0..p-s-1]; // reference to code
					goto lexstringsuffix;
				// token string
				case 'q':
					if(*p=='"') goto delimitedstring;
					if(*p!='{') goto case 'Q';
					p++; s = p; sl = line;
					del = 0;
					readtstring: for(int nest=1;;){ // TODO: implement more efficiently
						Token tt;
						code=code[p-code.ptr..$]; // update code to allow recursion
						lexTo((&tt)[0..1]);
						p=code.ptr;
						switch(tt.type){
							case Tok!"EOF":
								errors~=tokError("unterminated token string literal", (s-2)[0..1], sl);
								break readtstring;
							case Tok!"{":  nest++; break;
							case Tok!"}":  nest--; if(!nest) break readtstring; break;
							default: break;
						}
					}
					res[0].type = Tok!"``";
					res[0].str = s[0..p-s-1]; // reference to code
					goto lexstringsuffix;
					delimitedstring:
					res[0].type = Tok!"``";
					s=++p; sl=line;
					switch(*p){
						case 'a': .. case 'z':
						case 'A': .. case 'Z':
							for(;;){
								switch(*p){
									case '\r': if(p[1]=='\n') p++; goto case;
									case '\n': line++; break;
									case 0, 0x1A: break;
									case 'a': .. case 'z':
									case 'A': .. case 'Z':
									case '0': .. case '9':
										p++;
										continue;
									case 0x80: .. case 0xFF:
										len=0;
										try{auto ch=utf.decode(p[0..4],len);
											if(isAlpha(ch)){p+=len; continue;}
											break;
										}catch{invCharSeq(); break;}
									default: break;
								}
								break;
							}
							if(*p!='\n' && *p!='\r') errors~=tokError("heredoc identifier must be followed by a new line",p[0..1]);
							while(((*p!='\n') & (*p!='\r')) & ((*p!=0) & (*p!=0x1A))) mixin(skipUnicodeCont); // mere error handling
							auto ident=s[0..p-s];
							if(*p=='\r'){line++;p++;if(*p=='\n') p++;}
							else if(*p=='\n'){line++;p++;}
							s=p;
							readheredoc: while((*p!=0) & (*p!=0x1A)){ // always at start of new line here
								for(auto ip=ident.ptr, end=ident.ptr+ident.length;;){
									if(ip==end) break readheredoc;
									switch(*p){
										mixin(caseNl);
										case 0x80: .. case 0xFF:
											len=0;
											try{auto ch=utf.decode(p[0..4],len);
												if(isAlpha(ch)){
													if(p[0..len]!=ip[0..len]) break;
													p+=len; ip+=len; continue;
												}
												break;
											}catch{invCharSeq(); break;}
										default: 
											if(*p!=*ip) break;
											p++; ip++; continue;
									}
									break;
								}
								while(((*p!='\n') & (*p!='\r')) & ((*p!=0) & (*p!=0x1A))) mixin(skipUnicodeCont);
								if(*p=='\r'){line++;p++;if(*p=='\n') p++;}
								else if(*p=='\n'){line++;p++;}
							}
							res[0].str = p>s+ident.length?s[0..p-s-ident.length]:""; // reference to code
							if(*p!='"') errors~=tokError("unterminated heredoc string literal",(s-1)[0..1],sl);
							else p++;
							break;
						default:
							del=*p; char rdel=del; dchar ddel=0;
							switch(del){
								case '[': rdel=']'; s=++p; break;
								case '(': rdel=')'; s=++p; break;
								case '<': rdel='>'; s=++p; break;
								case '{': rdel='}'; s=++p; break;
								case '\r': if(p[1]=='\n') p++; goto case;
								case '\n': line++; p++; goto case;
								case ' ','\t','\v':
									errors~=tokError("string delimiter cannot be whitespace",p[0..1]);
									goto case;
								case 0x80: case 0xFF:
									s=p;
									len=0;
									try{
										ddel=utf.decode(p[0..4],len);
										s=p+=len;
									}catch{invCharSeq();}
								default: p++; break;
							}
							if(ddel){
								while((*p!=0) & (*p!=0x1A)){
									if(*p=='\r'){line++;p++;if(*p=='\n') p++;}
									else if(*p=='\n'){line++;p++;}
									else if(*p<0x80){p++; continue;}
									try{
										auto x=utf.decode(p[0..4],len);
										if(ddel==x){
											res[0].str = s[0..p-s]; // reference to code
											p+=len; break;
										}
										p+=len;
									}catch{invCharSeq();}								
								}
							}else{
								for(int nest=1;(nest!=0) & (*p!=0) & (*p!=0x1A);){
									if(*p=='\r'){line++;p++;if(*p=='\n') p++;}
									else if(*p=='\n'){line++;p++;}
									else if(*p==rdel){nest--; p++;}
									else if(*p==del){nest++; p++;}
									else if(*p & 0x80){
										try{
											utf.decode(p[0..4],len);
											p+=len;
										}catch{invCharSeq();}
									}else p++;
								}
								res[0].str = s[0..p-s-1]; // reference to code
							}
							if(*p!='"'){
								if(*p) errors~=tokError("expected '\"' to close delimited string literal",p[0..1]);
								else errors~=tokError("unterminated delimited string literal",(s-2)[0..1],sl);
							}else p++;
							break;
					}
					goto lexstringsuffix;
				// Hex string
				case 'x':
					if(*p!='"') goto case 'X';
					auto r=appender!string(); p++; s=p; sl=line;
					readhexstring: for(int c=0,ch,d;;p++,c++){
						switch(*p){
							mixin(caseNl); // handle newlines
							case ' ', '\t', '\v': c--; break;
							case 0, 0x1A:
								errors~=tokError("unterminated hex string literal",(s-1)[0..1],sl);
								break readhexstring;
							case '0': .. case '9': d=*p-'0'; goto handlexchar;
							case 'a': .. case 'f': d=*p-('a'-0xa); goto handlexchar;
							case 'A': .. case 'F': d=*p-('A'-0xA); goto handlexchar;
							handlexchar:
								if(c&1) r.put(cast(char)(ch|d));
								else ch=d<<4; break;
							case '"':
								if(c&1) errors~=tokError(format("found %s character%s when expecting an even number of hex digits",toEngNum(c),c!=1?"s":""),s[0..p-s]);
								p++; break readhexstring;
							default:
								if(*p<128) errors~=tokError(format("found '%s' when expecting hex digit",*p),p[0..1]);
								else{
									s=p;
									len=0;
									try{
										auto chr = utf.decode(p[0..4],len);
										p+=len-1;
										if(isWhite(chr)) break; //TODO: newlines
									}catch{invCharSeq();}
									errors~=tokError(format("found '%s' when expecting hex digit",s[0..len]),s[0..len]);
								}
								break;
						}
					}
					res[0].type = Tok!"``";
					res[0].str = r.data;
					goto lexstringsuffix;
				// DQString
				case '"':
					{
					// appender only used if there is an escape sequence, slice otherwise
					// TODO: how costly is eager initialization?
					auto r=appender!string();
					auto start = s = p;
					readdqstring: for(;;){
						switch(*p){
							mixin(caseNl);
							case 0, 0x1A:
								errors~=tokError("unterminated string literal",(start-1)[0..1]);
								break readdqstring;
							case '\\':
								r.put(s[0..p++-s]);
								try r.put(readEscapeSeq(p));
								catch(EscapeSeqException e) if(e.msg) errors~=tokError(e.msg,e.loc); else invCharSeq();
								s = p;
								continue;
							case '"': p++; break readdqstring;
							default: mixin(skipUnicode);
						}
					}					
					res[0].type = Tok!"``";
					if(!r.data.length) res[0].str = start[0..p-1-start];
					else{ r.put(s[0..p-1-s]); res[0].str = r.data; }
					goto lexstringsuffix;
					}
					lexstringsuffix:
					if(*p=='c')      res[0].type = Tok!"``c", p++;
					else if(*p=='w') res[0].type = Tok!"``w", p++;
					else if(*p=='d') res[0].type = Tok!"``d", p++;
					break;
				// identifiers and keywords
				case '_':
				case 'a': .. case 'p': /*q, r*/ case 's': .. case 'w': /*x*/ case 'y', 'z':
				case 'A': .. case 'Z':
					s = p-1;
					identifier:
					readident: for(;;){
						switch(*p){
							case '_':
							case 'a': .. case 'z':
							case 'A': .. case 'Z':
							case '0': .. case '9':
								p++;
								break;
							case 0x80: .. case 0xFF:
								len=0;
								try if(isAlpha(utf.decode(p[0..4],len))) p+=len;
									else break readident;
								catch{break readident;} // will be caught in the next iteration
								break;
							default: break readident;
						}
					}
					
					res[0].name = s[0..p-s];
					res[0].type=isKeyword(res[0].name);
					break;
				case 0x80: .. case 0xFF:
					len=0; p--;
					try{auto ch=utf.decode(p[0..4],len);
						s=p, p+=len;
						if(isAlpha(ch)) goto identifier;
						if(!isWhite(ch)) errors~=tokError(format("unsupported character '%s'",ch),s[0..len]);
						// else if(isNewLine(ch)) line++; // TODO: implement this everywhere
						continue;
					}catch{} goto default;
				default:
					p--; invCharSeq(); p++;
					continue;
			}
			res[0].loc.rep=begin[0..p-begin];
			res[0].loc.line=sline;
			res=res[1..$];
			num++;
		}
		code=code[p-code.ptr..$];
		return num;
	}
	
	/* Lex a number FSM. TDPL p33/35
	   Returns either a valid literal token or one of the following:
	   errExp       = tokError("exponent expected");
	   errsOverflow = tokError("signed integer constant exceeds long.max");
	   errOverflow  = tokError("integer constant exceeds ulong.max");
	   //errRepr      = tokError("numerical constant is not representable in [float|double|real]");
	   errOctDepr   = tokError("octal literals are deprecated");
	*/
	private Token lexNumber(ref immutable(char)* _p){
		static assert(real.mant_dig <= 64);
		auto p = _p;
		enum dlim  = ulong.max / 10; // limit for decimal values (prevents overflow)
		enum helim = int.max / 10;   // ditto for binary exponent (hex floats)
		enum elim  = int.max / 10;   // ditto for exponent
		Token tok;
		bool leadingzero = 0;
		bool isfloat = 0;// true if floating point literal
		bool isimag = 0; // true if imaginary floating point literal. as in DMD, this only works for decimals
		bool toobig  = 0;// true if value exceeds ulong.max
		ulong val = 0;   // current literal value
		real rval = 0.0L;// real value
		long exp = 0;    // exponent
		bool neg = 0;    // exponent is negative
		int dig = 0;     // number of consumed digits
		int dot = -1;    // position of decimal dot, counted from the left (-1=not encountered yet)
		int adjexp = 0;  // exponent adjustment due to very long literal
		enum : int {DEC, BIN, OCT, HEX}
		int base = DEC;
		// powers of 2 and 10 for fast computation of rval given the mantissa and exponents. (TODO: Get rid of pw2)
		static immutable pw2 = mixin("["~{string r; foreach(i;0..16) r~="0x1p"~to!string(1L<<i)~"L,"; return r;}()~"]");
		static immutable pw10= mixin("["~{string r; for(int i=15;i>=0;i--) r~= "1e"~to!string(1L<<i)~"L,"; return r;}()~"]");
		static immutable pn10= mixin("["~{string r; for(int i=15;i>=0;i--) r~= "1e-"~to!string(1L<<i)~"L,"; return r;}()~"]");
		selectbase: switch(*p){
			case '0':
				p++;
				switch(*p){
					case 'x', 'X':
						p++;
						base = HEX;
						while(*p == '0') p++; // eat leading zeros
						readhex: for(;dig<16;p++){
							switch(*p){
								case '0': .. case '9':
									val = val << 4 | *p-'0'; dig++;
									break;
								case 'a': .. case 'f':
									val = val << 4 | *p-('a'-0xa); dig++;
									break;
								case 'A': .. case 'F':
									val = val << 4 | *p-('A'-0xA); dig++;
									break;
								case '.':
									if(p[1] != '.' && dot == -1) dot = dig, isfloat=1;
									else break readhex; goto case;
								case '_': // ignore embedded _
									break; 
								default:
									break readhex;	
							}
						}
						if(dig == 16 && ('8' <= *p && *p <= '9' || 'a' <= *p && *p <= 'f' || 'A' <=*p && *p <= 'F')){ // round properly
							val++;
							if(!val) val = 1, adjexp = 16; // cope with overflow
						}
						consumehex: for(;;p++){
							switch(*p){
								case '0': .. case '9':
								case 'a': .. case 'f':
								case 'A': .. case 'F':
									dig++; adjexp++;
									break;
								case '.':
									if(p[1] != '.' && dot == -1) dot = dig, isfloat = 1; // break; }
									else break consumehex; goto case;
								case '_': // ignore embedded _
									break;
								case 'p', 'P':
									isfloat = 1;
									p++;
									neg = 0;
									switch(*p){
										case '-': neg = 1; goto case;
										case '+': p++;     goto default;
										default:  break; 
									}
									if('0'> *p || *p > '9') goto Lexp;
									readhexp: for(;;p++){
										switch(*p){
											case '0': .. case '9':
												exp = (exp << 1) + (exp << 3) + *p -'0';
												break;
											case '_': // ignore embedded _.
												break;
											default:
												break readhexp;
										}
										if(exp > helim){p++;break readhexp;}
									}
									goto default;
								default:
									break consumehex;	
							}
						}
						isfloat |= *p == 'f' || *p == 'F';
						if(isfloat){ // compute value of hex floating point literal
							if(dot==-1) dot = dig;
							if(neg) exp += dig - dot - adjexp << 2L;
							else    exp -= dig - dot - adjexp << 2L;
							if(exp<0) neg = !neg, exp=-exp;
							if('0' <= *p && *p <= '9' || exp>=8184 || !val){
								p++, rval = neg || !val ? .0L : real.infinity;
								while('0' <= *p && *p <= '9') p++;
							}else{ // TODO: Could construct value directly in memory
								rval = 1.0L;
								for(int i=0,j=cast(int)(exp&-1u);i<16;i++,j>>=1) if(j&1) rval*=pw2[i];
								if(neg) rval = val / rval;
								else rval *= val;
							}
						}
						if(adjexp) val = ulong.max; // for error handling
						break selectbase;
					case 'b', 'B':
						p++;
						base = BIN;
						readbin: for(;dig<64;p++){
							switch(*p){
								case '0', '1':
									val <<= 1; dig++;
									val |= *p-'0'; goto case;
								case '_': // ignore embedded _
									break;
								default:
									break readbin;
							}
						}
						break selectbase;
					/*case 'o': // non-standard
						base = OCT;*/
					default: // 0xxx-style octal is deprecated, interpret as decimal and give an error
						leadingzero = 1;
						break;
				}
				while(*p == '0') p++; // eat leading zeros of decimal
				if(('1' > *p || *p > '9') && *p != '.'){
					isfloat |= *p == 'f' || *p == 'F' || *p == 'i' || *p == 'L' && p[1]=='i';
					leadingzero=0; break;
				}
				goto case;
			case '1': .. case '9': case '.':
				readdec: for(;;p++){
					switch(*p){
						case '0': .. case '9':
							val = (val << 1) + (val << 3) + *p -'0'; dig++;
							break;
						case '.':
							if('0'<=p[1]&&p[1]<='9' && dot == -1) dot = dig, isfloat=1; // break; }
							else break readdec; goto case;
						case '_': // ignore embedded _
							break;
						default:
							break readdec;
					}
					if(val >= dlim){
						p++;
						if(val > dlim) break readdec;
						if('0' <= *p && *p <= '5') val = (val << 1) + (val << 3) + *p -'0', dig++, p++;
						break readdec;
					}
				}
				ulong val2=0, mulp=1;
				enum mlim = ulong.max/10000000;
				consumedec: for(;;p++){
					switch(*p){
						case '0': .. case '9':
							dig++; adjexp++; toobig=1;
							if(mulp<mlim) val2 = (val2 << 1) + (val2 << 3) + *p -'0', mulp*=10, adjexp--;
							break;
						case '.':
							switch(p[1]){
								case 'a': .. case 'z':
								case 'A': .. case 'Z':
								case '.', '_':
									break consumedec;
								default: break;
							}
							if(dot == -1) dot = dig, isfloat = 1; // break; }
							else break consumedec; goto case;
						case '_': // ignore embedded _
							break;
						case 'e', 'E':
							isfloat = 1;
							p++;
							neg = 0;
							switch(*p){
								case '-': neg = 1; goto case;
								case '+': p++;     goto default;
								default:  break; 
							}
							if('0'> *p || *p > '9') goto Lexp;
							readexp: for(;;p++){
								switch(*p){
									case '0': .. case '9':
										exp = (exp << 1) + (exp << 3) + *p -'0';
										break;
									case '_': // ignore embedded _.
										break;
									default:
										break readexp;
								}
								if(exp > elim){p++;break readexp;}
							}
						goto default;
						default:
							break consumedec;
					}
				}
				isfloat |= *p == 'f' || *p == 'F' || *p == 'i' || *p == 'L' && p[1] == 'i';
				if(isfloat){ // compute value of floating point literal (not perfectly accurate)
					if(dot==-1) dot = dig;
					if(neg) exp += cast(long) dig - dot - adjexp;
					else    exp -= cast(long) dig - dot - adjexp;
					if(exp<0) neg = !neg, exp=-exp;
					if('0' <= *p && *p <= '9' || exp>=32768 || !val){
						rval = neg || !val ? .0L : real.infinity;
						while('0' <= *p && *p <= '9') p++; // BUGS: Ignores 'overlong' input.
					}else{
						//Move some digits from val to val2 for more precise rounding behavior
						while(val>0x7fffffffffff) val2+=val%10*mulp, val/=10, mulp = (mulp<<1) + (mulp<<3);
						rval = cast(real)val*mulp+val2;
						if(neg){for(int i=0,j=1<<15;i<16;i++,j>>=1) if(exp&j) rval*=pn10[i];}
						else for(int i=0,j=1<<15;i<16;i++,j>>=1) if(exp&j) rval*=pw10[i];
					}
				}
				goto default;
			default:
				break;
		}
		if(isfloat){
			tok.flt80 = rval;
			if(*p == 'f' || *p == 'F') p++, tok.type = Tok!".0f";
			else if(*p == 'L') p++, tok.type = Tok!".0L";
			else tok.type = Tok!".0"; // TODO: Complain if not representable
			if(*p == 'i') p++, tok.type += 3; static assert(Tok!".0f"+3==Tok!".0fi" && Tok!".0"+3==Tok!".0i" && Tok!".0L"+3==Tok!".0Li");
			return _p = p, tok;
		}
		{
		// parse suffixes:
		bool sfxl = 0, sfxu = 0;
		switch(*p){
			case 'L':
				sfxl = 1;
				p++;
				if(*p == 'u' || *p == 'U') sfxu = 1, p++;
				break;
			case 'u', 'U':
				sfxu = 1;
				p++;
				if(*p=='L') sfxl = 1, p++;
				break;
			default:
				break;
		}
		tok.int64 = val;
		// determining literal type according to TDPL p32
		switch(sfxl << 1 | sfxu){
			case 0:
				if(val <= int.max) tok.type = Tok!"0";
				else               tok.type = Tok!"0L";
				break;
			case 1:         
				if(val <= uint.max) tok.type = Tok!"0U";
				else                tok.type = Tok!"0LU";
				break;
			case 2:
				tok.type = Tok!"0L";
				break;
			default:
				tok.type = Tok!"0LU";
		}
		if(tok.type == Tok!"0L"){
			if(toobig) Lerr: tok = tokError("signed integer constant exceeds long.max",_p[0..p-_p]);
			else if(val > long.max){
				if(base == HEX) tok.type = Tok!"0LU";
				else goto Lerr;
			}
		}
		if(tok.type == Tok!"0LU" && adjexp) tok = tokError("integer constant exceeds ulong.max",_p[0..p-_p]);
		if(leadingzero && val > 7) tok = tokError("octal literals are deprecated",_p[0..p-_p]);
		return _p=p, tok;
		}
		Lexp: return _p=p, tokError("exponent expected",p[0..1]);
	}
}

// Exception thrown on unrecognized escape sequences
private class EscapeSeqException: Exception{string loc; this(string msg,string loc){this.loc=loc;super(msg);}}

/* Reads an escape sequence and increases the given pointer to point past the sequence
	returns a dchar representing the read escape sequence or
	throws EscapeSeqException if the input is not well formed
 */
private dchar readEscapeSeq(ref immutable(char)* _p) in{assert(*(_p-1)=='\\');}body{ // pure
	auto p=_p;
	switch(*p){
		case '\'','\?','"','\\':
		return _p=p+1, *p;
		case 'a': return _p=p+1, '\a';
		case 'b': return _p=p+1, '\b';
		case 'f': return _p=p+1, '\f';
		case 'n': return _p=p+1, '\n';
		case 'r': return _p=p+1, '\r';
		case 't': return _p=p+1, '\t';
		case 'v': return _p=p+1, '\v';
		case '0': .. case '7': // BUG: Actually works for all extended ASCII characters
			auto s=p;
			for(int r=*p++-'0', i=0;;i++, r=(r<<3)+*p++-'0')
				if(i>2||'0'>*p||*p>'7'){
					_p=p; if(r>255) throw new EscapeSeqException(format("escape sequence '\\%s' exceeds ubyte.max",s[0..p-s]),(s-1)[0..p-s+1]);
					return cast(dchar)r;
				}
		case 'x', 'u', 'U':
			auto s=p;
			int numh=*p=='x'?p++,2:*p++=='u'?4:8;
			int r;
			foreach(i,x;p[0..numh]){
				switch(x){
					case '0': .. case '9': r=r<<4 | x-'0'; break;
					case 'a': .. case 'f': r=r<<4 | x-('a'-0xa); break;
					case 'A': .. case 'F': r=r<<4 | x-('A'-0xA); break;
					default:
						_p=p;
						throw new EscapeSeqException(format("escape hex sequence has %s digit%s instead of %s",
						                                    toEngNum(cast(uint)i),(i!=1?"s":""),toEngNum(numh)),(_p-1)[0..p-_p+1]);
				}
				p++;
			}
			_p=p;
			if(!utf.isValidDchar(cast(dchar)r)) throw new EscapeSeqException(format("invalid UTF character '\\%s'",s[0..p-s]),(s-1)[0..p-s+1]);
			return cast(dchar)r;
		case '&':
			auto s=++p;
			while('A'<=*p && *p <='Z' || 'a'<=*p && *p <='z') p++;
			if(*p!=';') throw new EscapeSeqException("unterminated named character entity",p[0..1]);
			_p=p+1;
			switch(s[0..p-s]){
				mixin({
					string r;
					struct E{string k; uint v;}
					E[] entities=mixin(import("namedcharentities")); // no AAs in CTFE =@
					foreach(x;entities) r~=`case "`~x.k~`": return cast(dchar)`~to!string(x.v)~`;`;
					return r;
				}());
				default: throw new EscapeSeqException(format("unrecognized named character entity '\\&%s'",s[0..p-s+1]),(s-1)[0..p-s+2]);
			}
		default:
			if(*p<128){_p=p+1; throw new EscapeSeqException(format("unrecognized escape sequence '\\%s'",*p),p[0..1]);}
			else{
				auto s=p;
				size_t len=0;
				try{
					utf.decode(p[0..4],len);
					p+=len;
				}catch{throw new EscapeSeqException(null,p[0..1]);}
				_p=p; throw new EscapeSeqException(format("unrecognized escape sequence '\\%s'",s[0..len]),s[0..len]);
			}
	}
}


unittest{
	alias token t;
	assert(lex(".\r..\v...\t  ....\r\n") == [t!".", t!"\n", t!"..", t!"...", t!"...", t!".",t!"\n"]);
	assert(to!string(lex(ulong.max.stringof)[0]) == ulong.max.stringof);
	assert(lex(ulong.max.stringof[0..$-2])[0].type == Tok!"Error");
	foreach(i;0..1000UL){
		ulong v = i^^4*1337;
		ulong w = lex(to!string(v))[0].int64;
		assert(w == v);
	}
	// 184467440737095516153.6L is rounded to 184467440737095516160.0L
	assert(lex("184467440737095516153.6L")[0].flt80 == 184467440737095516153.6L);//184467440737095516160.0L);
	assert(lex("0x1234_5678_9ABC_5A5AL")[0].int64 == 0x1234_5678_9ABC_5A5AL);
}

private string isKw(string[] cases){
	string r="switch(s){";
	foreach(x;cases) r~=`case "`~x~`": return Tok!"`~x~`";`;
	return r~="default: break;}";
}
TokenType isKeyword(string s){
	switch(s.length){
		case 2: //["do", "if", "in", "is"];
			if(s[0]=='i'){
				if(s[1]=='f') return Tok!"if";
				if(s[1]=='s') return Tok!"is";
				if(s[1]=='n') return Tok!"in";
			}else if(s[0]=='d' && s[1]=='o') return Tok!"do";
			break;
		case 3://["asm", "for", "int", "new", "out", "ref", "try"]
			switch(s[0]){
				case 'i': if(s[1]=='n' && s[2]=='t') return Tok!"int"; break;
				case 'f': if(s[1]=='o' && s[2]=='r') return Tok!"for"; break;
				case 'n': if(s[1]=='e' && s[2]=='w') return Tok!"new"; break;
				case 'r': if(s[1]=='e' && s[2]=='f') return Tok!"ref"; break;
				case 'o': if(s[1]=='u' && s[2]=='t') return Tok!"out"; break;
				case 't': if(s[1]=='r' && s[2]=='y') return Tok!"try"; break;
				case 'a': if(s[1]=='s' && s[2]=='m') return Tok!"asm"; break;
				default: break;
			}
			break;
		case 4: //["auto", "body", "bool", "byte", "case", "cast", "cent", "char", "else", "enum", "goto", "lazy", "long", "null", "pure", "real", "this", "true", "uint", "void", "with"]
			switch(s[0]){
				case 'a': if(s[1]=='u' && s[2]=='t' && s[3]=='o') return Tok!"auto"; break;
				case 'b': if(s[1]=='y' && s[2]=='t' && s[3]=='e') return Tok!"byte";
					if(s[1]=='o'){
						if(s[2]=='o' && s[3]=='l') return Tok!"bool";
						if(s[2]=='d' && s[3]=='y') return Tok!"body";
					}
					break;
				case 'c':
					if(s[1]=='a' && s[2]=='s'){
						if(s[3]=='e') return Tok!"case";
						if(s[3]=='t') return Tok!"cast";
					}
					if(s[1]=='e' && s[2]=='n' && s[3]=='t') return Tok!"cent";
					if(s[1]=='h' && s[2]=='a' && s[3]=='r') return Tok!"char";
					break;
				case 'e':
					if(s[1]=='l' && s[2]=='s' && s[3]=='e') return Tok!"else";
					if(s[1]=='n' && s[2]=='u' && s[3]=='m') return Tok!"enum";
					break;
				case 'g': if(s[1]=='o' && s[2]=='t' && s[3]=='o') return Tok!"goto"; break;
				case 'l':
					if(s[1]=='o' && s[2]=='n' && s[3]=='g') return Tok!"long";
					if(s[1]=='a' && s[2]=='z' && s[3]=='y') return Tok!"lazy";
				case 'n': if(s[1]=='u' && s[2]=='l' && s[3]=='l') return Tok!"null"; break;
				case 'p': if(s[1]=='u' && s[2]=='r' && s[3]=='e') return Tok!"pure"; break;
				case 'r': if(s[1]=='e' && s[2]=='a' && s[3]=='l') return Tok!"real"; break;
				case 't':
					if(s[1]=='h' && s[2]=='i' && s[3]=='s') return Tok!"this";
					if(s[1]=='r' && s[2]=='u' && s[3]=='e') return Tok!"true";
					break;
				case 'u': if(s[1]=='i' && s[2]=='n' && s[3]=='t') return Tok!"uint"; break;
				case 'v': if(s[1]=='o' && s[2]=='i' && s[3]=='d') return Tok!"void"; break;
				case 'w': if(s[1]=='i' && s[2]=='t' && s[3]=='h') return Tok!"with"; break;
				default: break;
			}
		case 5: mixin(isKw(["alias", "align", "break", "catch", "class", "const", "creal", "dchar", "debug", "false", "final", "float", "inout", "ireal", "macro", "mixin", "scope", "short", "super", "throw", "ubyte", "ucent", "ulong", "union", "wchar", "while"])); break;
		case 6: mixin(isKw(["assert", "cfloat", "delete", "double", "export", "extern", "ifloat", "import", "module", "pragma", "public", "return", "shared", "static", "struct", "switch", "typeid", "typeof", "ushort"])); break;
		case 7: mixin(isKw(["cdouble", "default", "finally", "foreach", "idouble", "nothrow", "package", "private", "typedef", "version"])); break;
		case 8: mixin(isKw(["abstract", "continue", "delegate", "function", "override", "template", "unittest", "volatile", "__thread", "__traits"])); break;
		case 9: mixin(isKw(["immutable", "interface", "invariant", "protected", "__gshared"])); break;
		case 10: if(s=="deprecated") return Tok!"deprecated"; break;
		case 12: if(s=="synchronized") return Tok!"synchronized"; break;
		case 15: if(s=="foreach_reverse") return Tok!"foreach_reverse"; break;
		default: break;
	}
	return Tok!"i";
}









