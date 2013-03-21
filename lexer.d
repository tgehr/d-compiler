module lexer;
import std.string, utf = std.utf, std.uni;
import std.stdio, std.conv;
import std.algorithm : startsWith;
import std.traits : EnumMembers;

import util;

// enum TokenType;
mixin("enum TokenType{"~TokenNames()~"}");

template Tok(string type){mixin(TokImpl());}
template TokChars(TokenType type){mixin(TokCharsImpl());}


private immutable{
string[2][] complexTokens =
	[["i",     "Identifier"                ],
	 ["``",    "StringLiteral"             ],
	 ["``c",   "StringLiteralC"            ],
	 ["``w",   "StringLiteralW"            ],
	 ["``d",   "StringLiteralD"            ],
	 ["''",    "CharacterLiteral"          ],
	 ["0",     "Integer32Literal"          ],
	 ["0U",    "Unsigned32Literal"         ],
	 ["0L",    "Integer64Literal"          ],
	 ["0LU",   "Unsigned64Literal"         ],
	 [".0f",   "FloatLiteral"              ],
	 [".0",    "DoubleLiteral"             ],
	 [".0L",   "RealLiteral"               ],
	 [".0fi",  "ImaginaryFloatLiteral"     ],
	 [".0i",   "ImaginaryDoubleLiteral"    ],
	 [".0Li",  "ImaginaryLiteral"          ]];
 // TODO: imaginary literals
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
	 [">>>=",  "ArithmeticRightShiftAssign"],
	 [">>",    "RightShift"                ],
	 [">>>",   "ArithmeticRightShift"      ],
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
	 ["\n",    "NewLine",                  ],
	 ["Error", "Error"                     ],
	 ["__error","ErrorLiteral"             ],
	 ["EOF",   "Eof"                       ]];
string[2][] compoundTokens =
	[["auto ref", "AutoRef"                ],
	 ["!is"     , "NotIs"                  ],
	 ["!in"     , "NotIn"                  ]];

string[] keywords = ["abstract", "alias", "align", "asm", "assert", "auto", "body", "bool", "break", "byte", "case", "cast", "catch", "cdouble", "cent", "cfloat", "char", "class", "const", "continue", "creal", "dchar", "debug", "default", "delegate", "delete", "deprecated", "do", "double", "else", "enum", "export", "extern", "false", "final", "finally", "float", "for", "foreach", "foreach_reverse", "function", "goto", "idouble", "if", "ifloat", "immutable", "import", "in", "inout", "int", "interface", "invariant", "ireal", "is", "lazy", "long", "macro", "mixin", "module", "new", "nothrow", "null", "out", "override", "package", "pragma", "private", "protected", "public", "pure", "real", "ref", "return", "scope", "shared", "short", "static", "struct", "super", "switch", "synchronized", "template", "this", "throw", "true", "try", "typedef", "typeid", "typeof", "ubyte", "ucent", "uint", "ulong", "union", "unittest", "ushort", "version", "void", "volatile", "wchar", "while", "with", /*"__FILE__", "__LINE__",*/ "__gshared", "__thread", "__traits"];

// TODO: Minimize (does not work if enum is left away, or keywordTokens is not a template)
enum string[2][] tokens = specialTokens ~ complexTokens ~ simpleTokens ~ compoundTokens ~ keywordTokens!();
}
private{
template keywordTokens(){
	enum keywordTokens={
		string[2][] r;
		foreach(i,kw;keywords) r~=[kw,kw~"_"];
		return r;
	}();
}

string lowerf(string s){
	if('A'<=s[0]&&s[0]<='Z') return cast(char)(s[0]+('a'-'A'))~s[1..$];
	return s;
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

struct Location{
	string mod;
	uint line;
	
	void error(string msg){
		stderr.writeln(mod, "(", line, "): error: ", msg);
	}
}

string toString(immutable(Token)[] a){string r;foreach(t;a) r~='['~t.toString()~']'; return r;}
string escape(string i,bool isc=false){ // TODO: replace with std lib one as soon as available
	string r;
	foreach(dchar x;i){
		switch(x){
			case '"': if(isc) goto default; r~="\\\""; break;
			case '\'': if(!isc) goto default; r~="\\'"; break;
			case '\\': r~="\\\\"; break;
			case '\a': r~="\\a"; break;
			case '\b': r~="\\b"; break;
			case '\f': r~="\\f"; break;
			case '\n': r~="\\n"; break;
			case '\r': r~="\\r"; break;
			case '\t': r~="\\t"; break;
			case '\v': r~="\\v"; break;
			case '\0': r~="\\0"; break;
			default:
				if(isWhite(x)) r~=format("\\u%4.4X",cast(uint)x); // wtf? 
				else r~=x; break;
		}
	}
	return r;
}
struct Token{
	TokenType type;
	string toString() const{
		switch(type) {
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
			case Tok!"''":
				return '\''~escape(to!string(cast(dchar)int64),false)~'\'';
			case Tok!"0":
				return to!string(int64);
			case Tok!"0U":
				return to!string(int64)~'U';
			case Tok!"0L":
				return to!string(int64)~'L';
			case Tok!"0LU":
				return to!string(int64)~"LU";
			case Tok!".0":
				return to!string(flt80);
			case Tok!".0f":
				return to!string(flt80)~'f';
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
				return tokens[cast(int)type][0];
		}
	}
	union{
		string str, name;  // string literals, identifiers
		ulong int64;       // integer literals
		real flt80;        // float, double, real literals
	}
}
template token(string t){enum token=Token(Tok!t);}

Token tokError(string s) pure{
	auto r = token!"Error";
	r.str = s;
	return r;
}

//TODO: Replace some switches by ifs
//TODO: Remove this restriction:
/+static assert({
	foreach(i;simpleTokens){
		string s=i[0];
		bool found = s.length==1;
		foreach(j;simpleTokens) if(j[0] == s[0..$-1]) found = true;
		if(!found) return false;
	}return true;
}(),"Every non-empty prefix of simpleTokens must be a valid token.");+/
string caseSimpleToken(string prefix="", bool needs = false){
	string r;
	int c=0,d=0;
	foreach(i;simpleTokens){string s=i[0]; if(s.startsWith(prefix)) c++;}
	if(c==1) r~=`tok = token!"`~prefix~'"'~";\nbreak;\n";
	else{
		if(needs) r~="switch(*p){\n";
		foreach(i;simpleTokens){
			string s = i[0]; if(s[0]=='/' || s[0] == '.') continue; // / can be the start of a comment, . could be the start of a float literal
			if(s.startsWith(prefix) && s.length==prefix.length+1){
				r~=`case '`~s[$-1]~"':\n"~(needs?"p++;\n":"");
				r~=caseSimpleToken(s,true);
			}
		}
		if(needs) r~=`default: tok = token!"`~prefix~`"`~";\nbreak;\n}\nbreak;\n";
	}
	return r;
}

immutable(Token)[] lex(string code)in{assert(!code[$-4]&&!code[$-3]&&!code[$-2]&&!code[$-1]);}body{ // four padding zero bytes required because of UTF
	if(code.length > int.max) return [tokError("no support for sources exceeding 2GB")];
	if(!code.length) return [];
	//if(code[$-1]!='\0') code ~= '\0'; //make sure we have an EOF token
	//auto lexed = appender!(immutable(Token)[])();
	auto lexed = mallocAppender!(immutable(Token)[])();
	auto p=code.ptr;
	auto s=p;
	Token tok;
	ulong value;
	char del;
	size_t len;
	typeof(p) invCharSeq_l=null;
	void invCharSeq(){if(p>invCharSeq_l+1) invCharSeq_l=p, lexed.put(tokError("invalid character sequence")); p++;}
	int nl = 0; // count number of newlines to be able to give the unterminated string Error in the approp. place
	// text macros:
	enum skipUnicode = q{if(*p<0x80){p++;break;} len=0; try utf.decode(p[0..4],len), p+=len; catch{invCharSeq();}};
	enum skipUnicodeCont = q{if(*p<0x80){p++;continue;} len=0; try utf.decode(p[0..4],len), p+=len; catch{invCharSeq();}}; // don't break, continue
	enum caseNl = q{case '\r':  if(p[1]=='\n') p++; goto case; case '\n': p++; lexed.put(token!"\n"); continue;};
	enum caseNl2 = q{case '\r': if(p[1]=='\n') p++; goto case; case '\n': p++; nl++; continue;}; // just count newlines
	loop: for(;;) { // breaks on EOF
		switch(*p++){
			// whitespace
			case 0, 0x1A:
				tok = token!"EOF";
				break loop;
			case ' ', '\t', '\v':
				continue;   // ignore whitespace
			case '\r': if(*p=='\n') p++; goto case;
			case '\n':
				tok=token!"\n"; // needed for line information in the parser
				break;
			
			// simple tokens
			mixin(caseSimpleToken());
			
			// slash is special
			case '/':
				switch(*p){
					case '=': tok = token!"/="; p++;
					break;
					case '/': p++;
						while(((*p!='\n') & (*p!='\r')) & ((*p!=0) & (*p!=0x1A))) mixin(skipUnicodeCont);
						continue; // ignore comment
					case '*':
						p++;
						consumecom2: for(;;){
							switch(*p){
								mixin(caseNl); // handle newlines
								case '*': p++; if(*p=='/'){p++; break consumecom2;} break;
								case 0, 0x1A: break consumecom2; //TODO: Error
								default: mixin(skipUnicode);
							}
						}
						continue; // ignore comment
					case '+':
						int d=1; p++;
						consumecom3: while(d){
							switch(*p){
								mixin(caseNl); // handle newlines
								case '+':  p++; if(*p=='/') d--, p++; break;
								case '/':  p++; if(*p=='+') d++, p++; break;
								case 0, 0x1A: break consumecom3; //TODO: ERROR
								default: mixin(skipUnicode);
							}
						}
						continue; // ignore comment
					default: tok = token!"/";
				}
				break;
			// dot is special
			case '.':
				if('0' > *p || *p > '9'){
					if(*p != '.')      tok = token!".";
					else if(*++p!='.') tok = token!"..";
					else               tok = token!"...", p++;
					break;
				}
				p++; goto case;
			// numeric literals
			case '0': .. case '9':
				tok = lexNumber(--p);
				if(tok.type == Tok!"Error") lexed.put(tok), tok=token!"__error";
				break;
			// character literals
			case '\'':
				tok.type = Tok!"''";
				if(*p=='\\'){
					try p++, tok.int64 = cast(ulong)readEscapeSeq(p);
					catch(EscapeSeqException e) e.msg?lexed.put(tokError(e.msg)):invCharSeq();
				}else{
					try{
						len=0;
						tok.int64 = utf.decode(p[0..4],len);
						p+=len;
					}catch{invCharSeq();}
				}
				if(*p!='\''){
					//while((*p!='\''||(p++,0)) && *p && *p!=0x1A) mixin(skipUnicodeCont);
					lexed.put(tokError("unterminated character constant"));
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
				nl = 0;
				s = p;
				readwysiwyg: for(;;){
					if(*p==del){p++; break;} 
					switch(*p){
						mixin(caseNl2); // handle newlines
						case 0, 0x1A:
							lexed.put(tokError("unterminated string literal"));
							break readwysiwyg;
						default: mixin(skipUnicode);
					}
				}
				tok.type = Tok!"``";
				tok.str = s[0..p-s-1]; // reference to code
				goto lexstringsuffix;
			// token string
			case 'q':
				if(*p=='"') goto delimitedstring;
				if(*p!='{') goto case 'Q';
				nl = 0;
				p++; s = p;
				readtstring: for(int nest=1;;){
					switch(*p){
						mixin(caseNl2);
						case 0, 0x1A:
							lexed.put(tokError("unterminated string literal"));
							break readtstring;
						case '{': p++; nest++; break;
						case '}': p++; nest--; if(!nest) break readtstring; break;
						default: mixin(skipUnicode);
					}
				}
				tok.type = Tok!"``";
				tok.str = s[0..p-s-1]; // reference to code
				goto lexstringsuffix;
				delimitedstring:
				tok.type = Tok!"``";
				nl=0;
				s=++p;
				switch(*p){
					case 'a': .. case 'z':
					case 'A': .. case 'Z':
						for(;;){
							switch(*p){
								case '\r': if(p[1]=='\n') p++; goto case;
								case '\n': nl++; break;
								case 0, 0x1A: break;
								case 'a': .. case 'z':
								case 'A': .. case 'Z':
								case '0': .. case '9':
									p++;
									continue;
								case 0x80: .. case 0xFF:
									len=0;
									try{auto ch=utf.decode(p[0..4],len);
										if(isUniAlpha(ch)){p+=len; continue;}
										break;
									}catch{invCharSeq(); break;}
								default: break;
							}
							break;
						}
						if(*p!='\n' && *p!='\r') lexed.put(tokError("heredoc identifier must be followed by a new line"));
						while(((*p!='\n') & (*p!='\r')) & ((*p!=0) & (*p!=0x1A))) mixin(skipUnicodeCont); // mere error handling
						auto ident=s[0..p-s];
						if(*p=='\r'){nl++; if(*++p=='\n') p++;}
						else if(*p=='\n') nl++, p++;
						s=p;
						readheredoc: while((*p!=0) & (*p!=0x1A)){ // always at start of new line here
							for(auto ip=ident.ptr, end=ident.ptr+ident.length;;){
								if(ip==end) break readheredoc;
								switch(*p){
									mixin(caseNl2);
									case 0x80: .. case 0xFF:
										len=0;
										try{auto ch=utf.decode(p[0..4],len);
											if(isUniAlpha(ch)){
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
							if(*p=='\r'){nl++; if(*++p=='\n') p++;}
							else if(*p=='\n') nl++, p++;
						}
						tok.str = p>s+ident.length?s[0..p-s-ident.length]:""; // reference to code
						if(*p!='"'){lexed.put(tokError("unterminated heredoc string literal")); break;}
						else p++;
						break;
					default:
						del=*p; char rdel=del; dchar ddel=0;
						switch(del){
							case '[': rdel=']'; s=++p; break;
							case '(': rdel=')'; s=++p; break;
							case '<': rdel='>'; s=++p; break;
							case '{': rdel='}'; s=++p; break;
							case ' ','\t','\v','\r','\n':
								lexed.put(tokError("string delimiter cannot be whitespace"));
							case 0x80: case 0xFF:
								s=p;
								len=0;
								try{
									ddel=utf.decode(p[0..4],len);
									s=p+=len;
								}catch{invCharSeq();}
							default: break;
						}
						if(ddel){
							while((*p!=0) & (*p!=0x1A)){
								if(*p=='\r'){nl++; if(*++p=='\n') p++;}
								else if(*p=='\n') nl++, p++;
								else if(*p<0x80){p++; continue;}
								try{
									auto x=utf.decode(p[0..4],len);
									if(ddel==x){
										tok.str = s[0..p-s]; // reference to code
										p+=len; break;
									}
									p+=len;
								}catch{invCharSeq();}								
							}
						}else{
							for(int nest=1;(nest!=0) & (*p!=0) & (*p!=0x1A);p++){
								if(*p=='\r'){nl++; if(*++p=='\n') p++;}
								else if(*p=='\n') nl++, p++;
								else if(*p==rdel) nest--;
								else if(*p==del) nest++;
								else if(*p & 0x80){
									try{
										utf.decode(p[0..4],len);
										p+=len-1;
									}catch{invCharSeq();}
								}
							}
							tok.str = s[0..p-s-1]; // reference to code
						}
						if(*p!='"') lexed.put(tokError("expected '\"' to close delimited string literal"));
						else p++;
						break;
				}
				goto lexstringsuffix;
			// Hex string
			case 'x':
				if(*p!='"') goto case 'X';
				nl=0;
				auto r=mallocAppender!string(); p++;
				readhexstring: for(int c=0,ch,d;;p++,c++){
					switch(*p){ // TODO: display correct error locations
						mixin(caseNl2); // handle newlines
						case 0, 0x1A:
							lexed.put(tokError("unterminated hex string literal"));
							break readhexstring;
						case '0': .. case '9': d=*p-'0'; goto handlexchar;
						case 'a': .. case 'f': d=*p-('a'-0xa); goto handlexchar;
						case 'A': .. case 'F': d=*p-('A'-0xA); goto handlexchar;
						handlexchar:
							if(c&1) r.put(ch|d);
							else ch=d<<4; break;
						case '"': // TODO: improve error message
							if(c&1) lexed.put(tokError(format("found %s character%s when expecting an even number of hex digits",toEngNum(c),c!=1?"s":"")));
							p++; break readhexstring;
						default:
							if(*p<128) lexed.put(tokError(format("found '%s' when expecting hex digit",*p)));
							else{
								s=p;
								len=0;
								try{
									utf.decode(p[0..4],len);
									p+=len-1;
								}catch{invCharSeq();}
								lexed.put(tokError(format("found '%s' when expecting hex digit",s[0..len])));
							}
							break;
					}
				}
				tok.type = Tok!"``";
				tok.str = r.data;
				goto lexstringsuffix;
			// DQString
			case '"':
				auto r=mallocAppender!string();
				nl=0;
				auto start = p;
				readdqstring: for(;;){
					s = p;
					switch(*p){
						case '\r': if(p[1]=='\n') p++; goto case;  // handle newlines
						case '\n': p++; nl++; break;
						case 0, 0x1A:
							lexed.put(tokError("unterminated string literal"));
							break readdqstring;
						case '\\':
							p++;
							try r.put(readEscapeSeq(p));
							catch(EscapeSeqException e) e.msg?lexed.put(tokError(e.msg)):invCharSeq(); // TODO: always error out at the correct location
							continue;
						case '"': p++; break readdqstring;
						default: mixin(skipUnicode);
					}
					r.put(s[0..p-s]);
				}
				tok.type = Tok!"``";
				tok.str = r.data;
				goto lexstringsuffix;
				lexstringsuffix:
				if(*p=='c')      tok.type = Tok!"``c", p++;
				else if(*p=='w') tok.type = Tok!"``w", p++;
				else if(*p=='d') tok.type = Tok!"``d", p++;
				lexed.put(tok);
				foreach(i;0..nl) lexed.put(token!"\n");
				continue;
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
							try if(isUniUpper(utf.decode(p[0..4],len))) p+=len;
							    else break readident;
							catch{break readident;} // will be caught in the next iteration
							break;
						default: break readident;
					}
				}
				tok.type = Tok!"i";
				tok.name = s[0..p-s];
				switch(tok.name){
					// TODO: If this is removed, dmd builds an executable, else an object file. reduce.
					mixin({string r; foreach(kw;keywords) r~="case \""~kw~"\": tok.type=Tok!\""~kw~"\"; break;\n";return r;}());
					default: break;
				}
				break;
			case 0x80: .. case 0xFF:
				len=0; p--;
				try{auto ch=utf.decode(p[0..4],len);
					s=p, p+=len;
					if(isUniAlpha(ch)) goto identifier;
					lexed.put(tokError(format("unsupported character '%s'",ch)));
					continue;
				}catch{} goto default; // moved outside handler to make -w shut up
			default:
				invCharSeq();
				continue;
		}
		lexed.put(tok);
	}
	lexed.put(tok); // for EOF
	return lexed.data;
}
/* Lex a number FSM. TDPL p33/35
	Returns either a valid literal token or one of the following:
	errExp       = tokError("exponent expected");
	errsOverflow = tokError("signed integer constant exceeds long.max");
	errOverflow  = tokError("integer constant exceeds ulong.max");
	//errRepr      = tokError("numerical constant is not representable in [float|double|real]");
	errOctDepr   = tokError("octal literals are deprecated");
 */
private Token lexNumber(ref immutable(char)* _p) {
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
							for(int i=0,j=exp&-1u;i<16;i++,j>>=1) if(j&1) rval*=pw2[i];
							if(neg) rval = val / rval;
							else rval *= val;
						}
					}
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
				isfloat |= *p == 'f' || *p == 'F' || (*p=='i'||*p=='L'&&p[1]=='i');
				leadingzero=0; break;
			}
			goto case;
		case '1': .. case '9':
			readdec: for(;;p++){
				switch(*p){
					case '0': .. case '9':
						val = (val << 1) + (val << 3) + *p -'0'; dig++;
						break;
					case '.':
						if(p[1] != '.' && dot == -1) dot = dig, isfloat=1; // break; }
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
						if(p[1] != '.' && dot == -1) dot = dig, isfloat = 1; // break; }
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
			isfloat |= *p == 'f' || *p == 'F' || *p == 'i';
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
		if(toobig || val > long.max && base!=HEX) tok = tokError("signed integer constant exceeds long.max");
		else if(val > long.max && base == HEX) tok.type = Tok!"0LU"; // EXTENSION: Just here to match what DMD does
	}else if(tok.type == Tok!"0LU" && adjexp) tok = tokError("integer constant exceeds ulong.max");
	if(leadingzero && val > 7) tok = tokError("octal literals are deprecated");
	return _p=p, tok;
	Lexp: return _p=p, tokError("exponent expected");
}

// Exception thrown on unrecognized escape sequences
class EscapeSeqException: Exception{this(string msg){super(msg);}}

/* Reads an escape sequence and increases the given pointer to point past the sequence
	returns a dchar representing the read escape sequence or
	throws EscapeSeqException if the input is not well formed
 */
private dchar readEscapeSeq(ref immutable(char)* _p) {
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
		case '0': .. case '7': // ENHANCEMENT: Actually works for all ASCII characters
			auto s=p;
			for(int r=*p++-'0', i=0;;i++, r=(r<<3)+*p++-'0')
				if(i>2||'0'>*p||*p>'7'){
					_p=p; if(r>255) throw new EscapeSeqException("escape sequence '\\"~s[0..p-s]~"' exceeds ubyte.max");
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
						                                    toEngNum(cast(uint)i),(i!=1?"s":""),toEngNum(numh)));
				}
				p++;
			}
			_p=p;
			if(!utf.isValidDchar(cast(dchar)r)) throw new EscapeSeqException(format("invalid UTF character '\\%s'",s[0..p-s]));
			return cast(dchar)r;
		case '&':
			auto s=++p;
			while('A'<=*p && *p <='Z' || 'a'<=*p && *p <='z') p++;
			if(*p!=';') throw new EscapeSeqException("unterminated named character entity");
			_p=p+1;
			switch(s[0..p-s]){
				mixin({
					string r;
					struct E{string k; uint v;}
					E[] entities=mixin(import("namedcharentities")); // no AAs in CTFE =@
					foreach(x;entities) r~=`case "`~x.k~`": return cast(dchar)`~to!string(x.v)~`;`;
					return r;
				}());
				default: throw new EscapeSeqException(format("unrecognized named character entity '\\&%s;'",s[0..p-s]));
			}
		default:
			if(*p<128){_p=p+1; throw new EscapeSeqException(format("unrecognized escape sequence '\\%s'",*p));}
			else{
				auto s=p;
				size_t len=0;
				try{
					utf.decode(p[0..4],len);
					p+=len;
				}catch{throw new EscapeSeqException(null);}
				_p=p; throw new EscapeSeqException(format("unrecognized escape sequence '\\%s'",s[0..len]));
			}
	}
}

string readDelimitedString(ref immutable(char)* _p, ref MallocAppender!string lexed)in{assert(*_p=='"');}body{
	auto p=_p+1;

	return "";
}




unittest{
	alias token t;
	assert(lex(".\r..\v...\t  ....\r\n") == [t!".", t!"\n", t!"..", t!"...", t!"...", t!".",t!"\n"]);
	assert(to!string(lex(ulong.max.stringof)[0]) == ulong.max.stringof);
	assert(lex(ulong.max.stringof[0..$-2])[0].type == Tok!"Error");
	for(ulong i=0;i<1000;i++){
		ulong v = i^^4*1337;
		ulong w = lex(to!string(v))[0].int64;
		assert(w == v);
	}
	// 184467440737095516153.6L is rounded to 184467440737095516160.0L
	assert(lex("184467440737095516153.6L")[0].flt80 == 184467440737095516153.6L);//184467440737095516160.0L);
	assert(lex("0x1234_5678_9ABC_5A5AL")[0].int64 == 0x1234_5678_9ABC_5A5AL);
}










