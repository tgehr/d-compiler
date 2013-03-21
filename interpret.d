// Written in the D programming language.

import lexer, expression, semantic, scope_, type;
import util;
import std.string;
import std.conv: to;

private template NotYetImplemented(T){
	static if(is(T _==BinaryExp!S,TokenType S) && !is(T==BinaryExp!(Tok!".")))
		enum NotYetImplemented = false;
	else static if(is(T _==UnaryExp!S,TokenType S))
		enum NotYetImplemented = false;
		else enum NotYetImplemented = !is(T==Expression) && !is(T:Type) && !is(T:Symbol) && !is(T:LiteralExp) && !is(T==CastExp) && !is(T==ArrayLiteralExp) && !is(T==IndexExp) && !is(T==SliceExp) && !is(T==TernaryExp) && !is(T==CallExp) && !is(T==MixinExp) && !is(T==IsExp) && !is(T==AssertExp);
}

enum IntFCEplg = q{needRetry = false; return this;};
template IntFCChld(string s){
	enum IntFCChld={
		string r;
		auto ss=s.split(",");
		foreach(t; ss){
			r~=mixin(X!q{
				@(t) = @(t)._interpretFunctionCalls(sc);
				mixin(PropRetry!q{@(t)});
			});
		}
		return r~PropErr!s~IntFCEplg;
	}();
}

// should never be interpreted:
mixin template Interpret(T) if(is(T==MixinExp) || is(T==IsExp)){
	override bool checkInterpret(Scope sc){assert(0);}
	override Expression interpret(Scope sc){assert(0);}
	protected override Expression _interpretFunctionCalls(Scope sc){assert(0);}
}
mixin template Interpret(T) if(is(T:Expression) && NotYetImplemented!T){
	override Expression interpret(Scope sc){
		assert(sc, "expression "~toString()~" was assumed to be interpretable");
		sc.error(format("expression '%s' is not interpretable at compile time yet",loc.rep),loc);
		mixin(ErrEplg);
	}
}

mixin template Interpret(T) if(is(T==Expression)){
	// scope may be null if it is evident that the expression can be interpreted
	bool checkInterpret(Scope sc)in{assert(sstate == SemState.completed);}body{
		assert(sc, loc.rep);
		sc.error(format("expression '%s' is not interpretable at compile time",loc.rep),loc);
		sstate = SemState.error;
		return false;
	}
	static int numint = 0;
	Expression interpret(Scope sc)in{assert(sstate == SemState.completed);	}body{
		//assert(!numint);
		if(!checkInterpret(sc)) mixin(ErrEplg);
		auto a=_interpretFunctionCalls(sc);
		mixin(PropRetry!q{a}); // this throws away all progress. TODO: can this be improved?
		if(a.sstate == SemState.error) return a;
		auto r = a.interpretV().toExpr();
		r.loc=a.loc;
		r.type=a.type;
		//pragma(msg, __traits(allMembers,ArrayLiteralExp)); // TODO: report bug
		if(auto al = a.isArrayLiteralExp()){ // TODO: override in subclass?
			auto rl = r.isArrayLiteralExp();
			assert(rl);
			copyLocations(rl,al);
		}

		assert(!isConstant() || !needRetry); // TODO: file bug, so that this can be 'out'
		return r; 
	}
	Variant interpretV()in{assert(sstate == SemState.completed);}body{
		//return Variant.error(format("expression '%s' is not interpretable at compile time"),loc.rep);
		return Variant("TODO: cannot interpret "~to!string(this)~" yet");
		//return Variant.init;
	}
protected:
	// for interpret.d internal use only, protection system cannot express this.
	Expression _interpretFunctionCalls(Scope sc){return this;}
}

// TODO: investigate the void[][] = [[[2]]]; case some more
void copyLocations(ArrayLiteralExp r, ArrayLiteralExp a){
	assert(r.lit.length == a.lit.length);
	foreach(i,x;a.lit){
		r.lit[i].loc = x.loc;
		if(auto rl = r.lit[i].isArrayLiteralExp()){
			if(auto al = x.isArrayLiteralExp()){
				copyLocations(rl, al);
			}
		}
	}
}

mixin template Interpret(T) if(is(T==CastExp)){
	override bool checkInterpret(Scope sc){return e.checkInterpret(sc);}
	override Variant interpretV(){
		auto le=e.isLiteralExp(); // polysemous string literals might be cast
		if(le&&le.isPolyString()){
			auto vle=e.interpretV();
			// TODO: factor this out into a final member function of Type?
			auto el = type.getElementType();
			assert(!!el, "cannot convert");
			auto typeu = type.getHeadUnqual();
			if(typeu is Type.get!string()
			|| typeu is Type.get!wstring()
			|| typeu is Type.get!dstring())
				return e.interpretV().convertTo(type);
			// TODO: allocation ok?
			Variant[] r = new Variant[vle.length];
			foreach(i,ref x;r) x = vle[i].convertTo(el);
			return Variant(r);
		}else return e.interpretV().convertTo(type);
	}
protected:
	override Expression _interpretFunctionCalls(Scope sc){mixin(IntFCChld!q{e});}
}
mixin template Interpret(T) if(is(T==Type)){
	override bool checkInterpret(Scope sc){return true;}
	override Expression interpret(Scope sc){return this;}
}mixin template Interpret(T) if(!is(T==Type) && is(T:Type)){}

mixin template Interpret(T) if(is(T==Symbol)){
	override bool checkInterpret(Scope sc){
		if(auto vd = meaning.isVarDecl()){
			if(vd.stc&STCenum
			|| vd.stc&STCimmutable && vd.init.isConstant())
				return true;
		}
		return super.checkInterpret(sc);
	}
	override Variant interpretV(){
		if(auto vd = meaning.isVarDecl()){
			assert(meaning.sstate == SemState.completed);
			/+if(vd.stc&STCenum|STCimmutable) +/
			return vd.init.interpretV();
		}
		assert(0);
	}
}mixin template Interpret(T) if(!is(T==Symbol) && is(T:Symbol)){}
mixin template Interpret(T) if(is(T==LiteralExp)){
	private template getTokOccupied(T){
		enum vocc = to!string(getOccupied!T);
		static if(vocc == "wstr") enum occ = "str";
		else static if(vocc == "dstr") enum occ = "str";
		else static if(vocc == "fli80") enum occ = "flt80";
		else enum occ = vocc;
		enum getTokOccupied = occ;
	}
	private Variant value;
	this(Token lit){ // TODO: suitable contract
		this.lit=lit;
		if(lit.type==Tok!"true") lit.int64=1;
		else if(lit.type==Tok!"false") lit.int64=0;
		swtch:switch(lit.type){
			foreach(x; ToTuple!literals){
				static if(x!="null"){
					alias typeof(mixin(x)) U;
					enum occ = getTokOccupied!U;
					static if(x=="``w"||x=="``d"){
						case Tok!x: value=Variant(to!U(mixin(`lit.`~occ))); break swtch;
					}else static if(x==".0fi"||x==".0i"||x==".0Li"){
						case Tok!x: value=Variant(cast(U)(mixin(`lit.`~occ)*1i)); break swtch;
					}else{
						case Tok!x: value=Variant(cast(U)mixin(`lit.`~occ)); break swtch;
					}
				}else{
					case Tok!x: value=Variant(null); break swtch;
				}
			}
			default: assert(0, to!string(lit.type));
		}
	}
	this(Variant value){ this.value = value; }

	static LiteralExp create(alias New=New,T)(T val){//workaround for long standing bug
		// TODO: get rid of most of this logic
		/+Token lit;

		static if(is(T==bool)){
			lit.type = val?Tok!"true":Tok!"false";
			lit.int64 = val;
		}else{
			// TODO: this sometimes allocates.
			foreach(x; ToTuple!literals){
				static if(is(typeof(mixin(x))==T)){
					lit.type = Tok!x;
					alias typeof(mixin(`lit.`~getTokOccupied!T)) U;
					static if(x=="``"w||x=="``"d)
						mixin(`lit.`~getTokOccupied!T) = to!U(val);
					else mixin(`lit.`~getTokOccupied!T) = cast(U)val;

				}
			}
			static if(is(T==dchar)||is(T==wchar)){
				lit.type = Tok!"' '";
				lit.int64 = val;
			}
		}+/
		//return New!LiteralExp(lit).semantic(null);
		return New!LiteralExp(Variant(val)).semantic(null);
		//lit.type = Tok!"``";
		//lit.str = str;
	}


	override bool checkInterpret(Scope sc){ return true; }
	override LiteralExp interpret(Scope sc){ return this; }
	override Variant interpretV(){ return value; }
}

mixin template Interpret(T) if(is(T==ArrayLiteralExp)){
	override bool checkInterpret(Scope sc){
		bool ok = true;
		foreach(x; lit) if(!x.checkInterpret(sc)) ok=false;
		return ok;
	}
	override Variant interpretV(){
		// TODO: this GC allocation is probably justified
		Variant[] res = new Variant[lit.length];
		foreach(i, ref x; res) x = lit[i].interpretV();
		return Variant(res);
	}
protected:
	override Expression _interpretFunctionCalls(Scope sc){
		foreach(ref x; lit){
			x = x._interpretFunctionCalls(sc);
			mixin(PropRetry!q{x});
		}
		mixin(PropErr!q{lit});
		mixin(IntFCEplg);
	}
}

mixin template Interpret(T) if(is(T==IndexExp)){
	override bool checkInterpret(Scope sc){
		if(!a.length) return e.checkInterpret(sc);
		assert(a.length==1);
		return e.checkInterpret(sc)&a[0].checkInterpret(sc);
	}
	override Variant interpretV(){
		if(a.length==0) return e.interpretV();
		assert(a.length==1);
		assert(e.isConstant());
		auto lit = e.interpretV();
		auto ind = a[0].interpretV();
		if(lit.isEmpty() || ind.isEmpty()) return Variant.init;
		return lit[ind];
	}
protected:
	override Expression _interpretFunctionCalls(Scope sc){
		e=e._interpretFunctionCalls(sc);
		mixin(PropRetry!q{e});
		mixin(PropErr!q{e});
		if(a.length>=1){
			assert(a.length==1);
			a[0] = a[0]._interpretFunctionCalls(sc);
			mixin(PropRetry!q{a[0]});
			mixin(PropErr!q{a[0]});
		}
		mixin(IntFCEplg);
	}
}

mixin template Interpret(T) if(is(T==SliceExp)){
	override bool checkInterpret(Scope sc){
		return e.checkInterpret(sc) & l.checkInterpret(sc) & r.checkInterpret(sc);
	}
	override Variant interpretV(){
		return e.interpretV()[l.interpretV()..r.interpretV()];
	}
protected:
	override Expression _interpretFunctionCalls(Scope sc){mixin(IntFCChld!q{e,l,r});}
}

mixin template Interpret(T) if(is(T==AssertExp)){
	override bool checkInterpret(Scope sc){
		return a[0].checkInterpret(sc) & (a.length<2 || a[1].checkInterpret(sc));
	}
	override Variant interpretV(){return Variant(toString());} // good enough
protected:
	override Expression _interpretFunctionCalls(Scope sc){
		a[0]=a[0]._interpretFunctionCalls(sc);
		mixin(PropRetry!q{a[0]});
		if(a.length>1){
			a[1]=a[1]._interpretFunctionCalls(sc);
			mixin(PropRetry!q{a[1]});
		}
		mixin(PropErr!q{a});
		auto cond = a[0].interpretV();
		if(!cond){
			if(a.length<2){
				sc.error(format("assertion failure: %s is false",a[0].loc.rep), loc);
			}else{
				auto expr = a[1];
				if(auto e = cast(CastExp)expr) expr = e.e;
				sc.error(expr.interpretV().get!string(), loc);
			}
			mixin(ErrEplg);
		}
		mixin(SemEplg);
	}
}

mixin template Interpret(T) if(is(T _==UnaryExp!S,TokenType S)){
	static if(is(T _==UnaryExp!S,TokenType S)):
	static if(S!=Tok!"&"&&S!=Tok!"*"): // TODO: implement where possible
	static if(S!=Tok!"++"&&S!=Tok!"--"):
	override bool checkInterpret(Scope sc){return e.checkInterpret(sc);}
	override Variant interpretV(){
		return e.interpretV().opUnary!(TokChars!S)();
	}
protected:
	override Expression _interpretFunctionCalls(Scope sc){mixin(IntFCChld!q{e});}
}


mixin template Interpret(T) if(is(T _==BinaryExp!S, TokenType S) && !is(T==BinaryExp!(Tok!"."))){
	static if(is(T _==BinaryExp!S, TokenType S)):
	static if(!isAssignOp(S)):
	override bool checkInterpret(Scope sc){
		return e1.checkInterpret(sc)&e2.checkInterpret(sc);
	}
	override Variant interpretV(){
		static if(S==Tok!","){
			return e2.interpretV();
		}else static if(isRelationalOp(S)&&S!=Tok!"is"&&S!=Tok!"in"||isArithmeticOp(S)||isBitwiseOp(S)||isShiftOp(S)||isLogicalOp(S))
			return e1.interpretV().opBinary!(TokChars!S)(e2.interpretV());
		else static if(S==Tok!"~"){
			if(e1.type.equals(e2.type)) return e1.interpretV().opBinary!"~"(e2.interpretV());
			// TODO: this might be optimized. this gc allocates
			// TODO: get rid of bulky string special casing code
			if(auto ety = e1.type.getElementType()){
				if(ety.equals(e2.type)){
					Variant rhs = e2.interpretV();
					if(ety is Type.get!(immutable(char))())
						rhs = Variant(""c~rhs.get!char());
					else if(ety is Type.get!(immutable(wchar))())
						rhs = Variant(""w~rhs.get!wchar());
					else if(ety is Type.get!(immutable(dchar))())
						rhs = Variant(""d~rhs.get!dchar());
					else rhs = Variant([rhs]);
					return e1.interpretV().opBinary!"~"(rhs);
				}
			}
			assert(e2.type.getElementType() &&
			       e2.type.getElementType().equals(e1.type));
			auto ety = e1.type;
			auto lhs = e1.interpretV();
			if(ety is Type.get!(immutable(char))())
				lhs = Variant(""c~lhs.get!char());
			else if(ety is Type.get!(immutable(wchar))())
				lhs = Variant(""w~lhs.get!wchar());
			else if(ety is Type.get!(immutable(dchar))())
				lhs = Variant(""d~lhs.get!dchar());
			else lhs = Variant([lhs]);
			return lhs.opBinary!"~"(e2.interpretV());
		}else return super.interpretV();
	}
protected:
	override Expression _interpretFunctionCalls(Scope sc){mixin(IntFCChld!q{e1,e2});}
}

mixin template Interpret(T) if(is(T==TernaryExp)){
	override bool checkInterpret(Scope sc){
		return e1.checkInterpret(sc)&e2.checkInterpret(sc)&e3.checkInterpret(sc);
	}
	override Variant interpretV(){
		auto r = e1.interpretV();
		assert(r.getType() is Type.get!bool(), to!string(r.getType()));
		return r ? e2.interpretV() : e3.interpretV();
	}

protected:
	override Expression _interpretFunctionCalls(Scope sc){mixin(IntFCChld!q{e1,e2,e3});}
}

mixin template Interpret(T) if(is(T==CallExp)){
	private Variant val;
	override bool checkInterpret(Scope sc){return true;} // be optimistic
protected:
	override Expression _interpretFunctionCalls(Scope sc){
		foreach(ref x; args) x = x.interpret(sc);
		mixin(PropErr!q{args});
		import std.algorithm;
		if(auto sym = cast(Symbol)e) // TODO: get rid of casts?
			if(auto fn = cast(FunctionDef)sym.meaning){
				sym.makeStrong();				
				sym.sstate = SemState.begin;
				mixin(SemChldPar!q{e});
				if(fn.sstate == SemState.error){
					// TODO: better error messages/error message handling scheme
					sc.error("interpretation of invalid function failed",loc);
					mixin(ErrEplg);
				}
				if(fn.type.ret !is Type.get!void()){
					auto r = fn.interpretCall(array(map!(_=>_.interpretV())(args)), sc.handler).toExpr();
					r.type = type;
					return r;
				}
			}
		sc.error(format("cannot interpret function call '%s' at compile time",toString()),loc);
		mixin(ErrEplg);
	}
}

// bytecode interpreter for functions
import expression, declaration, statement;

enum Instruction : uint{
	hlt, 
	nop,
	// flow control
	jmp,                        // jump to (constant) location of argument
	jz,                         // jump if zero
	jnz,                        // jump if non-zero
	call,                       // function call (todo)
	ret,                        // return from function
	// stack control
	push,                       // push 1
	pop,                        // pop 1
	pushp,                      // push 1 from constant stack location
	popp,                       // pop and store 1 to constant stack location
	push2,                      // push 2
	pop2,                       // pop 2
	pushp2,                     // push 2s to consecutive constant stack locations
	popp2,                      // pop and store 2 to consecutive constant stack locations
	popr,                       // pop 2 and store higher to stack location given by lower
	poprkv,                     // like popr, but keep value on stack (dup-rot-popr)
	poprkr,                     // like popr, but keep stack reference on stack
	pushr,                      // pop and push stack location given by value
	popr2,                      // pop 3, store 2 higher to stack location given by lowest
	poprkv2,                    // like popr2, but keep value on stack
	poprkr2,                    // like popr2, but keep stack reference on stack
	pushr2,                     // pop and push 2 consecutive stack locations given by value
	swap,                       // swap topmost values
	swap2,                      // swap topmost value pairs
	dup,                        // push top of stack
    dup2,                       // duplicate the 2 topmost stack entries
	rot,                        // rotate the 3 topmost entries by moving top 2 entries down
	rot2,                       // rotate the 3 topmost pairs of 2
	rot221,                     // rotate the 2 topmost pairs of 2 and the following entry
	alloca,                     // pop 1 and reserve stack space
	// temporaries              
	tmppush,                    // pop 1 and push to temporary stack
	tmppop,                     // pop 2 and push to temporary stack
	// type conversion
	int2bool,                   // pop 1, convert to bool and push 1
	real2bool,                  // pop 2, interpret as real convert to bool and push 1
	uint2real,                  // pop 1, convert to real, push 2
	real2uint,                  // pop 2, convert to ulong push 1
	int2real,                   // pop 1, interpret as signed, convert to real, push 2
	real2int,                   // pop 2, convert to long, interpret as ulong, push 1
	float2real,                 // pop 1, interpret as float, convert to real, push 2
	real2float,                 // pop 2, convert to float, push 1
	double2real,                // pop 1, interpret as double, convert to real, push 2
	real2double,                // pop 2, convert to double, push 1
	trunc,                      // truncate top to given number of bits
	truncs,                     // truncate top to given number of bits, sign extend
	// arithmetics
	negi,                       // negate top of stack
	noti,                       // ~ top of stack
	notb,                       // ! top of stack
	addi,                       // add 2 ulongs
	subi,                       // subtract top from ltop
	muli,                       // multiply 2 ulongs
	divi,                       // divide ltop by top unsigned
	divsi,                      // divide ltop by top signed
	modi,                       // ltop%top unsigned
	modsi,                      // ltop%top signed
	// shifts
	shl,                        // logic shift left
	shr,                        // logic shift right
	sar,                        // shift arithmetic right
	// bitwise ops
	or,
	xor,
	and,
	// comparison
	cmpei,                      // compare for equality
	cmpli,                      // signed <
	cmpbi,                      // unsigned <
	cmplei,                     // signed <=
	cmpbei,                     // unsigned <=
	cmpnei,                     // compare for inequality
	cmpgi,                      // signed >
	cmpai,                      // unsigned >
	cmpgei,                     // signed >=
	cmpaei,                     // unsigned >=
	// array operations
	newarray,                   // creates an array, stack top is ptr, ltop is length
	makearray,                  // pop values from the stack and turn them into an array
	appenda,
	concata,
	// arrays of simple types
	loada,                     // stack top is the index
	loadak,                    // like loada, but keep array and index on stack
	storea,
	storeakr,
	storeakv,
	// array of arrays
	loadaa,
	loadaak,
	storeaa,
	storeaakr,
	storeaakv,
	// error handling table
	errtbl,
}

private enum isize = Instruction.sizeof;

size_t numArgs(Instruction inst){
	alias Instruction I;
	enum TBD = -1;
	static int[] args =
		[// flow control
		 I.hlt: 0, I.jmp: 1, I.jz: 1, I.jnz: 1, I.call: TBD, I.ret: 0,
		 // stack control
		 I.push:  1, I.pop:  0, I.pushp:  1, I.popp:  1,
		 I.push2: 2, I.pop2: 0, I.pushp2: 1, I.popp2: 1,
		 I.popr: 0, I.pushr: 0, I.popr2: 0, I.pushr2: 0,
		 I.swap: 0, I.swap2: 0, I.dup: 0, I.dup2: 0,
		 I.rot: 0, I.rot2: 0, I.rot221: 0,
		 I.alloca: 0,
		 // temporaries
		 I.tmppush: 0, I.tmppop: 0,
		 // type conversion
		 I.int2bool:   0, I.real2bool:  0,
		 I.uint2real:  0, I.real2uint:  0,
		 I.int2real:   0, I.real2int:   0,
		 I.float2real: 0, I.real2float: 0,
		 I.double2real:0, I.real2double:0,
		 I.trunc:      1, I.truncs     :1,
		 // arithmetics
		 I.negi: 0, I.noti: 0, I.addi: 0, I.subi: 0,I.muli: 0,
		 I.divi: 0, I.divsi: 0, I.modi: 0, I.modsi: 0, I.shl: 0, I.shr: 0, I.sar: 0,
		 // comparison
		 I.cmpei: 0, I.cmpli: 0, I.cmpbi: 0, I.cmplei: 0, I.cmpbei: 0,
		 I.cmpnei: 0, I.cmpgi: 0, I.cmpai: 0, I.cmpgei: 0, I.cmpaei: 0,
		 // array operations
		 I.newarray: 1, I.makearray: 1, I.appenda: 0, I.concata: 0,
		 I.loada: 1, I.loadak: 1, I.storea: 1, I.storeakr: 1, I.storeakv: 1,
		 I.loadaa: 0, I.loadaak: 0, I.storeaa: 0, I.storeaakr: 0, I.storeaakv: 0,
		 // error handling table
		 I.errtbl: 0,
		 ];
		 
	return args[inst];
}

bool mayFail(Instruction inst){
	alias Instruction I;
	static bool[] fail =
		[// flow control
		 I.hlt: 1, I.call: 1,
		 // arithmetics
		 I.divi: 1, I.divsi: 1, I.modi: 1, I.modsi: 1,
		 // I.shl: 1, I.shr: 1, I.sar: 1 // TODO: those may fail too
		 // array operations
		 I.loada: 1, I.loadak: 1, I.storea: 1, I.storeakr: 1, I.storeakv: 1,
		 I.loadaa: 1, I.loadaak: 1, I.storeaa: 1, I.storeaakr: 1, I.storeaakv: 1,
		 ];
	return fail[inst];
}
alias Node ErrorInfo;


alias immutable(ulong)[] ByteCode;

struct Stack{
	ulong[] stack;
	static assert(ulong.sizeof>=(void*).sizeof);
	size_t stp=-1;
	@property length(){return stack.length;}
	void push()(ulong c){
		if(stp+1>=stack.length) stack.length*=2;		
		stack[++stp]=c;
	}
	void push(T)(T c) if(!is(T:ulong)){
		static if(is(T==float)||is(T==ifloat)){
			ulong hlp = *cast(uint*)&c;
			push(hlp);
		}else static if(is(T==double)||is(T==idouble))
			push(*cast(ulong*)&c);
		else static if(is(T==real)||is(T==ireal)){
			static if(real.sizeof==12){
				push(*cast(ulong*)&c);
				push(*(cast(uint*)&c+2));
			}else static if(real.sizeof==16){
				push(*cast(ulong*)&c);
				push(*(cast(ulong*)&c+1));
			}else static assert(0);
		}else static if(is(T _:U[],U)){
			push(cast(ulong)(c.length*U.sizeof));
			push(cast(ulong)c.ptr);
		}else static assert(0, "TODO: "~T.stringof);
	}
	ulong pop()(){return stack[stp--];}
	void pop()(size_t num){assert(stp+1>=num);stp-=num;}
	T pop(T)() if(!is(T:ulong)){
		static if(is(T==float)||is(T==ifloat)){
			auto hlp = cast(uint)pop();
			return *cast(T*)&hlp;
		}else static if(is(T==double)||is(T==idouble)){
			auto hlp = pop();
			return *cast(T*)&hlp;
		}else static if(is(T==real)||is(T==ireal)){
			T hlp;
			static if(real.sizeof==12){
				*(cast(uint*)&hlp+2)=cast(uint)pop();
				*cast(ulong*)&hlp=pop();
			}else static if(real.sizeof==16){
				*(cast(ulong*)&hlp+1)=cast(uint)pop();
				*cast(ulong*)&hlp=pop();				
			}else static assert(0);
			return hlp;
		}else static if(is(T _:U[],U)){
			auto ptr=cast(U*)pop();
			auto len=cast(size_t)pop();
			assert(!(len%U.sizeof), U.stringof);
			return ptr[0..len/U.sizeof];
		}else static assert(0, "TODO: "~T.stringof);
	}

	void popFront(size_t num)in{assert(stp+1>=num);}body{
		if(!num) return;
		foreach(i, ref x; stack[0..stp+1-num]) x=stack[num+i];
		stp-=num;
	}

	ref ulong top(){return stack[stp];}
	ref ulong ltop(){return stack[stp-1];}
	string toString(){
		import std.conv;
		return to!string(stack[0..stp+1]);
	}
}

struct ByteCodeBuilder{
	private ulong[] byteCode;
	private ErrorInfo[] errtbl;
	private size_t stackOffset=0;
	private size_t iloc;
	debug{
		enum State{
			idle,
			waitingForLabel,
		}
		State state;
	}
	
	void addStackOffset(size_t amt){stackOffset+=amt;}
	size_t getStackOffset(){return stackOffset;}

	ulong getLocation(){return byteCode.length;}

	ByteCode getByteCode(){
		auto r = cast(ByteCode)((byteCode~=Instruction.errtbl)~=cast(ByteCode)errtbl);
		byteCode = null;
		return r;
	}
	void ignoreResult(size_t size){
		while(size>=2){emit(Instruction.pop2); size-=2;}
		if(size) emit(Instruction.pop);
		/+alias Instruction I;
		switch(byteCode[iloc]){
			case I.call: assert(0, "TODO");
			case I.push, I.push2:
				byteCode = byteCode[0..iloc];
				byteCode.assumeSafeAppend();
				
		}+/
	}
	void error(string err, Location loc){assert(0, err);}
	
	void emit(Instruction inst){//in{assert(!mayFail(inst));}body{
		assert(byteCode.length<ulong.max); // TODO: add this restriction explicitly
		iloc = byteCode.length;
		byteCode~=inst;
	}
	void emitConstant(ulong c){
		static assert(is(typeof(byteCode) == ulong[]));
		byteCode~=c;
	}
	void emitConstant(float c){
		byteCode~=*cast(uint*)&c;
	}
	void emitConstant(double c){
		byteCode~=*cast(ulong*)&c;
	}
	void emitConstant(real c){
		static if(real.sizeof == 12){
			byteCode~=*cast(ulong*)&c;
			byteCode~=*((cast(uint*)&c)+2);
		}else static if(real.sizeof == 16){
			byteCode~=*cast(ulong*)&c;
			byteCode~=*((cast(ulong*)&c)+1);
		}else static assert(0);
	}

	struct Label{
		private{
			ByteCodeBuilder* outer;
			size_t loc;
		}
		void here()in{
			assert(outer && outer.byteCode[loc] == ~0);
		}body{
			assert(outer.byteCode.length<=ulong.max); // TODO: add this restriction explicitly
			outer.byteCode[loc] = cast(ulong)outer.byteCode.length;
		}
	}

	Label emitLabel(){
		auto r = Label(&this, byteCode.length);
		emitConstant(~0);
		return r;
	}

	struct Alloca{
		private{
			ByteCodeBuilder* outer;
			size_t loc;
			size_t origoff;
		}
		void done(){
			outer.byteCode[loc] = cast(ulong)(outer.stackOffset-origoff);
		}
	}

	Alloca emitAlloca(){
		emit(Instruction.push);
		auto r = Alloca(&this, byteCode.length, stackOffset);
		emitConstant(~0);
		emit(Instruction.alloca);
		return r;
	}
}

abstract class LValueStrategy{
	private mixin template Singleton(){
		private static typeof(this) inst = null;
		public static opCall(){
			if(!inst) inst = new typeof(this)();
			return inst;
		}
	}
	abstract void emitStore(ref ByteCodeBuilder);  // store value on top of stack in address
	abstract void emitStoreKR(ref ByteCodeBuilder);// keep address on stack
	abstract void emitStoreKV(ref ByteCodeBuilder);// keep value on stack

	abstract void emitLoadKR(ref ByteCodeBuilder); // load value at address, keep address
}

class LVpopr(uint n): LValueStrategy{
	mixin Singleton;
	private enum _sfx = (n==1?``:to!string(n));
	override void emitStore(ref ByteCodeBuilder bld){
		bld.emit(mixin(`Instruction.popr`~_sfx));
	}
	override void emitStoreKR(ref ByteCodeBuilder bld){
		bld.emit(mixin(`Instruction.poprkr`~_sfx));
	}
	override void emitStoreKV(ref ByteCodeBuilder bld){
		bld.emit(mixin(`Instruction.poprkv`~_sfx));
	}

	override void emitLoadKR(ref ByteCodeBuilder bld){
		bld.emit(Instruction.dup);          // duplicate address
		bld.emit(mixin(`Instruction.pushr`~_sfx)); // load location
	}
}

class LVstorea(ulong els): LValueStrategy{
	mixin Singleton;
	override void emitStore(ref ByteCodeBuilder bld){
		bld.emit(Instruction.storea);
		bld.emitConstant(els);
	}
	override void emitStoreKR(ref ByteCodeBuilder bld){
		bld.emit(Instruction.storeakr);
		bld.emitConstant(els);
	}
	override void emitStoreKV(ref ByteCodeBuilder bld){
		bld.emit(Instruction.storeakv);
		bld.emitConstant(els);
	}

	override void emitLoadKR(ref ByteCodeBuilder bld){
		bld.emit(Instruction.loadak);
		bld.emitConstant(els);
	}
}
static LValueStrategy getLVstorea(ulong els){ // TODO: flyweights instead of templates?
	switch(els){
		case 1:  return LVstorea!1();
		case 2:  return LVstorea!2();
		case 4:  return LVstorea!4();
		case 8:  return LVstorea!8();
		case 12: return LVstorea!12();
		case 16: return LVstorea!16();
		default: assert(0, "unsupported element size "~to!string(els));
	}
}

class LVstoreaa: LValueStrategy{
	mixin Singleton;
	override void emitStore(ref ByteCodeBuilder bld){
		bld.emit(Instruction.storeaa);
	}
	override void emitStoreKR(ref ByteCodeBuilder bld){
		bld.emit(Instruction.storeaakr);
	}
	override void emitStoreKV(ref ByteCodeBuilder bld){
		bld.emit(Instruction.storeaakv);
	}
	
	override void emitLoadKR(ref ByteCodeBuilder bld){
		bld.emit(Instruction.loadaak);
	}
}

string toString(ByteCode byteCode){
	import std.conv;
	int off = 0;
	string r;
	while(off<byteCode.length){
		r~=to!string(off)~": "~to!string(cast(Instruction)byteCode[off]);
		auto args = numArgs(cast(Instruction)byteCode[off]);
		off++;
		if(args==2) r~=" "~to!string(byteCode[off])~"..."~to!string(byteCode[off+1]);
		else if(args==1) r~=" "~to!string(byteCode[off]);
		off+=args;
		r~="\n";
	}
	return r;
}


/* for debugging purposes
 */
bool _displayByteCode = false;
bool _displayByteCodeIntp = false;

import error;
void doInterpret(ByteCode byteCode, ref Stack stack, ErrorHandler handler)in{
	assert(stack.length>2);
}body{
	size_t ip = 0;
	size_t nargs = stack.stp+1;
	bool keepr = false, keepv = false;
	ulong[5] tmp;
	auto tmpstack = Stack(tmp[]);
	import std.stdio;
	scope(exit) if(_displayByteCodeIntp) writeln("stack: ",stack);
	for(;;){
		if(_displayByteCodeIntp){
			writeln("stack: ",stack);
			write("inst: ",cast(Instruction)byteCode[ip]);
			if(numArgs(cast(Instruction)byteCode[ip])){
				write(" ",byteCode[ip+1]);
				if(numArgs(cast(Instruction)byteCode[ip])==2)
					write("...",byteCode[ip+2]);
			}
			writeln();
		}

		final switch(cast(Instruction)byteCode[ip++]){
			alias Instruction I;
			case I.hlt:
				handler.error("encountered hlt", Location.init);
			case I.nop: break;
			// flow control:
			case I.jz:
				if(!stack.pop()) goto case I.jmp;
				ip++;
				break;
			case I.jnz:
				if(stack.pop()) goto case I.jmp;
				ip++;
			break;
			case I.jmp:
				//writeln("jumping to ",byteCode[ip]);
				ip = cast(size_t)byteCode[ip]; break;
			case I.call: assert(0, "function calls not implemented");
			case I.ret:
				// clean up stack
				stack.popFront(nargs);
				return;
			// stack control:
			case I.push:
				stack.push(byteCode[ip++]);
				break;
			case I.pushp:
				stack.push(stack.stack[cast(size_t)byteCode[ip++]]);
				break;
			case I.popp:
				stack.stack[cast(size_t)byteCode[ip++]]=stack.pop();
				break;
			case I.pop:
				stack.pop();
				break;
			case I.push2:
				stack.push(byteCode[ip++]);
				stack.push(byteCode[ip++]);
				break;
			case I.pushp2:
				auto loc = cast(size_t)byteCode[ip++];
				stack.push(stack.stack[loc]);
				stack.push(stack.stack[loc+1]);
				break;
			case I.popp2:
				auto loc = cast(size_t)byteCode[ip++];
				stack.stack[loc+1] = stack.pop();
				stack.stack[loc] = stack.pop();
				break;
			case I.pop2:
				stack.pop(); stack.pop();
				break;
			case I.popr:
				auto val = stack.pop();
				auto loc = cast(size_t)stack.pop();
				stack.stack[loc] = val;
				break;
			case I.poprkv:
				auto val = stack.pop();
				auto loc = cast(size_t)stack.pop();
				stack.stack[loc] = val;
				stack.push(val);
				break;
			case I.poprkr:
				auto val = stack.pop();
				auto loc = cast(size_t)stack.top();
				stack.stack[loc] = val;
				break;
			case I.pushr:
				auto loc = cast(size_t)stack.pop();
				stack.push(stack.stack[loc]);
				break;
			case I.popr2:
				auto val2 = stack.pop();
				auto val1 = stack.pop();
				auto loc = cast(size_t)stack.pop();
				stack.stack[loc]  =val1;
				stack.stack[loc+1]=val2;
				break;
			case I.poprkv2:
				auto val2 = stack.pop();
				auto val1 = stack.pop();
				auto loc = cast(size_t)stack.pop();
				stack.stack[loc]  =val1;
				stack.stack[loc+1]=val2;
				stack.push(val1);
				stack.push(val2);
				break;
			case I.poprkr2:
				auto val2 = stack.pop();
				auto val1 = stack.pop();
				auto loc = cast(size_t)stack.top();
				stack.stack[loc]  =val1;
				stack.stack[loc+1]=val2;
				break;				
			case I.pushr2:
				auto loc = cast(size_t)stack.pop();
				stack.push(stack.stack[loc]);
				stack.push(stack.stack[loc+1]);
				break;
			case I.swap:
				auto v1 = stack.pop();
				auto v2 = stack.pop();
				stack.push(v1);
				stack.push(v2);
				break;
			case I.swap2:
				auto a2 = stack.pop();
				auto a1 = stack.pop();
				auto b2 = stack.pop();
				auto b1 = stack.pop();
				stack.push(a1);
				stack.push(a2);
				stack.push(b1);
				stack.push(b2);
				break;
			case I.dup:
				stack.push(stack.top());
				break;
			case I.dup2:
				stack.push(stack.stack[stack.stp-1]);
				stack.push(stack.stack[stack.stp-1]);
				break;
			case I.rot:
				auto top = stack.pop();
				auto ltop = stack.pop();
				auto lltop = stack.pop();
				stack.push(top);
				stack.push(lltop);
				stack.push(ltop);
				break;
			case I.rot2:
				auto top2 = stack.pop();
				auto top1 = stack.pop();
				auto ltop2 = stack.pop();
				auto ltop1 = stack.pop();
				auto lltop2 = stack.pop();
				auto lltop1 = stack.pop();
				stack.push(top1);
				stack.push(top2);
				stack.push(lltop1);
				stack.push(lltop2);
				stack.push(ltop1);
				stack.push(ltop2);
				break;
			case I.rot221:
				auto top2 = stack.pop();
				auto top1 = stack.pop();
				auto ltop2 = stack.pop();
				auto ltop1 = stack.pop();
				auto lltop = stack.pop();
				stack.push(top1);
				stack.push(top2);
				stack.push(lltop);
				stack.push(ltop1);
				stack.push(ltop2);
				break;
			case I.alloca:
				auto amt = cast(size_t)stack.pop();
				foreach(i;0..amt) stack.push(0); // TODO: do in one go
				nargs += amt;
				foreach(i; nargs..stack.stp+1)
					swap(stack.stack[i], stack.stack[i-amt]);
				break;
			// temporaries
			case I.tmppush:
				tmpstack.push(stack.pop());
				break;
			case I.tmppop:
				stack.push(tmpstack.pop());
				break;
			// type conversion
			case I.int2bool:
				stack.top() = cast(bool)stack.top();
				break;
			case I.real2bool:
				auto v = stack.pop!real();
				stack.push(cast(bool)v);
				break;
			case I.trunc:
				stack.top()&=(1UL<<byteCode[ip++])-1;
				break;
			case I.truncs:
				auto bits = byteCode[ip++];
				auto mask = (1UL<<bits)-1;
				stack.top()&=mask;
				if(stack.top() & (1UL<<bits-1)) stack.top()|=~mask;
				break;
			case I.uint2real:
				stack.push(cast(real)stack.pop());
				break;
			case I.real2uint:
				stack.push(cast(ulong)stack.pop!real());
				break;
			case I.int2real:
				stack.push(cast(real)cast(long)stack.pop());
				break;
			case I.real2int:
				stack.push(cast(long)stack.pop!real());
				break;
			case I.real2double:
				stack.push(cast(double)stack.pop!real());
				break;
			case I.double2real:
				stack.push(cast(real)stack.pop!double());
				break;
			case I.real2float:
				stack.push(cast(float)stack.pop!real());
				break;
			case I.float2real:
				stack.push(cast(real)stack.pop!float());
				break;
			// arithmetics
			case I.negi:
				stack.top() = -stack.top();
				break;
			case I.noti:
				stack.top() = ~stack.top();
				break;
			case I.notb:
				stack.top() = !stack.top();
				break;
			case I.addi:
				auto val = stack.pop();
				stack.top()+=val;
				break;
			case I.subi:
				auto val = stack.pop();
				stack.top()-=val;
				break;
			case I.muli:
				auto val = stack.pop();
				stack.top()*=val;
				break;
			case I.divi:
				auto val = stack.pop();
				stack.top()/=val;
				break;
			case I.divsi:
				long val = stack.pop();
				stack.top()=cast(long)stack.top()/val;
				break;
			case I.modi:
				auto val = stack.pop();
				stack.top()%=val;
				break;
			case I.modsi:
				long val = stack.pop();
				stack.top()=cast(long)stack.top()%val;
				break;
			// shifts
			case I.shl:
				auto val = stack.pop();
				stack.top()<<=val;
				break;
			case I.shr:
				auto val = stack.pop();
				stack.top()>>>=val;
				break;
			case I.sar:
				auto val = stack.pop();
				stack.top()=cast(long)stack.top()>>val;
				break;
			// bitwise ops
			case I.or:
				auto val = stack.pop();
				stack.top()|=val;
				break;
			case I.xor:
				auto val = stack.pop();
				stack.top()^=val;
				break;
			case I.and:
				auto val = stack.pop();
				stack.top()&=val;
				break;
			// comparison
			case I.cmpei:
				auto val = stack.pop();
				stack.top()=stack.top()==val;
				break;
			case I.cmpnei:
				auto val = stack.pop();
				stack.top()=stack.top()!=val;
				break;
			case I.cmpli:
				long val = stack.pop();
				stack.top()=cast(long)stack.top()<val;
				break;
			case I.cmplei:
				long val = stack.pop();
				stack.top()=cast(long)stack.top()<=val;
				break;
			case I.cmpbi:
				auto val = stack.pop();
				stack.top()=stack.top()<val;
				break;
			case I.cmpbei:
				auto val = stack.pop();
				stack.top()=stack.top()<=val;
				break;
			case I.cmpgi:
				long val = stack.pop();
				stack.top()=cast(long)stack.top()>val;
				break;
			case I.cmpai:
				auto val = stack.pop();
				stack.top()=stack.top()>val;
				break;
			case I.cmpgei:
				long val = stack.pop();
				stack.top()=cast(long)stack.top()>=val;
				break;
			case I.cmpaei:
				auto val = stack.pop();
				stack.top()=stack.top()>=val;
				break;
			// array operations
			case I.newarray:
				auto els = cast(size_t)byteCode[ip++];
				auto len = cast(size_t)stack.pop();
				stack.push(new void[els*len]);
				break;
			case I.makearray:
				auto els = cast(size_t)byteCode[ip++];
				auto len = cast(size_t)stack.pop();
				auto stlen = els>8?len*2:len;
				assert(nargs+stlen<=stack.stp+1);
				auto el = stack.stack[stack.stp+1-stlen..stack.stp+1];
				auto r = new void[els*len];
				switch(els){
					case 1: foreach(i,x; el) *cast(ubyte*)&r[i]=cast(ubyte)x; break;
					case 2: foreach(i,x; el) *cast(ushort*)&r[2*i]=cast(ushort)x; break;
					case 4: foreach(i,x; el) *cast(uint*)&r[4*i]=cast(uint)x; break;
					case 8: foreach(i,x; el) *cast(ulong*)&r[8*i]=cast(ulong)x; break;
					case 12: // eg. real, ireal on 32 bit
						for(size_t i=0,j=0;i<el.length;i+=2,j+=12){
							*cast(ulong*)&r[j]=cast(ulong)el[i];
							*(cast(uint*)&r[j]+2)=cast(uint)el[i+1];
						}
						break;
					case 16:
						for(size_t i=0,j=0;i<el.length;i+=2,j+=16){
							*cast(ulong*)&r[j]=cast(ulong)el[i];
							*(cast(ulong*)&r[j]+1)=cast(ulong)el[i+1];
						}
						break;
					default: assert(0, "unsupported size "~to!string(els));
				}
				stack.pop(stlen);
				stack.push(r);
				break;
			case I.appenda:
				auto arr2 = stack.pop!(void[])();
				auto arr1 = stack.pop!(void[])();
				stack.push(arr1 ~= arr2);
				break;
			case I.concata:
				auto arr2 = stack.pop!(void[])();
				auto arr1 = stack.pop!(void[])();
				stack.push(arr1 ~ arr2);
				break;
			case I.loadak:
				keepr = true; goto case I.loada;
			case I.loada:
				auto els = cast(size_t)byteCode[ip++];
				auto i = cast(size_t)stack.pop();
				auto r = stack.pop!(void[])();
				assert(i*els<r.length);// TODO: bounds check
				if(keepr){
					stack.push(r);
					stack.push(i);
					keepr=false;
				}
				switch(els){
					case 1: stack.push(*cast(ubyte*)&r[i]); break;
					case 2: stack.push(*cast(ushort*)&r[2*i]); break;
					case 4: stack.push(*cast(uint*)&r[4*i]); break;
					case 8: stack.push(*cast(ulong*)&r[8*i]); break;
					case 12: // eg. real, ireal on 32 bit
						stack.push(*cast(ulong*)&r[12*i]);
						stack.push(*(cast(uint*)&r[12*i]+2));
						break;
					case 16:
						stack.push(*cast(ulong*)&r[16*i]);
						stack.push(*(cast(ulong*)&r[16*i]+1));
						break;
					default: assert(0);
				}
				break;
			case I.storeakr:
				keepr = true; goto case I.storea;
			case I.storeakv:
				keepv = true; goto case I.storea;
			case I.storea:
				auto els = cast(size_t)byteCode[ip++];
				assert(els<=16);
				auto v2 = els>8?stack.pop():0;
				auto v1 = stack.pop();
				auto i = cast(size_t)stack.pop();
				auto r = stack.pop!(void[])();
				switch(els){
					case 1: *cast(ubyte*)&r[i]=cast(ubyte)v1; break;
					case 2: *cast(ushort*)&r[2*i]=cast(ushort)v1; break;
					case 4: *cast(uint*)&r[4*i]=cast(uint)v1; break;
					case 8: *cast(ulong*)&r[8*i]=cast(ulong)v1; break;
					case 12: // eg. real, ireal on 32 bit
						*cast(ulong*)&r[12*i]=cast(ulong)v1;
						*(cast(uint*)&r[12*i]+2)=cast(uint)v2;
						break;
					case 16:
						*cast(ulong*)&r[16*i]=cast(ulong)v1;
						*(cast(ulong*)&r[16*i]+1)=cast(ulong)v2;
						break;
					default: assert(0);
				}
				if(keepr){
					stack.push(r);
					stack.push(i);
					keepr = false;
				}
				if(keepv){
					stack.push(v1);
					assert(els<=16);
					if(els>8) stack.push(v2);
					keepv = false;
				}
				break;
			case I.loadaa:
				auto i = cast(size_t)stack.pop();
				auto arr = stack.pop!(void[][])();
				assert(i<arr.length); // TODO: bounds check
				stack.push(arr[i]);
				break;
			case I.loadaak:
				auto i = cast(size_t)stack.pop();
				auto arr = stack.pop!(void[][])();
				stack.push(arr);
				stack.push(i);
				assert(i<arr.length); // TODO: bounds check
				stack.push(arr[i]);
			case I.storeaakr:
				keepr = true; goto case I.storeaa;
			case I.storeaakv:
				keepv = true; goto case I.storeaa;
			case I.storeaa:
				auto v = stack.pop!(void[])();
				auto i = cast(size_t)stack.pop();
				auto arr = stack.pop!(void[][])();
				assert(i<arr.length); // TODO: bounds check
				arr[i]=v;
				if(keepr){
					stack.push(arr);
					stack.push(i);
					keepr = false;
				}
				if(keepv){
					stack.push(v);
					keepv = false;
				}
				break;
			case I.errtbl:
				assert(0);
		}
	}
}


mixin template CTFEInterpret(T) if(!is(T==Node)&&!is(T==FunctionDef) && !is(T==BlockStm) && !is(T==LabeledStm) && !is(T==ExpressionStm) && !is(T==IfStm) && !is(T==ForStm) && !is(T==WhileStm) && !is(T==DoStm) && !is(T==LiteralExp) && !is(T==ArrayLiteralExp) && !is(T==ReturnStm) && !is(T==CastExp) && !is(T==Symbol) && !is(T==ConditionDeclExp) && !is(T==VarDecl) && !is(T==Expression) && !is(T _==BinaryExp!S,TokenType S) &&!is(T _==UnaryExp!S,TokenType S) && !is(T _==PostfixExp!S,TokenType S) &&!is(T==Declarators)){}

mixin template CTFEInterpret(T) if(is(T==Node)){
	void byteCompile(ref ByteCodeBuilder bld){
		import std.stdio; writeln(this);
		assert(0, to!string(typeid(this)));}
}

mixin template CTFEInterpret(T) if(is(T==Expression)){
	// some expressions can be lvalues
	LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){assert(0, to!string(typeid(this)));}
}

mixin template CTFEInterpret(T) if(is(T _==UnaryExp!S,TokenType S)){
	static if(is(T _==UnaryExp!S,TokenType S)):	
	static if(S!=Tok!"&" && S!=Tok!"*"):
	override void byteCompile(ref ByteCodeBuilder bld){
		alias Instruction I;
		assert(e.type.isBasicType);
		static if(S==Tok!"+"){}
		else static if(S==Tok!"-"||S==Tok!"~"||S==Tok!"!"){
			e.byteCompile(bld);
			if(auto bt = e.type.isIntegral){
				bld.emit(S==Tok!"-"?I.negi:S==Tok!"~"?I.noti:I.notb);
				static if(S==Tok!"!"){if(e.type !is Type.get!bool()) bld.emit(I.int2bool);}
				else{
					auto size = bt.bitSize();
					if(size<63){
						bld.emit(bt.isSigned()?I.truncs:I.trunc);
						bld.emitConstant(size);
					}
				}
			}
		}else static if(S==Tok!"++" || S==Tok!"--") byteCompileHelper(bld, false);
		else static assert(0,TokChars!S);
	}
	static if(S==Tok!"++" || S==Tok!"--"):
	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		return byteCompileHelper(bld, true);
	}

	private final LValueStrategy byteCompileHelper(ref ByteCodeBuilder bld, bool isLvalue){
		alias Instruction I;
		auto strat = e.byteCompileLV(bld);
		strat.emitLoadKR(bld);
		if(auto bt = e.type.isIntegral()){
			assert(bt.getSizeof()<=8);
			bld.emit(I.push);
			bld.emitConstant(1);
			bld.emit(S==Tok!"++"?I.addi:I.subi);
			auto size = bt.bitSize();
			if(size < 64){
				bld.emit(bt.isSigned()?I.truncs:I.trunc);
				bld.emitConstant(size);
			}
			if(isLvalue){
				strat.emitStoreKR(bld);
				return strat;
			}else{
				strat.emitStoreKV(bld);
				return null;
			}
		}else{super.byteCompile(bld); assert(0);} // TODO: fix!
	}
}

mixin template CTFEInterpret(T) if(is(T _==PostfixExp!S,TokenType S)){
	static if(is(T _==PostfixExp!S,TokenType S)):
	static assert(S==Tok!"++"||S==Tok!"--");
	override void byteCompile(ref ByteCodeBuilder bld){
		alias Instruction I;
		auto strat = e.byteCompileLV(bld);
		strat.emitLoadKR(bld);
		if(auto bt = e.type.isIntegral()){
			assert(bt.getSizeof()<=8);
			bld.emit(I.dup);
			bld.emit(I.push);
			bld.emitConstant(1);
			bld.emit(S==Tok!"++"?I.addi:I.subi);
			auto size = bt.bitSize();
			if(size < 64){
				bld.emit(bt.isSigned()?I.truncs:I.trunc);
				bld.emitConstant(size);
			}
			bld.emit(I.swap);
			bld.emit(I.tmppush);
			strat.emitStore(bld);
			bld.emit(I.tmppop);
		}else{super.byteCompile(bld); assert(0);} // TODO: fix!
	}
}

// workaround for DMD bug, other part is in expression.IndexExp
mixin template CTFEInterpretIE(T) if(is(T _==IndexExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		alias Instruction I;
		assert(a.length == 1);
		e.byteCompile(bld);
		a[0].byteCompile(bld);
		/+ (added a bytecode instruction that can do this)
		static if((void[]).sizeof<=ulong.sizeof){
			if(type.getElementType()){
				static assert((void[]).sizeof == ulong.sizeof);
				static assert((void*).sizeof == uint.sizeof);
				bld.emit(I.push);
				bld.emitConstant(2);
				bld.emit(I.muli);
				bld.emit(I.loadak);
				bld.emitConstant(uint.sizeof);
				bld.emit(I.tmppush); // push length to temp stack
				bld.emit(I.push);
				bld.emitConstant(1);
				bld.emit(I.addi);
				bld.emit(I.loada);
				bld.emitConstant(uint.sizeof);
				bld.emit(I.tmppop);
				bld.emit(I.swap);
				bld.emit(I.loadaa);
				return;
			}
		}else static assert((void[]).sizeof == 2*ulong.sizeof);
		+/
		if(type.getHeadUnqual().isDynArrTy()){
			bld.emit(I.loadaa);
			return;
		}
		bld.emit(I.loada);
		bld.emitConstant(getCTSizeof(type));
	}

	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		assert(a.length == 1);
		e.byteCompile(bld);
		a[0].byteCompile(bld);
		if(type.getHeadUnqual().isDynArrTy()) return LVstoreaa();
		return getLVstorea(getCTSizeof(type));
	}
}

mixin template CTFEInterpret(T) if(is(T _==BinaryExp!S,TokenType S)){
	static if(is(T _==BinaryExp!S,TokenType S)):
	static if(S!=Tok!"."):
	override void byteCompile(ref ByteCodeBuilder bld){
		import std.typetuple;
		alias Instruction I;
		static if(S==Tok!"="){
			auto strat = e1.byteCompileLV(bld);
			e2.byteCompile(bld);
			strat.emitStoreKV(bld);
		}else static if(S==Tok!","){
			e1.byteCompile(bld);
			bld.ignoreResult(getBCSizeof(e1.type));
			e2.byteCompile(bld);
		}else static if(isAssignOp(S)&&S!=Tok!"~=" || isArithmeticOp(S) || isShiftOp(S) || isBitwiseOp(S) ||isRelationalOp(S)&&S!=Tok!"in"&&S!=Tok!"!in"){
			static if(isAssignOp(S)){
				auto strat = e1.byteCompileLV(bld);
				strat.emitLoadKR(bld);
				enum op = TokChars!S[0..$-1];
			}else{
				e1.byteCompile(bld);
				enum op = TokChars!S;
			}
			e2.byteCompile(bld);
			assert(type.isBasicType());
			assert(e1.type is e2.type);
			if(auto bt=e1.type.isIntegral()){
				auto size = bt.bitSize(), signed = bt.isSigned();
				static if(op=="+") bld.emit(I.addi); // less checking, for convenience
				else static if(op=="-") bld.emit(I.subi);
				else static if(op=="*") bld.emit(I.muli);
				else static if(op=="/") bld.emit(signed?I.divsi:I.divi);
				else static if(op=="%") bld.emit(signed?I.modsi:I.modi);
				else static if(op=="^^") bld.emit(I.hlt); // TODO: probably better left to fn?
				else static if(op=="<<") bld.emit(I.shl);
				else static if(op==">>") bld.emit(signed?I.sar:I.shr);
				else static if(op==">>>") bld.emit(I.shr);
				else static if(op=="|") bld.emit(I.or);
				else static if(op=="^") bld.emit(I.xor);
				else static if(op=="&") bld.emit(I.and);
				else static if(op=="=="||op=="is"||op=="!<>") bld.emit(I.cmpei);
				else static if(op=="!="||op=="!is"||op=="<>") bld.emit(I.cmpnei);
				else static if(op=="<"||op=="!>=") bld.emit(signed?I.cmpli:I.cmpbi);
				else static if(op=="<="||op=="!>") bld.emit(signed?I.cmplei:I.cmpbei);
				else static if(op==">"||op=="!<=") bld.emit(signed?I.cmpgi:I.cmpai);
				else static if(op==">="||op=="!<") bld.emit(signed?I.cmpgei:I.cmpaei);
				else static if(op=="<>="||op=="!<>="){
					bld.ignoreResult(getBCSizeof(e2.type));
					bld.ignoreResult(getBCSizeof(e1.type));
					bld.emit(I.push);
					bld.emitConstant(op=="<>=");
				}else static assert(0, op);
				if(!isBitwiseOp(S) && !isRelationalOp(S) && size<64){
					bld.emit(signed?I.truncs:I.trunc);
					bld.emitConstant(size);
				}
				static if(isAssignOp(S)) strat.emitStoreKV(bld);
			}else super.byteCompile(bld);
		}else static if(S==Tok!"||"||S==Tok!"&&"){
			assert(e1.type is Type.get!bool() && e2.type is Type.get!bool());
			e1.byteCompile(bld);
			bld.emit(I.dup);
			bld.emit(S==Tok!"||"?I.jnz:I.jz);
			auto end=bld.emitLabel();
			bld.emit(I.pop);
			e2.byteCompile(bld);
			end.here();
		}else static if(S==Tok!"~"){
			e1.byteCompile(bld);
			if(e1.type is e2.type.getElementType())
				emitMakeArray(bld,e2.type,1);
			e2.byteCompile(bld);
			if(e2.type is e1.type.getElementType())
				emitMakeArray(bld,e1.type,1);
			bld.emit(I.concata);
		}else static if(S==Tok!"~="){
			auto strat = e1.byteCompileLV(bld);
			strat.emitLoadKR(bld);
			e2.byteCompile(bld);
			if(e2.type is e1.type.getElementType())
				emitMakeArray(bld,e1.type,1);
			bld.emit(I.appenda);
			strat.emitStoreKV(bld);
		}else super.byteCompile(bld);
	}
}

mixin template CTFEInterpret(T) if(is(T==BlockStm)){
	override void byteCompile(ref ByteCodeBuilder bld){ foreach(x; s) x.byteCompile(bld); }
}
mixin template CTFEInterpret(T) if(is(T==LabeledStm)){
	override void byteCompile(ref ByteCodeBuilder bld){ s.byteCompile(bld); } // TODO: label resolution
}
mixin template CTFEInterpret(T) if(is(T==ExpressionStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		e.byteCompile(bld);
		auto l = getBCSizeof(e.type);
		assert(~l);
		bld.ignoreResult(l);
	}
}
mixin template CTFEInterpret(T) if(is(T==IfStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		bld.Label otherwise, end;
		e.byteCompile(bld);
		bld.emit(Instruction.jz);
		otherwise=bld.emitLabel();
		s1.byteCompile(bld);
		if(s2){
			bld.emit(Instruction.jmp);
			end = bld.emitLabel();
			otherwise.here();
			s2.byteCompile(bld);
			end.here();
		}else otherwise.here();
	}
}
mixin template CTFEInterpret(T) if(is(T==WhileStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		auto start = bld.getLocation();
		e.byteCompile(bld);
		bld.emit(Instruction.jz);
		auto end = bld.emitLabel();
		s.byteCompile(bld);
		bld.emit(Instruction.jmp);
		bld.emitConstant(start);
		end.here();
	}
}

mixin template CTFEInterpret(T) if(is(T==DoStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		auto start = bld.getLocation();
		s.byteCompile(bld);
		e.byteCompile(bld);
		bld.emit(Instruction.jnz);
		bld.emitConstant(start);
	}
}

mixin template CTFEInterpret(T) if(is(T==ForStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		s1.byteCompile(bld);
		auto start = bld.getLocation();
		e1.byteCompile(bld);
		bld.emit(Instruction.jz);
		auto end = bld.emitLabel();
		s2.byteCompile(bld);
		e2.byteCompile(bld);
		bld.ignoreResult(getBCSizeof(e2.type));
		bld.emit(Instruction.jmp);
		bld.emitConstant(start);
		end.here();
	}
}

mixin template CTFEInterpret(T) if(is(T==ReturnStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		if(e) e.byteCompile(bld);
		bld.emit(Instruction.ret);
	}
}

mixin template CTFEInterpret(T) if(is(T==LiteralExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		auto tu = type.getHeadUnqual();
		if(auto bt = tu.isBasicType()){
			if(bt.isIntegral()){
				bld.emit(Instruction.push);
				if(bt.isSigned) bld.emitConstant(cast(int)value.get!ulong());
				else bld.emitConstant(cast(uint)value.get!ulong());
				return;
			}else if(tu is Type.get!float()||type is Type.get!ifloat()){
				bld.emit(Instruction.push);
				bld.emitConstant(value.get!float());
				return;
			}else if(tu is Type.get!double()||type is Type.get!idouble){
				bld.emit(Instruction.push);
				bld.emitConstant(value.get!double());
				return;
			}else if(tu is Type.get!real()||type is Type.get!ireal()){
				bld.emit(Instruction.push2);
				bld.emitConstant(value.get!real());
				return;
			}
		}else if(tu is Type.get!string()){
			// the reference in 'value' makes sure this is not garbage collected
			string r = value.get!string();
			bld.emit(Instruction.push);
			bld.emitConstant(cast(ulong)r.length);
			bld.emit(Instruction.push);
			bld.emitConstant(cast(ulong)r.ptr);
			return;
		}
		bld.error(format("cannot interpret %s during compile time yet.",toString()), loc);
	}
}

void emitMakeArray(ref ByteCodeBuilder bld, Type ty, ulong elems)in{
	assert(ty.getElementType());
}body{
	alias Instruction I;
	ty = ty.getElementType().getHeadUnqual();
	if(auto bt = ty.isBasicType()){
		bld.emit(I.push);
		bld.emitConstant(elems);
		bld.emit(I.makearray);
		bld.emitConstant(getCTSizeof(ty));
	}else if(ty.isDynArrTy() || ty is Type.get!EmptyArray()){
		// arrays require special treatment, because they are not 
		// compactly packed on the stack on a 32 bit system
		static assert((void*).sizeof==size_t.sizeof); // TODO: get rid of this restriction
		auto siz = (void[]).sizeof/2;
		bld.emit(I.push);
		bld.emitConstant(2*elems);
		bld.emit(I.makearray);
		bld.emitConstant(siz);
	}else assert(0, "unsupported element type "~to!string(ty));
}


mixin template CTFEInterpret(T) if(is(T==ArrayLiteralExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		foreach(x; lit) x.byteCompile(bld);
		emitMakeArray(bld, type, cast(ulong)lit.length);
	}
}

mixin template CTFEInterpret(T) if(is(T==CastExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		e.byteCompile(bld);
		import std.typetuple;
		alias Instruction I;
		auto t1 = e.type.getHeadUnqual(), t2 = type.getHeadUnqual();
		if(auto from=t1.isIntegral()){
			if(auto to=t2.isIntegral()){
				if(from.bitSize()<=to.bitSize()) return;
				if(to is Type.get!bool()){
					bld.emit(I.int2bool);
					return;
				}
				bld.emit(to.isSigned() ? I.truncs : I.trunc);
				bld.emitConstant(to.bitSize());
				return;
			}else foreach(T; TypeTuple!(float, double, real)){ // TODO: imaginary/complex
				if(t2 is Type.get!T()){
					bld.emit(from.isSigned ? I.int2real : I.uint2real);
					static if(!is(T==real)) bld.emit(mixin(`I.real2`~T.stringof));
					return;
				}
			}
		}else foreach(T; TypeTuple!(float, double, real)){
			if(t1 is Type.get!T()){
				if(auto to=t2.isIntegral()){
					static if(!is(T==real)) bld.emit(mixin(`I.`~T.stringof~`2real`));
					if(to is Type.get!bool){
						bld.emit(I.real2bool);
						return;
					}
					auto signed = to.isSigned();
					bld.emit(signed?I.real2int:I.real2uint);
					if(to.bitSize()<64){
						bld.emit(signed ? I.truncs : I.trunc);
						bld.emitConstant(to.bitSize());
					}
					return;
				}else foreach(S; TypeTuple!(float, double, real)){
					if(type is Type.get!S()){
						static if(is(S==T)) return;
						else{
							static if(!is(T==real)) bld.emit(mixin(`I.`~T.stringof~`2real`));
							static if(!is(S==real)) bld.emit(mixin(`I.real2`~S.stringof));
							return;
						}
					}
				}
				break;
			}
		}
		// TODO: sanity check for reinterpreted references
		if(t1.getElementType() && t2.getElementType()) return;
		bld.error(format("cannot interpret cast from '%s' to '%s' at compile time", e.type,type),loc);
	}
}

mixin template CTFEInterpret(T) if(is(T==Symbol)){
	override void byteCompile(ref ByteCodeBuilder bld){
		if(auto vd = meaning.isVarDecl()){
			if(vd.stc&STCenum || vd.stc&STCimmutable && vd.init.isConstant()){
				vd.init.byteCompile(bld);
			}else{
				// TODO: nested functions
				size_t len;
				auto off = vd.getBCStackLoc(len);
				assert(~off && len && len<=2); // TODO: do hlt instead
				bld.emit(len==1?Instruction.pushp:Instruction.pushp2);
				bld.emitConstant(off);
			}
			return;
		}
		bld.error(format("cannot interpret symbol '%s' at compile time", toString()), loc);
	}
	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		if(auto vd = meaning.isVarDecl()){
			// TODO: nested functions, global immutable variables
			size_t len;
			auto off = vd.getBCStackLoc(len);
			assert(~off && len && len<=2); // TODO: do hlt instead
			bld.emit(Instruction.push);
			bld.emitConstant(off);
			return len==1?LVpopr!1():LVpopr!2();
		}
		bld.error(format("cannot interpret symbol '%s' at compile time", toString()), loc);
		assert(0); // TODO: fix
	}
}

mixin template CTFEInterpret(T) if(is(T==ConditionDeclExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		decl.byteCompile(bld);
		sym.byteCompile(bld);
	}
}

// get size in ulongs on the bc stack
uint getBCSizeof(Type type){
	if(auto bt = type.isBasicType())
		return (bt.bitSize()+63)/64;
	if(type.isDynArrTy()) return 2;
	return -1;
}
// get compile time size of a type in bytes
size_t getCTSizeof(Type type){
	if(type.getHeadUnqual().isDynArrTy()) return (void[]).sizeof;
	if(type is Type.get!real()) return real.sizeof;
	return cast(size_t)type.getSizeof();
}
mixin template CTFEInterpret(T) if(is(T==Declarators)){
	override void byteCompile(ref ByteCodeBuilder bld){
		foreach(x; decls) x.byteCompile(bld);
	}
}
mixin template CTFEInterpret(T) if(is(T==VarDecl)){
	override void byteCompile(ref ByteCodeBuilder bld){
		auto off = bld.getStackOffset();
		auto len = getBCSizeof(type);
		if(len!=-1){
			if(len<=2){ // TODO: fix
				setBCStackLoc(off, len);
				bld.addStackOffset(len);
				if(init){
					init.byteCompile(bld); // TODO: in semantic, add correct 'init's
					bld.emit(len==2?Instruction.popp2:Instruction.popp);
					bld.emitConstant(off);
				}
				return;
			}
		}
		bld.error(format("cannot interpret local variable of type '%s' at compile time yet.",type.toString()),loc);
	}

	final void setBCStackLoc(size_t off, size_t len){
		byteCodeStackOffset = off;
		byteCodeStackLength = len;
	}
	final size_t getBCStackLoc(ref size_t len){
		len = byteCodeStackLength;
		return byteCodeStackOffset;
	}
private:
	size_t byteCodeStackOffset = -1;
	size_t byteCodeStackLength = 0;
}

mixin template CTFEInterpret(T) if(is(T==FunctionDef)){
	ByteCode byteCode;
	final Variant interpretCall(Variant[] args, ErrorHandler handler)in{
		assert(sstate == SemState.completed);
		assert(type.params.length == args.length);
	}body{
		ulong[100] stackst;
		auto stack=Stack(stackst[]);

		import std.typetuple;
		foreach(i,x; type.params){
			auto ty = x.type.getHeadUnqual();
			if(auto bt = ty.isIntegral()){
				stack.push(args[i].get!ulong());
				x.setBCStackLoc(stack.stp, 1);
				goto paramok;
			}else if(ty is Type.get!float() || ty is Type.get!ifloat()){
				stack.push(args[i].get!float());
				x.setBCStackLoc(stack.stp, 1);
				goto paramok;
			}else if(ty is Type.get!double() || ty is Type.get!idouble()){
				stack.push(args[i].get!double());
				x.setBCStackLoc(stack.stp, 1);
				goto paramok;
			}else if(ty is Type.get!real() || ty is Type.get!ireal()){
				stack.push(args[i].get!real());
				x.setBCStackLoc(stack.stp-1, 2);
				goto paramok;
			}else foreach(T;TypeTuple!(string, wstring, dstring))
				if(ty is Type.get!T()){ // TODO: extend to all array types
					stack.push(args[i].get!T());
					x.setBCStackLoc(stack.stp-1, 2);
					goto paramok;
				}
			if(ty.getElementType()){
				stack.push(args[i].get!(void[])());
				x.setBCStackLoc(stack.stp-1, 2);
				goto paramok;
			}
			assert(0, "unsupported argument type "~x.type.toString());
		paramok:;
		}

		if(byteCode is null){
			ByteCodeBuilder bld;
			bld.addStackOffset(stack.stp+1); // leave room for locals
			byteCode = bld.getByteCode();
			auto alloca = bld.emitAlloca(); // reserve local variables
			byteCompile(bld);
			alloca.done();
			byteCode = bld.getByteCode();
			if(_displayByteCode){
				import std.stdio; writeln("byteCode for ",name,":\n",byteCode.toString());
			}
		}

		import core.memory;
		GC.disable(); // TODO: solve in a better way
		byteCode.doInterpret(stack, handler);
		GC.enable();
		
		auto ret = type.ret.getHeadUnqual();
		if(auto bt = ret.isBasicType()){
		swtch:switch(bt.op){
				foreach(x; ToTuple!integralTypes){ // TODO: floating point
					case Tok!x: return Variant(mixin(`cast(`~x~`)stack.pop()`));
				}
				import std.typetuple;
				foreach(T; TypeTuple!(float, ifloat, double, idouble, real, ireal))
					case Tok!(T.stringof):
					return Variant(stack.pop!T());
				default: break;
			}
		}else foreach(T;TypeTuple!(string, wstring, dstring))
		      if(ret is Type.get!T()) return Variant(stack.pop!T());
		if(ret.getElementType()) return Variant.fromVoidArray(stack.pop!(void[])(),ret);
		assert(0,"unsupported return type "~type.ret.toString());
	}

	final override void byteCompile(ref ByteCodeBuilder bld){
		// TODO: parameters and locals
		bdy.byteCompile(bld);
	}
}



