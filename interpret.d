// Written in the D programming language.

import lexer, expression, semantic, scope_, type;
import util;
import std.string;
import std.conv: to;

private template NotYetImplemented(T){
	static if(is(T _==BinaryExp!S,TokenType S) && !is(T==BinaryExp!(Tok!".")) || is(T==ABinaryExp) || is(T==AssignExp))
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
		if(isAConstant()) return this;
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
		r.dontConstFold();
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
	override bool checkInterpret(Scope sc){
		if(e.type.implicitlyConvertsTo(type)) return e.checkInterpret(sc);
		if(type.getHeadUnqual().isPointerTy()){
			sc.error(format("cannot interpret cast from '%s' to '%s' at compile time",e.type,type),loc);
			return false;
		}
		return e.checkInterpret(sc);
	}
	override Variant interpretV(){
		auto le=e.isLiteralExp(); // polysemous string literals might be cast
		auto el = type.getElementType();
		if(el&&le&&le.isPolyString()){
			auto vle=e.interpretV();
			auto typeu = type.getHeadUnqual();
			if(typeu.isSomeString()) return e.interpretV().convertTo(type);
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
			if(vd.sstate == SemState.error) return false;
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
		return New!LiteralExp(Variant(val)).semantic(null);
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

mixin template Interpret(T) if(is(T==ABinaryExp)||is(T==AssignExp)){}
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
					Expression r;
					try{
						r = fn.interpretCall(array(map!(_=>_.interpretV())(args)), sc.handler).toExpr();
						r.type = type;
						return r;
					}catch(Exception){
						sc.note("during evaluation requested here", loc);
						mixin(ErrEplg);
					}
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
	push2,                      // push 2
	pop2,                       // pop 2
	popn,                       // pop n
	pushp,                      // push 1 from constant stack location
	popp,                       // pop and store 1 to constant stack location
	pushp2,                     // push 2s to consecutive constant stack locations
	popp2,                      // pop and store 2 to consecutive constant stack locations
	pushpn,                     // pop and store to n consecutive constant stack locations
	poppn,                      // pop and store n to consecutive constant stack locations
	pushr,                      // pop and push stack location given by value
	popr,                       // pop 2 and store higher to stack location given by lower
	pushr2,                     // pop and push 2 consecutive stack locations given by value
	popr2,                      // pop 3, store 2 higher to stack location given by lowest
	pushrn,                     // pop and push n consecutive stack locations given by value
	poprn,                      // pop n+1, store n higher to stack location given by lowest
	poprkv,                     // like popr, but keep value on stack (dup-rot-popr)
	poprkr,                     // like popr, but keep stack reference on stack
	poprkv2,                    // like popr2, but keep value on stack
	poprkr2,                    // like popr2, but keep stack reference on stack
	poprkvn,                    // like poprn, but keep value on stack
	poprkrn,                    // like poprn, but keep stack reference on stack
	swap,                       // swap topmost values
	swap2,                      // swap topmost value pairs
	swapn,                      // swap topmost n-tuples
	dup,                        // push top of stack
    dup2,                       // duplicate the 2 topmost stack entries
	dupn,                       // duplicate the n topmost stack entries
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
	shl32,                      // logic shift left, shamt below 32
	shr32,                      // logic shift right, shamt below 32
	sar32,                      // shift arithmetic right, shamt below 32
	shl64,                      // logic shift left, shamt below 64
	shr64,                      // logic shift right, shamt below 64
	sar64,                      // shift arithmetic right, shamt below 64
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
	ptra,                       // get pointer field
	lengtha,                    // get length field
	newarray,                   // creates an array, stack top is ptr, ltop is length
	makearray,                  // pop values from the stack and turn them into an array
	appenda,
	concata,
	// arrays of simple types
	loada,                      // stack top is the index
	loadak,                     // like loada, but keep array and index on stack
	storea,
	storeakr,
	storeakv,
	slicea,
	// array of arrays (not actually required anymore, but instruction size is smaller)
	loadaa,
	loadaak,
	storeaa,
	storeaakr,
	storeaakv,
	// pointers
	loadap,                    // generate a pointer to an array location
	ptrtoa,
	addp,                      // add an integer to a pointer
	// error handling table
	errtbl,
}

private enum isize = Instruction.sizeof;

size_t numArgs(Instruction inst){
	alias Instruction I;
	enum TBD = -1;
	static int[] args =
		[// flow control
		 I.hlt: 0, I.jmp: 1, I.jz: 1, I.jnz: 1, I.call: 1, I.ret: 0,
		 // stack control
		 I.push:  1, I.pop:  0, I.popn: 1, I.pushp:  1, I.popp:  1,
		 I.push2: 2, I.pop2: 0, I.pushp2: 1, I.popp2: 1, I.pushpn: 2, I.poppn: 2,
		 I.pushr: 0, I.popr: 0, I.pushr2: 0, I.popr2: 0, I.pushrn: 1, I.poprn: 1,
		 I.poprkv: 0, I.poprkr: 0, I.poprkv2: 0, I.poprkr2: 0, I.poprkvn: 1, I.poprkrn: 1, 
		 I.swap: 0, I.swap2: 0, I.swapn: 1, I.dup: 0, I.dup2: 0, I.dupn: 1,
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
		 I.divi: 0, I.divsi: 0, I.modi: 0, I.modsi: 0,
		 I.shl32: 0, I.shr32: 0, I.sar32: 0, I.shl64: 0, I.shr64: 0, I.sar64: 0,
		 // comparison
		 I.cmpei: 0, I.cmpli: 0, I.cmpbi: 0, I.cmplei: 0, I.cmpbei: 0,
		 I.cmpnei: 0, I.cmpgi: 0, I.cmpai: 0, I.cmpgei: 0, I.cmpaei: 0,
		 // array operations
		 I.newarray: 1, I.makearray: 1, I.appenda: 0, I.concata: 0,
		 I.loada: 1, I.loadak: 1, I.storea: 1, I.storeakr: 1, I.storeakv: 1, I.slicea: 1,
		 I.loadaa: 0, I.loadaak: 0, I.storeaa: 0, I.storeaakr: 0, I.storeaakv: 0,
		 // pointer operations
		 I.loadap: 1, I.ptrtoa: 0, I.addp: 1,
		 // error handling table
		 I.errtbl: 0,
		 ];
	return args[inst];
}

bool isUnsafe(Instruction inst){
	alias Instruction I;
	static bool[] fail =
		[// flow control
		 I.hlt: 1,
		 // arithmetics
		 I.divi: 1, I.divsi: 1, I.modi: 1, I.modsi: 1,
		 I.shl32: 1, I.shr32: 1, I.sar32: 1, I.shl64: 1, I.shr64: 1, I.sar64: 1,
		 // array operations
		 I.loada: 1, I.loadak: 1, I.storea: 1, I.storeakr: 1, I.storeakv: 1, I.slicea: 1,
		 I.loadaa: 1, I.loadaak: 1, I.storeaa: 1, I.storeaakr: 1, I.storeaakv: 1,
		 // pointer operations
		 I.loadap: 1, I.ptrtoa: 1,
		 I.max: 0
		 ];
	return fail[inst];
}
alias Node ErrorInfo;

private class HltErrorInfo: Node{
	// kind
	// _doAnalyze
}

alias immutable(ulong)[] ByteCode;

import variant;

struct Stack{
	ulong[] stack;
	static assert(ulong.sizeof>=(void*).sizeof);
	size_t stp=-1;
	@property length(){return stack.length;}
	void push()(ulong c){
		if(stp+1>=stack.length){void[] va = stack; va.length *= 2; stack=cast(ulong[])va;}
		stack[++stp]=c;
	}
	// TODO: just do this based on sizeof
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
		}else static if(is(T==BCSlice)){
			static assert(ulong.sizeof==8);
			static if(T.sizeof==16){
				push(*cast(ulong*)&c);
				push(*(cast(ulong*)&c+1));
			}else static if(T.sizeof==32){
				push(*cast(ulong*)&c);
				push(*(cast(ulong*)&c+1));
				push(*(cast(ulong*)&c+2));
				push(*(cast(ulong*)&c+3));
			}else static assert(0);
		}else static if(is(T==BCPointer)){
			static if(T.sizeof==12){
				push(*cast(ulong*)&c);
				push(*(cast(uint*)&c+2));
			}else static if(T.sizeof==24){
				push(*cast(ulong*)&c);
				push(*(cast(ulong*)&c+1));
				push(*(cast(ulong*)&c+2));
			}else static assert(0);
		}/+else static if(is(T _:U[],U)){
			push(cast(ulong)(c.length*U.sizeof));
			push(cast(ulong)c.ptr);
		}+/else static assert(0, "TODO: "~T.stringof);
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
		}else static if(is(T==BCSlice)){
			static assert(ulong.sizeof==8);
			T c;
			static if(T.sizeof==16){
				*(cast(ulong*)&c+1) = pop();
				*cast(ulong*)&c = pop();
			}else static if(T.sizeof==32){
				*(cast(ulong*)&c+3) = pop();
				*(cast(ulong*)&c+2) = pop();
				*(cast(ulong*)&c+1) = pop();
				*cast(ulong*)&c     = pop();
			}else static assert(0);
			return c;
		}else static if(is(T==BCPointer)){
			T c;
			static if(T.sizeof==12){
				*(cast(uint*)&c+2) = cast(uint)pop();
				*cast(ulong*)&c    = pop();
			}else static if(T.sizeof==24){
				*(cast(ulong*)&c+2) = pop();
				*(cast(ulong*)&c+1) = pop();
				*cast(ulong*)&c     = pop();
			}else static assert(0);
			return c;
		}/+else static if(is(T _:U[],U)){
			auto ptr=cast(U*)pop();
			auto len=cast(size_t)pop();
			assert(!(len%U.sizeof), U.stringof);
			return ptr[0..len/U.sizeof];
		}+/else static assert(0, "TODO: "~T.stringof);
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
		static if(ErrorInfo.sizeof%ulong.sizeof)
			if(errtbl.length*ErrorInfo.sizeof%ulong.sizeof){
			errtbl~=null;
			assert(!((cast(ulong)errtbl.ptr)%ulong.sizeof));
		}
		auto r = cast(ByteCode)((byteCode~=Instruction.errtbl)~=cast(ByteCode)errtbl);
		byteCode = null;
		return r;
	}
	ErrorInfo[] getErrtbl(){return errtbl;}
	void ignoreResult(size_t size){
		emitPop(size);
	}
	void error(string err, Location loc){assert(0, err);}
	
	void emit(Instruction inst)in{assert(!isUnsafe(inst));}body{
		assert(byteCode.length<ulong.max); // TODO: add this restriction explicitly
		iloc = byteCode.length;
		byteCode~=inst;
	}

	void emitUnsafe(Instruction inst, ErrorInfo info)in{assert(isUnsafe(inst));}body{
		byteCode~=inst;
		errtbl~=info;
	}

	void emitDup(ulong num){
		if(num == 1) return emit(Instruction.dup);
		if(num == 2) return emit(Instruction.dup2);
		emit(Instruction.dupn);
		emitConstant(num);
	}

	void emitSwap(ulong num){
		if(num == 1) return emit(Instruction.swap);
		if(num == 2) return emit(Instruction.swap2);
		emit(Instruction.swapn);
		emitConstant(num);
	}
	void emitTmppush(ulong num){
		foreach(i;0..num) emit(Instruction.tmppush);
	}
	void emitTmppop(ulong num){
		foreach(i;0..num) emit(Instruction.tmppop);
	}

	void emitPop(ulong num){
		if(num == 1) return emit(Instruction.pop);
		if(num == 2) return emit(Instruction.pop2);
		emit(Instruction.popn);
		emitConstant(num);
	}

	void emitPushp(ulong num){
		if(num == 1) return emit(Instruction.pushp);
		if(num == 2) return emit(Instruction.pushp2);
		emit(Instruction.pushpn);
		emitConstant(num);
	}

	void emitPopp(ulong num){
		if(num == 1) return emit(Instruction.popp);
		if(num == 2) return emit(Instruction.popp2);
		emit(Instruction.poppn);
		emitConstant(num);
	}

	void emitPushr(ulong num){
		if(num == 1) return emit(Instruction.pushr);
		if(num == 2) return emit(Instruction.pushr2);
		emit(Instruction.pushrn);
		emitConstant(num);
	}

	void emitPopr(ulong num){
		if(num == 1) return emit(Instruction.popr);
		if(num == 2) return emit(Instruction.popr2);
		emit(Instruction.poprn);
		emitConstant(num);
	}

	void emitConstant(ulong c){
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
			size_t loc = -1; // no allocation if label used exactly once
			size_t[] locs;
			ulong pos = -1;
		}
		void here()in{
			assert(outer && loc == -1 || outer.byteCode[loc] == ~0);
		}body{
			pos = cast(ulong)outer.byteCode.length;
			if(loc == -1) return;
			assert(outer.byteCode.length<=ulong.max); // TODO: add this restriction explicitly
			outer.byteCode[loc] = pos;
			foreach(l; locs) outer.byteCode[l] = pos;
		}

		bool initialized(){return outer !is null;}
	}

	Label getLabel(){
		return Label(&this);
	}
	Label emitLabel(){
		auto r = Label(&this, byteCode.length);
		emitConstant(~0);
		return r;
	}
	void emitLabel(ref Label lbl)in{assert(lbl.outer is &this);}body{
		if(~lbl.pos) emitConstant(lbl.pos);
		else{
			if(!~lbl.loc) lbl.loc=byteCode.length;
			else lbl.locs ~= byteCode.length;
			emitConstant(~0);
		}
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

	abstract void emitLoad(ref ByteCodeBuilder); // load value at address
	abstract void emitLoadKR(ref ByteCodeBuilder); // load value at address, keep address

	abstract void emitPointer(ref ByteCodeBuilder);
}

class LVpopr: LValueStrategy{
	ulong n;
	static opCall(ulong n){
		return new LVpopr(n);
	}

	private this(ulong nn){
		n = nn;
	}

	override void emitStore(ref ByteCodeBuilder bld){
		if(n==1) bld.emit(Instruction.popr);
		else if(n==2) bld.emit(Instruction.popr2);
		else{
			bld.emit(Instruction.poprn);
			bld.emitConstant(n);
		}
	}
	override void emitStoreKR(ref ByteCodeBuilder bld){
		if(n==1) bld.emit(Instruction.poprkr);
		else if(n==2) bld.emit(Instruction.poprkr2);
		else{
			bld.emit(Instruction.poprkrn);
			bld.emitConstant(n);
		}
	}
	override void emitStoreKV(ref ByteCodeBuilder bld){
		if(n==1) bld.emit(Instruction.poprkv);
		else if(n==2) bld.emit(Instruction.poprkv2);
		else{
			bld.emit(Instruction.poprkvn);
			bld.emitConstant(n);
		}
	}

	override void emitLoad(ref ByteCodeBuilder bld){
		if(n==1) bld.emit(Instruction.pushr);
		else if(n==2) bld.emit(Instruction.pushr2);
		else{
			bld.emit(Instruction.pushrn);
			bld.emitConstant(n);
		}
	}
	override void emitLoadKR(ref ByteCodeBuilder bld){
		bld.emit(Instruction.dup);          // duplicate address
		if(n==1) bld.emit(Instruction.pushr);
		else if(n==2) bld.emit(Instruction.pushr2);
		else{
			bld.emit(Instruction.pushrn);
			bld.emitConstant(n);
		}
	}

	override void emitPointer(ref ByteCodeBuilder bld){
		assert(0, "cannot create stack references");
	}
}

LVstorea LVpointer(Type elty, ErrorInfo info){
	return new LVstorea(elty, info, true);
}
class LVstorea: LValueStrategy{
	ulong els;
	ulong bcsiz;
	bool isarr;
	bool isptr;
	ErrorInfo info;
	static opCall(Type elty, ErrorInfo info){
		return new LVstorea(elty, info, false);
	}
	private this(Type elty, ErrorInfo inf, bool ptr){
		isarr = cast(bool)elty.getHeadUnqual().isDynArrTy();
		if(!isarr) els = getCTSizeof(elty);
		bcsiz = getBCSizeof(elty);
		info = info;
		isptr=ptr;
	}
	private void ptrPrlg(ref ByteCodeBuilder bld, bool isstore){
		if(isptr){
			if(isstore) bld.emitTmppush(bcsiz);
			bld.emitUnsafe(Instruction.ptrtoa, info);
			bld.emit(Instruction.push);
			bld.emitConstant(0);
			if(isstore) bld.emitTmppop(bcsiz);
		}
	}
	override void emitStore(ref ByteCodeBuilder bld){
		ptrPrlg(bld,true);
		bld.emitUnsafe(isarr?Instruction.storeaa:Instruction.storea, info);
		if(!isarr) bld.emitConstant(els);
	}
	override void emitStoreKR(ref ByteCodeBuilder bld){
		ptrPrlg(bld,true);
		bld.emitUnsafe(isarr?Instruction.storeaakr:Instruction.storeakr, info);
		if(!isarr) bld.emitConstant(els);
	}
	override void emitStoreKV(ref ByteCodeBuilder bld){
		ptrPrlg(bld,true);
		bld.emitUnsafe(isarr?Instruction.storeaakv:Instruction.storeakv, info);
		if(!isarr) bld.emitConstant(els);
	}
	
	override void emitLoad(ref ByteCodeBuilder bld){
		ptrPrlg(bld,false);
		bld.emitUnsafe(isarr?Instruction.loadaa:Instruction.loada, info);
		if(!isarr) bld.emitConstant(els);		
	}
	override void emitLoadKR(ref ByteCodeBuilder bld){
		ptrPrlg(bld,false);
		bld.emitUnsafe(isarr?Instruction.loadaak:Instruction.loadak, info);
		if(!isarr) bld.emitConstant(els);
	}

	override void emitPointer(ref ByteCodeBuilder bld){
		if(!isptr){
			bld.emitUnsafe(Instruction.loadap, info);
			bld.emitConstant(els);
		}
	}
}

class LVconditional: LValueStrategy{
	LValueStrategy strat1, strat2;
	static opCall(LValueStrategy strat1, LValueStrategy strat2){
		return new LVconditional(strat1, strat2);
	}
	private this(LValueStrategy s1, LValueStrategy s2){
		strat1 = s1;
		strat2 = s2;
	}
	private static _emitAll(){
		string r;
		foreach(s;["emitStore", "emitStoreKR", "emitStoreKV",
		           "emitLoad", "emitLoadKR", "emitPointer"]){
			r~=mixin(X!q{
				override void @(s)(ref ByteCodeBuilder bld){
					alias Instruction I;
					bld.emit(I.tmppop);
					bld.emit(I.jz);
					auto otherwise=bld.emitLabel();
					strat1.@(s)(bld);
					bld.emit(I.jmp);
					auto end=bld.emitLabel();
					otherwise.here();
					strat2.@(s)(bld);
					end.here();
				}
			});
		}
		return r;
	}
	mixin(_emitAll());
}

string toString(ByteCode byteCode){
	import std.conv;
	int off = 0;
	string r;
	while(off<byteCode.length){
		r~=to!string(off)~": "~to!string(cast(Instruction)byteCode[off]);
		auto args = numArgs(cast(Instruction)byteCode[off]);
		if(byteCode[off]==Instruction.errtbl) break;
		off++;
		if(args==2) r~=" "~to!string(byteCode[off])~", "~to!string(byteCode[off+1]);
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
	assert(stack.length>0);
}body{
Ltailcall:
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
					write(", ",byteCode[ip+2]);
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
			case I.call:
				auto nfargs = cast(size_t)byteCode[ip++];
				FunctionDef def = cast(FunctionDef)cast(void*)stack.pop();
				assert(def.scope_);
				if(def.sstate != SemState.completed) def = def.semantic(def.scope_);
				if(def.sstate != SemState.completed){
					if(def.sstate == SemState.error) throw new Exception("TODO: error!");
					else{assert(def.needRetry); throw new Exception("TODO: retry!");}
				}
				if(byteCode[ip] == I.ret){// tail calls
					// clean up stack
					stack.popFront(nargs);
					byteCode = def.byteCode;
					goto Ltailcall;
				}
				 // TODO: make less hacky
				stack.push(0); stack.pop();
				stack.stp-=nfargs;
				Stack newstack = Stack(stack.stack[stack.stp+1..$], nfargs-1);
				doInterpret(def.byteCode, newstack, handler);
				if(newstack.stack.ptr!=stack.stack.ptr+stack.stp){
					stack.stack = stack.stack[0..stack.stp+1];
					stack.stack.assumeSafeAppend();
					stack.stack~=newstack.stack;
				}
				stack.stp+=newstack.stp+1;
				break;
			case I.ret:
				// clean up stack
				stack.popFront(nargs);
				return;
			// stack control:
			case I.push:
				stack.push(byteCode[ip++]);
				break;
			case I.pop:
				stack.pop();
				break;
			case I.push2:
				stack.push(byteCode[ip++]);
				stack.push(byteCode[ip++]);
				break;
			case I.pop2:
				stack.pop(); stack.pop();
				break;
			case I.popn:
				auto n = byteCode[ip++];
				foreach(i;0..n) stack.pop();
				break;
			case I.pushp:
				stack.push(stack.stack[cast(size_t)byteCode[ip++]]);
				break;
			case I.popp:
				stack.stack[cast(size_t)byteCode[ip++]]=stack.pop();
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
			case I.pushpn:
				auto n   = cast(size_t)byteCode[ip++];
				auto loc = cast(size_t)byteCode[ip++];
				foreach(i;0..n) stack.push(stack.stack[loc++]);
				break;
			case I.poppn:
				auto n   = cast(size_t)byteCode[ip++];
				auto loc = cast(size_t)byteCode[ip++]+n;
				foreach(i;0..n) stack.stack[--loc] = stack.pop();
				break;
			case I.pushr:
				auto loc = cast(size_t)stack.pop();
				stack.push(stack.stack[loc]);
				break;
			case I.popr:
				auto val = stack.pop();
				auto loc = cast(size_t)stack.pop();
				stack.stack[loc] = val;
				break;
			case I.pushr2:
				auto loc = cast(size_t)stack.pop();
				stack.push(stack.stack[loc]);
				stack.push(stack.stack[loc+1]);
				break;
			case I.popr2:
				auto val2 = stack.pop();
				auto val1 = stack.pop();
				auto loc = cast(size_t)stack.pop();
				stack.stack[loc]  =val1;
				stack.stack[loc+1]=val2;
				break;
			case I.pushrn:
				auto n   = cast(size_t)byteCode[ip++];
				auto loc = cast(size_t)stack.pop();
				foreach(i;0..n) stack.push(stack.stack[loc++]);
				break;
			case I.poprkrn:
				keepr = true; goto case I.poprn;
			case I.poprn:
				auto n   = cast(size_t)byteCode[ip++];
				auto loc = cast(size_t)stack.stack[stack.stp-n]+n;
				foreach(i;0..n) stack.stack[--loc]=stack.pop();
				if(keepr) keepr = false;
				else stack.pop(); // throw away loc
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
			case I.poprkvn:
				auto n   = cast(size_t)byteCode[ip]; // pushrn increases ip
				auto loc = cast(size_t)stack.stack[stack.stp-n]+n;
				foreach(i;0..n) stack.stack[--loc]=stack.pop();
				goto case I.pushrn; // restore value
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
			case I.swapn:
				auto n = cast(size_t)byteCode[ip++];
				for(auto i=stack.stp-2*n+1, j=stack.stp-n+1;j<=stack.stp; i++, j++)
					swap(stack.stack[i], stack.stack[j]);
				break;
			case I.dup:
				stack.push(stack.top());
				break;
			case I.dup2:
				stack.push(stack.stack[stack.stp-1]);
				stack.push(stack.stack[stack.stp-1]);
				break;
			case I.dupn:
				auto n = cast(size_t)byteCode[ip++];
				foreach(i;0..n) stack.push(stack.stack[stack.stp-n+1]);
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
				stack.push(cast(bool)stack.pop!real());
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
				if(val){ stack.top()/=val; break; }
				goto Ldivbyzero;
			case I.divsi:
				long val = stack.pop();
				if(val){ stack.top()=cast(long)stack.top()/val; break; }
				goto Ldivbyzero;
			case I.modi:
				auto val = stack.pop();
				if(val){ stack.top()%=val; break; }
				goto Ldivbyzero;
			case I.modsi:
				long val = stack.pop();
				if(val){ stack.top()=cast(long)stack.top()%val; break; }
				goto Ldivbyzero;
			// shifts
			case I.shl32:
				auto val = stack.pop();
				if(val<32){ stack.top()<<=val; break; }
				tmp[0] = val; // shamt
				tmp[1] = 31;  // max shamt
				goto Lshiftoutofrange;
			case I.shr32:
				auto val = stack.pop();
				if(val<32){ stack.top()>>>=val; break; }
				tmp[0] = val; // shamt
				tmp[1] = 31;  // max shamt
				goto Lshiftoutofrange;
			case I.sar32:
				long val = stack.pop();
				if(val<32){ stack.top()=cast(long)stack.top()>>val; break; }
				tmp[0] = val; // shamt
				tmp[1] = 31;  // max shamt
				goto Lshiftoutofrange;
			case I.shl64:
				auto val = stack.pop();
				if(val<64){ stack.top()<<=val; break; }
				tmp[0] = val; // shamt
				tmp[1] = 63;  // max shamt
				goto Lshiftoutofrange;
			case I.shr64:
				auto val = stack.pop();
				if(val<64){ stack.top()>>>=val; break; }
				tmp[0] = val; // shamt
				tmp[1] = 63;  // max shamt
				goto Lshiftoutofrange;
			case I.sar64:
				long val = stack.pop();
				if(val<64){ stack.top()=cast(long)stack.top()>>val; break; }
				tmp[0] = val; // shamt
				tmp[1] = 63;  // max shamt
				goto Lshiftoutofrange;
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
			case I.ptra:
				auto bcs = stack.pop!BCSlice();
				stack.push(bcs.getPtr());
				break;
			case I.lengtha:
				auto bcs = stack.pop!BCSlice();
				stack.push(bcs.getLength());
				break;
			case I.newarray:
				auto els = cast(size_t)byteCode[ip++];
				auto len = cast(size_t)stack.pop();
				stack.push(BCSlice(new void[els*len]));
				break;
			case I.makearray:
				auto els = cast(size_t)byteCode[ip++];
				auto len = cast(size_t)stack.pop();
				assert(els<=32); // todo; fix
				auto stlen = len*((els+ulong.sizeof-1)/ulong.sizeof);
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
					case 24:
						for(size_t i=0,j=0;i<el.length;i+=3,j+=24){
							*cast(ulong*)&r[j]=cast(ulong)el[i];
							*(cast(ulong*)&r[j]+1)=cast(ulong)el[i+1];
							*(cast(ulong*)&r[j]+2)=cast(ulong)el[i+2];
						}
						break;
					case 32:
						for(size_t i=0,j=0;i<el.length;i+=4,j+=32){
							*cast(ulong*)&r[j]=cast(ulong)el[i];
							*(cast(ulong*)&r[j]+1)=cast(ulong)el[i+1];
							*(cast(ulong*)&r[j]+2)=cast(ulong)el[i+2];
							*(cast(ulong*)&r[j]+3)=cast(ulong)el[i+3];
						}
						break;						
					default: assert(0, "unsupported size "~to!string(els));
				}
				stack.pop(stlen);
				stack.push(BCSlice(r));
				break;
			case I.appenda:
				auto arr2 = stack.pop!BCSlice().slice;
				auto arr1 = stack.pop!BCSlice().slice;
				stack.push(BCSlice(arr1 ~= arr2));
				break;
			case I.concata:
				auto arr2 = stack.pop!BCSlice().slice;
				auto arr1 = stack.pop!BCSlice().slice;
				stack.push(BCSlice(arr1 ~ arr2));
				break;
			case I.loadak:
				keepr = true; goto case I.loada;
			case I.loada:
				auto els = cast(size_t)byteCode[ip++];
				auto i = cast(size_t)stack.pop();
				auto bcs = stack.pop!BCSlice();
				if(keepr){
					stack.push(bcs);
					stack.push(i);
					keepr=false;
				}
				auto r = bcs.slice;
				if(i*els>=r.length) {
					tmp[0] = i;            // index
					tmp[1] = r.length/els; // array dimension
					goto Loutofbounds;
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
					case 24:
						stack.push(*cast(ulong*)&r[24*i]);
						stack.push(*(cast(ulong*)&r[24*i]+1));
						stack.push(*(cast(ulong*)&r[24*i]+2));
						break;
					case 32:
						stack.push(*cast(ulong*)&r[32*i]);
						stack.push(*(cast(ulong*)&r[32*i]+1));
						stack.push(*(cast(ulong*)&r[32*i]+2));
						stack.push(*(cast(ulong*)&r[32*i]+3));
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
				auto bcs = stack.pop!BCSlice();
				auto r = bcs.slice;
				if(i*els>=r.length) {
					tmp[0] = i;            // index
					tmp[1] = r.length/els; // array dimension
					goto Loutofbounds;
				}
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
					stack.push(bcs);
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
			case I.slicea:
				auto els = cast(size_t)byteCode[ip++];
				auto r = cast(size_t)stack.pop();
				auto l = cast(size_t)stack.pop();
				auto a = stack.pop!BCSlice();
				if(l*els<=r*els && r*els<=a.slice.length){
					a.slice = a.slice[l*els..r*els];
					stack.push(a);
					break;
				}
				tmp[0] = l;
				tmp[1] = r;
				tmp[2] = a.slice.length/els;
				goto Lsliceoutofbounds;
			// arrays of arrays
			case I.loadaa:
				auto i = cast(size_t)stack.pop();
				auto bcs = stack.pop!BCSlice();
				auto r = cast(BCSlice[])bcs.slice;
				if(i<r.length) { stack.push(r[i]); break; }
				tmp[0] = i;            // index
				tmp[1] = r.length;     // array dimension
				goto Loutofbounds;
			case I.loadaak:
				auto i = cast(size_t)stack.pop();
				auto bcs = stack.pop!BCSlice();
				auto r = cast(BCSlice[])bcs.slice;
				stack.push(bcs);
				stack.push(i);
				if(i<r.length) { stack.push(r[i]); break; }
				tmp[0] = i;            // index
				tmp[1] = r.length;     // array dimension
				goto Loutofbounds;
				break;
			case I.storeaakr:
				keepr = true; goto case I.storeaa;
			case I.storeaakv:
				keepv = true; goto case I.storeaa;
			case I.storeaa:
				auto v = stack.pop!BCSlice();
				auto i = cast(size_t)stack.pop();
				auto bcs = stack.pop!BCSlice();
				auto r = cast(BCSlice[])bcs.slice;
				if(i>=r.length) {
					tmp[0] = i;            // index
					tmp[1] = r.length;     // array dimension
					goto Loutofbounds;
				}
				r[i]=v;
				if(keepr){
					stack.push(bcs);
					stack.push(i);
					keepr = false;
				}
				if(keepv){
					stack.push(v);
					keepv = false;
				}
				break;
			// pointer operations
			case I.loadap:
				auto els = cast(size_t)byteCode[ip++];
				auto i   = cast(size_t)stack.pop();
				auto bcs = stack.pop!BCSlice();
				auto ptr = bcs.getPtr();
				ptr.ptr+=i*els;
				stack.push(ptr);
				break;
			case I.ptrtoa:
				auto r = stack.pop!BCPointer();
				if(r.ptr>=r.container.ptr && r.ptr<r.container.ptr+r.container.length){
					stack.push(BCSlice(r.container, r.ptr[0..r.container.ptr+r.container.length-r.ptr]));
					break;
				}
				tmp[0] = r.ptr is null; // is null
				tmp[1] = r.ptr == r.container.ptr+r.container.length; // off by one at the end
				tmp[2] = cast(ulong)r.ptr;
				tmp[3] = cast(ulong)r.container.ptr; // for checking of off by one at the beg.
				goto Linvalidpointer;
			case I.addp:
				auto els = cast(size_t)byteCode[ip++];
				auto val = cast(size_t)stack.pop();
				auto ptr = stack.pop!BCPointer();
				ptr.ptr+=val*els;
				stack.push(ptr);
				break;
			case I.errtbl:
				assert(0);
		}
	}
	ErrorInfo obtainErrorInfo(){
		size_t i, j;
		for(i=0, j=0;i<ip; i++){
			if(isUnsafe(cast(Instruction)byteCode[i])) j++;
			i+=numArgs(cast(Instruction)byteCode[i]);
		}
		for(; byteCode[i]!=Instruction.errtbl; i++)
			i+=numArgs(cast(Instruction)byteCode[i]);

		return (cast(ErrorInfo[])byteCode[i+1..$])[j-1];
	}
Ldivbyzero:
	auto info0 = obtainErrorInfo();
	handler.error("divide by zero", info0.loc);
	goto Lfail;
Loutofbounds:
	auto info1 = obtainErrorInfo();
	auto s_t = Type.get!Size_t();
	if(s_t.getSizeof()==uint.sizeof) tmp[0] = cast(uint)tmp[0];
	else assert(s_t.getSizeof()==ulong.sizeof);
	handler.error(format("array index %sU is out of bounds [0U..%dU)",tmp[0],tmp[1]),info1.loc);
	goto Lfail;
Lshiftoutofrange:
	auto info2 = obtainErrorInfo();
	bool isSigned;
	if(auto e = cast(BinaryExp!(Tok!"<<"))info2) isSigned=(cast(BasicType)e.e2.type).isSigned();
	else if(auto e = cast(BinaryExp!(Tok!">>"))info2) isSigned=(cast(BasicType)e.e2.type).isSigned();
	else if(auto e = cast(BinaryExp!(Tok!">>>"))info2) isSigned=(cast(BasicType)e.e2.type).isSigned();
	if(isSigned) handler.error(format("shift amount of %d is outside the range 0..%d", cast(long)tmp[0], tmp[1]),info2.loc);
	else handler.error(format("shift amount of %d is outside the range 0..%d", tmp[0], tmp[1]),info2.loc);
	goto Lfail;
Linvalidpointer:
	auto info3 = obtainErrorInfo();
	bool offby1=cast(bool)tmp[1];
	if(!offby1){
		auto exp=cast(Expression)info3;
		if(exp && tmp[2]+getCTSizeof(exp.type)==tmp[3]) offby1 = true;
	}
	handler.error(format("%s pointer dereference%s",tmp[0]?"null":"invalid",offby1?" (off by one)":""), info3.loc);
	goto Lfail;
Lsliceoutofbounds:
	auto info4 = obtainErrorInfo();
	auto s_t2 = Type.get!Size_t();
	if(s_t2.getSizeof()==uint.sizeof) tmp[0]=cast(uint)tmp[0], tmp[1]=cast(uint)tmp[1];
	else assert(s_t2.getSizeof()==ulong.sizeof);
	if(tmp[0]>tmp[2]||tmp[1]>tmp[2]){
		handler.error(format("slice indices [%dU..%dU] are out of bounds [0U..%dU]",tmp[0],tmp[1],tmp[2]),info4.loc);
	}else{
		assert(tmp[0]>tmp[1]);
		handler.error(format("lower slice index %dU exceeds upper slice index %dU",tmp[0],tmp[1]),info4.loc);
	}
	goto Lfail;
Lfail:
	throw new Exception("");
}


mixin template CTFEInterpret(T) if(!is(T==Node)&&!is(T==FunctionDef) && !is(T==EmptyStm) && !is(T==BlockStm) && !is(T==LabeledStm) && !is(T==ExpressionStm) && !is(T==IfStm) && !is(T==ForStm) && !is(T==WhileStm) && !is(T==DoStm) && !is(T==LiteralExp) && !is(T==ArrayLiteralExp) && !is(T==ReturnStm) && !is(T==CastExp) && !is(T==Symbol) && !is(T==ConditionDeclExp) && !is(T==VarDecl) && !is(T==Expression) && !is(T _==BinaryExp!S,TokenType S) && !is(T==ABinaryExp) && !is(T==AssignExp) && !is(T==TernaryExp)&&!is(T _==UnaryExp!S,TokenType S) && !is(T _==PostfixExp!S,TokenType S) &&!is(T==Declarators) && !is(T==BreakStm) && !is(T==ContinueStm) && !is(T==GotoStm) && !is(T==BreakableStm) && !is(T==LoopingStm) && !is(T==SliceExp) && !is(T==CallExp) && !is(T==Declaration)){}


mixin template CTFEInterpret(T) if(is(T==Node)){
	void byteCompile(ref ByteCodeBuilder bld){
		import std.stdio; writeln(this);
		assert(0, to!string(typeid(this)));}
}

mixin template CTFEInterpret(T) if(is(T==Declaration)){
	override void byteCompile(ref ByteCodeBuilder bld){
		/+ do nothing +/
	}

}

mixin template CTFEInterpret(T) if(is(T==Expression)){
	// some expressions can be lvalues
	LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){assert(0, to!string(typeid(this))~" "~to!string(this));}
}

mixin template CTFEInterpret(T) if(is(T==EmptyStm)){
	void byteCompile(ref ByteCodeBuilder bld){ /+ ; +/ }
}

mixin template CTFEInterpret(T) if(is(T _==UnaryExp!S,TokenType S)){
	static if(is(T _==UnaryExp!S,TokenType S)):	
	override void byteCompile(ref ByteCodeBuilder bld){
		alias Instruction I;
		auto tu = e.type.getHeadUnqual();
		static if(S==Tok!"+"){
			assert(tu.isBasicType()||tu.isPointerTy());
			e.byteCompile(bld);
		}else static if(S==Tok!"-"||S==Tok!"~"||S==Tok!"!"){
			assert(tu.isBasicType());
			e.byteCompile(bld);
			if(auto bt = tu.isIntegral()){
				bld.emit(S==Tok!"-"?I.negi:S==Tok!"~"?I.noti:I.notb);
				static if(S==Tok!"!"){if(tu !is Type.get!bool()) bld.emit(I.int2bool);}
				else{
					auto size = bt.bitSize();
					if(size<63){
						bld.emit(bt.isSigned()?I.truncs:I.trunc);
						bld.emitConstant(size);
					}
				}
			}
		}else static if(S==Tok!"++" || S==Tok!"--") byteCompileHelper(bld, false);
		else static if(S==Tok!"&"){
			auto strat = e.byteCompileLV(bld);
			strat.emitPointer(bld);
		}else static if(S==Tok!"*"){
			e.byteCompile(bld);
			bld.emitUnsafe(I.ptrtoa, this);
			bld.emit(I.push);
			bld.emitConstant(0);
			if(type.getHeadUnqual().isDynArrTy()) bld.emitUnsafe(I.loadaa, this);
			else{
				bld.emitUnsafe(I.loada, this);
				bld.emitConstant(getCTSizeof(type));
			}
		}else static assert(0,TokChars!S);
	}

	static if(S==Tok!"*"){
		override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
			e.byteCompile(bld);
			auto ptr=e.type.getHeadUnqual().isPointerTy();
			return LVpointer(ptr.ty, this);
		}
	}

	static if(S==Tok!"++" || S==Tok!"--"):
	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		return byteCompileHelper(bld, true);
	}

	private final LValueStrategy byteCompileHelper(ref ByteCodeBuilder bld, bool isLvalue){
		alias Instruction I;
		auto strat = e.byteCompileLV(bld);
		strat.emitLoadKR(bld);
		if(auto bt = type.isIntegral()){
			bld.emit(I.push);
			bld.emitConstant(1);
			bld.emit(S==Tok!"++"?I.addi:I.subi);
			auto size = bt.bitSize();
			if(size < 64){
				bld.emit(bt.isSigned()?I.truncs:I.trunc);
				bld.emitConstant(size);
			}
		}else if(auto ptr = type.isPointerTy()){
			bld.emit(I.push);
			bld.emitConstant(S==Tok!"++"?1:-1);
			bld.emit(I.addp);
			bld.emitConstant(getCTSizeof(ptr.ty));
		}else assert(0);
		if(isLvalue){
			strat.emitStoreKR(bld);
			return strat;
		}else{
			strat.emitStoreKV(bld);
			return null;
		}
	}
}

mixin template CTFEInterpret(T) if(is(T _==PostfixExp!S,TokenType S)){
	static if(is(T _==PostfixExp!S,TokenType S)):
	static assert(S==Tok!"++"||S==Tok!"--");
	override void byteCompile(ref ByteCodeBuilder bld){
		bld.emit(Instruction.nop);
		alias Instruction I;
		auto strat = e.byteCompileLV(bld);
		strat.emitLoadKR(bld);
		auto tu = e.type.getHeadUnqual();
		auto siz = getBCSizeof(tu);
		bld.emitDup(siz);
		bld.emit(I.push);
		bld.emitConstant(S==Tok!"++"?1:-1);
		if(auto bt = tu.isIntegral()){
			assert(bt.getSizeof()<=8);
			bld.emit(I.addi);
			auto size = bt.bitSize();
			if(size < 64){
				bld.emit(bt.isSigned()?I.truncs:I.trunc);
				bld.emitConstant(size);
			}
		}else if(auto ptr = tu.isPointerTy()){
			bld.emit(I.addp);
			bld.emitConstant(getCTSizeof(ptr.ty));
		}else{super.byteCompile(bld); assert(0);} // TODO: fix!
		bld.emitSwap(siz);
		bld.emitTmppush(siz);
		strat.emitStore(bld);
		bld.emitTmppop(siz);
	}
}

// workaround for DMD bug, other part is in expression.IndexExp
mixin template CTFEInterpretIE(T) if(is(T _==IndexExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		alias Instruction I;
		assert(a.length == 1);
		e.byteCompile(bld);
		a[0].byteCompile(bld);
		static if(size_t.sizeof>uint.sizeof){
			// compiler has larger size_t than target.
			auto t_siz=getCTSizeof(a[0].type);
			if(t_siz<size_t.sizeof){
				bld.emit(I.truncs);
				bld.emitConstant(t_siz*8);
			}
		}
		auto siz = getCTSizeof(type);
		if(e.type.getHeadUnqual().isPointerTy()){
			bld.emit(I.addp);
			bld.emitConstant(siz);
			bld.emitUnsafe(I.ptrtoa, this);
			bld.emit(I.push);
			bld.emitConstant(0);
		}
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
			bld.emitUnsafe(I.loadaa, this);
			return;
		}
		bld.emitUnsafe(I.loada, this);
		bld.emitConstant(siz);
	}

	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		alias Instruction I;
		assert(a.length == 1);
		e.byteCompile(bld);
		// TODO: static arrays
		a[0].byteCompile(bld);
		auto siz = getCTSizeof(type);
		static if(size_t.sizeof>uint.sizeof){
			// compiler has larger size_t than target.
			auto t_siz=getCTSizeof(a[0].type);
			if(t_siz<size_t.sizeof){
				bld.emit(I.truncs);
				bld.emitConstant(t_siz*8);
			}
		}
		if(e.type.getHeadUnqual().isPointerTy()){
			bld.emit(I.addp);
			bld.emitConstant(siz);
			return LVpointer(type, this);
		}
		return LVstorea(type, this);
	}
}

mixin template CTFEInterpret(T) if(is(T==SliceExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		e.byteCompile(bld);
		// TODO: static arrays
		l.byteCompile(bld);
		Type elm;
		ulong siz;
		static if(size_t.sizeof>uint.sizeof){
			// compiler has larger size_t than target.
			auto t_siz=getCTSizeof(l.type);
			if(t_siz<size_t.sizeof){
				bld.emit(Instruction.truncs);
				bld.emitConstant(t_siz*8);
			}
		}
		if(auto ptr = e.type.getHeadUnqual().isPointerTy()){
			elm = ptr.ty;
			siz = getCTSizeof(elm);
			bld.emit(Instruction.dup);
			bld.emit(Instruction.tmppush);
			bld.emit(Instruction.addp);
			bld.emitConstant(siz);
			bld.emitUnsafe(Instruction.ptrtoa, this);
			bld.emit(Instruction.push);
			bld.emitConstant(0);
			r.byteCompile(bld);
			static if(size_t.sizeof>uint.sizeof){
				if(t_siz<size_t.sizeof){
					bld.emit(Instruction.truncs);
					bld.emitConstant(t_siz*8);
				}
			}
			bld.emit(Instruction.tmppop);
			bld.emit(Instruction.subi);
		}else{
			elm=e.type.getElementType();
			siz = getCTSizeof(elm);
			r.byteCompile(bld);
			static if(size_t.sizeof>uint.sizeof){
				if(t_siz<size_t.sizeof){
					bld.emit(Instruction.truncs);
					bld.emitConstant(t_siz*8);
				}
			}
		}
		bld.emitUnsafe(Instruction.slicea, this);
		bld.emitConstant(siz);
	}
}

mixin template CTFEInterpret(T) if(is(T==ABinaryExp)||is(T==AssignExp)){}
mixin template CTFEInterpret(T) if(is(T _==BinaryExp!S,TokenType S)){
	static if(is(T _==BinaryExp!S,TokenType S)):
	static if(S!=Tok!"."):
	override void byteCompile(ref ByteCodeBuilder bld){
		byteCompileHelper(bld, false);
	}

	static if(isAssignOp(S) && S!=Tok!"=")
	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		return byteCompileHelper(bld, true);
	}

	private LValueStrategy byteCompileHelper(ref ByteCodeBuilder bld, bool isLvalue) in{assert(!isLvalue || isAssignOp(S) && S!=Tok!"=");}body{
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

			if(auto ptr=type.isPointerTy()){
				static if(S==Tok!"+"){
					if(e2.type.isIntegral()){
						e1.byteCompile(bld);
						e2.byteCompile(bld);
					}else{
						assert(e1.type.isIntegral());
						e2.byteCompile(bld);
						e1.byteCompile(bld);
					}
					bld.emit(I.addp);
					bld.emitConstant(getCTSizeof(ptr.ty));
					assert(!isLvalue);
					return null;
				}else static if(S==Tok!"-"){
					e1.byteCompile(bld);
					e2.byteCompile(bld);
					bld.emit(I.negi);
					bld.emit(I.addp);
					bld.emitConstant(getCTSizeof(ptr.ty));
					assert(!isLvalue);
					return null;
				}else static if(S==Tok!"+="||S==Tok!"-="){
					assert(e2.type.isIntegral());
					auto strat = e1.byteCompileLV(bld);
					strat.emitLoadKR(bld);
					e2.byteCompile(bld);
					static if(S==Tok!"-=") bld.emit(I.negi);
					bld.emit(I.addp);
					bld.emitConstant(getCTSizeof(ptr.ty));
					if(!isLvalue){ strat.emitStore(bld); return null; }
					else{ strat.emitStoreKR(bld); return strat; }
				}
			}else{
				assert(type.isBasicType());
				static if(S!=Tok!"<<"&&S!=Tok!">>"&&S!=Tok!">>>") assert(e1.type is e2.type);
			}

			static if(isAssignOp(S)){
				auto strat = e1.byteCompileLV(bld);
				strat.emitLoadKR(bld);
				enum op = TokChars!S[0..$-1];
			}else{
				e1.byteCompile(bld);
				enum op = TokChars!S;
			}
			e2.byteCompile(bld);


			if(auto bt=e1.type.getUnqual().isBasicType()){
				assert(!isShiftOp(S) && !isBitwiseOp(S) || bt.isIntegral());
				auto size = bt.bitSize(), signed = bt.isSigned();
				static if(op=="<<"||op==">>"||op==">>>"){
					bool isNarrow = size == 32;
					assert(isNarrow || size == 64);
				}
				static if(op=="+") bld.emit(I.addi);
				else static if(op=="-") bld.emit(I.subi);
				else static if(op=="*") bld.emit(I.muli);
				else static if(op=="/") bld.emitUnsafe(signed?I.divsi:I.divi, this);
				else static if(op=="%") bld.emitUnsafe(signed?I.modsi:I.modi, this);
				else static if(op=="^^") assert(0, "TODO (?)");
				else static if(op=="<<") bld.emitUnsafe(isNarrow?I.shl32:I.shl64, this);
				else static if(op==">>"){
					if(signed) bld.emitUnsafe(isNarrow?I.sar32:I.sar64, this);
					else bld.emitUnsafe(isNarrow?I.shr32:I.shr64, this);
				}else static if(op==">>>") bld.emitUnsafe(isNarrow?I.shr32:I.shr64, this);
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
				if(S!=Tok!"=" && !isBitwiseOp(S) && !isRelationalOp(S) && size<64){
					bld.emit(signed?I.truncs:I.trunc);
					bld.emitConstant(size);
				}
				static if(isAssignOp(S)){
					if(!isLvalue){ strat.emitStoreKV(bld); return null; }
					else{ strat.emitStoreKR(bld); return strat; }
				}
			}else{
				// TODO: operators for all built-in types
				super.byteCompile(bld);
				return null;
			}
		}else static if(S==Tok!"||"||S==Tok!"&&"){
			assert(e1.type is Type.get!bool());
			e1.byteCompile(bld);
			auto tu = type.getHeadUnqual();
			bool keepresult = tu is Type.get!bool();
			if(keepresult) bld.emit(I.dup);
			else assert(tu is Type.get!void());
			bld.emit(S==Tok!"||"?I.jnz:I.jz);
			auto end=bld.emitLabel();
			if(keepresult) bld.emit(I.pop);
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
			bld.emit(I.nop);
			auto strat = e1.byteCompileLV(bld);
			bld.emit(I.nop);
			strat.emitLoadKR(bld);
			e2.byteCompile(bld);
			if(e2.type is e1.type.getElementType())
				emitMakeArray(bld,e1.type,1);
			bld.emit(I.appenda);
			if(!isLvalue){ strat.emitStoreKV(bld); return null; }
			else{ strat.emitStoreKR(bld); return strat; }
		}else super.byteCompile(bld);

		assert(!isLvalue);
		return null;
	}
}

mixin template CTFEInterpret(T) if(is(T==TernaryExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		alias Instruction I;
		e1.byteCompile(bld);
		bld.emit(I.jz);
		auto otherwise=bld.emitLabel();
		e2.byteCompile(bld);
		bld.emit(I.jmp);
		auto end=bld.emitLabel();
		otherwise.here();
		e3.byteCompile(bld);
		end.here();
	}

	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		alias Instruction I;
		e1.byteCompile(bld);
		bld.emit(I.jz);
		auto otherwise=bld.emitLabel();
		auto strat1=e2.byteCompileLV(bld);
		bld.emit(I.push);
		bld.emitConstant(1);
		bld.emit(I.tmppush);
		bld.emit(I.jmp);
		auto end=bld.emitLabel();
		otherwise.here();
		auto strat2=e3.byteCompileLV(bld);
		bld.emit(I.push);
		bld.emitConstant(0);
		bld.emit(I.tmppush);
		end.here();
		return LVconditional(strat1, strat2);
	}
}

mixin template CTFEInterpret(T) if(is(T==BlockStm)){
	override void byteCompile(ref ByteCodeBuilder bld){ foreach(x; s) x.byteCompile(bld); }
}
mixin template CTFEInterpret(T) if(is(T==LabeledStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		if(!bclabel.initialized()) bclabel = bld.getLabel();
		bclabel.here();
		s.byteCompile(bld);
	}
	ref ByteCodeBuilder.Label getBCLabel(ref ByteCodeBuilder bld){
		if(!bclabel.initialized()) bclabel = bld.getLabel();
		return bclabel;
	}
private:
	ByteCodeBuilder.Label bclabel;
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

mixin template CTFEInterpret(T) if(is(T==BreakableStm)){
protected:
	final void setBCEnd(ByteCodeBuilder.Label* end){ bcend = end; }
	final void emitBCEnd(ref ByteCodeBuilder bld){bld.emitLabel(*bcend);}
	final void cleanupBCEnd(){ bcend = null; }
	enum doBCEnd = q{
		auto end = bld.getLabel();
		setBCEnd(&end);
		scope(exit){
			end.here();
			cleanupBCEnd();
		}
	};
private:
	ByteCodeBuilder.Label* bcend;
}
mixin template CTFEInterpret(T) if(is(T==LoopingStm)){
protected:
	final void setBCStart(ulong start){ bcstart = start; }
	void emitBCContinueLabel(ref ByteCodeBuilder bld){ bld.emitConstant(bcstart); }
	enum doBCStart = q{
		auto start = bld.getLocation();
		setBCStart(start);
	};
private:
	ulong bcstart;
}

mixin template CTFEInterpret(T) if(is(T==WhileStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		mixin(doBCStart~doBCEnd);
		e.byteCompile(bld);
		bld.emit(Instruction.jz);
		bld.emitLabel(end);
		s.byteCompile(bld);
		bld.emit(Instruction.jmp);
		bld.emitConstant(start);
	}
}

mixin template CTFEInterpret(T) if(is(T==DoStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		mixin(doBCStart~doBCEnd);
		s.byteCompile(bld);
		e.byteCompile(bld);
		bld.emit(Instruction.jnz);
		bld.emitConstant(start);
	}
}

mixin template CTFEInterpret(T) if(is(T==ForStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		s1.byteCompile(bld);
		mixin(doBCStart~doBCEnd);
		auto bccnt = bld.getLabel();
		bccontinue = &bccnt; scope(exit) bccontinue = null;
		if(e1){
			e1.byteCompile(bld);
			bld.emit(Instruction.jz);
			bld.emitLabel(end);
		}
		s2.byteCompile(bld);
		bccnt.here();
		if(e2){
			e2.byteCompile(bld);
			bld.ignoreResult(getBCSizeof(e2.type));
		}
		bld.emit(Instruction.jmp);
		bld.emitConstant(start);
	}
	override void emitBCContinueLabel(ref ByteCodeBuilder bld){
		bld.emitLabel(*bccontinue);
	}
private:
	ByteCodeBuilder.Label* bccontinue;
}

mixin template CTFEInterpret(T) if(is(T==ReturnStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		if(e) e.byteCompile(bld);
		bld.emit(Instruction.ret);
	}
}

mixin template CTFEInterpret(T) if(is(T==ContinueStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		bld.emit(Instruction.jmp);
		theLoop.emitBCContinueLabel(bld);
	}
}
mixin template CTFEInterpret(T) if(is(T==BreakStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		bld.emit(Instruction.jmp);
		brokenOne.emitBCEnd(bld);
	}
}
mixin template CTFEInterpret(T) if(is(T==GotoStm)){
	override void byteCompile(ref ByteCodeBuilder bld){
		bld.emit(Instruction.jmp);
		bld.emitLabel(target.getBCLabel(bld));
	}
}

mixin template CTFEInterpret(T) if(is(T==LiteralExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		auto tu = type.getHeadUnqual();
		if(auto bt = tu.isBasicType()){
			if(bt.isIntegral()){
				bld.emit(Instruction.push);
				if(bt.isSigned()) bld.emitConstant(cast(int)value.get!ulong());
				else bld.emitConstant(cast(uint)value.get!ulong());
				return;
			}else if(tu is Type.get!float()||type is Type.get!ifloat()){
				bld.emit(Instruction.push);
				bld.emitConstant(value.get!float());
				return;
			}else if(tu is Type.get!double()||type is Type.get!idouble()){
				bld.emit(Instruction.push);
				bld.emitConstant(value.get!double());
				return;
			}else if(tu is Type.get!real()||type is Type.get!ireal()){
				bld.emit(Instruction.push2);
				bld.emitConstant(value.get!real());
				return;
			}
		}else if(tu.getElementType()){
			auto r = value.get!BCSlice();
			assert(!bcSaveFromGC);
			bcSaveFromGC = r.container.ptr;
			size_t size = getBCSizeof(tu);
			assert(!(size&1));
			for(size_t i=0;i<size;i+=2){
				bld.emit(Instruction.push2);
				bld.emitConstant(*(cast(ulong*)&r+i));
				bld.emitConstant(*(cast(ulong*)&r+i+1));				
			}
			return;
		}
		bld.error(format("cannot interpret %s during compile time yet.",toString()), loc);
	}
private:
	void* bcSaveFromGC;
}

void emitMakeArray(ref ByteCodeBuilder bld, Type ty, ulong elems)in{
	assert(ty.getElementType());
}body{
	alias Instruction I;
	ty = ty.getElementType().getHeadUnqual();
	bld.emit(I.push);
	bld.emitConstant(elems);
	bld.emit(I.makearray);
	bld.emitConstant(getCTSizeof(ty));
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
					bld.emit(from.isSigned() ? I.int2real : I.uint2real);
					static if(!is(T==real)) bld.emit(mixin(`I.real2`~T.stringof));
					return;
				}
			}
		}else foreach(T; TypeTuple!(float, double, real)){
			if(t1 is Type.get!T()){
				if(auto to=t2.isIntegral()){
					static if(!is(T==real)) bld.emit(mixin(`I.`~T.stringof~`2real`));
					if(to is Type.get!bool()){
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
		// TODO: sanity check for array cast alignment
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
				assert(~off && len && len<=4); // TODO: do hlt instead
				bld.emitPushp(len);
				bld.emitConstant(off);
				if(vd.addressTaken){
					bld.emitUnsafe(Instruction.ptrtoa, this);
					bld.emit(Instruction.push);
					bld.emitConstant(0);
					bld.emitUnsafe(Instruction.loada, this);
					bld.emitConstant(getCTSizeof(vd.type));
				}
			}
			return;
		}else if(auto fd=meaning.isFunctionDef()){
			static assert(fd.sizeof<=(void*).sizeof&&(void*).sizeof<=ulong.sizeof);
			bld.emit(Instruction.push);
			bld.emitConstant(cast(ulong)cast(void*)fd);
			return;
		}
		import std.stdio; writeln(meaning.isFunctionDef());
		bld.error(format("cannot interpret symbol '%s' at compile time", toString()), loc);
	}
	override LValueStrategy byteCompileLV(ref ByteCodeBuilder bld){
		if(auto vd = meaning.isVarDecl()){
			// TODO: nested functions, global immutable variables
			size_t len;
			auto off = vd.getBCStackLoc(len);
			if(!vd.addressTaken){
				bld.emit(Instruction.push);
				bld.emitConstant(off);
				return LVpopr(len);
			}else{
				auto ty = vd.type.getHeadUnqual();
				bld.emit(Instruction.push);
				bld.emitConstant(off);
				bld.emitPushr(getBCSizeof(ty.getPointer()));
				bld.emitUnsafe(Instruction.ptrtoa, this);
				bld.emit(Instruction.push);
				bld.emitConstant(0);
				return LVstorea(ty, this);
			}
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
	type = type.getHeadUnqual();
	if(auto bt = type.isBasicType()){
		if(bt.op == Tok!"void") return 0;
		return (bt.bitSize()+63)/64;
	}
	if(type.isDynArrTy()) return (BCSlice.sizeof+ulong.sizeof-1)/ulong.sizeof;
	if(type.isPointerTy()) return (BCPointer.sizeof+ulong.sizeof-1)/ulong.sizeof;
	return -1;
}
// get compile time size of a type in bytes
size_t getCTSizeof(Type type){
	if(type.getHeadUnqual().isDynArrTy()) return BCSlice.sizeof;
	if(type.getHeadUnqual().isPointerTy()) return BCPointer.sizeof;
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
			if(init) init.byteCompile(bld); // TODO: in semantic, add correct 'init's
			else foreach(i;0..len){bld.emit(Instruction.push); bld.emitConstant(0);}
			import std.stdio;
			if(!addressTaken){
				bld.emitPopp(len);
				bld.emitConstant(off);
				setBCStackLoc(off, len);
				bld.addStackOffset(len);
				return;
			}
			// TODO: must allocate all of these together in one go
			emitMakeArray(bld, type.getDynArr(), 1);
			auto ptrlen = getBCSizeof(type.getPointer());
			bld.emit(Instruction.ptra);
			bld.emitPopp(ptrlen);
			bld.emitConstant(off);
			setBCStackLoc(off, ptrlen);
			bld.addStackOffset(ptrlen);
			return;
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

	bool addressTaken = false;
private:
	size_t byteCodeStackOffset = -1;
	size_t byteCodeStackLength = 0;
}

mixin template CTFEInterpret(T) if(is(T==FunctionDef)){
	private ByteCode _byteCode;
	private ErrorInfo[] bcErrtbl; // keep references for GC

	private size_t bcnumargs=-1;

	private void bcpreanalyze(bool nostacklocs=false){
		static struct MarkAddressTaken{
			enum manualPropagate = true;
			void perform(Symbol self){
				if(auto vd = self.meaning.isVarDecl())
					vd.addressTaken = true;
			}
			void perform(UnaryExp!(Tok!"++") self){
				runAnalysis!MarkAddressTaken(self.e);
			}
			void perform(UnaryExp!(Tok!"--") self){
				runAnalysis!MarkAddressTaken(self.e);
			}
			void perform(TernaryExp self){
				runAnalysis!MarkAddressTaken(self.e2);
				runAnalysis!MarkAddressTaken(self.e3);
			}
			void perform(IndexExp self){
				if(self.type.isArrayTy())
					runAnalysis!MarkAddressTaken(self.e);
			}
			// interestingly, assignexp is not an lvalue in D!
		}
		static struct AddressTakenAnalysis{
			void perform(UnaryExp!(Tok!"&") self){
				runAnalysis!MarkAddressTaken(self.e);
			}
		}
		runAnalysis!AddressTakenAnalysis(this);

		if(~bcnumargs||nostacklocs) return;

		size_t loc = 0, len = 0;
		foreach(i,x; type.params){
			auto ty = x.type.getHeadUnqual();
			if(x.addressTaken) len = getBCSizeof(ty.getPointer());
			else len = getBCSizeof(ty);
			x.setBCStackLoc(loc, len);
			loc+=len;
		}
		bcnumargs = loc;
	}

	@property ByteCode byteCode(){
		if(_byteCode is null){
			ByteCodeBuilder bld;
			if(bcnumargs == -1) bcpreanalyze();
			bld.addStackOffset(bcnumargs); // leave room for locals
			auto alloca = bld.emitAlloca(); // reserve local variables
			bdy.byteCompile(bld);
			alloca.done();
			_byteCode = bld.getByteCode();
			bcErrtbl = bld.getErrtbl();
			if(_displayByteCode){
				import std.stdio; writeln("byteCode for ",name,":\n",_byteCode.toString());
			}
		}
		return _byteCode;
	}

	final Variant interpretCall(Variant[] args, ErrorHandler handler)in{
		assert(sstate == SemState.completed);
		assert(type.params.length == args.length);
	}body{
		ulong[100] stackst;
		auto stack=Stack(stackst[]);

		bcpreanalyze(true);

		foreach(i,x; type.params){
			auto ty = x.type.getHeadUnqual();
			if(x.addressTaken){
				stack.push(Variant([args[i]]).get!BCSlice().getPtr());
				auto len = getBCSizeof(ty.getPointer());
				x.setBCStackLoc(stack.stp-len+1, len);
			}else{
				if(auto bt = ty.isIntegral()){
					stack.push(args[i].get!ulong());
					goto paramok;
				}else if(ty is Type.get!float() || ty is Type.get!ifloat()){
					stack.push(args[i].get!float());
					goto paramok;
				}else if(ty is Type.get!double() || ty is Type.get!idouble()){
					stack.push(args[i].get!double());
					goto paramok;
				}else if(ty is Type.get!real() || ty is Type.get!ireal()){
					stack.push(args[i].get!real());
					goto paramok;
				}
				if(ty.getElementType()){
					stack.push(args[i].get!BCSlice());
					goto paramok;
				}
				assert(0, "unsupported argument type "~x.type.toString());
			paramok:;
				auto len = getBCSizeof(ty);
				x.setBCStackLoc(stack.stp-len+1, len);
			}
		}
		bcnumargs = stack.stp+1;

		byteCode.doInterpret(stack, handler);

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
		}
		if(ret.getElementType()) return Variant.fromBCSlice(stack.pop!BCSlice(),ret);
		assert(0,"unsupported return type "~type.ret.toString());
	}

	// final override void byteCompile(ref ByteCodeBuilder bld){ }
}

mixin template CTFEInterpret(T) if(is(T==CallExp)){
	override void byteCompile(ref ByteCodeBuilder bld){
		foreach(x;args) x.byteCompile(bld);
		e.byteCompile(bld);
		bld.emit(Instruction.call);
		bld.emitConstant(reduce!((a,b)=>a+getBCSizeof(b.type))(0UL,args));
	}
}

