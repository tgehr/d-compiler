
import std.array, std.conv, std.algorithm, std.string;

import lexer, parser, expression, statement, declaration, scope_, util;

public import operators;

string uniqueIdent(string base){
	shared static id=0;
	return base~to!string(id++);
}
// helper macros

template PropErr(string s){ // propagate the 'error' semantic state TODO: maybe exceptions?
	enum PropErr={
		string r;
		auto ss=s.split(",");
		foreach(t;ss){
			r~=mixin(X!q{
				static if(is(typeof(@(t)): Node)){
					if(@(t).sstate==SemState.error){
						sstate=SemState.error;
						return this;
					}
				}else{
					foreach(x;@(t)){
						if(x.sstate==SemState.error){
							sstate=SemState.error;
							return this;
						}
					}
				}
			});
		}
		return r;
	}();
}

template SemChld(string s){ // perform semantic analysis on child node, propagate all errors
	enum SemChld={
		string r;
		auto ss=s.split(",");
		foreach(t;ss){
			r~=mixin(X!q{
				static if(is(typeof(@(t)): Node)) @(t)=@(t).semantic(sc);
				else foreach(ref x;@(t)){x=x.semantic(sc);};
			});
		}
		return r~PropErr!s;
	}();
}

template SemChldExp(string s){ // perform semantic analysis on child node, require that it is an expression
	enum SemChldExp={
		string r;
		auto ss=s.split(",");
		foreach(t;ss){
			r~=mixin(X!q{
				static if(is(typeof(@(t)): Node)) @(t)=@(t).expSemantic(sc);
				else foreach(ref x;@(t)){x=x.expSemantic(sc);};
			});
		}
		return r~PropErr!s;
	}();
}


enum SemState{
	error,
	fwdRefs,
	pre,
	begin,
	started,
	completed,
}

enum SemPrlg=q{
	if(sstate == SemState.completed || sstate == SemState.error) return this;
	//if(sstate>SemState.begin){sc.error("cyclic dependency",loc);sstate=SemState.error;return this;}
};
enum SemEplg=q{
	sstate = SemState.completed;
	return this;
};
enum ErrEplg=q{
	sstate=SemState.error;
	return this;
};
template Semantic(T) if(is(T==Node)){
	Node semantic(Scope s)in{assert(sstate>=SemState.begin);}body{
		s.error("unimplemented feature",loc);
		sstate = SemState.error;
		return this;
	}
}

// error nodes (TODO: file bug against covariance error)

mixin template Semantic(T) if(is(T==ErrorDecl)||is(T==ErrorExp)||is(T==ErrorStm)||is(T==ErrorTy)){
	override T semantic(Scope sc){ return this; } // DMD compiler bug: T is required
	static if(is(T:Declaration)):
	override T presemantic(Scope sc){
		scope_ = sc;
		return this;
	}
}


// expressions
mixin template Semantic(T) if(is(T==Expression)){
	Type type;
	override Expression semantic(Scope sc){ sc.error("unimplemented feature",loc); sstate = SemState.error; return this; }

	Type typeSemantic(Scope sc){
		Expression me;
		if(sstate != SemState.completed){ // TODO: is this ok?
			me = semantic(sc);
			if(me.sstate == SemState.error) return New!ErrorTy();
			if(auto ty=me.isType()) return ty;
		}else me=this;
		sc.error(format("%s '%s' is used as a type",me.kind,me.loc.rep),me.loc);
		return New!ErrorTy();
	}

	final Expression expSemantic(Scope sc){
		auto f = semantic(sc);
		mixin(PropErr!q{f});
		if(f.isType()){
			sc.error(format("%s '%s' is not an expression", kind, loc.rep), loc);
			mixin(ErrEplg);
		}
		return f;
	}

	Expression isLvalue(){return null;}
	final Expression implicitlyConvertTo(Type to)in{assert(to.sstate == SemState.completed);}body{
		if(type is to) return this;
		auto r = New!ImplicitCastExp(to,this);

		r.loc = loc;
		return r;
	}
	final bool checkMutate(Scope sc, const ref Location l){
		if(isLvalue()){
			if(type.isMutable()) return true;
			else sc.error(format("%s '%s' of type '%s' is read-only",kind,loc.rep,type),l);
		}else sc.error(format("%s '%s' is not an lvalue",kind,loc.rep),l);
		return false;
	}
	final Expression convertTo(Type to){
		if(type is to) return this;
		auto r = New!CastExp(STC.init,to,this);
		r.loc = loc;
		return r;
	}
	bool implicitlyConvertsTo(Type rhs){
		if(type.implicitlyConvertsTo(rhs)) return true;
		auto l = type.getHeadUnqual().isIntegral(), r = rhs.getHeadUnqual().isIntegral();
		if(l && r){
			// TODO: fix this. This is not yet right
			if(l.op == Tok!"long" || l.op == Tok!"ulong") return r.getLongRange().contains(getLongRange());
			return r.getIntRange().contains(this.getIntRange());
		}
		return false;
	}

	Expression matchCall(Expression[] args, ref MatchContext context){
		return null;
	}
	void matchError(Scope sc, Location loc, Expression[] args){
		sc.error(format("%s '%s' is not callable",kind,toString()),loc);
	}

	IntRange getIntRange(){return type.getIntRange();}
	LongRange getLongRange(){return type.getLongRange();}
}

mixin template Semantic(T) if(is(T==LiteralExp)){
	override Expression semantic(Scope sc){
		switch(lit.type){ // TODO: remove some boilerplate
			case Tok!"``":
				type=Type.get!(immutable(char)[])(); break;
			case Tok!"``c":
				type=Type.get!(immutable(char)[])(); break;
			case Tok!"``w":
				type=Type.get!(immutable(wchar)[])(); break;
			case Tok!"``d":
				type=Type.get!(immutable(dchar)[])(); break;
			case Tok!"''":
				if(lit.int64<128) type=Type.get!char();
				else type=Type.get!dchar(); break;
			case Tok!"0":
				type=Type.get!int(); break;
			case Tok!"0U":
				type=Type.get!uint(); break;
			case Tok!"0L":
				type=Type.get!long(); break;
			case Tok!"0LU":
				type=Type.get!ulong(); break;
			case Tok!".0f":
				type=Type.get!float(); break;
			case Tok!".0":
				type=Type.get!double(); break;
			case Tok!".0L":
				type=Type.get!real(); break;
			case Tok!".0fi":
				type=Type.get!ifloat(); break;
			case Tok!".0i":
				type=Type.get!idouble(); break;
			case Tok!".0Li":
				type=Type.get!ireal(); break;
			case Tok!"null":
				type=Type.get!Null(); break;
			case Tok!"true", Tok!"false":
				type=Type.get!bool(); break;
				lit.int64=lit.type == Tok!"true";
			default: return super.semantic(sc); // TODO: verify
		}
		mixin(SemEplg);
	}

	override bool implicitlyConvertsTo(Type rhs){
		if(super.implicitlyConvertsTo(rhs)) return true;
		if(lit.type != Tok!"``") return false;
		// resolve the literal type
		if(rhs is Type.get!(immutable(dchar)[])()) lit.type = Tok!"``d";
		else if(rhs is Type.get!(immutable(wchar)[])()) lit.type = Tok!"``w";
		else return false;
		type = rhs;
		return true;
	}

	override IntRange getIntRange(){
		switch(lit.type){
			case Tok!"''":
				if(lit.int64<128) goto case Tok!"0";
				goto case Tok!"0U";
			case Tok!"0", Tok!"true", Tok!"false":
				return IntRange(cast(int)lit.int64,cast(int)lit.int64,true);
			case Tok!"0U":
				return IntRange(cast(uint)lit.int64,cast(uint)lit.int64,false);
			default: return super.getIntRange();
		}
	}
	override LongRange getLongRange(){
		bool signed=true;
		switch(lit.type){
			case Tok!"0LU": signed=false; goto case;
			case Tok!"''", Tok!"0", Tok!"0U", Tok!"0L":
			case Tok!"true", Tok!"false":
				return LongRange(lit.int64,lit.int64,signed);
			default: return super.getLongRange();
		}
	}
}

enum Match{
	none,
	conversion,
	convConst,
	exact,
}
enum InoutRes{
	none,
	mutable,
	immutable_,
	const_,
	inout_,
	inoutConst, // inout(const(T))
}
// enum member functions would be nice
InoutRes mergeIR(InoutRes ir1, InoutRes ir2){
	if(ir1 == ir2) return ir1;
	if(ir1 == InoutRes.none) return ir2;
	if(ir2 == InoutRes.none) return ir1;
	return InoutRes.const_;
}
struct MatchContext{
	auto inoutRes = InoutRes.none;
	auto match = Match.exact;
}


mixin template Semantic(T) if(is(T==ArrayLiteralExp)){
	override Expression semantic(Scope sc){
		if(!lit.length){type=Type.get!EmptyArray(); sstate=SemState.completed; return this;}
		mixin(SemChld!q{lit});
		auto ty=lit[0].type;
		foreach(x;lit[1..$]){
			// TODO: implicit casts
			if(auto newty=ty.combine(x.type)) ty=newty;
			else{sc.error(format("incompatible type '%s' in array of '%s'",x.type,ty),x.loc); sstate=SemState.error; return this;}
		}
		type=ty.getDynArr();
		mixin(SemEplg);
	}

	override bool implicitlyConvertsTo(Type rhs){
		if(super.implicitlyConvertsTo(rhs)) return true;
		Type et = null;
		rhs = rhs.getHeadUnqual();
		if(auto da = rhs.isDynArrTy()) et = da.ty;
		else if(auto ar = rhs.isArrayTy()) et = ar.ty;
		if(!et) return false;
		foreach(x; lit) if(!x.implicitlyConvertsTo(et)) return false;
		return true;
	}
}

mixin template Semantic(T) if(is(T _==PostfixExp!S,TokenType S)){
	static if(is(T _==PostfixExp!S,TokenType S)):
	static assert(S==Tok!"++" || S==Tok!"--");
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChldExp!q{e});
		if(e.checkMutate(sc,loc)){
			auto v = Type.get!void();
			auto ty = e.type.getHeadUnqual();
			if((ty.isBasicType() && e !is v)||ty.isPointerTy()){
				type = e.type;
				mixin(SemEplg);
			}
		}else mixin(ErrEplg);
		sc.error(format("type '%s' does not support postfix "~TokChars!op,e.type),loc);
		mixin(ErrEplg);
	}
}

mixin template Semantic(T) if(is(T==IndexExp)){
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e,a});
		if(auto ty=e.isType()){
			// TODO: TypeTuple slice
			if(!a.length) return ty.getDynArr();
			return super.semantic(sc); // TODO: implement
		}else{
			auto ty = e.type.getHeadUnqual();
			if(auto dyn=ty.isDynArrTy()){
				type = dyn.ty;
			}else if(auto arr=ty.isArrayTy()){
				// TODO: sanity check against length
				type = arr.ty;
			}else if(auto ptr=ty.isPointerTy()){
				if(!a.length){
					sc.error("need bounds to slice pointer", loc);
					mixin(ErrEplg);
				}
				type = ptr.ty;
			}else{ // TODO: operator overloading
				sc.error(format("'%s' is not indexable", e.type),loc);
				mixin(ErrEplg);
			} // it is a dynamic array, an array or pointer type
			if(!a.length) type = type.getDynArr();
			else if(a.length>1){
				sc.error(format("can only use one index to index '%s'",e.type),a[1].loc.to(a[$-1].loc));
				a[0] = a[0].implicitlyConvertTo(Type.get!Size_t()).semantic(sc);
			}
			mixin(SemEplg);
		}
	}
	
	override Type typeSemantic(Scope sc){
		// mixin(SemPrlg);
		// TODO: TypeTuple slice
		Type ty;
		e=ty=e.typeSemantic(sc);
		if(ty.sstate == SemState.error) return New!ErrorTy();
		if(!a.length) return ty.getDynArr().semantic(sc);
		return super.typeSemantic(sc); // TODO: implement
	}

	override Expression isLvalue(){
		return this;
	}
}

mixin template Semantic(T) if(is(T==SliceExp)){
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e,l,r});
		if(e.isType()) return super.semantic(sc); // TODO: TypeTuple slice
		else{
			auto ty = e.type.getHeadUnqual();
			if(auto dyn=ty.isDynArrTy()){
				type = dyn.ty;
			}else if(auto arr=ty.isArrayTy()){
				// TODO: sanity check against length
				type = arr.ty;
			}else if(auto ptr=ty.isPointerTy()){
				type = ptr.ty;
			}else{ // TODO: operator overloading
				sc.error(format("'%s' is not sliceable",e.type),loc);
				mixin(ErrEplg);
			} // it is a dynamic array, an array or pointer type
			type = type.getDynArr();
			auto s_t = Type.get!Size_t();
			l = l.implicitlyConvertTo(s_t).semantic(sc);
			r = r.implicitlyConvertTo(s_t).semantic(sc);
			// TODO: use options instead, as soon as that is decided
			if(s_t is Type.get!uint() && l.getIntRange().gr(r.getIntRange())
				          ||s_t is Type.get!ulong() && l.getLongRange().gr(r.getLongRange())){
				sc.error("lower bound exceeds upper bound",l.loc.to(r.loc));
			}
			mixin(SemEplg);
		}
	}
	override Type typeSemantic(Scope sc){
		// mixin(SemPrlg);
		// TODO: TypeTuple slice
		return super.typeSemantic(sc);
	}
}

mixin template Semantic(T) if(is(T==CallExp)){
	override Expression semantic(Scope sc){ // TODO: type checking
		mixin(SemPrlg);
		mixin(SemChld!q{e,args});
		MatchContext context;
		if(auto c = e.matchCall(args, context)) fun = c;
		else{
			e.matchError(sc,loc, args);
			mixin(ErrEplg);
		}
		if(auto tt = e.type.isFunctionTy()){
			type = tt.retTy.resolveInout(context.inoutRes);
			foreach(i,x; tt.params){
				auto pty = x.type.resolveInout(context.inoutRes);
				args[i]=args[i].implicitlyConvertTo(pty);
			}
		}else{
			type = Type.get!void(); // TODO: fix
		}
		// TODO: convert arguments types
		mixin(SemEplg);
	}
private:
	Expression fun;
}

mixin template Semantic(T) if(is(T _==UnaryExp!S,TokenType S)){
	static if(is(T _==UnaryExp!S,TokenType S)):
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		static if(S!=Tok!"!"){mixin(SemChldExp!q{e});}
		static if(S!=Tok!"&"&&S!=Tok!"!") auto ty=e.type.getHeadUnqual();
		static if(S==Tok!"!"){
			auto bl = Type.get!bool();
			e = e.convertTo(bl).expSemantic(sc);
			mixin(PropErr!q{e});
			type = bl;
			mixin(SemEplg);
		}else static if(S==Tok!"-" || S==Tok!"+" || S==Tok!"~"){
			auto v = Type.get!void();
			if(ty.isBasicType() && e !is v){
				type = e.type;
				mixin(SemEplg);
			}
		}else static if(S==Tok!"++" || S==Tok!"--"){
			if(e.checkMutate(sc,loc)){
				auto v = Type.get!void();
				if((ty.isBasicType() && e !is v)||ty.isPointerTy()){
					type = e.type;
					mixin(SemEplg);
				}
			}else mixin(ErrEplg);
		}else static if(S==Tok!"*"){
			if(auto p=ty.isPointerTy()){
				type = p.ty;
				mixin(SemEplg);
			}else{
				sc.error(format("cannot dereference expression '%s' of non-pointer type '%s'",e.loc.rep,e.type),loc);
				mixin(ErrEplg);
			}
		}else static if(S==Tok!"&"){
			if(auto lv = e.isLvalue()){
				type=e.type.getPointer();
				mixin(SemEplg);
			}else{
				sc.error(format("cannot take address of expression '%s'",e.loc.rep),loc);
				mixin(ErrEplg);
			}
		}else static assert(0);
		// TODO: operator overloading
		// TODO: array ops
		static if(S!=Tok!"++" && S!=Tok!"--"){
			sc.error(format("invalid argument type '%s' to unary "~TokChars!S,e.type),loc);
		}else{
			sc.error(format("type '%s' does not support prefix "~TokChars!S,e.type),loc);
		}
		mixin(ErrEplg);
	}

	static if(S==Tok!"++"||S==Tok!"--"||S==Tok!"*")
		override Expression isLvalue(){return this;}

	private static string __dgliteralRng(){
		string r;
		foreach(x;["IntRange","LongRange"]){
			r~=mixin(X!q{
				override @(x) get@(x)(){
					alias @(x) R;
					auto r = e.get@(x)();
					static if(S==Tok!"!"){
						bool t = r.min==0&&r.max==0;
						bool f = !r.contains(R(0,0,r.signed));
						return t ? R(1,1,true)
							 : f ? R(0,0,true)
							 :     R(0,1,true);
					}else static if(S==Tok!"+") return r;
					else static if(S==Tok!"-") return -r;
					else static if(S==Tok!"++"||S==Tok!"--"){
						r = mixin(`r`~TokChars!S[0]~`R(1,1,r.signed)`);
						if(auto ty = e.type.isIntegral()){
							static if(is(R==IntRange)){
								r = r.narrow(ty.isSigned(),ty.bitSize());
							}else{
								auto nr = r.narrow(ty.isSigned(),ty.bitSize());
								return R(nr.min,nr.max,nr.signed);
							}
						}
						return r;
					}else static if(S==Tok!"~") return ~r;
					return super.get@(x)();
				}
			});
		}
		return r;
	}
	mixin(__dgliteralRng());
}

mixin template Semantic(T) if(is(T==BinaryExp!(Tok!"."))){}

mixin template Semantic(T) if(is(T _==BinaryExp!S,TokenType S) && !is(T==BinaryExp!(Tok!"."))){
	static if(is(T _==BinaryExp!S,TokenType S)):
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChldExp!q{e1,e2});
		
		static if(isAssignOp(S)){
			// TODO: array ops
			if(e1.checkMutate(sc,loc)){
				type = e1.type;
				e2=e2.implicitlyConvertTo(type).semantic(sc);
				if(e2.sstate == SemState.error) sstate=SemState.error;
				return this;
			}else mixin(ErrEplg);
			//sc.error(format("expression '%s' is not assignable",e1.loc.rep),loc);
		}else static if(isRelationalOp(S)){
			if(auto ty=e1.type.combine(e2.type)){
				auto tyu=ty.getHeadUnqual();
				if(tyu.isBasicType() || tyu.isPointerTy()){
					e1 = e1.implicitlyConvertTo(ty).semantic(sc);
					e2 = e2.implicitlyConvertTo(ty).semantic(sc);
					type = Type.get!bool();
					static if(S!=Tok!"=="||S!=Tok!"!="){
						if(!ty.isComplex())	mixin(SemEplg);
						else{
							sc.error("cannot compare complex operands",loc);
							mixin(ErrEplg);
						}
					}
				}
			}
		}else static if(isLogicalOp(S)){
			static assert(S==Tok!"&&"||S==Tok!"||");
			auto bl = Type.get!bool();
			e1 = e1.convertTo(bl);
			// allow (bool) && (void), (bool) || (void)
			auto ty2 = e2.type.getHeadUnqual();
			if(ty2 !is Type.get!void()){
				e2 = e2.convertTo(bl);
				ty2 = bl;
			}
			mixin(SemChld!q{e1,e2});
			type = ty2;
			mixin(SemEplg);
		}else{
			auto t1=e1.type.getHeadUnqual(), t2=e2.type.getHeadUnqual();
			auto bt1=t1.isBasicType(), bt2=t2.isBasicType();
			auto v = Type.get!void();
			static if(isShiftOp(S)){
				if(bt1 && bt2 && bt1 !is v && bt2 !is v){
					if(bt1.isIntegral()&&bt2.isIntegral()){
						bt1=bt1.intPromote();
						// correctly promote qualified types
						if(bt1 is t1) t1 = e1.type; else t1 = bt1;
						e1 = e1.implicitlyConvertTo(t1).semantic(sc);
						type = t1;
						mixin(SemEplg);
					}
				}
			}else static if(isArithmeticOp(S) || isBitwiseOp(S)){
				if(bt1 && bt2 && bt1 !is v && bt2 !is v){
					bt1=bt1.intPromote(); bt2=bt2.intPromote();
					// correctly promote qualified types
					if(bt1 is t1) t1 = e1.type; else t1 = bt1;
					if(bt2 is t2) t2 = e2.type; else t2 = bt2;
					if(auto ty=t1.combine(t2)){
						e1 = e1.implicitlyConvertTo(ty).semantic(sc);
						e2 = e2.implicitlyConvertTo(ty).semantic(sc);
						type = ty;
						mixin(SemEplg);
					}
				}else static if(S==Tok!"+"||S==Tok!"-"){ // pointer arithmetics
					if(bt1&&bt1.isIntegral() && t2.isPointerTy()){
						type = e2.type;
						mixin(SemEplg);
					}else if(bt2&&bt2.isIntegral() && t1.isPointerTy()){
						type = e1.type;
						mixin(SemEplg);
					}
				}
			}else static if(S==Tok!"~"){
				Type el1 = t1, el2 = t2;
				bool f1 = true, f2 = true;
				if(auto dy1 = t1.isDynArrTy()) el1=dy1.ty;
				else if(auto ar1 = t1.isArrayTy()) el1=ar1.ty;
				else f1 = false;
				if(auto dy2 = t2.isDynArrTy()) el2=dy2.ty;
				else if(auto ar2 = t2.isArrayTy()) el2=ar2.ty;
				else f2 = false;

				if(f1 && f2){
					if(e1.implicitlyConvertsTo(el2)){
						f1 = false;
						el1 = t1;
					}
					if(e2.implicitlyConvertsTo(el1)){
						f2 = false;
						el2 = t2;
					}
				}

				// TODO: if arr1 is of type int[][], what is the meaning of arr1~[]?
				switch(f1<<1|f2){
					case 0b11: // both are arrays
						bool conv1 = e2.implicitlyConvertsTo(t1);
						bool conv2 = e1.implicitlyConvertsTo(t2);
						if(conv1 ^ conv2){
							if(conv1 && !conv2) type = el1;
							else if(conv2 && !conv1) type = el2;
						}else if(auto ty = el1.refCombine(el2, 0)){
							if(el1 !is el2) type = ty.getHeadUnqual();
							else type = ty;
						}
						break;
					case 0b10: // array ~ element
						if(e2.implicitlyConvertsTo(el1)) type = el1;
						break;
					case 0b01: // element ~ array
						if(e1.implicitlyConvertsTo(el2)) type = el2;
						break;
					default:  // both are elements
						break;
				}
				if(type){
					// TODO: unique data mustn't be const-qualified
					// TODO: except if the unqualified type has mutable indirections
					//auto stc = type.getHeadSTC();
					//if(stc&STCconst){
					//	stc&=~STCconst;
					//	// TODO: immutable~const should be immutable
					//	// TODO: except if the unqualified type has const indirections
					//	// if((el1.isImmutable() || el2.isImmutable())
					//	//   && el1 is el1.getConst() && el2 is el2.getConst()) 
					//	// 	stc|=STCimmutable;
					//	type = type.getHeadUnqual().applySTC(stc);
					//}
					if(!f1) e1 = e1.implicitlyConvertTo(type);
					if(!f2) e2 = e2.implicitlyConvertTo(type);
					type = type.getDynArr();
					if(f1) e1 = e1.implicitlyConvertTo(type);
					if(f2) e2 = e2.implicitlyConvertTo(type);
					mixin(SemEplg);
				}
			}
		}
		static if(S==Tok!","){
			type=e2.type;
			mixin(SemEplg);
		}else{
			// TODO: operator overloading
			sc.error(format("incompatible types '%s' and '%s' for binary "~TokChars!S,e1.type,e2.type),loc);
			mixin(ErrEplg);
		}
	}

	static if(S==Tok!"~"){ // '~' always reallocates, therefore conversion semantics are less strict
		override bool implicitlyConvertsTo(Type rhs){
			if(super.implicitlyConvertsTo(rhs)) return true;
			// the type qualifiers of the head of the element type are unimportant.
			// example: if arr1, arr2 are of type int[], then arr1~arr2 implicitly converts to immutable(int)[]
			// example: if arr is of type int*[] then arr~arr implicitly converts to const(int)*[]
			Type el1 = null, el2 = null;
			Type t1 = type.getHeadUnqual(), t2 = rhs.getHeadUnqual();
			if(auto dy1 = t1.isDynArrTy()) el1=dy1.ty;
			else if(auto ar1 = t1.isArrayTy()) el1=ar1.ty;
			if(auto dy2 = t2.isDynArrTy()) el2=dy2.ty;
			else if(auto ar2 = t2.isArrayTy()) el2=ar2.ty;
			if(el1&&el2&&el1.getHeadUnqual().refConvertsTo(el2.getHeadUnqual(), 0)) return true;
			// if both operands implicitly convert to the result type, their concatenation does too.
			// example: [1,2,3]~[4,5,6] implicitly converts to short[]
			return e1.implicitlyConvertsTo(rhs) && e2.implicitlyConvertsTo(rhs);
		}
	}


	private static string __dgliteralRng(){
		string r;
		foreach(x;["IntRange","LongRange"]){
			r~=mixin(X!q{
				override @(x) get@(x)(){
					static if(isArithmeticOp(S) || isBitwiseOp(S)){
						return mixin(`e1.get@(x)()`~TokChars!S~`e2.get@(x)()`);
					}else static if(S==Tok!"," || isAssignOp(S)){
						return e2.get@(x)(); 
					}else static if(isIntRelationalOp(S)){
						auto r1 = e1.get@(x)(), r2 = e2.get@(x)();
						if(r1.min==r1.max && r2.min==r2.max)
							return mixin(`r1.min`~TokChars!S~`r2.min`)?@(x)(1,1,true):@(x)(0,0,true);
						static if(S==Tok!"=="){
							return r1.overlaps(r2)?@(x)(0,1,true):@(x)(0,0,true);
						}else static if(S==Tok!"!="){
							return r1.overlaps(r2)?@(x)(0,1,true):@(x)(1,1,true);
						}else static if(S==Tok!">"){
							return r1.gr(r2)  ? @(x)(1,1,true)
								 : r1.leq(r2) ? @(x)(0,0,true)
								 :              @(x)(0,1,true);
						}else static if(S==Tok!">="){
							return r1.geq(r2) ? @(x)(1,1,true)
								 : r1.le(r2)  ? @(x)(0,0,true)
								 :              @(x)(0,1,true);
						}else static if(S==Tok!"<"){
							return r1.le(r2)  ? @(x)(1,1,true)
								 : r1.geq(r2) ? @(x)(0,0,true)
								 :              @(x)(0,1,true);
						}else static if(S==Tok!"<="){
							return r1.leq(r2) ? @(x)(1,1,true)
								 : r1.gr(r2)  ? @(x)(0,0,true)
								 :              @(x)(0,1,true);
						}
					}else static if(isRelationalOp(S)){
						return super.get@(x)();
					}else static if(isLogicalOp(S)){
						auto r1 = e1.get@(x)(), r2 = e2.get@(x)();
						bool f1=!r1.min&&!r1.max, f2=!r2.min&&!r2.max;
						bool t1=!r1.contains(@(x)(0,0,r1.signed));
						bool t2=!r2.contains(@(x)(0,0,r2.signed));
						static if(S==Tok!"||"){
							if(t1||t2) return @(x)(1,1,true);
							if(f1&&f2) return @(x)(0,0,true);
						}else static if(S==Tok!"&&"){
							if(t1&&t2) return @(x)(1,1,true);
							if(f1||f2) return @(x)(0,0,true);
						}else static assert(0);
						return @(x)(0,1,true);
					}else static if(S==Tok!"~"){
						return super.get@(x)();
					}else static assert(0);
				}
			});
		}
		return r;
	}
	mixin(__dgliteralRng());
}

template Semantic(T) if(is(T X==TernaryExp)){
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		e1=e1.semantic(sc);
		mixin(SemChld!q{e2,e3});
		auto ty1=e2.type, ty2=e3.type;
		auto ty=ty1.combine(ty2);
		if(!ty){
			sc.error(format("incompatible types for ternary operator: '%s' and '%s'",e2.type,e3.type),loc);
			mixin(ErrEplg);
		}
		mixin(PropErr!q{e1});
		type=ty;
		mixin(SemEplg);
	}

	override bool implicitlyConvertsTo(Type rhs){
		if(super.implicitlyConvertsTo(rhs)) return true;
		return e2.implicitlyConvertsTo(rhs) && e3.implicitlyConvertsTo(rhs);
	}

	private static string __dgliteralRng(){
		string r;
		foreach(x;["IntRange","LongRange"]){
			r~=mixin(X!q{
				override @(x) get@(x)(){
					auto r1 = e1.get@(x)();
					bool t = !r1.contains(@(x)(0,0,true));
					bool f = !r1.min&&!r1.max;
					if(t) return e2.get@(x)();
					if(f) return e3.get@(x)();
					return e2.get@(x)().merge(e3.get@(x)());
				}
			});
		}
		return r;
	}

	mixin(__dgliteralRng());
}
class Symbol: Expression{ // semantic node
	Declaration meaning;
	protected this(){} // subclass can construct parent lazily
	this(Declaration m)in{assert(m&&1);}body{meaning = m;}
	override Symbol semantic(Scope sc){
		mixin(SemPrlg);
		assert(!!meaning);
		mixin(PropErr!q{meaning});
		static Symbol circ = null;
		// TODO: always display the exact cycle that caused the error
		enum CircErrMsg=q{
			if(circ){
				if(circ is this) circ = null;
				else sc.note("part of dependency cycle here",loc);
			}
		};
		if(sstate >= SemState.started){
			sc.error("circular dependencies are illegal",loc);
			if(!circ) circ = this;
			mixin(ErrEplg);
		}else sstate = SemState.started;
		if(auto vd=meaning.isVarDecl()){
			if(!vd.type || vd.stc & STCenum){
				meaning = meaning.semantic(meaning.scope_);
				mixin(CircErrMsg);
				mixin(PropErr!q{meaning});
			}
			assert(!!vd.type);
			type=vd.type.typeSemantic(sc);
		}else if(auto fd=meaning.isFunctionDecl()){
			if(!fd.type.ret){
				meaning = meaning.semantic(meaning.scope_);
				mixin(CircErrMsg);
				mixin(PropErr!q{meaning});
			}
			assert(!!fd.type.ret);
			type = fd.type.typeSemantic(meaning.scope_);
		}// TODO: overloads and templates
		else type=Type.get!void(); // same as DMD
		//mixin(CircErrMsg); // TODO: re-enable?
		mixin(PropErr!q{type});

		mixin(SemEplg);
	}
	override string toString(){return meaning.name;}
	override @property string kind(){return meaning.kind;}

	// override Type isType(){...} // TODO.
	override Expression isLvalue(){
		if(meaning.isVarDecl()) return this;
		return null;
	}

	override Expression matchCall(Expression[] args, ref MatchContext context){
		if(auto m = meaning.matchCall(args, context)){
			meaning = m;
			return this;
		}
		return null;
	}
	override void matchError(Scope sc, Location loc, Expression[] args){
		meaning.matchError(sc,loc,args);
	}
}

mixin template Semantic(T) if(is(T==CastExp)){
	override Expression semantic(Scope sc){
		// TODO: sanity checks etc.
		mixin(SemPrlg);
		mixin(SemChld!q{e});
		if(!ty) {
			// TODO: works differently for classes..?
			type = e.type.getHeadUnqual().applySTC(stc);
		}else{
			type=ty.typeSemantic(sc).applySTC(stc);
			mixin(PropErr!q{type});
		}
		mixin(SemEplg);
	}

	private IntRange getBoolRange(BasicType ty){
		int osiz = ty.bitSize();
		bool t,f;
		if(osiz==32){
			auto r = e.getIntRange();
			f = r.min==0 && r.max==0;
			t = !r.contains(IntRange(0,0,r.signed));
		}else{
			auto r = e.getLongRange();
			f = r.min==0 && r.max==0;
			t = !r.contains(LongRange(0,0,r.signed));
		}
		return t ? IntRange(1,1,true)
		     : f ? IntRange(0,0,true)
		     :     IntRange(0,1,true);
	}

	IntRange getIntRange(){
		auto ty = e.type.getHeadUnqual().isIntegral();
		auto nt = type.getHeadUnqual().isIntegral();
		if(!ty||!nt) return type.getIntRange();
		if(nt is Type.get!bool()) return getBoolRange(ty);
		int size=nt.bitSize();
		int osiz=ty.bitSize();
		bool signed=nt.isSigned();
		if(size<osiz){ // narrowing conversion
			if(osiz==64){
				auto r = e.getLongRange();
				return r.narrow(signed, size);
			}else{
				auto r = e.getIntRange();
				return r.narrow(signed, size);
			}
		}else{ // non-narrowing conversion
			assert(osiz<64);
			auto r=e.getIntRange();
			if(signed) r=r.toSigned();
			else r=r.toUnsigned();
			return r;
		}
	}
	LongRange getLongRange(){
		auto ty = e.type.getHeadUnqual().isIntegral();
		auto nt = type.getHeadUnqual().isIntegral();
		if(!ty||!nt) return type.getLongRange();
		int size=nt.bitSize();
		int osiz=ty.bitSize();
		bool signed=nt.isSigned();
		LongRange r;
		if(osiz==64) r=e.getLongRange();
		else{
			auto or=e.getIntRange();
			ulong min, max;
			if(or.signed) min=cast(int)or.min, max=cast(int)or.max;
			else min = or.min, max = or.max;
			r=LongRange(min, max, true);
		}
		if(signed) r=r.toSigned();
		else r=r.toUnsigned();
		return r;
	}
}

class ImplicitCastExp: CastExp{ // semantic node
	this(Expression tt, Expression exp){super(STC.init, tt, exp);}
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e});
		ty=type=ty.semantic(sc).isType();
		assert(type && 1); // if not a type the program is in error
		mixin(PropErr!q{type});
		if(e.implicitlyConvertsTo(type)){mixin(SemEplg);}
		sc.error(format("cannot implicitly convert expression '%s' of type '%s' to '%s'",e.loc.rep,e.type,type),e.loc); // TODO: replace toString with actual representation
		//error(format("no viable conversion from type '%s' to '%s'",e.type,type),e.loc);
		mixin(ErrEplg);
	}
	override string toString(){return e.toString();}
}



mixin template Semantic(T) if(is(T==Identifier)){
	override Symbol semantic(Scope sc){
		mixin(SemPrlg);
		meaning=sc.lookup(this);
		mixin(PropErr!q{meaning});
		return super.semantic(sc);
	}
}

mixin template Semantic(T) if(is(T==FunctionLiteralExp)){
	override Symbol semantic(Scope sc){
		assert(sstate != SemState.completed);
		if(!fty) fty=New!FunctionTy(STC.init,cast(Expression)null,cast(Parameter[])null,VarArgs.none);
		auto dg=New!FunctionDef(fty,New!Identifier(uniqueIdent("__dgliteral")),cast(BlockStm)null,cast(BlockStm)null,cast(Identifier)null,bdy);
		dg.sstate = SemState.begin;
		dg=dg.semantic(sc);
		auto e=New!Symbol(dg);// TODO: take address
		e.loc=loc;
		return e.semantic(sc);
	}
}

// types
mixin template Semantic(T) if(is(T==Type)){
	override Type semantic(Scope sc){return this;}
	override Type typeSemantic(Scope sc){return semantic(sc);}
	Type checkVarDecl(Scope, VarDecl){return this;}

	Type getArray(long size){
		if(auto r=arrType.get(size,null)) return r;
		return arrType[size]=ArrayTy.create(this,size);
	}

	private static auto __funcliteralTQ(){string r;
		foreach(x; typeQualifiers~["pointer","dynArr"]){ // getConst, getImmutable, getShared, getInout, getPointer, getDynArr. remember to keep getArray in sync.
			r ~= mixin(X!q{
				private Type @(x)Type;
				Type get@(upperf(x))(){
					if(@(x)Type) return @(x)Type;
					return @(x)Type=get@(upperf(x))Impl();
				}
				protected Type get@(upperf(x))Impl(){return @(upperf(x))Ty.create(this);}
				Type getTail@(upperf(x))(){return this;}
				Type in@(upperf(x))Context(){return this;}
			});
		}
		return r;
	}mixin(__funcliteralTQ());

	Type applySTC(STC stc){
		auto r = this;
		if(stc&STCimmutable)        r = r.getImmutable();
		if(stc&STCconst||stc&STCin) r = r.getConst();
		if(stc&STCinout)            r = r.getInout();
		if(stc&STCshared)           r = r.getShared();
		return r;
	}
	
	STC getHeadSTC(){ return STC.init;}

	Type getHeadUnqual(){return this;} // is implemented as lazy field in the relevant classes

	bool isMutable(){return true;}
	/* this alias exists in order to be robust against language changes
	   involving an additional qualifier that can co-exist with immutable
	*/
	alias isImmutableTy isImmutable;
	// TODO: isConst, on by-need basis

	BasicType isIntegral(){return null;}
	BasicType isComplex(){return null;}

	final Type isSomeString(){
		return this is get!string() || this is get!wstring() || this is get!dstring() ? this : null;
	}

	/* used for IFTI, template type parameter matching
	   and for matching inout
	 */
	Type adaptTo(Type from, ref InoutRes inoutRes){
		return this;
	}

	Type resolveInout(InoutRes inoutRes){
		return this;
	}

	override bool implicitlyConvertsTo(Type rhs){
		return this.refConvertsTo(rhs.getHeadUnqual(),0);
	}


	// bool isSubtypeOf(Type rhs){...}

	/* stronger condition than subtype relationship.
	   a 'num'-times reference to a this must be a subtype of
	   a 'num'-times reference to an rhs.
	*/
	bool refConvertsTo(Type rhs, int num){
		if(this is rhs) return true;
		if(num < 2){
			if(auto d=rhs.isConstTy()) return refConvertsTo(d.ty.getTailConst(), 0);
		}
		return false;
	}
	
	final protected Type mostGeneral(Type rhs){
		if(rhs is this) return this;
		bool l2r=this.implicitlyConvertsTo(rhs);
		bool r2l=rhs.implicitlyConvertsTo(this);
		if(l2r ^ r2l){
			if(l2r) return rhs;
			return this;
		}
		return null;
	}

	final protected Type refMostGeneral(Type rhs, int num){
		if(rhs is this) return this;
		bool l2r=this.refConvertsTo(rhs, num);
		bool r2l=rhs.refConvertsTo(this, num);
		if(l2r ^ r2l){
			if(l2r) return rhs;
			return this;
		}
		return null;
	}

	/* common type computation. TDPL p60
	   note: most parts of the implementation are in subclasses
	*/

	Type combine(Type rhs){
		if(auto r = mostGeneral(rhs)) return r;
		auto unqual = rhs.getHeadUnqual();
		if(unqual !is rhs) return unqual.combine(this);
		return null;
	}
	
	Type refCombine(Type rhs, int num){
		if(auto d=rhs.isQualifiedTy()) return d.refCombine(this, num);
		if(auto r = refMostGeneral(rhs, num)) return r;
		if(num < 2){
			if(num) return getConst().refCombine(rhs.getConst(), 0);
			auto tconst = getTailConst();
			if(this !is tconst) return tconst.refCombine(rhs.getTailConst(), 0);
		}
		return null;
	}

	/* get the ranges associated with a type. expressions often
	   allow more specific statements about their range.
	*/
	override IntRange getIntRange(){return IntRange.full(true);}
	override LongRange getLongRange(){return LongRange.full(true);}
}

mixin template Semantic(T) if(is(T==FunctionTy)||is(T==FunctionPtr)||is(T==DelegateTy)){
	override T semantic(Scope sc){
		mixin(SemPrlg);
		static if(is(T==FunctionTy)) if(ret) retTy = ret.typeSemantic(sc);
		// TODO: implement fully
		// for now: update sstate
		mixin(SemEplg);
	}
}


mixin template Semantic(T) if(is(T==BasicType)){
	override BasicType semantic(Scope sc){
		mixin({
			string r=`switch(op){`;
			foreach(x; basicTypes)
				r~=mixin(X!q{case Tok!"@(x)": return Type.get!@(x)();});
			return r~`default: assert(0);}`;
		}());
	}
	override Type checkVarDecl(Scope sc, VarDecl me){
		if(op!=Tok!"void") return this;
		sc.error(format("%s '%s' has invalid type '%s'", me.kind, me.name, this), me.loc);
		return New!ErrorTy();
	}
	
	BasicType intPromote(){
		switch(op){
			case Tok!"bool":
			case Tok!"byte", Tok!"ubyte", Tok!"char":
			case Tok!"short", Tok!"ushort", Tok!"wchar":
				return Type.get!int();
			case Tok!"dchar":
				return Type.get!uint();
			default: return this;
		}
	}

	private static immutable int[] strength=
		[Tok!"bool":1,Tok!"char":2,Tok!"byte":2,Tok!"ubyte":2,Tok!"wchar":3,Tok!"short":3,Tok!"ushort":3,
		 Tok!"dchar":4,Tok!"int":4,Tok!"uint":4,Tok!"long":5,Tok!"ulong":5,Tok!"float":6,Tok!"double":6,Tok!"real":6,
		 Tok!"ifloat":-1,Tok!"idouble":-1,Tok!"ireal":-1,Tok!"cfloat":-2,Tok!"cdouble":-2,Tok!"creal":-2];

	override BasicType isIntegral(){return strength[op]>=0 && strength[op]<=5 ? this : null;}
	override BasicType isComplex(){return strength[op]==-2 ? this : null;}
	final int bitSize()in{assert(!!isIntegral());}body{
		switch(op){
			case Tok!"bool", Tok!"char", Tok!"byte", Tok!"ubyte":
				return 8;
			case Tok!"wchar", Tok!"short", Tok!"ushort":
				return 16;
			case Tok!"dchar", Tok!"int", Tok!"uint":
				return 32;
			case Tok!"long", Tok!"ulong":
				return 64;
			default: return -1;
		}
	}
	final bool isSigned()in{assert(!!isIntegral());}body{
		switch(op){
			case Tok!"bool", Tok!"ubyte", Tok!"ushort", Tok!"dchar", Tok!"uint", Tok!"ulong":
				return false;
			default: return true;
		}
	}

	override bool implicitlyConvertsTo(Type rhs){
		if(auto bt=rhs.getHeadUnqual().isBasicType()){ // transitive closure of TDPL p44
			if(op == Tok!"void") return false;
			if(strength[op]>=0 && strength[bt.op]>=0) return strength[op]<=strength[bt.op];
			if(strength[bt.op]==-2) return true;
			return strength[op] == -1 && strength[bt.op] == -1; // both must be imaginary
		}
		return false;
	}

	override Type combine(Type rhs){
		if(this is rhs.getHeadUnqual()) return this;
		if(auto bt=rhs.getHeadUnqual().isBasicType()){
			if(strength[op]>=0&&strength[bt.op]>=0){
				if(strength[op]<4&&strength[bt.op]<4) return Type.get!int();
				if(strength[op]<strength[bt.op]) return bt;
				if(strength[op]>strength[bt.op]) return this;
			}else{
				if(strength[bt.op]==-2) return bt.complCombine(this);
				else if(strength[bt.op]==-1) return bt.imagCombine(this);
			}
			switch(strength[op]){
				case -2:
					return complCombine(bt);
				case -1: // imaginary types
					return imagCombine(bt);
				case 4:
					return Type.get!uint();
				case 5:
					return Type.get!ulong();
				case 6:
					if(op==Tok!"float" && bt.op==Tok!"float") return this;
					else if(op!=Tok!"real" && bt.op!=Tok!"real") return Type.get!double();
					else return Type.get!real();
				default: assert(0);
			}
		}
		return super.combine(rhs);
	}

	// TODO: compress into a single template and two alias
	private BasicType imagCombine(BasicType bt)in{assert(strength[op]==-1);}body{
		if(strength[bt.op]==-1){
			if(op==Tok!"ifloat" && bt.op==Tok!"ifloat") return this;
			else if(op!=Tok!"ireal" && bt.op!=Tok!"ireal") return Type.get!idouble();
			else return Type.get!ireal();
		}
		// imaginary + complex
		if(strength[bt.op]==-2){
			if(op==Tok!"ifloat" && bt.op==Tok!"cfloat") return Type.get!cfloat();
			if(op!=Tok!"ireal" && bt.op!=Tok!"creal") return Type.get!cdouble();
			if(op==Tok!"ireal" || bt.op==Tok!"creal") return Type.get!creal();
		}
		// imaginary + 2's complement integer
		if(strength[bt.op]<6){
			if(op==Tok!"ifloat") return Type.get!cfloat();
			if(op==Tok!"idouble") return Type.get!cdouble();
			if(op==Tok!"ireal") return Type.get!creal();
		}
		// imaginary + 'real'
		if(op==Tok!"ifloat" && bt.op==Tok!"float") return Type.get!cfloat();
		if(op!=Tok!"ireal" && bt.op!=Tok!"real") return Type.get!cdouble();
		return Type.get!creal();		
	}
	private BasicType complCombine(BasicType bt)in{assert(strength[op]==-2);}body{
		if(strength[bt.op]==-2){
			if(op==Tok!"cfloat" && bt.op==Tok!"cfloat") return this;
			else if(op!=Tok!"creal" && bt.op!=Tok!"creal") return Type.get!cdouble();
			else return Type.get!creal();
		}
		// complex + imaginary
		if(strength[bt.op]==-1){
			if(op==Tok!"cfloat" && bt.op==Tok!"ifloat") return Type.get!cfloat();
			if(op!=Tok!"creal" && bt.op!=Tok!"ireal") return Type.get!cdouble();
			if(op==Tok!"creal" || bt.op==Tok!"ireal") return Type.get!creal();
		}
		// complex + 2's complement integer
		if(strength[bt.op]<6){
			if(op==Tok!"cfloat") return Type.get!cfloat();
			if(op==Tok!"cdouble") return Type.get!cdouble();
			if(op==Tok!"creal") return Type.get!creal();
		}
		// complex + 'real'
		if(op==Tok!"cfloat" && bt.op==Tok!"float") return Type.get!cfloat();
		if(op!=Tok!"creal" && bt.op!=Tok!"real") return Type.get!cdouble();
		return Type.get!creal();		
	}

	override IntRange getIntRange(){
		switch(op){
			mixin({
				string r;
				foreach(x;["dchar", "uint"])
					r~=mixin(X!q{case Tok!"@(x)": return IntRange(@(x).min,@(x).max,false);});
				foreach(x;["bool","byte","ubyte","char","short","ushort","wchar","int"])
					r~=mixin(X!q{case Tok!"@(x)": return IntRange(@(x).min,@(x).max,true);});
				return r;
			}());
			default: return super.getIntRange();
		}
	}
	override LongRange getLongRange(){
		switch(op){
			case Tok!"ulong": return LongRange(ulong.min,ulong.max,false);
			mixin({
				string r;
				foreach(x;["bool","byte","ubyte", "char","short","ushort","wchar","int","dchar","uint","long"])
					r~=mixin(X!q{case Tok!"@(x)": return LongRange(@(x).min,@(x).max,true);});
				return r;
			}());
			default: return super.getLongRange();
		}
	}
	
}


mixin template Semantic(T) if(is(T==ConstTy)||is(T==ImmutableTy)||is(T==SharedTy)||is(T==InoutTy)){

	private enum qual = T.stringof[0..$-2];

	static Type create(Type next)in{
		assert(next.sstate == SemState.completed);
	}body{
		auto tt = mixin(`next.in`~qual~`Context()`);
		if(tt==next){
			assert(!mixin(`next.`~lowerf(qual)~`Type`));
			auto r = New!T(tt);
			r.ty = tt;
			r.sstate = SemState.completed;
			return r;
		}else return mixin(`tt.get`~qual)();
	}

	invariant(){assert(sstate < SemState.started || ty);}
	Type ty;
	override Type semantic(Scope sc){
		mixin(SemPrlg);
		e=ty=e.typeSemantic(sc);
		sstate = SemState.started;
		Type r;
		mixin(PropErr!q{e});
		static if(is(T==ConstTy)) r=ty.getConst();
		else static if(is(T==ImmutableTy)) r=ty.getImmutable();
		else static if(is(T==SharedTy)) r=ty.getShared();
		else static if(is(T==InoutTy)) r=ty.getInout();
		else static assert(0);
		sstate = SemState.completed;
		return r.semantic(sc);
	}

	static if(is(T==ConstTy)||is(T==ImmutableTy)||is(T==InoutTy))
		override bool isMutable(){return false;}

	static if(is(T==InoutTy)){
		override Type adaptTo(Type from, ref InoutRes res){
			if(auto imm = from.isImmutableTy()){
				res = mergeIR(res, InoutRes.immutable_);
			}else if(auto con = from.isConstTy()){
				assert(!con.ty.isInoutTy()); // normal form: inout(const(T))
				res = mergeIR(res, InoutRes.const_);
			}else if(auto sha = from.isSharedTy()){
				// information could be burried, eg shared(const(int))
				return adaptTo(sha.ty, res);
			}else if(auto ino = from.isInoutTy()){
				res = mergeIR(res, ino.ty.isConstTy() ?
				                   InoutRes.inoutConst :
				                   InoutRes.inout_);
			}else res = mergeIR(res, InoutRes.mutable);

			return ty.getTailInout().adaptTo(from.getHeadUnqual(), res).getInout();
		}
		override Type resolveInout(InoutRes res){
			assert(ty.resolveInout(res) is ty);
			final switch(res){
				case InoutRes.none, InoutRes.inout_:
					return this;
				case InoutRes.mutable:
					return ty;
				case InoutRes.immutable_:
					return ty.getImmutable();
				case InoutRes.const_:
					return ty.getConst();
				case InoutRes.inoutConst:
					return ty.getConst().getInout();
			}
		}
	}else{
		override Type adaptTo(Type from, ref InoutRes res){
			return mixin(`ty.getTail`~qual~`().adaptTo(from, res).get`~qual)();
		}
		override Type resolveInout(InoutRes res){
			return mixin(`ty.resolveInout(res).get`~qual)();
		}
	}
	
	override bool implicitlyConvertsTo(Type rhs){
		return getHeadUnqual().implicitlyConvertsTo(rhs.getHeadUnqual());
	}

	override bool refConvertsTo(Type rhs, int num){
		if(this is rhs) return true;
		if(auto d=mixin(`rhs.is`~T.stringof)())
			// const and immutable imply covariance
			static if(is(T==ConstTy) || is(T==ImmutableTy)){
				return mixin(`ty.getTail`~qual)().refConvertsTo(mixin(`d.ty.getTail`~qual)(), 0);
			}else{
				// shared and inout do not imply covariance unless they are also const:
				auto nn = this is getConst() ? 0 : num;
				return mixin(`ty.getTail`~qual)().refConvertsTo(mixin(`d.ty.getTail`~qual)(),nn);
			}
		static if(is(T==ImmutableTy)||is(T==InoutTy))if(num < 2){
			static if(is(T==ImmutableTy)){
				if(rhs is rhs.getConst()){
					// immutable(Sub)* implicitly converts to
					// [const|inout const|shared const|shared inout const](Super)*
					return ty.getTailImmutable().refConvertsTo(rhs.getHeadUnqual(), 0);
				}
			}else static if(is(T==InoutTy)){
				// inout(Sub)* implicitly converts to const(Super)*
				if(auto d=rhs.isConstTy()){
					return ty.inConstContext().getTailInout().refConvertsTo(d.ty.getTailConst(), 0);
				}
			}
		}
		return false;
	}

	override Type combine(Type rhs){
		if(this is rhs) return this;
		// special rules apply to basic types:
		if(rhs.isBasicType()) return getHeadUnqual().combine(rhs);
		if(auto r = mostGeneral(rhs)) return r;
		auto lhs = getHeadUnqual();
		rhs = rhs.getHeadUnqual();
		if(auto r = lhs.combine(rhs)) return r;
		return null;
	}

	override Type refCombine(Type rhs, int num){
		if(auto r = refMostGeneral(rhs, num)) return r;
		if(num<2){
			static if(is(T==ConstTy)||is(T==ImmutableTy)){
				auto r = rhs.getConst();
				if(rhs is r) return null; // stop recursion
				return refCombine(r,num);
			}else{
				auto l=getConst(), r=rhs.getConst();
				if(this is l && rhs is r) return null; // stop recursion
				return l.refCombine(r,num);
			}
		}
		return null;
	}

	override IntRange getIntRange(){return ty.getIntRange();}
	override LongRange getLongRange(){return ty.getLongRange();}


	override protected Type getConstImpl() {
		static if(is(T==ConstTy)||is(T==ImmutableTy)) return this;
		else static if(is(T==SharedTy)) return ty.getConst().getShared();
		else static if(is(T==InoutTy)) return ty.getConst().getInout();
		else static assert(0);
	}
	override protected Type getImmutableImpl(){
		static if(is(T==ImmutableTy)) return this;
		else return ty.getImmutable();
	}
	override protected Type getSharedImpl(){
		static if(is(T==ImmutableTy) || is(T==SharedTy)) return this;
		else return super.getSharedImpl();
	}

	static if(!is(T==ConstTy)){
		override protected Type getInoutImpl(){
			static if(is(T==InoutTy)||is(T==ImmutableTy)) return this;
			else static if(is(T==SharedTy)) return ty.getInout().getShared();
			else static assert(0);
		}
	}

	override Type getHeadUnqual(){
		if(hunqualType) return hunqualType;
		return hunqualType=mixin(`ty.getHeadUnqual().getTail`~qual)();
	}

	override STC getHeadSTC(){
		return ty.getHeadSTC()|mixin("STC"~lowerf(qual));
	}

	private static string __dgliteralTail(){ // TODO: maybe memoize this?
		string r;
		foreach(q;typeQualifiers){
			r~=mixin(X!q{
				override Type getTail@(upperf(q))(){
					return ty.getTail@(upperf(q))().get@(qual)();
				}
			});
		}
		return r;
	}
	mixin(__dgliteralTail());

	// TODO: maybe memoize this?
	override Type inConstContext(){
		static if(is(T==ConstTy)) return ty.inConstContext();
		else return mixin(`ty.inConstContext().get`~qual)();
	}
	override Type inImmutableContext(){
		return ty.inImmutableContext();
	}
	override Type inSharedContext(){
		static if(is(T==SharedTy)) return ty.inSharedContext();
		else return mixin(`ty.inSharedContext().get`~qual)();
	}
	override Type inInoutContext(){
		static if(is(T==InoutTy)) return ty.inInoutContext();
		else return mixin(`ty.inInoutContext().get`~qual)();
	}

private:
	Type hunqualType;
}

mixin template GetTailOperations(string tail, string puthead){
	static string __dgliteralTailQualified(){// "delegate literals cannot be class members..."
		string r;
		foreach(q;typeQualifiers){
			r~=mixin(X!q{
				Type tail@(upperf(q))Type;
				override Type getTail@(upperf(q))(){
					if(tail@(upperf(q))Type) return tail@(upperf(q))Type;
					return tail@(upperf(q))Type=@(tail).get@(upperf(q))().@(puthead);
			    }
				override Type in@(upperf(q))Context(){ // TODO: memoize
					assert(@(tail)&&1);
					return @(tail).in@(upperf(q))Context().@(puthead);
				}
			});
		}
		return r;
	}
	mixin(__dgliteralTailQualified());
}


mixin template Semantic(T) if(is(T==PointerTy)||is(T==DynArrTy)||is(T==ArrayTy)){

	static if(is(T==ArrayTy)){
		static T create(Type next, long size)in{
			assert(next.sstate == SemState.completed);
		}body{
			auto r = New!T(next, size);
			r.ty = next;
			r.sstate = SemState.completed;
			return r;
		}
	}else{
		static T create(Type next)in{
			assert(next.sstate == SemState.completed);
		}body{
			auto r = New!T(next);
			r.ty = next;
			r.sstate = SemState.completed;
			return r;
		}
	}

	Type ty;
	override Type semantic(Scope sc){
		mixin(SemPrlg);
		e=ty=e.typeSemantic(sc);
		Type r;
		mixin(PropErr!q{e});
		static if(is(T==ArrayTy)) r=ty.getArray(length);
		else r = mixin("ty.get"~T.stringof[0..$-2]~"()");
		sstate = SemState.completed;
		return r;
	}

	override Type adaptTo(Type from, ref InoutRes res){
		if(auto tt = mixin(`from.getHeadUnqual().is`~T.stringof)()){
			return mixin(`ty.adaptTo(tt.ty,res).`~puthead);
		}else return this;
	}
	override Type resolveInout(InoutRes res){
		return mixin(`ty.resolveInout(res).`~puthead);
	}

	// this adds one indirection for pointers and dynamic arrays
	override bool refConvertsTo(Type rhs, int num){
		if(auto c=mixin(`rhs.is`~T.stringof)())
			return ty.refConvertsTo(c.ty,num+!is(T==ArrayTy));
		return super.refConvertsTo(rhs,num);
	}
	override Type combine(Type rhs){
		if(auto r = mostGeneral(rhs)) return r;
		auto unqual = rhs.getHeadUnqual();
		return unqual.refCombine(this, 0);
		return null;
	}
	override Type refCombine(Type rhs, int num){
		if(auto c=mixin(`rhs.is`~T.stringof)())
			if(auto d=ty.refCombine(c.ty,num+!is(T==ArrayTy)))
				return mixin(`d.`~puthead);
		return super.refCombine(rhs,num);
	}

	private enum puthead = "get"~(is(T==ArrayTy)?"Array(length)":typeof(this).stringof[0..$-2]~"()");
	mixin GetTailOperations!("ty", puthead);
}

mixin template Semantic(T) if(is(T==NullPtrTy)||is(T==EmptyArrTy)){
	override bool implicitlyConvertsTo(Type rhs){
		rhs = rhs.getHeadUnqual();
		static if(is(T==NullPtrTy)){
			// TODO: add || rhs.isClassTy()
			if(rhs.isPointerTy() || rhs.isDynArrTy()) return true;
		}else static if(is(T==EmptyArrTy)){
			if(rhs.isDynArrTy()) return true;
		}else static assert(0);
		if(auto arr = rhs.isArrayTy()) return arr.length == 0;
		return false;
	}
}


mixin template Semantic(T) if(is(T==TypeofExp)){
	override Type semantic(Scope sc){
		mixin(SemPrlg);
		//if(sstate == SemState.started){
		//	// TODO: show other parts of cycle
		//	sc.error("recursive typeof declaration",loc);
		//	mixin(ErrEplg);
		//}
		sstate = SemState.started;
		auto f = e.semantic(sc);
		mixin(PropErr!q{f});
		if(f.isType()){
			sc.error(format("typeof argument '%s' is not an expression",e.loc.rep),e.loc);
			mixin(ErrEplg);
        }else e=f;
		if(!e.type) return Type.get!void();
		return e.type.semantic(sc);
		mixin(SemEplg);
	}
}

mixin template Semantic(T) if(is(T==ConditionDeclExp)){
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		if(!decl) decl=New!VarDecl(stc,ty,name,init).semantic(sc);
		mixin(PropErr!q{decl});
		if(!sym) sym = name.semantic(sc);
		mixin(PropErr!q{sym});
		type = sym.type;
		mixin(SemEplg);
	}
private:
	VarDecl decl;
	Symbol sym;
}

// statements

mixin template Semantic(T) if(is(T==Statement)){
	override Statement semantic(Scope sc){
		sc.error("unimplemented feature",loc);
		sstate = SemState.error;
		return this;
	}
}

mixin template Semantic(T) if(is(T==EmptyStm)){
	override EmptyStm semantic(Scope sc){
		sstate = SemState.completed;
		return this;
	}
}

mixin template Semantic(T) if(is(T==BlockStm)){
	BlockStm semanticNoScope(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{s});
		mixin(SemEplg);
	}
	
	override BlockStm semantic(Scope sc){
		if(!mysc) mysc = New!BlockScope(sc);
		return semanticNoScope(mysc);
	}
private:
	FunctionScope mysc = null;	
}


mixin template Semantic(T) if(is(T==ExpressionStm)){
	override Statement semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e});
		mixin(SemEplg);
	}
}

mixin template Semantic(T) if(is(T==IfStm)){
	override Statement semantic(Scope sc){
		mixin(SemPrlg);
		if(!tsc) tsc = New!BlockScope(sc);
		e = e.semantic(tsc);
		auto bl = Type.get!bool();
		if(e.type !is bl) e = e.convertTo(bl).semantic(tsc);
		s1 = s1.semantic(tsc);
		if(s2){
			if(!esc) esc = New!BlockScope(sc);
			s2 = s2.semantic(esc);
			mixin(PropErr!q{s2});
		}
		mixin(PropErr!q{e,s1});
		mixin(SemEplg);
	}
private:
	BlockScope tsc, esc;
}

mixin template Semantic(T) if(is(T==WhileStm)){
	override WhileStm semantic(Scope sc){
		mixin(SemPrlg);
		if(!lsc) lsc = New!BlockScope(sc);
		e = e.semantic(lsc);
		s = s.semantic(lsc);
		mixin(PropErr!q{e,s});
		mixin(SemEplg);
	}
private:
	BlockScope lsc;
}

mixin template Semantic(T) if(is(T==DoStm)){
	override DoStm semantic(Scope sc){
		mixin(SemPrlg);
		if(!lsc) lsc = New!BlockScope(sc);
		s = s.semantic(lsc);
		e = e.semantic(sc);   // TODO: propose e.semantic(lsc);
		mixin(PropErr!q{e,s});
		mixin(SemEplg);
	}
private:
	BlockScope lsc;
}


mixin template Semantic(T) if(is(T==ForStm)){
	override ForStm semantic(Scope sc){
		mixin(SemPrlg);
		if(!lsc) lsc = New!BlockScope(sc);
		if(s1){ // s1 is NoScope
			if(auto bl=s1.isBlockStm()) s1 = bl.semanticNoScope(lsc);
			else s1=s1.semantic(lsc);
		}if(e1) e1=e1.semantic(lsc);
		if(e2) e2=e2.semantic(lsc); s2=s2.semantic(lsc);
		if(s1) mixin(PropErr!q{s1});
		if(e1) mixin(PropErr!q{e1});
		if(e2) mixin(PropErr!q{e2});
		mixin(PropErr!q{s2});
		return this;
	}
private:
	BlockScope lsc;
}

mixin template Semantic(T) if(is(T==ReturnStm)){
	override ReturnStm semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e});
		// TODO: match with function return type
		mixin(SemEplg);
	}
}

// declarations
mixin template Semantic(T) if(is(T==EmptyDecl)){
	override EmptyDecl presemantic(Scope sc){
		if(sstate == SemState.pre) sstate = SemState.begin;
		scope_ = sc;
		return this;
	}
	override EmptyDecl semantic(Scope sc){
		sstate = SemState.completed;
		return this;
	}
}

mixin template Semantic(T) if(is(T==Declaration)){
	Scope scope_ = null;

	invariant(){assert(sstate != SemState.pre || !scope_);}

	Declaration presemantic(Scope sc){ // insert into symbol table, but don't do the heavy processing yet
		//if(scope_) return this;
		if(sstate != SemState.pre) return this;
		sstate = SemState.begin;
		if(!name){sc.error("unimplemented feature",loc); sstate = SemState.error; return this;} // TODO: obvious
		if(!sc.insert(this)) sstate = SemState.error;
		return this;
	}
	override Declaration semantic(Scope sc){
		mixin(SemPrlg);
		if(sstate==SemState.pre){
			auto ps=presemantic(sc);
			if(ps!is this) return ps.semantic(sc);
		}
		mixin(SemEplg);
	}

	Declaration matchCall(Expression[] args, ref MatchContext context){
		return null;
	}
	void matchError(Scope sc, Location loc, Expression[] args){
		sc.error(format("%s '%s' is not callable",kind,name),loc);
	}
}
mixin template Semantic(T) if(is(T==VarDecl)){
	Type type;

	override VarDecl presemantic(Scope sc){return cast(VarDecl)cast(void*)super.presemantic(sc);}

	override VarDecl semantic(Scope sc){
		mixin(SemPrlg);
		if(rtype) type=rtype.typeSemantic(sc);
		if(init){
			init=init.expSemantic(sc);
			// deduce type
			if(!type && init.sstate!=SemState.error) type=init.type;
		}else if(!type){
			sc.error(format("initializer required for '%s' declaration",STCtoString(stc)),loc);
			mixin(ErrEplg);
		}
		if(sstate == SemState.pre && name){ // insert into function scope
			// TODO: replace by call to presemantic
			if(!sc.insert(this)){mixin(ErrEplg);}
		}
		if(!type||type.sstate==SemState.error) mixin(ErrEplg); // deliberately don't propagate init's semantic 'error' state if possible
		type = type.applySTC(stc).checkVarDecl(sc,this);
		mixin(PropErr!q{type});
		// TODO: quick hack, make prettier
		if(init){
			init=init.implicitlyConvertTo(type).semantic(sc);
			mixin(PropErr!q{init});
		}

		mixin(SemEplg);
	}
}

mixin template Semantic(T) if(is(T==Parameter)){
	override VarDecl presemantic(Scope sc){
		if(!name) return this;
		return super.presemantic(sc);
	}
}

mixin template Semantic(T) if(is(T==CArrayDecl)){ // TODO: should CArrayDecl inherit VarDecl?
	//override Declaration presemantic(Scope sc){return cast(CArrayDecl)cast(void*)super.presemantic(sc);}
	override VarDecl semantic(Scope sc){
		while(postfix !is name){
			assert(!!cast(IndexExp)postfix);
			auto id = cast(IndexExp)cast(void*)postfix;
			postfix = id.e;
			id.e = rtype;
			rtype = id;
		}
		return super.semantic(sc);
	}
}


mixin template Semantic(T) if(is(T==Declarators)){
	override Declaration presemantic(Scope sc){
		if(sstate>SemState.pre) return this;
		foreach(ref x; decls) x=x.presemantic(sc);
		sstate=SemState.begin;
		return this;
	}
	override Declaration semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{decls});
		mixin(SemEplg);
	}
}

abstract class OverloadableDecl: Declaration{ // semantic node
	this(STC stc,Identifier name){super(stc,name);}
	override OverloadableDecl isOverloadableDecl(){return this;}
}

class OverloadSet: Declaration{ // purely semantic node
	this(OverloadableDecl[] args...)in{assert(args.length);}body{
		super(STC.init,args[0].name);
		foreach(d;args) add(d);
		sstate = SemState.begin; // do not insert into scope
	}
	this(Identifier name){super(STC.init,name);}
	void add(OverloadableDecl decl){decls~=decl;}
	override string toString(){return join(map!(to!string)(decls),"\n");}
	override OverloadSet isOverloadSet(){return this;}
private:
	OverloadableDecl[] decls; // TODO: use more efficient data structure
}

mixin template Semantic(T) if(is(T==FunctionDecl)){
	override FunctionDecl semantic(Scope sc){
		mixin(SemPrlg);
		if(!type.ret){
			sc.error("function body required for return type inference",loc);
			mixin(ErrEplg);
		}
		type = type.semantic(sc);
		foreach(p; type.params){
			p.sstate = SemState.begin; // never insert into scope
			p.semantic(sc);
		}
		mixin(PropErr!q{type.params});
		mixin(SemEplg);
	}

	override Declaration matchCall(Expression[] args, ref MatchContext context){
		// TODO: variadic arguments
		if(args.length != type.params.length) return null;
		// TODO: matching levels
		auto at = new Type[args.length];
		foreach(i,p; type.params){
			at[i] = p.type.adaptTo(args[i].type, context.inoutRes);
		}
		foreach(ref x;at) x = x.resolveInout(context.inoutRes);
		foreach(i,p; type.params){
			if(!args[i].implicitlyConvertsTo(at[i])) return null;
		}
		return this;
	}

	override void matchError(Scope sc, Location loc, Expression[] args){
		if(args.length != type.params.length){
			sc.error(format("too %s arguments to function '%s'",args.length<type.params.length?"few":"many", signatureString()[0..$-1]),loc);
			return;
		}
		int num=0;
		InoutRes inoutRes;
		auto at = new Type[args.length];
		foreach(i,p; type.params){
			at[i] = p.type.adaptTo(args[i].type, inoutRes);
		}
		foreach(ref x;at) x = x.resolveInout(inoutRes);
		foreach(i,p; type.params){
			if(!args[i].implicitlyConvertsTo(at[i])) num++;
		}
		if(num>1){
			sc.error(format("incompatible argument types (%s) to function '%s'", join(map!"a.type.toString()"(args),","),signatureString()[0..$-1]),loc);
			sc.note("declared here",this.loc);
		}else{
			foreach(i,p; type.params){
				if(!args[i].implicitlyConvertsTo(at[i])){
					//if(args[i].sstate == SemState.error) continue;
					args[i].implicitlyConvertTo(at[i]).semantic(sc); // trigger consistent error message
					if(p.name) sc.note(format("while matching function parameter '%s'",p.name),p.loc);
					else sc.note("while matching function parameter",p.loc);
					break;
				}
			}
		}
	}
}

mixin template Semantic(T) if(is(T==FunctionDef)){
	override FunctionDef semantic(Scope sc){
		mixin(SemPrlg);
		if(!type.ret) type.ret = Type.get!int(); // BUG!
		if(!fsc) fsc = New!FunctionScope(sc);
		if(sstate == SemState.pre) presemantic(sc); // add self to parent scope
		//mixin(SemChld!q{type.params});
		foreach(p; type.params) p.presemantic(fsc); // add parameters to function scope
		type = type.semantic(sc);
		foreach(p; type.params) p.semantic(sc);
		bdy.semanticNoScope(fsc);
		mixin(PropErr!q{type.params, bdy});
		mixin(SemEplg);
	}
private:
	FunctionScope fsc;
}

mixin template Semantic(T) if(is(T==PragmaDecl)){
	override Declaration presemantic(Scope sc){
		if(auto b=bdy.isDeclaration()) bdy=b.presemantic(sc);
		return this;
	}
	override Declaration semantic(Scope sc){
		mixin(SemPrlg);
		sstate = SemState.max;
		if(args.length<1){sc.error("missing arguments to pragma",loc); sstate=SemState.error; return this;}
		if(auto id=args[0].isIdentifier()){
			switch(id.name){
				case "msg":
					if(args.length<2){if(bdy)mixin(SemChld!q{bdy}); mixin(SemEplg);}
					foreach(ref x; args[1..$]) x = x.semantic(sc);
					// TODO: interpret!
					import std.stdio;
					foreach(x; args[1..$]){
						if(x.type !is Type.get!string()) stderr.write(x);
						else stderr.write(x);
					}
					stderr.writeln();
					if(bdy) mixin(SemChld!q{bdy});
					mixin(PropErr!q{args[1..$]});
					mixin(SemEplg);
				default: break;

				// for debugging. TODO: remove
				case "__range":
					if(args.length!=2) break;
					args[1]=args[1].semantic(sc);
					mixin(PropErr!q{args[1..$]});
					sstate = args[1].sstate;
					if(sstate == SemState.completed){
						import std.stdio;
						auto ty=args[1].type.isIntegral();
						if(ty&&ty.bitSize()<=32) stderr.writeln(args[1].getIntRange());
						else stderr.writeln(args[1].getLongRange());
					}
					mixin(SemEplg);
			}
		}
		sc.error(format("unrecognized pragma '%s'",args[0].loc.rep),args[0].loc); // TODO: maybe remove this
		bdy = bdy.semantic(sc);
		mixin(ErrEplg);
	}
}
