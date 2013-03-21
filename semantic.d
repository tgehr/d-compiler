// Written in the D programming language.

import std.array, std.conv, std.algorithm, std.string;

import lexer, parser, expression, statement, declaration, scope_, util;

import variant;

public import operators;
public import interpret;

string uniqueIdent(string base){
	shared static id=0;
	return base~to!string(id++);
}
// helper macros

template PropErr(string s){ // propagate the 'error' semantic state TODO: maybe exceptions?
	enum PropErr=s.length?{
		string r;
		auto ss=s.split(",");
		foreach(t;ss){
			r~=mixin(X!q{
				static if(is(typeof(@(t)): Node)){
					if(@(t).sstate==SemState.error){
						sstate=SemState.error;
						needRetry=false;
						return this;
					}
				}else{
					foreach(x;@(t)){
						if(x.sstate==SemState.error){
							sstate=SemState.error;
							needRetry=false;
							return this;
						}
					}
				}
			});
		}
		return r;
	}():q{if(sstate==SemState.error){needRetry=false;return this;}};
}

template PropRetry(string s){
	enum PropRetry=mixin(X!q{
		if(@(s).needRetry){
			needRetry=true;
			//import std.stdio; w/riteln("propagated retry from ",@(s).toString()," to ",toString());
			return this;
		}
	});
}

private template _SemChldImpl(string s, string op){ // TODO: get rid of duplication
	enum _SemChldImpl={
		string r;
		auto ss=s.split(",");
		foreach(t;ss){
			r~=mixin(X!q{
				static if(is(typeof(@(t)): Node)){
					@(t)=@(t).@(op);
					mixin(PropRetry!q{@(t)});
					static if(is(typeof(@(t)): Expression) && !is(typeof(@(t)):Type)
					          &&(!is(typeof(this):Expression)||is(typeof(this):Type)))
					if(@(t).sstate == SemState.completed) @(t) = @(t).constFold();
				}else foreach(ref x;@(t)){
					x=x.@(op);
					mixin(PropRetry!q{x});
					static if(is(typeof(x): Expression) && !is(typeof(x):Type)
					          &&(!is(typeof(this):Expression)||is(typeof(this):Type)))
					if(x.sstate == SemState.completed) x = x.constFold();
				}
			});
		}
		return r;
	}();

}

template SemChld(string s){ // perform semantic analysis on child node, propagate all errors
	enum SemChld=_SemChldImpl!(s,q{semantic(sc)})~PropErr!s;
}

template SemChldPar(string s){
	enum SemChldPar=_SemChldImpl!(s,q{semantic(sc)});
}

template SemChldExp(string s){ // perform semantic analysis on child node, require that it is an expression
	enum SemChldExp=_SemChldImpl!(s,q{expSemantic(sc)})~PropErr!s;
}


enum SemState:ubyte{
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
	needRetry = false;
	return this;
};
enum ErrEplg=q{
	sstate=SemState.error;
	needRetry = false;
	return this;
};

bool gRetryAgain = false; // TODO: fix this

enum RetryEplg=q{
	if(!needRetry) gRetryAgain = true; // TODO: fix this
	needRetry = true;
	return this;
};

template Semantic(T) if(is(T==Node)){
	// TODO: needRetry and sstate could be final properties to save one byte of space
	// profile to see if it is worth it.
	SemState sstate = SemState.begin;
	bool needRetry = false;

	invariant(){assert(sstate!=SemState.error||!needRetry);}

	Node semantic(Scope s)in{assert(sstate>=SemState.begin);}body{
		s.error("unimplemented feature",loc);
		mixin(ErrEplg);
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
	invariant(){
		assert(sstate != SemState.completed || type && type.sstate == SemState.completed);
	}
	override Expression semantic(Scope sc){ sc.error("unimplemented feature",loc); sstate = SemState.error; return this; }

	Type typeSemantic(Scope sc){
		Expression me;
		if(sstate != SemState.completed){ // TODO: is this ok?
			me = semantic(sc);
			if(auto ty=me.isType()) return ty;
			// TODO: is it possible that propagating retry would be required?
			if(me.sstate == SemState.error) return New!ErrorTy();
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

	bool isConstant(){ return false; }

	final Expression constFold()in{assert(sstate == SemState.completed);}body{
		if(!isConstant()) return this;
		//import std.stdio; wrietln("folding constant ", this);
		return interpret(null);
	}

	Expression isLvalue(){return null;}

	final bool checkMutate(Scope sc, ref Location l){ // should be const ref location...
		if(isLvalue()){
			if(type.isMutable()) return true;
			else sc.error(format("%s '%s' of type '%s' is read-only",kind,loc.rep,type),l);
		}else sc.error(format("%s '%s' is not an lvalue",kind,loc.rep),l);
		return false;
	}

	bool implicitlyConvertsTo(Type rhs){
		if(type.implicitlyConvertsTo(rhs)) return true;
		auto l = type.getHeadUnqual().isIntegral(), r = rhs.getHeadUnqual().isIntegral();
		if(l && r){
			// note: r.getLongRange is always valid for basic types
			if(l.op == Tok!"long" || l.op == Tok!"ulong") return r.getLongRange().contains(getLongRange());
			return r.getIntRange().contains(this.getIntRange());
		}
		return false;
	}
	final Expression implicitlyConvertTo(Type to)in{assert(to.sstate == SemState.completed);}body{
		if(type is to) return this;
		auto r = New!ImplicitCastExp(to,this);
		r.loc = loc;
		return r;
	}
	bool typeEquals(Type rhs)in{assert(sstate == SemState.completed);}body{
		return type.equals(rhs);
	}

	bool convertsTo(Type rhs)in{assert(sstate == SemState.completed);}body{
		if(type.convertsTo(rhs.getUnqual().getConst())) return true;
		if(implicitlyConvertsTo(rhs.getUnqual().getConst())) return true;
		return false;
	}

	final Expression convertTo(Type to)in{assert(type&&to);}body{
		if(type is to) return this;
		auto r = New!CastExp(STC.init,to,this);
		r.loc = loc;
		return r;
	}

	Expression matchCall(scope Expression[] args, ref MatchContext context){
		return null;
	}
	void matchError(Scope sc, Location loc, Expression[] args){
		sc.error(format("%s '%s' is not callable",kind,toString()),loc);
	}

	IntRange getIntRange(){return type.getIntRange();}
	LongRange getLongRange(){return type.getLongRange();}
}
//pragma(msg, __traits(classInstanceSize,Expression)); // 0u. TODO: reduce and report

mixin template Semantic(T) if(is(T==LiteralExp)){
	override LiteralExp semantic(Scope sc){
	/+theswitch: switch(lit.type){
			foreach(x; ToTuple!literals){
				static if(x!="' '"&&x!="true"&&x!="false"){
					case Tok!x: type=Type.get!(typeof(mixin(x)))(); break theswitch;
				}
			}
			case Tok!"' '":
				if(lit.int64<128) type=Type.get!char();
				else type=Type.get!dchar(); break;
			case Tok!"true", Tok!"false":
				type=Type.get!bool(); break;
				lit.int64=lit.type == Tok!"true";
			default: assert(0, to!string(lit.type)~" is not a valid literal type");
		}+/
		type = value.getType();
		mixin(SemEplg);
	}

	override bool isConstant(){ return true; }

	final bool isPolyString(){return lit.type == Tok!"``";}

	override bool typeEquals(Type rhs){
		if(super.typeEquals(rhs)) return true;
		if(!isPolyString()) return false;
		return rhs is Type.get!wstring()||rhs is Type.get!dstring();
	}

	override bool implicitlyConvertsTo(Type rhs){
		if(super.implicitlyConvertsTo(rhs)) return true;
		if(!isPolyString()) return false;
		return Type.get!wstring().implicitlyConvertsTo(rhs)
			|| Type.get!dstring().implicitlyConvertsTo(rhs);
	}


	override IntRange getIntRange(){
		switch(lit.type){
			case Tok!"' '":
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
			case Tok!"' '", Tok!"0", Tok!"0U", Tok!"0L":
			case Tok!"true", Tok!"false":
				return LongRange(lit.int64,lit.int64,signed);
			default: return super.getLongRange();
		}
	}
}

enum Match{
	none,
	convert,
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
		if(!lit.length){type=Type.get!EmptyArray(); mixin(SemEplg);}
		mixin(SemChld!q{lit});
		auto ty=lit[0].type;
		foreach(x;lit[1..$]){
			if(auto newty=ty.combine(x.type)) ty=newty;
			else{
				sc.error(format("incompatible type '%s' in array of '%s'",x.type,ty),x.loc);
				mixin(ErrEplg);
			}
		}
		// TODO: implicit casts
		foreach(ref x; lit) x = x.implicitlyConvertTo(ty);
		mixin(SemChldPar!q{lit});
		assert(all!(_=>_.sstate == SemState.completed)(lit));
		type=ty.getDynArr();
		mixin(SemEplg);
	}

	override bool isConstant(){
		foreach(x; lit) if(!x.isConstant()) return false;
		return true;
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
		if(!isConstant()){
			e = e.constFold();
			foreach(ref x; a) x = x.constFold();
		}
		if(auto ty=e.isType()){
			// TODO: TypeTuple slice
			if(!a.length) return ty.getDynArr();
			return super.semantic(sc); // TODO: implement
		}else{
			auto ty = e.type.getHeadUnqual();
			bool isEmpty = false;
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
			}else if(ty is Type.get!EmptyArray()){
				type = Type.get!void();
				isEmpty = true;
			}else{ // TODO: operator overloading
				sc.error(format("'%s' is not indexable", e.type),loc);
				mixin(ErrEplg);
			} // it is a dynamic array, an array or pointer type
			if(!a.length) type = type.getDynArr();
			else{
				if(a.length>1){
					sc.error(format("can only use one index to index '%s'",e.type),a[1].loc.to(a[$-1].loc));
					mixin(ErrEplg);
				}
				auto s_t = Type.get!Size_t();
				a[0] = a[0].implicitlyConvertTo(s_t);
				mixin(SemChld!q{a[0]});
				e = e.constFold();
				// TODO: length could be a maximum
				ulong length;
				if(auto le = e.isArrayLiteralExp())
					length = le.lit.length;
				else if(e.isConstant()){
					auto v = e.interpretV(); // TODO: this is inefficient
					length = v.length;
				}else if(!isEmpty) goto after;
				//import std.stdio; wrietln("duh ",e,length);
				LongRange rng;
				if(s_t is Type.get!uint()){
					auto r = a[0].getIntRange();
					rng = LongRange(r.min, r.max,false);
				}else{
					assert(s_t is Type.get!ulong());
					rng = a[0].getLongRange();
				}
				if(!length||!rng.overlaps(LongRange(0,length-1,false))){
					a[0]=a[0].constFold();
					sc.error(format("array index %s is out of bounds [0U..%dU)",a[0].toString(),length),loc);
					mixin(ErrEplg);
				}
			after:;
			}
			mixin(SemEplg);
		}
	}

	override bool isConstant(){
		if(!a.length) return e.isConstant();
		assert(a.length==1,to!string(this));
		return e.isConstant() && a[0].isConstant();
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
		if(e.isLvalue()) return this;
		return null;
	}
/+ // TODO (?)
	static string __dgliteralRng(){
		string r;
		foreach(x;["IntRange", "LongRange"]){
			r~=mixin(X!q{
				override @(x) get@(x)(){
					if(ty.isArrayTy()||ty.isDynArrTy()){
						
					}else return super.get@(x)(); // TODO: associative arrays
				}
			});
		}
		return r;
	}
	mixin(__dgliteralRng());
+/

}

mixin template Semantic(T) if(is(T==SliceExp)){
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e,l,r});
		// mixin(MaybeFold!q{e,l,r}); // TODO: this is better
		if(!isConstant()){
			e = e.constFold();
			l = l.constFold();
			r = r.constFold();
		}
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
			mixin(PropRetry!q{l}); // TODO: is this needed?
			r = r.implicitlyConvertTo(s_t).semantic(sc);
			mixin(PropRetry!q{r});
			mixin(PropErr!q{l,r});

			// TODO: remove code duplication between here and IndexExp.semantic
			// TODO: length could be a maximum
			ulong length;
			if(auto le = e.isArrayLiteralExp())
				length = le.lit.length;
			else if(e.isConstant()){
				auto v = e.interpretV(); // TODO: this is inefficient
				length = v.length;
			}
			LongRange[2] rng;
			if(s_t is Type.get!uint()){
				auto r1 = l.getIntRange(), r2 = r.getIntRange();
				rng[0] = LongRange(r1.min, r1.max,false);
				rng[1] = LongRange(r2.min, r2.max,false);
			}else{
				assert(s_t is Type.get!ulong());
				rng[0] = l.getLongRange();
				rng[1] = r.getLongRange();
			}
			if(!rng[0].overlaps(LongRange(0,length-1,false))
			|| !rng[1].overlaps(LongRange(0,length,false))){
				l=l.constFold(); r=r.constFold();
				sc.error(format("slice indices [%s..%s] are out of bounds [0U..%dU]",l.toString(),r.toString(),length),loc);
				mixin(ErrEplg);
			}
			if(s_t is Type.get!uint() && l.getIntRange().gr(r.getIntRange())
			|| s_t is Type.get!ulong() && l.getLongRange().gr(r.getLongRange())){
				sc.error("lower bound exceeds upper bound",l.loc.to(r.loc));
				mixin(ErrEplg);
			}

			mixin(SemEplg);
		}
	}
	override Type typeSemantic(Scope sc){
		// mixin(SemPrlg);
		// TODO: TypeTuple slice
		return super.typeSemantic(sc);
	}
	override bool isConstant(){
		return e.isConstant() && l.isConstant() && r.isConstant();
	}
}

mixin template Semantic(T) if(is(T _==UnaryExp!S,TokenType S)){
	static if(is(T _==UnaryExp!S,TokenType S)):
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChldExp!q{e});
		static if(S!=Tok!"&"&&S!=Tok!"!") auto ty=e.type.getHeadUnqual();
		static if(S==Tok!"!"){
			auto bl = Type.get!bool();
			e = e.convertTo(bl);
			mixin(SemChldExp!q{e});
			mixin(PropRetry!q{e});
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

	// TODO: constant addresses should be possible to be taken too
	static if(S==Tok!"+"||S==Tok!"-"||S==Tok!"~"||S==Tok!"!")
	override bool isConstant(){
		return e.isConstant();
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
		auto c1 = e1.isConstant(), c2 = e2.isConstant();
		if(c1^c2){ // if both are constant, then the entire expression will be folded
			if(c1) e1 = e1.constFold();
			else e2 = e2.constFold();
		}
		static if(isAssignOp(S)){
			// TODO: array ops
			if(e1.checkMutate(sc,loc)){
				type = e1.type;
				e2=e2.implicitlyConvertTo(type); // TODO: optimization: this would not need to check again
				mixin(SemChld!q{e2});
				e2 = e2.constFold();
				/+if(e2.implicitlyConvertsTo(type)){
					...
				}else{
					sc.error(format("assigning to a '%s' from incompatible type '%s'",
					                e1.type.toString(), e2.type.toString()), loc);
					mixin(ErrEplg);
				}+/
				mixin(SemEplg);
			}else mixin(ErrEplg);
			//sc.error(format("expression '%s' is not assignable",e1.loc.rep),loc);
		}else static if(S==Tok!"in"||S==Tok!"!in"||S==Tok!"is"||S==Tok!"!is"){
			type = Type.get!bool();
			return super.semantic(sc);// TODO: implement
		}else static if(isRelationalOp(S)){
			if(auto ty=e1.type.combine(e2.type)){
				auto tyu=ty.getHeadUnqual();
				if(tyu.isBasicType() || tyu.isPointerTy() || tyu.getElementType()){
					e1 = e1.implicitlyConvertTo(ty);
					e2 = e2.implicitlyConvertTo(ty);
					mixin(SemChld!q{e1,e2});
					assert(e1.sstate == SemState.completed
					    && e2.sstate == SemState.completed);
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
			// TODO:
			/+else{ // element-wise compare even succeeds when there is no common type
				Type el1=e1.type.getElementType(),el2=e2.type.getElementType();
				if(el1 && el2){
					// TODO: stub exp strategies are inefficient
					Expression x=New!(BinaryExp!S)(New!StubExp(el1),New!StubExp(el2));
					type = Type.get!bool();
					mixin(SemChld!q{x});
					mixin(SemEplg);
				}
			}+/
			// TODO: Associative arrays
			// TODO: operator overloading
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
						e1 = e1.implicitlyConvertTo(t1);
						mixin(SemChld!q{e1});
						assert(e1.sstate == SemState.completed);
						type = t1;
						int valid = true;
						bool narrow;
						if(bt1.bitSize()==32) narrow = true;
						else{narrow = false;assert(bt1.bitSize()==64);}
						if(bt2.bitSize()==32){
							auto r = e2.getIntRange();
							if(!r.overlaps(IntRange(0,narrow?31:63,r.signed))) valid = false;
						}else{
							assert(bt2.bitSize()==64);
							auto r = e2.getLongRange();
							if(!r.overlaps(LongRange(0,narrow?31:63,r.signed))) valid = false;
						}
						if(!valid){
							sc.error(format("shift amount is outside the range 0..%d",narrow?31:63),loc);
							mixin(ErrEplg);
						}
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
						e1 = e1.implicitlyConvertTo(ty);
						e2 = e2.implicitlyConvertTo(ty);
						mixin(SemChld!q{e1,e2});
						assert(e1.sstate == SemState.completed
						    && e2.sstate == SemState.completed);
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
				Type el1 = t1.getElementType(), el2 = t2.getElementType();
				bool f1 = !!el1, f2 = !!el2;

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
						}else{ // TODO: there might be a better place/approach for this logic
							auto l1 = e1.isLiteralExp(), l2 = e2.isLiteralExp();
							Type elo;
							if(l1 && l1.isPolyString()) elo = el2;
							else if(l2 && l2.isPolyString()) elo = el1;
							if(elo){
								auto elou = elo.getHeadUnqual();
								import std.typetuple;
								foreach(T; TypeTuple!(char,wchar,dchar)){
									if(elou is Type.get!T()){
										type = type.get!(immutable(T)).refCombine(elo,0);
										break;
									}
								}
							}
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
					if(f1) e1 = e1.implicitlyConvertTo(type).semantic(sc);
					if(f2) e2 = e2.implicitlyConvertTo(type).semantic(sc);
					mixin(SemChld!q{e1,e2});
					assert(e1.sstate == SemState.completed
					    && e2.sstate == SemState.completed);
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

	override bool isConstant(){
		return e1.isConstant() && e2.isConstant();
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
					static if(isArithmeticOp(S) || isShiftOp(S) || isBitwiseOp(S)){
						return mixin(`e1.get@(x)()`~TokChars!S~`e2.get@(x)()`);
					}else static if(S==Tok!"," || isAssignOp(S)){
						return e2.get@(x)();
					}else static if(isIntRelationalOp(S)){
						auto it = e1.type.isIntegral();
						if(!it) return @(x)(0,1,true);
						// TODO: make more efficient
						LongRange r1, r2;
						if(it.bitSize()<=32){
							auto ir1 = e1.getIntRange();
							auto ir2 = e2.getIntRange();
							if(ir1.signed){
								assert(ir2.signed);
								r1 = LongRange(cast(int)ir1.min,cast(int)ir1.max,true);
								r2 = LongRange(cast(int)ir2.min,cast(int)ir2.max,true);
							}else{
								assert(!ir1.signed);
								r1 = LongRange(ir1.min,ir1.max,true);
								r2 = LongRange(ir2.min,ir2.max,true);
							}
						}else r1 = e1.getLongRange(), r2 = e2.getLongRange();

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

template Semantic(T) if(is(T==TernaryExp)){
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e1});
		mixin(PropRetry!q{e1}); // TODO: is this needed?
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

	bool isConstant(){
		return e1.isConstant() && e2.isConstant() && e3.isConstant();
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

mixin template Semantic(T) if(is(T==IsExp)){
	override Expression semantic(Scope sc){
		if(!gscope) gscope = New!GaggingScope(sc);
		auto f = ty.typeSemantic(gscope);
		mixin(PropRetry!q{f});
		if(f.sstate == SemState.error) goto no;
		Token tok;
		switch(which){
			case WhichIsExp.type:
				goto yes;
			case WhichIsExp.isEqual, WhichIsExp.implicitlyConverts:
				if(tparams.length) goto default;
				if(tySpec){
					auto g = tySpec.typeSemantic(gscope);
					mixin(PropRetry!q{g});
					if(g.sstate == SemState.error) goto no;
					if(which == WhichIsExp.isEqual && f.equals(g) ||
					   which == WhichIsExp.implicitlyConverts && f.implicitlyConvertsTo(g))
						goto yes;
					else goto no;
				}
			default: return super.semantic(sc);
		}
	yes:
		tok = token!"true";
		goto ret;
	no:
		tok = token!"false";
		goto ret;
	ret:
		auto result = New!LiteralExp(tok).semantic(sc);
		result.loc = loc;
		return result;
	}
private:
	GaggingScope gscope;
}


// abstracts a symbol. almost all circular dependency diagnostics are located here.
// CallExp is aware of the possibility circular dependencies too, because it plays an
// important role in overloaded symbol resolution
// note: instances of this class have an identity independent from the referenced declaration
class Symbol: Expression{ // semantic node
	Declaration meaning;
	protected this(){} // subclass can construct parent lazily
	this(Declaration m)in{assert(m&&1);}body{meaning = m;}

	// TODO: always display the exact cycle that caused the error
	private enum CircErrMsg=q{
		if(circ){
			if(circ is this) circ = null;
			else scope_.note("part of dependency cycle here",loc);
			needRetry = false; // TODO: is this ok?
			sstate = SemState.error;
			meaning.sstate = SemState.error;
		}
	};
	private static Symbol circ = null;

	override Symbol semantic(Scope sc){
		mixin(SemPrlg);
		scope_=sc;
		assert(!!meaning);

		if(needRetry){
			sstate = SemState.begin; // TODO: ok?
			//needRetry = false;
		}
		if(sstate >= SemState.started){
			sc.error("circular dependencies are illegal",loc);
			if(!circ) circ = this;
			sstate = SemState.error;
			mixin(RetryEplg);
			//mixin(ErrEplg);
		}else sstate = SemState.started;
		// those are not virtual functions because of centralized symbol dependency handling
		if(auto vd=meaning.isVarDecl()){
			if(!vd.type || vd.stc & STCenum){
				meaning = meaning.semantic(meaning.scope_);
				mixin(CircErrMsg);
				mixin(PropRetry!q{meaning});
				mixin(PropErr!q{meaning});
			}
			assert(!!vd.type);
			type=vd.type.semantic(meaning.scope_);
		}else if(auto fd=meaning.isFunctionDecl()){
			if(fd.type.hasUnresolvedReturn()){
				meaning = meaning.semantic(meaning.scope_);
				mixin(CircErrMsg);
				mixin(PropRetry!q{meaning});
				mixin(PropErr!q{meaning});
			}
			type = fd.type = fd.type.semantic(meaning.scope_);
		}else if(typeid(this.meaning) is typeid(ErrorDecl)){mixin(ErrEplg);}
		// TODO: templates
		else type=Type.get!void(); // same as DMD
		mixin(CircErrMsg);
		mixin(PropRetry!q{type});
		mixin(PropErr!q{type});
		assert(!meaning.isFunctionDecl()||(cast(FunctionTy)type).ret);

		mixin(SemEplg);
	}
	override string toString(){return meaning.name;}
	override @property string kind(){return meaning.kind;}

	override bool isConstant(){
		//if(meaning.stc|STCstatic) return true;
		if(auto vd = meaning.isVarDecl()){
			if(vd.stc&STCenum) return true;
			if(vd.stc&STCimmutable && vd.init) return vd.init.isConstant();
		}
		return false;
	}
	/+ // DMD 2.058/2.059 behave approximately like this:
	override bool typeEquals(Type rhs){
		if(!(meaning.stc&STCenum)) return super.typeEquals(rhs);
		if(auto vd = meaning.isVarDecl()) return vd.init.typeEquals(rhs);
		return super.typeEquals(rhs);
	}+/

	// override Type isType(){...} // TODO.
	override Expression isLvalue(){
		//import std.stdio; wrietln(meaning," ",meaning.stc);
		if(meaning.isVarDecl() && !(meaning.stc&STCenum)) return this;
		return null;
	}

	/* This assumes that the reference to the Symbol is kept unique during SA
	 */
	override Expression matchCall(scope Expression[] args, ref MatchContext context){
		if(auto m = meaning.matchCall(args, context)){
			// resolve the overload in place and then rely on
			// semantic to catch eventual circular dependencies:

			if(m is meaning) return this; // common case
			mixin(CircErrMsg);
			meaning = m;
			sstate = SemState.begin;
			type = null;
			return Symbol.semantic(scope_);
		}
		return null;
	}
	override void matchError(Scope sc, Location loc, scope Expression[] args){
		meaning.matchError(sc,loc,args);
	}


	import vrange;
	override IntRange getIntRange(){
		if(auto vd=meaning.isVarDecl()){
			if(vd.stc&STCenum || vd.stc&STCstatic&&vd.stc&STCimmutable)
				return vd.init.getIntRange();
		}
		return super.getIntRange();
	}
	override LongRange getLongRange(){
		if(auto vd=meaning.isVarDecl()){
			if(vd.stc&STCenum || vd.stc&STCstatic&&vd.stc&STCimmutable)
				return vd.init.getLongRange();
		}
		return super.getLongRange();
	}




	mixin Interpret!Symbol;

private:
	Scope scope_;
}
// aware of circular dependencies
mixin template Semantic(T) if(is(T==CallExp)){
	override Expression semantic(Scope sc){ // TODO: type checking
		mixin(SemPrlg);
		mixin(SemChld!q{e,args});
		MatchContext context;
		if(auto c = fun !is null ? fun : e.matchCall(args, context)){
			fun = c;
			mixin(PropRetry!q{fun});
			mixin(PropErr!q{fun});
		}else{
			mixin(PropRetry!q{e});
			mixin(PropErr!q{}); // display error only once
			e.matchError(sc,loc, args);
			mixin(ErrEplg);
		}
		if(auto tt = fun.type.isFunctionTy()){
			type = tt.ret.resolveInout(context.inoutRes);
			foreach(i,x; tt.params[0..args.length]){
				auto pty = x.type.resolveInout(context.inoutRes);
				args[i]=args[i].implicitlyConvertTo(pty);
			}
		}else{
			sc.error("delegate and function pointer invocation unimplemented",loc);
			type = Type.get!void(); // TODO: fix
		}
		// TODO: convert arguments types
		mixin(SemEplg);
	}
private:
	Expression fun;
}


// everything concerning error gagging is centralized here
import error;
class GaggingErrorHandler: ErrorHandler{
	override void error(lazy string, Location){ /* do nothing */ }
	override void note(lazy string, Location){ /* do nothing */ }
}

class GaggingScope: Scope{
	Scope parent;
	this(Scope parent){this.parent = parent;super(New!GaggingErrorHandler());}
	override bool insert(Declaration decl){assert(0);} // cannot insert into gagging scope

	override void error(lazy string, Location){ /* do nothing */ }
	override void note(lazy string, Location){ /* do nothing */ }

	// forward other members:
	override Declaration lookup(Identifier ident, lazy Declaration alt){
		return parent.lookup(ident,alt);}
	override Declaration lookup(Identifier ident){
		// silence error message
		return parent.lookup(ident, New!ErrorDecl());
	}
	override FunctionDef getFunction(){return parent.getFunction();}
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
			mixin(PropRetry!q{type});
			mixin(PropErr!q{type});
		}
		if(e.convertsTo(type)){mixin(SemEplg);}
		sc.error(format("cannot cast expression '%s' of type '%s' to '%s'",e.loc.rep,e.type,type),e.loc); // TODO: replace toString with actual representation
		//error(format("no viable conversion from type '%s' to '%s'",e.type,type),e.loc);
		mixin(ErrEplg);
	}

	override bool isConstant(){
		// if conversion is fancy, it has already been rewritten at this point
		// TODO: maybe assert on this fact?
		return e.isConstant();
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
			assert(osiz<=32);
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
		auto tt=ty.semantic(sc);
		mixin(PropRetry!q{tt});
		type = tt.isType();
		assert(!!type); // if not a type the program is in error
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
		return super.semantic(sc);
	}
}

mixin template Semantic(T) if(is(T==FunctionLiteralExp)){
	override Symbol semantic(Scope sc){
		assert(sstate != SemState.completed);
		if(!fty) fty=New!FunctionTy(STC.init,cast(Expression)null,cast(Parameter[])null,VarArgs.none);
		auto dg=New!FunctionDef(fty,New!Identifier(uniqueIdent("__dgliteral")),cast(BlockStm)null,cast(BlockStm)null,cast(Identifier)null,bdy);
		dg.sstate = SemState.begin;
		dg.scope_ = sc; // Symbol will use this scope to reason for analyzing DG
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
	Type getUnqual(){return this;}     // ditto

	Type getElementType(){return null;}

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
	   and for matching inout. the formal parameter type is adapted
	   to match the actual argument as good as possible.
	 */
	Type adaptTo(Type from, ref InoutRes inoutRes){
		return this;
	}

	Type resolveInout(InoutRes inoutRes){
		return this;
	}

	/* important for is-expressions and parameter matching:
	   function, delegate and function pointer types cannot always
	   be uniqued away, since they may include default parameters
	 */
	bool equals(Type rhs){
		return this is rhs;
	}

	override bool convertsTo(Type rhs){
		return implicitlyConvertsTo(rhs.getUnqual().getConst());
	}

	override bool implicitlyConvertsTo(Type rhs){
		return this.refConvertsTo(rhs.getHeadUnqual(),0);
	}

	final bool constConvertsTo(Type rhs){
		return this.getUnqual().equals(rhs.getUnqual())
		    && this.refConvertsTo(rhs,0);
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

	/* common type computation. roughly TDPL p60
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
		static if(is(T==FunctionTy)){
			if(rret){
				ret = rret.typeSemantic(sc);
				mixin(PropRetry!q{ret}); // TODO: needed?
			}
			foreach(p; params){
				if(p.sstate==SemState.pre) p.sstate = SemState.begin; // never insert into scope
				p.semantic(sc); // TODO: rewriting parameters ever needed?
			}
			foreach(p;params){mixin(PropRetry!q{p});}
			if(ret) mixin(PropErr!q{ret});
			mixin(PropErr!q{params});
			if(ret) mixin(SemEplg);
			else return this; // return type might contain an error once it is resolved.
		}else mixin(SemEplg);
	}
	static if(is(T==FunctionTy)){
		override Type getPointer(){return New!FunctionPtr(this);} // TODO: this is sub-optimal
		final bool hasAutoReturn(){return rret is null;}
		final bool hasUnresolvedReturn(){return rret is null && ret is null;}
		final void resolveReturn(Type to)in{
			assert(hasUnresolvedReturn());
			assert(!!to && to.sstate == SemState.completed);
		}body{
			ret = to;
		}
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
		return integralBitSize(op);
	}
	final bool isSigned()in{assert(!!isIntegral());}body{
		return integralIsSigned(op);
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

	override bool convertsTo(Type rhs){
		if(super.convertsTo(rhs)) return true;
		// all basic types can be interpreted in a boolean context
		if(rhs.getUnqual() is Type.get!bool()) return true;
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

	/* directly create a semantically analyzed instance
	 */
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

	invariant(){assert(sstate < SemState.started || ty); mixin(_restOfInvariant);}
	Type ty; // the 'T' in 'qualified(T)', the "qualifyee"
	override Type semantic(Scope sc){
		mixin(SemPrlg);
		ty=e.typeSemantic(sc);
		mixin(PropRetry!q{ty});
		mixin(PropErr!q{ty});
		Type r;
		static if(is(T==ConstTy)) r=ty.getConst();
		else static if(is(T==ImmutableTy)) r=ty.getImmutable();
		else static if(is(T==SharedTy)) r=ty.getShared();
		else static if(is(T==InoutTy)) r=ty.getInout();
		else static assert(0);

		return r.semantic(sc);
	}

	static if(is(T==ConstTy)||is(T==ImmutableTy)||is(T==InoutTy))
		override bool isMutable(){return false;}


	/* some general notes:
	   the order of qualifiers is shared(inout(const(T))) or immutable(T) if
	   sstate == SemState.completed. 'create' and 'semantic' establish this dented invariant.
	   some of the code below relies on this order. it does not operate correctly on
	   incorrectly ordered input.
	 */
	private enum _restOfInvariant=q{ // TODO: fix this as soon as muliple invariants allowed
		import std.typetuple;
		alias TypeTuple!("ImmutableTy","SharedTy","InoutTy","ConstTy") Order;
		if(sstate == SemState.completed){
			foreach(x; Order){
				static if(!is(T==ImmutableTy)) if(x==T.stringof) break;
				assert(!mixin(`(cast()ty).is`~x)(), to!string(cast()ty));
			}
		}
	};

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
		/* hand through adaptTo and resolveInout calls
		 */
		override Type adaptTo(Type from, ref InoutRes res){
			return mixin(`ty.getTail`~qual~`().adaptTo(from, res).get`~qual)();
		}
		override Type resolveInout(InoutRes res){
			return mixin(`ty.resolveInout(res).get`~qual)();
		}
	}

	override bool equals(Type rhs){
		if(auto d=mixin(`rhs.is`~T.stringof)()) return ty.equals(d.ty);
		return false;
	}

	override bool implicitlyConvertsTo(Type rhs){
		// getHeadUnqual never returns a qualified type ==> no recursion
		return getHeadUnqual().implicitlyConvertsTo(rhs.getHeadUnqual());
	}

	override bool convertsTo(Type rhs){
		return getUnqual().convertsTo(rhs);
	}

	override bool refConvertsTo(Type rhs, int num){
		if(this is rhs) return true;
		if(auto d=mixin(`rhs.is`~T.stringof)())
			static if(is(T==ConstTy) || is(T==ImmutableTy)){
				// const and immutable imply covariance
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

	/* the following methods are overridden in order to keep the qualifier order straight
	 */

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

	/* getHeadUnqual needs to tail-qualify the qualifyee
	 */
	override Type getHeadUnqual(){
		if(hunqualType) return hunqualType;
		return hunqualType=mixin(`ty.getHeadUnqual().getTail`~qual)();
	}

	override Type getUnqual(){
		if(unqualType) return unqualType;
		return unqualType=ty.getUnqual();
	}

	override Type getElementType(){ return getHeadUnqual().getElementType(); }

	override STC getHeadSTC(){
		return ty.getHeadSTC()|mixin("STC"~lowerf(qual));
	}


	/* tail-qualifying is done by tail-qualifying the qualifyee
	   and then head-qualifying back the result appropriately
	 */
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

	/* any part of the type may be transitively qualified by some
	   qualifier at most once. since immutable implies const (and
	   shared) and it is stronger than unqualified, immutable(inout(T-)-)
	   is simplified to immutable(T--)
	 */
	// TODO: analyze whether or not memoizing these is worthwhile
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
	Type unqualType;
}

/* helper for Semantic![PointerTy|DynArrTy|ArrayTy]
   creates the members getTail[Qualified] and in[Qualified]Context
   parameters:
     tail:    string evaluating to the tail of the type
     puthead: string evaluating to a member that puts the head back on the tail
 */
private mixin template GetTailOperations(string tail, string puthead){
	static string __dgliteralTailQualified(){// "delegate literals cannot be class members..."
		string r;
		foreach(q;typeQualifiers){
			r~=mixin(X!q{
				Type tail@(upperf(q))Type;
				override Type getTail@(upperf(q))(){
					if(tail@(upperf(q))Type) return tail@(upperf(q))Type;
					return tail@(upperf(q))Type=@(tail).get@(upperf(q))().@(puthead);
			    }
				override Type in@(upperf(q))Context(){ // TODO: analyze if memoizing worthwhile
					assert(@(tail)&&1);
					return @(tail).in@(upperf(q))Context().@(puthead);
				}
			});
		}
		return r;
	}
	mixin(__dgliteralTailQualified());
}

// TODO: make sure static arrays are treated like real value types
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
		ty=e.typeSemantic(sc);
		mixin(PropRetry!q{ty});
		mixin(PropErr!q{ty});
		Type r;
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

	override bool equals(Type rhs){
		if(auto c=mixin(`rhs.is`~T.stringof)()) return ty.equals(c.ty);
		return false;
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
	}
	override Type refCombine(Type rhs, int num){
		if(auto c=mixin(`rhs.is`~T.stringof)())
			if(auto d=ty.refCombine(c.ty,num+!is(T==ArrayTy)))
				return mixin(`d.`~puthead);
		return super.refCombine(rhs,num);
	}

	private enum puthead = "get"~(is(T==ArrayTy)?"Array(length)":typeof(this).stringof[0..$-2]~"()");
	mixin GetTailOperations!("ty", puthead);

	override Type getUnqual(){
		return mixin(`ty.getUnqual().`~puthead);
	}

	static if(is(T==ArrayTy) || is(T==DynArrTy)):
	override Type getElementType(){return ty;}
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
	static if(is(T==EmptyArrTy)){
		override Type getElementType(){
			assert(type is Type.get!void());
			return type;
		}
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
		mixin(PropRetry!q{f});
		mixin(PropErr!q{f});
		f = f.constFold(); // TODO: should this be done at all?
		if(f.isType()){
			sc.error(format("typeof argument '%s' is not an expression",e.loc.rep),e.loc);
			mixin(ErrEplg);
        }else e=f;
		if(!e.type) return Type.get!void();
		return e.type.semantic(sc);
	}
}

mixin template Semantic(T) if(is(T==ConditionDeclExp)){
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		if(!decl) decl=New!VarDecl(stc,ty,name,init).semantic(sc);
		mixin(PropRetry!q{decl});
		if(!sym) sym = name.semantic(sc);
		mixin(PropRetry!q{sym});
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
		//mixin(SemChld!q{s});
		size_t initial = current;
		foreach(i,ref x; s[initial..$]){
			mixin(SemChldPar!q{x});
			current = max(current, initial+1+i);
		}
		mixin(PropErr!q{s});
		mixin(SemEplg);
	}

	override BlockStm semantic(Scope sc){
		if(!mysc) mysc = New!BlockScope(sc);
		return semanticNoScope(mysc);
	}
private:
	Scope mysc = null;
	size_t current = 0; // points to the next child to be semantically analyzed
	invariant(){assert(sstate!=SemState.completed || current == s.length);}
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
		auto bl = Type.get!bool();
		e = e.semantic(tsc); // TODO: get rid of direct call
		if(e.sstate == SemState.completed) e = e.constFold();
		mixin(SemChldPar!q{e});
		mixin(PropRetry!q{e});
		if(e.sstate == SemState.completed) e = e.convertTo(bl).semantic(tsc); // TODO: ditto
		mixin(PropRetry!q{e});
		s1 = s1.semantic(tsc); // TODO: ditto
		mixin(PropRetry!q{s1});
		if(s2){
			if(!esc) esc = New!BlockScope(sc);
			s2 = s2.semantic(esc); // TODO: ditto
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
		auto bl = Type.get!bool();
		e = e.semantic(lsc); // TODO: ditto
		if(e.sstate == SemState.completed) e = e.constFold();
		mixin(PropRetry!q{e});
		if(e.sstate == SemState.completed) e = e.convertTo(bl).semantic(lsc);
		s = s.semantic(lsc); // TODO: ditto
		mixin(PropRetry!q{s});
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
		auto bl = Type.get!bool();
		s = s.semantic(lsc); // TODO: ditto
		mixin(PropRetry!q{s}); // TODO: needed?
		mixin(SemChldPar!q{e});// TODO: propose SemChld!q{scope=lsc, e}
		mixin(PropRetry!q{e});
		if(e.sstate == SemState.completed){
			e = e.convertTo(bl).semantic(lsc); // TODO: get rid of direct call
			e = e.constFold();
		}
		mixin(PropErr!q{s,e});
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
			else s1=s1.semantic(lsc); // TODO: get rid of direct call
			mixin(PropRetry!q{s1});
		}
		if(e1){
			e1=e1.semantic(lsc); // TODO: ditto
			mixin(PropRetry!q{e1});
			auto bl = Type.get!bool();
			if(e1.sstate == SemState.completed){
				e1 = e1.convertTo(bl).semantic(lsc);
				e1=e1.constFold();
			}
		}
		if(e2){
			e2=e2.semantic(lsc); // TODO: ditto
			if(e2.sstate == SemState.completed) e2=e2.constFold();
			mixin(PropRetry!q{e2});
		}
		s2=s2.semantic(lsc);
		mixin(PropRetry!q{s2});
		if(s1) mixin(PropErr!q{s1});
		if(e1) mixin(PropErr!q{e1});
		if(e2) mixin(PropErr!q{e2});
		mixin(PropErr!q{s2});
		mixin(SemEplg);
	}
private:
	BlockScope lsc;
}

mixin template Semantic(T) if(is(T==ForeachStm)){
	override ForeachStm semantic(Scope sc){
		mixin(SemPrlg);
		if(!lsc) lsc = New!BlockScope(sc);
		mixin(SemChld!q{aggregate});
		auto ty = aggregate.type;
		// foreach over built-in arrays
		Type et = null;
		if(auto tt = ty.isArrayTy()) et = tt.ty;
		if(auto tt = ty.isDynArrTy()) et = tt.ty;
		if(et){
			if(vars.length>2){
				sc.error("at most two loop variables allowed for array foreach",
				         vars[0].loc.to(vars[$-1].loc));
				mixin(ErrEplg);
			}else{
				assert(vars.length);
				if(vars.length == 2 && !curparam){
					auto s_t = Type.get!Size_t();
					if(vars[0].rtype){
						vars[0].type = vars[0].rtype.typeSemantic(lsc);
						mixin(PropErr!q{vars[0].rtype});
						if(!vars[0].type.implicitlyConvertsTo(s_t)){ // TODO: This is a stub
							sc.error(format("invalid type '%s' for index variable '%s'", vars[0].rtype.loc.rep, vars[0].name.toString()), vars[0].rtype.loc);
							sstate = SemState.error;
						}
					}else vars[0].type = s_t;
					curparam++;
				}
				if(curparam < vars.length){
					if(vars[curparam].rtype){
						vars[curparam].type = vars[curparam].rtype.typeSemantic(lsc);
						mixin(PropErr!q{vars[curparam].rtype});
						if(!et.implicitlyConvertsTo(vars[curparam].type)){
							sc.error(format("cannot implicitly convert from element type '%s' to '%s'", et.toString(), vars[curparam].rtype.loc.rep),vars[curparam].rtype.loc);
							sstate = SemState.error;
						}
					}else vars[curparam].type = ty;
					curparam++;
				}
			}
		}
		// TODO: foreach over string types with automatic decoding
		// TODO: foreach over associative arrays
		// TODO: foreach over ranges
		// TODO: foreach with opApply
		// TODO: foreach over delegates
		// TODO: foreach over Tuples
		foreach(var; vars) var.semantic(lsc); // TODO: fix?
		//mixin(SemChld!q{scope=lsc, bdy}); // TODO: implement this
		bdy = bdy.semantic(lsc);
		mixin(PropErr!q{vars, aggregate});
		mixin(SemEplg);
	}

private:
	BlockScope lsc;
	size_t curparam=0;
}

mixin template Semantic(T) if(is(T==ReturnStm)){
	override ReturnStm semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChldPar!q{e});
		mixin(PropRetry!q{e});
		// TODO: match with function return type
		auto fun = sc.getFunction();
		assert(fun && fun.type);
		if(fun.type.hasUnresolvedReturn()){
			if(e.sstate == SemState.completed){
				fun.type.resolveReturn(e.type);
				mixin(RetryEplg);
			}else{
				fun.type.ret = New!ErrorTy();
				fun.sstate = SemState.error; // avoid spurious error messages
				fun.needRetry = false;
				mixin(PropErr!q{e});
			}
		}else{
			mixin(PropErr!q{fun.type.ret});
			e = e.implicitlyConvertTo(fun.type.ret);
			mixin(SemChld!q{e});
		}
		mixin(SemEplg);
	}
}

// declarations
mixin template Semantic(T) if(is(T==Declaration)){
	Scope scope_ = null;

	invariant(){assert(sstate != SemState.pre || !scope_);}

	// TODO: reduce DMD bug in presence of the out contract
	Declaration presemantic(Scope sc){//out(result){
		//assert(result is this); // TODO: remove return type?
		//}body{ // insert into symbol table, but don't do the heavy processing yet
		if(sstate != SemState.pre) return this;
		sstate = SemState.begin;
		if(!name){sc.error("unimplemented feature "~to!string(typeid(this)),loc); sstate = SemState.error; return this;} // TODO: obvious
		if(!sc.insert(this)) sstate = SemState.error;
		return this;
	}
	override Declaration semantic(Scope sc){
		mixin(SemPrlg);
		if(sstate==SemState.pre){
			auto ps=presemantic(sc);
			//if(ps!is this) return ps.semantic(sc);
		}
		mixin(SemEplg);
	}

	FunctionDecl matchCall(scope Expression[] args, ref MatchContext context){
		return null;
	}
	void matchError(Scope sc, Location loc, scope Expression[] args){
		sc.error(format("%s '%s' is not callable",kind,name),loc);
	}
}
mixin template Semantic(T) if(is(T==VarDecl)){
	Type type;

	override VarDecl presemantic(Scope sc){return cast(VarDecl)cast(void*)super.presemantic(sc);}

	override VarDecl semantic(Scope sc){
		mixin(SemPrlg);
		if(rtype){
			type=rtype.typeSemantic(sc);
			mixin(PropRetry!q{type});
		}
		if(init){
			init=init.expSemantic(sc);
			mixin(PropRetry!q{init});
			// deduce type
			if(!type && init.sstate!=SemState.error) type=init.type;
		}else if(!type){
			sc.error(format("initializer required for '%s' declaration",STCtoString(stc)),loc);
			mixin(ErrEplg);
		}
		if(sstate == SemState.pre && name){ // insert into scope
			// TODO: replace by call to presemantic (?)
			if(!sc.insert(this)){mixin(ErrEplg);}
			sstate = SemState.begin;
		}
		if(!type||type.sstate==SemState.error) mixin(ErrEplg); // deliberately don't propagate init's semantic 'error' state if possible
		type = type.applySTC(stc).checkVarDecl(sc,this);
		mixin(PropErr!q{type});

		if(init){
			init=init.implicitlyConvertTo(type);
			mixin(SemChldPar!q{init});
			if(stc&STCenum || stc&STCstatic){
				mixin(PropErr!q{init});
				assert(init.sstate == SemState.completed, to!string(init));
				init = init.interpret(sc);
				mixin(PropRetry!q{init});
				mixin(PropErr!q{init});
			}
			/+if(init.implicitlyConvertsTo(type)){
				... 
			}else{
				sc.error(format("initializing '%s' from incompatible type '%s'",rtype.loc.rep,init.type.toString()),loc);
				mixin(ErrEplg);
			}+/
		}else if(stc&STCenum){
			sc.error("manifest constants must have initializers",loc);
			mixin(ErrEplg);
		}

		mixin(SemEplg);
	}
}

mixin template Semantic(T) if(is(T==EmptyDecl)){
	override EmptyDecl presemantic(Scope sc){
		if(sstate == SemState.pre) sstate = SemState.begin;
		scope_ = sc;
		return this;
	}
	override EmptyDecl semantic(Scope sc){
		mixin(SemEplg);
	}
}


mixin template Semantic(T) if(is(T==StaticAssertDecl)){
	override StaticAssertDecl presemantic(Scope sc){
		if(sstate == SemState.pre) sstate = SemState.begin;
		return this;
	}
	override StaticAssertDecl semantic(Scope sc){
		mixin(SemPrlg);
		if(a.length<1){
			sc.error("missing arguments to static assert", loc);
			mixin(ErrEplg);
		}else if(a.length>2){
			sc.error("too many arguments to static assert", loc);
			mixin(ErrEplg);
		}
		mixin(SemChld!q{a});
		a[0] = a[0].convertTo(Type.get!bool());
		mixin(SemChld!q{a[0]});
		foreach(ref x;a){
			x = x.interpret(sc);
			mixin(PropRetry!q{x});
		}
		mixin(PropErr!q{a});
		if(!a[0].interpretV()){
			if(a.length == 1)
				sc.error(format("static assertion failure: '%s' is false",a[0].loc.rep), loc);
			else{
				sc.error(a[1].interpretV().get!string(), loc);
			}
		}
		mixin(SemEplg);
	}
}

mixin template Semantic(T) if(is(T==AliasDecl)){
	//override AliasDecl semantic(Scope sc){
	//	return this;
	//}
}


mixin template Semantic(T) if(is(T==BlockDecl)){
	override BlockDecl presemantic(Scope sc){
		foreach(ref x; decls) x=x.presemantic(sc);
		sstate = SemState.begin;
		return this;
	}
	override BlockDecl semantic(Scope sc){
		foreach(ref x; decls) x=x.semantic(sc); // TODO: get rid of direct call
		foreach(ref x; decls) mixin(PropRetry!q{x});
		mixin(PropErr!q{decls});
		return this;
	}
}


mixin template Semantic(T) if(is(T==Parameter)){
	override VarDecl presemantic(Scope sc){
		if(!name) return this;
		return super.presemantic(sc);
	}
}

mixin template Semantic(T) if(is(T==CArrayDecl)){
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
		if(sstate!=SemState.pre) return this;
		scope_=sc;
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

	private static struct Matched{ // local structs cannot be qualified yet
		MatchContext context;      // TODO: move into matchCall
		FunctionDecl decl;
	}

	override FunctionDecl matchCall(scope Expression[] args, ref MatchContext context){
		if(decls.length == 1) return decls[0].matchCall(args,context);
		auto matches = new Matched[decls.length]; // pointless GC allocation
		foreach(i,decl; decls) matches[i].decl = decls[i].matchCall(args, matches[i].context);

		auto best = reduce!max(map!(_=>_.context.match)(matches));
		//auto best = reduce!max(map!((_){return _.context.match;})(matches));
		if(best == Match.none){
			context.match = Match.none;
			altCand = -1;
			return null;
		}
		//TODO: the following line causes an ICE, reduce.
		//auto bestMatches = matches.partition!(_=>_.context.match!=best)();
		//auto numBest = bestMatches.length;
		size_t numBest = 0;
		for(size_t i=0;i<matches.length;i++){
			if(matches[i].context.match==best)
				swap(matches[numBest++], matches[i]);
		}
		if(numBest == 1){
			context = matches[0].context;
			return matches[0].decl;
		}
		auto bestMatches = matches[0..numBest];
		// find the most specialized match
		size_t candidate = 0;
		foreach(i, match; bestMatches[1..$]){
			// if there is a declaration that is at least as specialized
			// then it cannot be the unique best match
			if(match.decl.atLeastAsSpecialized(bestMatches[candidate].decl))
				candidate = i+1;
		}
		swap(bestMatches[0], bestMatches[candidate]);
		context = bestMatches[0].context;

		foreach(i, match; bestMatches[1..$]){
			if(!bestMatches[0].decl.atLeastAsSpecialized(match.decl)
			 || match.decl.atLeastAsSpecialized(bestMatches[0].decl)){
				// at least two identically good matches
				altCand = i+1;
				return null;
			}
		}
		altCand=candidate;
		return bestMatches[0].decl;
	}

	private size_t altCand; // TODO: somewhat fragile, maybe better to just recompute
	override void matchError(Scope sc, Location loc, scope Expression[] args){
		if(decls.length == 1) return decls[0].matchError(sc,loc,args);
		if(altCand==-1){
			sc.error(format("no matching function for call to '%s'",name), loc);
			foreach(decl; decls) sc.note("candidate function not viable", decl.loc);
		}else{
			assert(0 != altCand);
			// TODO: list all of the most specialized functions
			sc.error(format("call to '%s' is ambiguous",name), loc);
			sc.note("candidate function",decls[0].loc);
			sc.note("candidate function",decls[altCand].loc);
		}
	}
private:
	OverloadableDecl[] decls;
}

mixin template Semantic(T) if(is(T==FunctionDecl)){
	override FunctionDecl semantic(Scope sc){
		mixin(SemPrlg);
		if(type.hasAutoReturn()){
			sc.error("function body required for return type inference",loc);
			mixin(ErrEplg);
		}
		mixin(SemChld!q{type});
		mixin(SemEplg);
	}

	override FunctionDecl matchCall(scope Expression[] args, ref MatchContext context){
		// TODO: variadic arguments
		if(args.length > type.params.length ||
		   //any!(_=>_.init is null)(type.params[args.length..type.params.length])){
		   any!((_){return _.init is null;})(type.params[args.length..type.params.length])){
				context.match=Match.none;
				return null;
		}
		// semantically analyze the type if necessary
		type = type.semantic(scope_); // TODO: get rid of direct call
		mixin(PropRetry!q{type});

		immutable len = args.length;
		auto at = new Type[len]; // GC allocation, could be done on stack!
		// TODO: make behave like actual overloading
		foreach(i,p; type.params[0..len]){
			at[i] = p.type.adaptTo(args[i].type, context.inoutRes);
		}

		foreach(i,ref x;at) x = x.resolveInout(context.inoutRes);
		// the code that follows assumes the four matching level semantics
		static assert(Match.min == 0 && Match.max == Match.exact && Match.exact == 3);

		Match match = Match.exact;
		foreach(i,p; type.params[0..len]){
			if(args[i].typeEquals(at[i])) continue;
			if(!args[i].implicitlyConvertsTo(at[i])){
				match = Match.none;
				break;
			}else if(args[i].type.constConvertsTo(at[i])){
				if(match == Match.exact) match = Match.convConst;
			}else match = Match.convert; // Note: Match.none breaks the loop
		}
		context.match = match;
		return match == Match.none ? null : this;
	}

	bool atLeastAsSpecialized(FunctionDecl rhs){
		MatchContext dummy;
		// GC allocations, unneeded
		// TODO!: refactor
		//auto pt = array(map!(function Expression (_)=>new StubExp(_.type))(type.params));
		auto pt = array(map!(function Expression (_){return new StubExp(_.type);})(type.params));
		return !!rhs.matchCall(pt, dummy);
	}

	override void matchError(Scope sc, Location loc, scope Expression[] args){
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
					if(args[i].sstate == SemState.error) continue;
					// this is one of the few places where calling semantic
					// directly is justified:
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
		if(sstate == SemState.pre) presemantic(sc); // add self to parent scope

		mixin(SemChldPar!q{type});
		if(type.sstate == SemState.error) sstate = SemState.error;

		if(!fsc){
			fsc = New!FunctionScope(sc, this);
			// add parameters to function scope
			foreach(p; type.params) if(p.name) fsc.insert(p);
		}

		bdy.semanticNoScope(fsc); // TODO: is this ok?
		mixin(PropRetry!q{bdy});

		if(type.hasUnresolvedReturn()) type.resolveReturn(Type.get!void());
		mixin(PropErr!q{type, bdy});
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
		if(args.length<1){sc.error("missing arguments to pragma",loc); sstate=SemState.error; return this;}
		if(auto id=args[0].isIdentifier()){
			bool intprt = true;
			switch(id.name){
				case "__p":
					intprt = false;
				case "msg":
					if(args.length<2){if(bdy)mixin(SemChld!q{bdy}); mixin(SemEplg);}
					//foreach(ref x; args[1..$]) x = x.semantic(sc);
					mixin(SemChld!q{args[1..$]});
					foreach(x; args[1..$]){mixin(PropRetry!q{x});}
					mixin(PropErr!q{args[1..$]});
					if(intprt) foreach(ref x; args[1..$]) x = x.interpret(sc);
					foreach(x; args[1..$]){mixin(PropRetry!q{x});}
					mixin(PropErr!q{args[1..$]});
					import std.stdio;
					foreach(x; args[1..$])
						if(!x.isType()) stderr.write(x.interpretV().get!string());
						else stderr.write(x.toString());
					stderr.writeln();
					if(bdy) mixin(SemChld!q{bdy});
					mixin(PropRetry!q{bdy});
					mixin(PropErr!q{bdy});
					mixin(SemEplg);
				default: break;

				// some vendor specific pragmas
				case "__range":
					if(args.length!=2) break;
					mixin(SemChld!q{args[1]});
					mixin(PropErr!q{args[1]});
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
		sc.error(format("unrecognized pragma '%s'",args[0].loc.rep),args[0].loc); // TODO: option to ignore
		bdy = bdy.semantic(sc);
		mixin(ErrEplg);
	}
}

// string mixins

mixin template Semantic(T) if(is(T==MixinExp)||is(T==MixinStm)||is(T==MixinDecl)){
	static if(is(T==MixinExp)) alias Expression R; // workaround
	else static if(is(T==MixinStm)) alias Statement R;
	else static if(is(T==MixinDecl)) alias Declaration R;
	static if(is(R==Declaration)){
		override R presemantic(Scope sc){// TODO: module should not call presemantic on MixinDecl anyways
			if(sstate != SemState.pre) return this;
			sstate = SemState.begin;
			return this;
		}
	}
	override R semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e});
		// TODO: use get!string instead
		int which;
		Type[3] types = [Type.get!string(), Type.get!wstring(), Type.get!dstring()];
		foreach(i,t;types) if(!which && e.implicitlyConvertsTo(t)) which=i+1;
		if(!which){
			sc.error("expected string argument to string mixin", e.loc);
			mixin(ErrEplg);
		}		
		if(!e.checkInterpret(sc)) mixin(PropErr!q{e});
		foreach(i,t; types) if(i+1==which) e = e.convertTo(t).semantic(sc);
		assert(e.sstate == SemState.completed);
		auto str = e.interpretV().get!string();
		//str~=(is(T==MixinStm)&&str[$-1]!=';'?";":"")~"\0\0\0\0";
		str~="\0\0\0\0";
		Source src = New!Source("<mixin>", str);
		import parser;
		//auto handler = sc.handler;
		auto handler = New!StringMixinErrorHandler();
		auto ohan = sc.handler;
		sc.handler = handler;
		static if(is(T==MixinExp)) auto r=parseExpression(src,handler).semantic(sc);
		else static if(is(T==MixinStm)) auto r=New!BlockStm(parseStatements(src,handler)).semanticNoScope(sc); // TODO: use CompoundStm instead
		else static if(is(T==MixinDecl)) auto r=New!BlockDecl(STC.init,parseDeclDefs(src,handler)).semantic(sc);
		//ohan.note("mixed in here", loc);
		// TODO: this is a kludge!
		sc.handler = ohan;
		if(handler.errors.length){
			sc.error("mixed in code contained errors",loc);
			foreach(x; handler.errors) sc.handler.playErrorRecord(x);
			mixin(ErrEplg);
		}
		return r;
		//mixin(SemEplg);
	}
}
// TODO: this is a kludge!
class StringMixinErrorHandler: ErrorHandler{
	ErrorRecord[] errors;
	override void error(lazy string err, Location loc){
		errors~=ErrorRecord(err,loc);
	}
	override void note(lazy string err, Location loc){
		errors~=ErrorRecord(err,loc,true);
	}
}
