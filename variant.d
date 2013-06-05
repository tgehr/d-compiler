// Written in the D programming language.

import lexer, operators, expression, declaration, type, util;

import std.traits: isIntegral, isFloatingPoint, Unqual;
import std.range: ElementType;
import std.conv: to;
import std.string : text;

import std.stdio;

// TODO: refactor the whole code base into smaller modules
struct BCSlice{
	void[] container;
	void[] slice;

	this(void[] va){
		container = slice = va;
	}
	this(void[] cnt, void[] slc){
		container = cnt;
		slice = slc;
	}

	BCPointer getPtr(){
		return BCPointer(container, slice.ptr);
	}
	size_t getLength(){
		return slice.length;
	}

	void setLength(size_t len){
		slice.length = len;
		if(slice.ptr<container.ptr||slice.ptr>=container.ptr+container.length)
			container = slice;
	}
}

struct BCPointer{
	void[] container;
	void* ptr;
}



enum Occupies{
	none, str, wstr, dstr, int64, flt80, fli80, cmp80, arr, vars, err
}

template getOccupied(T){
	static if(is(T==string))
		enum getOccupied = Occupies.str;
	else static if(is(T==wstring))
		enum getOccupied = Occupies.wstr;
	else static if(is(T==dstring)){
		enum getOccupied = Occupies.dstr;
	}else static if(is(T:long)&&!is(T==struct)&&!is(T==class))
		enum getOccupied = Occupies.int64;
	else static if(isFloatingPoint!T){
		static assert(T.sizeof<=typeof(Variant.flt80).sizeof);
		enum getOccupied = Occupies.flt80;	
	}else static if(is(T==ifloat)||is(T==idouble)||is(T==ireal))
		enum getOccupied = Occupies.fli80;
	else static if(is(T==cfloat)||is(T==cdouble)||is(T==creal))
		enum getOccupied = Occupies.cmp80;
	else static if(is(T==Variant[]))
		enum getOccupied = Occupies.arr;
	else static if(is(T==typeof(null)))
		enum getOccupied = Occupies.none;
	else static if(is(T==Vars))
		enum getOccupied = Occupies.vars;
	else static assert(0);
}

private bool occString(Occupies occ){
	static assert(Occupies.str+1 == Occupies.wstr && Occupies.wstr+1 == Occupies.dstr);
	return occ >= Occupies.str && occ <= Occupies.dstr;
}

/+
template FullyUnqual(T){
	static if(is(T _:U[], U)) alias FullyUnqual!U[] FullyUnqual;
	else static if(is(T _:U*, U)) alias FullyUnqual!U* FullyUnqual;
	else alias Unqual!T FullyUnqual;
}+/

private struct Vars{ enum empty = (Variant[VarDecl]).init; }

private struct RTTypeID{
	Type type;
	Occupies occupies;
	TokenType whichBasicType;
	private template Arg(T){
		static if(is(T==Vars)) alias Type Arg;
		else alias Seq!() Arg;
	}
	static RTTypeID* get(U)(Arg!U arg){
		//static if(!is(U==Variant[]))
		//	alias Unqual!(immutable(U)) T; // only structural information, no type checking
		//else alias U T;
		alias Unqual!U T;
		static if(is(T==Vars)){
			// TODO: cache this
			auto r = new RTTypeID();
		}else{
			if(id!T.exists) return &id!T.memo;
			id!T.exists = true;
			alias id!T.memo r;
		}
		static if(!is(T==Variant[])&&!is(T==Vars)) r.type = Type.get!T();
		else r.type = Type.get!EmptyArray();
		static if(is(T==typeof(null))){
			r.occupies = Occupies.none;
/+			r.toExpr = function(ref Variant self){
				auto r = New!LiteralExp(token!"null");
				r.semantic(null);
				assert(!r.rewrite);
				r.dontConstFold();
				return r;
			};+/
		}else static if(is(T==string)||is(T==wstring)||is(T==dstring)){
			enum occ = getOccupied!T;
			r.whichBasicType=Tok!(is(T==string)?"``c":is(T==wstring)?"``w":is(T==dstring)?"``d":assert(0));
			r.occupies = occ;
		}else static if(isBasicType!T){//
			alias getOccupied!T occ;
			r.whichBasicType = Tok!(T.stringof);
			r.occupies = occ;
			/+r.toExpr = function Expression(ref Variant self){
				auto r=LiteralExp.create!New(cast(T)mixin(`self.`~to!string(occ)));
				r.dontConstFold();
				return r;
				//assert(0,"TODO");
			};+/
		}else static if(is(T==Variant[])){
			r.occupies = Occupies.arr;
		}else static if(is(T==Vars)){
			if(!arg){
				if(id!Vars.exists){
					return &id!Vars.memo;
				}else{
					id!Vars.memo=*r; // TODO: don't allocate
					id!Vars.exists=true;
				}
			}else{
				if(arg in aggrmemo) return aggrmemo[arg];
				aggrmemo[arg]=r;
			}

			r.type = arg;
			r.occupies = Occupies.vars;
			/+r.toExpr = function Expression(ref Variant self){
				// TODO: Aliasing?
				return LiteralExp.factory(self, self.id.type);
			};+/
		}else{		
			static assert(!isBasicType!T);
			static assert(0, "TODO");
			//r.toExpr = function Expression
		}
		foreach(member; __traits(allMembers,typeof(this))){
			static if(is(typeof(*mixin(member))==function))
				assert(mixin(`r.`~member)!is null);
		}
		static if(is(T==Vars)) return r;
		else return &r;
	}
private:
	// vtbl
	// Expression function(ref Variant) toExpr;
	
	template id(T){static: RTTypeID memo; bool exists;}
	static RTTypeID*[Type] aggrmemo;
}
/+
private struct WithLoc(T){
	T payload;
	// TODO: this can be represented in a smarter way
	Location[] locs;
	this(T pl, Location[] lcs){payload = pl; locs=lcs;}
	this(T pl, Location loc){payload = pl; locs=[loc];}

	WithLoc opBinary(op: "~")(WithLoc rhs){
		return WithLoc(payload~rhs.payload, locs~rhs.locs);
	}

	WithLoc opIndex(
}
+/
struct Variant{
	private RTTypeID* id;

	this(T)(T value)if(!is(T==Variant[])&&!is(T==Vars)){
		id = RTTypeID.get!T();
		mixin(to!string(getOccupied!T)~` = value;`);
	}

	this()(Variant[] arr, Variant[] cnt)in{
		assert(cnt.ptr<=arr.ptr&&arr.ptr+arr.length<=cnt.ptr+cnt.length);
		if(cnt.length){
			/+assert(value[0].id.type !is Type.get!char()  &&
			 value[0].id.type !is Type.get!wchar() &&
			 value[0].id.type !is Type.get!dchar() &&
			 value[0].id.type.getUnqual() is value[0].id.type,
			 "unsupported: "~to!string(value[0].id.type));+/
			auto id = cnt[0].id;
			foreach(x;cnt[1..$]) assert(id is x.id,cnt.text);
		}		
	}body{
		id = RTTypeID.get!(Variant[])();
		this.arr=arr;
		this.cnt=cnt;
	}

	this()(Variant[VarDecl] vars, Type type = null){ // templated because of DMD bug
		id = RTTypeID.get!Vars(type);
		this.vars=vars;
	}


	private union{
		typeof(null) none;
		string str; wstring wstr; dstring dstr;
		ulong int64;
		real flt80; ireal fli80; creal cmp80;
		struct{
			Variant[] arr;
			Variant[] cnt;
		}
		Variant[VarDecl] vars; // structs, classes, closures
		string err;
	}

	T get(T)(){
		static if(is(T==string)){
			if(id.occupies == Occupies.str) return str;
			else if(id.occupies == Occupies.wstr) return to!string(wstr);
			else if(id.occupies == Occupies.dstr) return to!string(dstr);
			else return toString();
		}
		else static if(is(T==wstring)){assert(id.occupies == Occupies.wstr); return wstr;}
		else static if(is(T==dstring)){assert(id.occupies == Occupies.dstr); return dstr;}
		else static if(is(T==ulong)||is(T==long)||is(T==char)||is(T==wchar)||is(T==dchar)){assert(id.occupies == Occupies.int64,"occupies was "~to!string(id.occupies)~" instead of int64"); return cast(T)int64;}
		else static if(is(T==float)||is(T==double)||is(T==real)){
			assert(id.occupies == Occupies.flt80);
			return flt80;
		}else static if(is(T==ifloat) || is(T==idouble)||is(T==ireal)){
			assert(id.occupies == Occupies.fli80);
			return fli80;
		}else static if(is(T==cfloat) || is(T==cdouble)||is(T==creal)){
			assert(id.occupies == Occupies.cmp80);
			return cmp80;
		}else static if(is(T==Variant[VarDecl])){
			if(id.occupies == Occupies.none) return null;
			assert(id.occupies == Occupies.vars,text(id.occupies));
			return vars;
		}else static if(is(T==Variant[])){
			assert(id.occupies == Occupies.arr);
			return arr;
		}else static assert(0, "cannot get this field (yet?)");
	}

	Variant[] getContainer()in{
		assert(id.occupies == Occupies.arr);
	}body{
		return cnt;
	}

	/* returns a type that fully specifies the memory layout
	   for strings, the relevant type qualifiers are preserved
	   otherwise, gives no guarantees for type qualifier preservation
	 */

	Type getType(){
		if(id.occupies == Occupies.arr){
			if(!length) return id.type;
			return arr[0].getType().getDynArr();
		}
		return id.type;
	}

	bool isEmpty(){return id is null;}

	Expression toExpr(){
		/+if(id) return id.toExpr(this);
		else return New!ErrorExp();+/
		if(id){
			auto r = LiteralExp.factory(this, getType());
			r.semantic(null);
			return r;
		}else return New!ErrorExp();
	}

	string toString(){
		auto type=getType().getHeadUnqual();
		if(type is Type.get!(typeof(null))()) return "null";
		if(type.isSomeString()){
			foreach(T;Seq!(string,wstring,dstring)){
				if(type !is Type.get!T()) continue;
				enum occ = getOccupied!T;
				enum sfx = is(T==string)  ? "c" :
					       is(T==wstring) ? "w" :
						   is(T==dstring) ? "d" : "";
				return to!string('"'~escape(mixin(`this.`~to!string(occ)))~'"'~sfx);
			}
		}
		if(auto bt=type.isBasicType()){
			switch(bt.op){
				foreach(x;ToTuple!basicTypes){
					static if(x!="void")
					case Tok!x:
						mixin(`alias typeof(`~x~`.init) T;`); // dmd parser workaround
						enum sfx = is(T==uint) ? "U" :
					       is(T==long)||is(T==real) ? "L" :
						   is(T==ulong) ? "LU" :
						   is(T==float) ? "f" :
				           is(T==ifloat) ? "fi" :
					       is(T==idouble) ? "i" :
						   is(T==ireal) ? "Li":"";
						enum left = is(T==char)||is(T==wchar)||is(T==dchar) ? "'" : "";
						enum right = left;
						// remove redundant "i" from imaginary literals
						enum oc1 = getOccupied!T;
						enum occ = oc1==Occupies.fli80?Occupies.flt80:oc1;
						
						string rlsfx = ""; // TODO: extract into its own function?
						string res = to!string(mixin(`cast(T)this.`~to!string(occ)));
						static if(occ==Occupies.flt80)
							if(this.flt80%1==0&&!res.canFind("e")) rlsfx=".0";
						return left~res~right~rlsfx~sfx;						
				}
				default: assert(0);
			}
		}
		if(type.getElementType()){
			import std.algorithm, std.array;
			return '['~join(map!(to!string)(this.arr),",")~']';
		}
		if(type.isAggregateTy()){
			if(this.vars is null) return "null";
			return this.id.type.toString(); // TODO: pick up toString?
		}
		assert(0,"cannot get string");
	}

	Variant convertTo(Type to)in{assert(!!id);}body{
		auto type = getType().getHeadUnqual();
		to = to.getHeadUnqual();
		if(to is type) return this;
		if(type is Type.get!(typeof(null))()){
			if(to is Type.get!(typeof(null))()) return this;
			if(to.getElementType()) return Variant((Variant[]).init,(Variant[]).init).convertTo(to);
			if(to.isAggregateTy()) return Variant(Vars.empty, to);
			// TODO: null pointers and delegates
			// auto tou=to.getHeadUnqual();
			assert(0,"cannot convert");
		}else if(type.isSomeString()){
			foreach(T;Seq!(string,wstring,dstring)){
				enum occ=getOccupied!T;
				if(type !is Type.get!T()) continue;
				if(to is Type.get!T()) return this;
				if(!is(T==string) && to is Type.get!string())
					return Variant(.to!string(mixin(`this.`~.to!string(occ))));
				else if(!is(T==wstring) && to is Type.get!wstring())
					return Variant(.to!wstring(mixin(`this.`~.to!string(occ))));
				else if(!is(T==dstring) && to is Type.get!dstring())
					return Variant(.to!dstring(mixin(`this.`~.to!string(occ))));
				else if(to.getElementType()){
					// TODO: revise allocation
					auto r = new Variant[this.length];
					foreach(i,x;mixin(`this.`~.to!string(occ))) r[i]=Variant(x);
					return Variant(r,r);//TODO: aliasing?
				}
				return this; // TODO: this is a hack and might break stuff (?)
				break;
			}
		}else if(auto tbt=type.isBasicType()){
			if(auto bt = to.getHeadUnqual().isBasicType()){
				switch(tbt.op){
					foreach(tx;ToTuple!basicTypes){
						static if(tx!="void"){
							case Tok!tx:// TODO: code generated for integral types is identical
							mixin(`alias typeof(`~tx~`.init) T;`); // dmd parser workaround
							enum occ=getOccupied!T;
							switch(bt.op){
								foreach(x;ToTuple!basicTypes){
									static if(x!="void")
									case Tok!x:
										return Variant(mixin(`cast(`~x~`)cast(T)this.`~.to!string(occ)));
								}
								case Tok!"void": return this;
								default: assert(0);
							}
						}
					}
					default: assert(0);
				}
			}
		}else if(type.isDynArrTy()){
			// assert(to.getHeadUnqual().getElementType()!is null);
			if(to is Type.get!string()){
				string s;
				foreach(x; this.arr) s~=cast(char)x.int64;
				return Variant(s);
			}else if(to is Type.get!wstring()){
				wstring s;
				foreach(x; this.arr) s~=cast(wchar)x.int64;
				return Variant(s);
			}else if(to is Type.get!dstring()){
				dstring s;
				foreach(x; this.arr) s~=cast(wchar)x.int64;
				return Variant(s);
			}
			// TODO: Sanity check.
			return this;
		}else if(type is Type.get!EmptyArray()){
			assert(to.isDynArrTy());
			if(to.isSomeString()){
				foreach(T;Seq!(string,wstring,dstring))
					if(to is Type.get!T()) return Variant(T.init/+,T.init+/);
			}
			return Variant((Variant[]).init,(Variant[]).init);
		}
		return this;
	}

	bool opCast(T)()if(is(T==bool)){
		assert(id.type == Type.get!bool(), to!string(id.type)~" "~toString());
		return cast(bool)int64;
	}

	private Variant strToArr()in{
		assert(occString(id.occupies));
	}body{ // TODO: get rid of this
		Variant[] r = new Variant[length];
		theswitch:switch(id.occupies){
			foreach(occ;ToTuple!([Occupies.str, Occupies.wstr, Occupies.dstr])){
				case occ:
					foreach(i,x; mixin(to!string(occ))) r[i] = Variant(x);
					break theswitch;
			}
			default: assert(0);
		}
		return Variant(r,r);
	}

	bool opEquals(Variant rhs){ return cast(bool)opBinary!"=="(rhs); }

	size_t toHash()@trusted{
		final switch(id.occupies){
			case Occupies.none: return 0;
				foreach(x; EnumMembers!Occupies[1..$]){
					case x: return typeid(mixin(to!string(x))).getHash(&mixin(to!string(x)));
				}
		}
		assert(0); // TODO: file bug
	}

	// TODO: BUG: shift ops not entirely correct
	Variant opBinary(string op)(Variant rhs)in{
		static if(isShiftOp(Tok!op)){
			assert(id.occupies == Occupies.int64 && rhs.id.occupies == Occupies.int64);
		}else{
			//assert(id.occupies == Occupies.arr || id.whichBasicType!=Tok!"" && id.whichBasicType == rhs.id.whichBasicType,
			//       to!string(id.whichBasicType)~"!="~to!string(rhs.id.whichBasicType));
			assert(id.occupies==rhs.id.occupies
			    || id.occupies == Occupies.arr && occString(rhs.id.occupies)
			    || rhs.id.occupies == Occupies.arr && occString(id.occupies)
			    || op == "%" && id.occupies == Occupies.cmp80 &&
			       (rhs.id.occupies == Occupies.flt80 || rhs.id.occupies == Occupies.fli80),
			       to!string(this)~" is incompatible with "~
			       to!string(rhs)~" in binary '"~op~"' expression");
		}
	}body{
		if(id.occupies == Occupies.arr){
			if(rhs.id.occupies != Occupies.arr) rhs=rhs.strToArr();
			static if(op=="~"){
				auto r=arr~rhs.arr;
				return Variant(r,r);
			}static if(op=="is"||op=="!is"){
				return Variant(mixin(`arr `~op~` rhs.arr`));
			}static if(op=="in"||op=="!in"){
				// TODO: implement this
				assert(0,"TODO");
			}else static if(isRelationalOp(Tok!op)){
				// TODO: create these as templates instead
				auto l1 = length, l2=rhs.length;
				static if(op=="=="){if(l1!=l2) return Variant(false);}
				else static if(op=="!=") if(l1!=l2) return Variant(true);
				if(l1&&l2){
					auto tyd = arr[0].id.type.combine(rhs.arr[0].id.type);
					assert(!tyd.dependee);// should still be ok though.
					Type ty = tyd.value;
					foreach(i,v; arr[0..l1<l2?l1:l2]){
						auto l = v.convertTo(ty), r = rhs.arr[i].convertTo(ty);
						if(l.opBinary!"=="(r)) continue;
						else{
							static if(op=="==") return Variant(false);
							else static if(op=="!=") return Variant(true);
							else return l.opBinary!op(r);
						}
					}
				}
				// for ==, != we know that the lengths must be equal
				static if(op=="==") return Variant(true);
				else static if(op=="!=") return Variant(false);
				else return Variant(mixin(`l1 `~op~` l2`));
			}
		}else if(id.occupies == Occupies.none){
			static if(is(typeof(mixin(`null `~op~` null`))))
				return Variant(mixin(`null `~op~` null`));
			assert(0);
		}else switch(id.whichBasicType){
			foreach(x; ToTuple!basicTypes){
				static if(x!="void"){
					alias typeof(mixin(x~`.init`)) T;
					alias getOccupied!T occ;
					static if(occ == Occupies.cmp80 && op == "%")
						// can do complex modulo real
						// relies on same representation for flt and fli
						enum occ2 = Occupies.flt80;
					else enum occ2 = occ;
					assert(id.occupies == occ);
					//assert(rhs.id.occupies == occ2);
					static if(isShiftOp(Tok!op)|| occ2 != occ) enum cst = ``;
					else enum cst = q{ cast(T) };
					enum code = q{
						Variant(mixin(`cast(T)` ~ to!string(occ) ~ op ~
						              cst~`rhs.` ~ to!string(occ2)))
					};
					static if(is(typeof(mixin(code)))) case Tok!x: return mixin(code);
				}
			}
			foreach(x; ToTuple!(["``c","``w","``d"])){
				alias typeof(mixin(x)) T;
				alias getOccupied!T occ;
				assert(id.occupies == occ);
				enum code = to!string(occ)~` `~op~` rhs.`~to!string(occ);
				static if(op!="-" && op!="+" && op!="<>=" && op!="!<>=") // DMD bug
				static if(is(typeof(mixin(code)))){
					case Tok!x: 
					if(rhs.id.occupies == id.occupies)
						return Variant(mixin(code));
					else return strToArr().opBinary!op(rhs);
				}
			}
			default: break;
		}
		assert(0, "no binary '"~op~"' support for "~id.type.toString());
	}
	Variant opUnary(string op)(){
		switch(id.whichBasicType){
			foreach(x; ToTuple!basicTypes){
				static if(x!="void"){
					alias typeof(mixin(x~`.init`)) T;
					alias getOccupied!T occ;
					enum code = q{ mixin(op~`cast(T)`~to!string(occ)) };
					static if(is(typeof(mixin(code))==T))
					case Tok!x: return Variant(mixin(code));
				}
			}
			default: assert(0, "no unary '"~op~"' support for "~id.type.toString());
		}
	}

	@property size_t length()in{
		assert(id.occupies==Occupies.arr||id.occupies == Occupies.str
		       || id.occupies == Occupies.wstr || id.occupies == Occupies.dstr);
	}body{
		if(id.occupies == Occupies.arr) return arr.length;
		else switch(id.occupies){
			foreach(x; ToTuple!(["str","wstr","dstr"])){
				case mixin(`Occupies.`~x): return mixin(x).length;
			}
			default: assert(0);
		}
	}

	Variant opIndex(Variant index)in{
		assert(index.id.occupies==Occupies.int64);
		assert(id.occupies == Occupies.arr||id.occupies == Occupies.str
		       || id.occupies == Occupies.wstr || id.occupies == Occupies.dstr);
	}body{
		if(id.occupies == Occupies.arr){
			assert(index.int64<arr.length, to!string(index.int64)~">="~to!string(arr.length));
			return arr[cast(size_t)index.int64];
		}else switch(id.occupies){
			foreach(x; ToTuple!(["str","wstr","dstr"])){
				case mixin(`Occupies.`~x):
					assert(index.int64<mixin(x).length);
					return Variant(mixin(x)[cast(size_t)index.int64]);
			}
			default: assert(0);
		}
	}
	Variant opIndex(size_t index){
		return this[Variant(index)];
	}

	Variant opSlice(Variant l, Variant r)in{
		assert(l.id.occupies==Occupies.int64);
		assert(id.occupies == Occupies.arr||id.occupies == Occupies.str
		       || id.occupies == Occupies.wstr || id.occupies == Occupies.dstr);
	}body{
		if(id.occupies == Occupies.arr){
			assert(l.int64<=arr.length && r.int64<=arr.length);
			assert(l.int64<=r.int64);
			return Variant(arr[cast(size_t)l.int64..cast(size_t)r.int64],cnt); // aliasing ok?
		}else switch(id.occupies){
			foreach(x; ToTuple!(["str","wstr","dstr"])){
				case mixin(`Occupies.`~x):
					assert(l.int64<mixin(x).length && r.int64<=mixin(x).length);
					return Variant(mixin(x)[cast(size_t)l.int64..cast(size_t)r.int64]);
			}
			default: assert(0);
		}
	}
	Variant opSlice(size_t l, size_t r){
		return this[Variant(l)..Variant(r)];
	}
}
