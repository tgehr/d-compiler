
import lexer, operators, expression, type, util;

import error;//: ErrorRecord; // fu?

import std.traits: isIntegral, isFloatingPoint, Unqual;
import std.range: ElementType;
import std.conv: to;
import std.string : text;

import std.stdio;

enum Occupies{
	none, str, wstr, dstr, int64, flt80, fli80, cmp80, arr, err
}

private template getOccupied(T){
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

private struct RTTypeID{
	Type type;
	Occupies occupies;
	TokenType whichBasicType;

	static RTTypeID* get(U)(){
		//static if(!is(U==Variant[]))
		//	alias Unqual!(immutable(U)) T; // only structural information, no type checking
		//else alias U T;
		alias Unqual!U T;
		if(id!T.exists) return &id!T.memo;
		id!T.exists = true;
		alias id!T.memo r;
		static if(!is(T==Variant[])) r.type = Type.get!T();
		else r.type = Type.get!EmptyArray();
		static if(is(T==typeof(null))){
			r.occupies = Occupies.none;
			r.toExpr = function(ref Variant self){
				return New!LiteralExp(token!"null");
			};
			r.convertTo = cannotConvert;
			r.toString = function(ref Variant self){return "null";};
		}else static if(is(T==string)||is(T==wstring)||is(T==dstring)){
			enum occ = getOccupied!T;
			r.whichBasicType=Tok!(is(T==string)?"``c":is(T==wstring)?"``w":is(T==dstring)?"``d":assert(0));
			r.occupies = occ;
			r.toExpr = function Expression(ref Variant self){
				return LiteralExp.create!New(mixin(`self.`~to!string(occ)));
			};
			r.convertTo = function Variant(ref Variant self, Type to){
				auto tou = to.getHeadUnqual();
				if(tou is Type.get!T()) return self;
				if(!is(T==string) && tou is Type.get!string())
					return Variant(.to!string(mixin(`self.`~.to!string(occ))));
				else if(!is(T==wstring) && tou is Type.get!wstring())
					return Variant(.to!wstring(mixin(`self.`~.to!string(occ))));
				else if(!is(T==dstring) && tou is Type.get!dstring())
					return Variant(.to!dstring(mixin(`self.`~.to!string(occ))));
				else if(to.getElementType()){
					// TODO: revise allocation
					auto r = new Variant[self.length];
					foreach(i,x;mixin(`self.`~.to!string(occ))) r[i]=Variant(x);
					return Variant(r);
				}
				assert(to.getElementType().getUnqual() is Type.get!(Unqual!(ElementType!T))());
				return self; // TODO: this is a hack and might break stuff (?)
			};
			enum sfx = is(T==string) ? "c" :
			           is(T==wstring)||is(T==real) ? "w" :
				       is(T==dstring) ? "d" : "";
			r.toString = function string(ref Variant self){
				return to!string('"'~escape(mixin(`self.`~to!string(occ)))~'"'~sfx);
			};
		}else static if(isBasicType!T){//
			alias getOccupied!T occ;
			r.whichBasicType = Tok!(T.stringof);
			r.occupies = occ;
			r.toExpr = function Expression(ref Variant self){
				return LiteralExp.create!New(cast(T)mixin(`self.`~to!string(occ)));
				//assert(0,"TODO");
			};
			r.convertTo = function Variant(ref Variant self, Type to){
				if(auto bt = to.getHeadUnqual().isBasicType()){
					switch(bt.op){
						foreach(x;ToTuple!basicTypes){
							static if(x!="void")
							case Tok!x:
							return Variant(mixin(`cast(`~x~`)self.`~.to!string(occ)));
						}
						default: break;
					}
				}
				return cannotConvert(self, to);
			};
			r.toString = function(ref Variant self){
				enum sfx = is(T==uint) ? "U" :
					       is(T==long)||is(T==real) ? "L" :
						   is(T==ulong) ? "LU" :
						   is(T==float) ? "f" :
				           is(T==ifloat) ? "fi" :
					       is(T==idouble) ? "i" :
						   is(T==ireal) ? "Li":"";
				enum left = is(T==char)||is(T==wchar)||is(T==dchar) ? "'" : "";
				enum right = left;
				return left~to!string(mixin(`cast(T)self.`~to!string(occ)))~right~sfx;
			};
		}else static if(is(T==Variant[])){
			r.occupies = Occupies.arr;
			r.toExpr = function Expression(ref Variant self){
				// TODO: allocation ok?
				Expression[] lit = new Expression[self.length];
				foreach(i,ref x;lit) x = self.arr[i].id.toExpr(self.arr[i]);
				return New!ArrayLiteralExp(lit).semantic(null); // TODO: ok?
			};
			r.convertTo = function Variant(ref Variant self, Type to){
				// assert(to.getHeadUnqual().getElementType()!is null);
				if(to is Type.get!string()){
					string s;
					foreach(x; self.arr) s~=cast(char)x.int64;
					return Variant(s);
				}else if(to is Type.get!wstring()){
					wstring s;
					foreach(x; self.arr) s~=cast(wchar)x.int64;
					return Variant(s);
				}else if(to is Type.get!dstring()){
					dstring s;
					foreach(x; self.arr) s~=cast(wchar)x.int64;
					return Variant(s);
				}
				// TODO: Sanity check.
				return self;
			};
			r.toString = function string(ref Variant self){
				return to!string(self.arr);
			};
		}else{
			static assert(!isBasicType!T);
			static assert(0, "TODO");
			//r.toExpr = function Expression
			r.convertTo = cannotConvert;
			r.toString = function (ref Variant self){
				return Variant("(Variant of type "~self.id.type.toString()~")");
			};
		}
		foreach(member; __traits(allMembers,typeof(this))){
			static if(is(typeof(*mixin(member))==function))
				assert(mixin(`r.`~member)!is null);
		}
		return &r;
	}
private:
	// vtbl
	Expression function(ref Variant) toExpr;
	string function(ref Variant) toString;
	Variant function(ref Variant,Type) convertTo;

	private static Variant function(ref Variant,Type) cannotConvert;
	static this(){ // meh
		cannotConvert = 
		function Variant(ref Variant self, Type to){
			assert(0, text("cannot convert ", self, " of type ",self.id.type, " to ",to));
		};
	}
	
	template id(T){static: RTTypeID memo; bool exists;}
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

	this(T)(T value)in{
		static if(is(T==Variant[])){
			if(value.length){
				/+assert(value[0].id.type !is Type.get!char()  &&
				       value[0].id.type !is Type.get!wchar() &&
				       value[0].id.type !is Type.get!dchar() &&
				       value[0].id.type.getUnqual() is value[0].id.type,
				       "unsupported: "~to!string(value[0].id.type));+/
				auto id = value[0].id;
				foreach(x;value[1..$]) assert(id is x.id);
			}
		}
	}body{
		id =  RTTypeID.get!T();
		mixin(to!string(getOccupied!T)~` = value;`);
	}

	static Variant error(string str, Location loc){
		Variant r;
		r.id = null;
		r.err = [ErrorRecord(str,loc)];
		return r;
	}

	bool isError(){
		return id is null;
	}

	const(ErrorRecord)[] getErrors()in{assert(isError());}body{
		return err;
	}

	private union{
		typeof(null) none;
		string str; wstring wstr; dstring dstr;
		ulong int64;
		real flt80; ireal fli80; creal cmp80;
		// TODO: arrays
		Variant[] arr;
		ErrorRecord[] err;
		// TODO: structs, classes
		// strings with location
		// TODO: WithLoc!string* strl; WithLoc!wstring* wstrl; WithLoc!dstring* dstrl;
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
		else static assert(0, "cannot get this field (yet?)");
	}

	Type getType(){
		assert(id.occupies != Occupies.arr); // TODO: fix this
		return id.type;
	}

	bool isEmpty(){return id is null;}

	Expression toExpr(){
		if(id) return id.toExpr(this);
		else return New!ErrorExp();
	}

	string toString(){
		return id.toString(this);
		/*final switch(id.occupies){
			foreach(x;__traits(allMembers, Occupies)){
				case mixin(`Occupies.`~x): return to!string(mixin(x));
			}
		}
		assert(0); // TODO: investigate, report bug*/
	}

	Variant convertTo(Type ty)in{assert(!!id);}body{return id.convertTo(this, ty);}

	bool opCast(T)()if(is(T==bool)){
		assert(id.type == Type.get!bool());
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
		return Variant(r);
	}

	// TODO: BUG: shift ops not entirely correct
	Variant opBinary(string op)(Variant rhs)in{
		static if(isShiftOp(Tok!op)){
			assert(id.occupies == Occupies.int64 && rhs.id.occupies == Occupies.int64);
		}else{
			assert(id.occupies == Occupies.arr || id.whichBasicType!=Tok!"" && id.whichBasicType == rhs.id.whichBasicType,
			       to!string(id.whichBasicType)~"!="~to!string(rhs.id.whichBasicType));
			assert(id.occupies==rhs.id.occupies
			    || id.occupies == Occupies.arr && occString(rhs.id.occupies)
			    || rhs.id.occupies == Occupies.arr && occString(id.occupies),
			       to!string(this)~" is incompatible with "~
			       to!string(rhs)~" in binary '"~op~"' expression");
		}
	}body{
		if(id.occupies == Occupies.arr){
			if(rhs.id.occupies != Occupies.arr) rhs=rhs.strToArr();
			static if(op=="~"){
				return Variant(arr~rhs.arr);
			}static if(op=="in"||op=="!in"||op=="is"||op=="!is"){
				// TODO: implement this
				assert(0,"TODO");
			}else static if(isRelationalOp(Tok!op)){
				auto l1 = length, l2=rhs.length;
				static if(op=="=="){if(l1!=l2) return Variant(false);}
				else static if(op=="!=") if(l1!=l2) return Variant(true);
				if(l1&&l2){
					Type ty = arr[0].id.type.combine(rhs.arr[0].id.type);
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
		}else switch(id.whichBasicType){
			foreach(x; ToTuple!basicTypes){
				static if(x!="void"){
					alias typeof(mixin(x~`.init`)) T;
					alias getOccupied!T occ;
					assert(id.occupies == occ);
					static if(isShiftOp(Tok!op)) enum cst = ``;
					else enum cst = q{ cast(T) };
					enum code = q{
						Variant(mixin(`cast(T)` ~ to!string(occ) ~ op ~
						              cst~`rhs.` ~ to!string(occ)))
					};
					static if(is(typeof(mixin(code)))) case Tok!x: return mixin(code);
				}
			}
			foreach(x; ToTuple!(["``c","``w","``d"])){
				alias typeof(mixin(x)) T;
				alias getOccupied!T occ;
				assert(id.occupies == occ);
				enum code = to!string(occ)~op~`rhs.`~to!string(occ);
				static if(op!="-" && op!="+" && op!="<>=" && op!="!<>=") // DMD bug
				static if(is(typeof(mixin(code)))) case Tok!x: 
					if(rhs.id.occupies == id.occupies)
						return Variant(mixin(code));
					else return strToArr().opBinary!op(rhs);
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
			assert(l.int64<arr.length && r.int64<=arr.length);
			assert(l.int64<=r.int64);
			return Variant(arr[cast(size_t)l.int64..cast(size_t)r.int64]); // aliasing ok?
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
