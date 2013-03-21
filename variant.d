
import lexer, operators, expression, type, util;

import std.traits: isIntegral, isFloatingPoint;
import std.conv: to;

import std.stdio;

enum Occupies{
	str, wstr, dstr, int64, flt80, fli80, cmp80
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
	else static assert(0);
}

struct RTTypeID{
	Type type;
	Occupies occupies;
	TokenType whichBasicType;

	static RTTypeID* get(T)(){
		if(id!T.exists) return &id!T.memo;
		alias id!T.memo r;
		r.type = Type.get!T();
		static if(is(T==typeof(null))){
			r.toExpr = function(ref Variant self){
				return New!LiteralExp(token!"null");
			};
			r.convertTo = cannotConvert;
			r.toString = function(ref Variant self){return "null";};
		}else static if(is(T==string)||is(T==wstring)||is(T==dstring)){
			enum occ = getOccupied!T;
			r.occupies = occ;
			r.toExpr = function(ref Variant self){
				return LiteralExp.create!New(mixin(`self.`~to!string(occ)));
			};
			r.convertTo = cannotConvert;
			r.toString = function(ref Variant self){return self.str;};
		}else static if(isBasicType!T){//
			alias getOccupied!T occ;
			r.whichBasicType = Tok!(T.stringof);
			r.occupies = occ;
			r.toExpr = function Expression(ref Variant self){
				return LiteralExp.create!New(cast(T)mixin(`self.`~to!string(occ)));
				//assert(0,"TODO");
			};
			r.convertTo = function (ref Variant self, Type to){
				if(auto bt = to.isBasicType()){
					switch(bt.op){
						foreach(x;ToTuple!basicTypes){
							static if(x!="void")
							case Tok!x:
							return Variant(mixin(`cast(`~x~`)self.`~.to!string(occ)));
						}
						default: break;
					}
				}
				assert(0, "cannot convert " ~ .to!string(self) ~ " to " ~ .to!string(to));
			};
			r.toString = function(ref Variant self){
				return to!string(mixin(`cast(T)self.`~to!string(occ)));
			};
		}else{
			static assert(!isBasicType!T);
			static assert(0, "TODO");
			r.convertTo = function Variant(ref Variant self, Type to){
				assert(0, "cannot convert " ~ .to!string(self) ~ " to " ~ .to!string(to));
			};
			r.toString = function Variant(ref Variant self){
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
			assert(0, "cannot convert " ~ .to!string(self) ~ " to " ~ .to!string(to));
		};
	}
	
	template id(T){static: RTTypeID memo; bool exists;}
}

struct Variant{
	RTTypeID* id;

	this(T)(T value){
		id =  RTTypeID.get!T();
		static if(!is(T==typeof(null))) mixin(to!string(getOccupied!T)~` = value;`);
	}

	union{
		string str; wstring wstr; dstring dstr;
		ulong int64;
		real flt80; ireal fli80; creal cmp80;
		// TODO: arrays
		// TODO: structs, classes
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

	// TODO: BUG: shift ops not entirely correct
	Variant opBinary(string op)(auto ref Variant rhs)in{
		static if(isShiftOp(Tok!op)){
			assert(id.occupies == Occupies.int64 && rhs.id.occupies == Occupies.int64);
		}else
			assert(id.whichBasicType == rhs.id.whichBasicType,
			       to!string(id.whichBasicType)~"!="~to!string(rhs.id.whichBasicType));
	}body{
		switch(id.whichBasicType){
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
			default: assert(0, "no binary '"~op~"' support for "~id.type.toString());
		}
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
}
