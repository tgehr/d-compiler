import std.typecons, std.string;
// TODO: actually use 128 bits computations

struct Cent{
	long val;
	Cent opBinary(string op)(Cent rhs){
		return Cent(mixin(`val `~op~` rhs.val`));
	}
	Cent opUnary(string op)(){
		return Cent(mixin(op~" val"));
	}
	this(T)(T from){ val=cast(typeof(val))from; }
	T opCast(T)()if(!is(T==string)){ return cast(T)val; }
	string toString(){
		return format("%d",val)~"C";
	}
}

struct UCent{
	ulong val;
	UCent opBinary(string op)(Cent rhs){
		return UCent(mixin(`val `~op~` rhs.val`));
	}
	UCent opUnary(string op)(){
		return UCent(mixin(op~" val"));
	}
	this(T)(T from){ val=cast(typeof(val))from; }
	T opCast(T)(){ return cast(T)val; }
	string toString(){
		return format("%d",val)~"UC";
	}
}
