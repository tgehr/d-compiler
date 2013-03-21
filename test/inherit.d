

class PP{
	enum x = "success!";
}
class CC: PP{
	pragma(msg, x); // TODO!
}



//static if(!is(typeof(a))) enum b = 2;
//static if(!is(typeof(b))) enum a = 2;


template Test(bool x){
	static if(x) enum Test = false;
	else enum Test = true;
}

pragma(msg, Test!false);

//static if(!is(typeof(b))) enum a = 2;
//static if(!is(typeof(a))) enum b = 2;
//pragma(msg, a);


template IfNotConvertible(alias From, alias To, alias A){
	static if(is(From:To)) alias Seq!() IfNotConvertible;
	else alias A IfNotConvertible;
}
class AClass{}

static assert(!is(typeof({
	class Contradict: IfNotConvertible!(Contradict, AClass, AClass){}
})));

class NoContradict: AClass, IfNotConvertible!(NoContradict, AClass, AClass){}


int test(){
	NoContradict c;
	AClass b = c;
	return 2;
}
//pragma(msg, test());



class X{}
class Y:X{}
class Z:Y{}

static assert(is(Y:X));
static assert(is(Z:Y));
static assert(is(Z:X));

void test(){
	X x;
	Y y;
	Z z;
	x=z;
	x=y;
	y=z;
	static assert(!is(typeof(z=x)));
	static assert(!is(typeof(y=x)));
	static assert(!is(typeof(z=y)));

	auto a = [y,z];
	static assert(is(typeof(a)==Y[]));
}

class U: X{}
class V: Y{}


void test2(){
	U u;
	V v;
	const(U) cu;
	const(V) cv;
	auto a = [u,v];
	static assert(is(typeof(a)==X[]));

	auto b = [cu,cv];
	pragma(msg, typeof(b));
	static assert(is(typeof(b)==const(X)[]));
}

alias Seq!int P;
interface W{}
class TT:Seq!(X,W){}

static assert(!is(typeof({class Foo:X,X{}})));

static assert(!is(typeof({
	struct S{
		class I4:G{}
		class I3:I1{}
		class I2:I3{}
		class I1:I2{}
		class G:I1{}
	}
})));



static assert(!is(typeof({
	interface FI{}
	class F{
		class C:Seq!(B!C,FI){int x;}
	}
})));
class B(T){
	static assert(is(T: B!T));
	static assert(is(IN:B!IN));
}

class A(T){
	pragma(msg, T);
	static assert(is(T: A!T),T);
	pragma(msg, "1 of ",T,":", is(T: A!T));
	pragma(msg, "2 of ",T,":", is(A!T: T));
	static assert(is(E:A!E));
}

static assert(!is(typeof({pragma(msg, "is(A!int): ",is(A!int)," ",A!int);})));

pragma(msg, is(A!E));

class C : A!C{}

class D(T) : A!T{
	// static if(is(T==D)) enum x = "success!";
	// static if(is(T:C!T)) enum x = "success!";
}


class E: D!E{
	//pragma(msg, x);
}

//pragma(msg, D);
//pragma(msg, C!D);



// +/
// +/
// +/

template Seq(T...){alias T Seq;}
