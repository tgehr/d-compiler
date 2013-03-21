/+
alias typeof((immutable(void[])).length) size_t;

pragma(msg, size_t);


void testpuredollar(){
	int[] x = [1,2,3];
	x[(()pure=>$,$-1)]=2; // must work
}



template Inex(a...){
	alias Inex!(1,a[0..n]) Inex;
}

pragma(msg, Inex!(2,2,3));


template Seq(T...){ alias T Seq;}

struct A{
	alias B.b b;
	static int foo;
	int bar;
}
struct B{
	shared int b;
	alias A.foo foo;
	alias A.bar bar;
}

void foo(){
	immutable(A) a;
	const(B) b;
	static assert(!is(typeof({a.b=2;})),"wrong type for this");
	a.foo=2; // ok: access mutable static member
	static assert(!is(typeof({a.bar=2;})),"a.bar is immutable");
	static assert(is(typeof(a.bar)==immutable(int)));
	
	static assert(!is(typeof({b.b=2;})), "b.b is shared const");
	static assert(is(typeof(b.b)==shared(const(int))));
	b.foo=2; // ok: access mutable static member of another type
	static assert(!is(typeof({b.bar=2;})), "wrong type for this");

	static assert(is(typeof(b.b)==const(typeof(B.b))));
	pragma(msg, typeof(B.b));
	pragma(msg, typeof(b.b));
}



/+struct Fancy{
	int a;
	int b;
	alias Seq!(a,b) c;
	//alias a c;
}

auto main(){
	Fancy f;
	f.a=2;
	f.c[0]=3;
	assert(a==3);
	f.b=2;
	assert(f.c[1]==2);
	return f.c;
}
pragma(msg, main());+/




void local(){
	int x;
	//alias x y;
	alias Seq!x y;
	static void foo(){y[0]++;}
}

template TT(int i){
	alias Rest V;
	static if(i) alias TT!(0).V Rest;
	static if(i) enum thisisone=true;
}

pragma(msg, TT!(0).V);
pragma(msg, TT!(1).V);

template SS(bool i){
	static if(i) alias int V;
	alias V A;
}

pragma(msg, SS!1.V);
pragma(msg, SS!(0).A);

alias QQ.x a;
alias QQ.y b;

double x,y;

alias Seq!(QQ.x, QQ.y) QQs;
pragma(msg, QQs);

struct QQ{
	//int x=2,y=3;
	int x(); int y;
	static void foo(){
		a();
		b=b;
	}
}


struct G {G g; }
struct F(T) { static int f(immutable ref T) {return 2;} }
pragma(msg, F!G.f(G.g));



struct WW{
	void foo(){
		a=2;
	}
}

immutable foo = 2; 
//pragma(msg, a);


struct Foo{
	//static double foo(){}
	static double foo(int){}
	int foo(){}
	static void goo(){
		Foo f;
		auto x=f.foo(2);
		auto y=Foo.foo();
		pragma(msg, "x: ",typeof(x)," y: ",typeof(y));
	}
}

struct Test{
	static inout(int) foo(inout(int)){return 1;}
	double foo(int){return 1.0;}
	static void goo(){
		//foo();
		pragma(msg, typeof(Test.foo(cast(shared)1)));

		Test.foo(2);
	}
}

alias S.t st;
struct S{
	int t;
	void foo(){
		st=2;
	}
}

// +/