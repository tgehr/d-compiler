
template hasSave(R){
	enum hasSave=is(typeof({
		R r;
		r=r.save;
	}));
}

static struct DontKnowIfHasSave{
	static if(!hasSave!(typeof(this))) @property void save(){ } // error
}


struct TryEscapeInout{
	void foo()inout{ }
	auto bar(){ return &foo; }
}
static assert(is(typeof(TryEscapeInout.bar)==void delegate()));
pragma(msg, typeof(TryEscapeInout.bar));

struct DelegateFromMemberFunc {
	char c[];
	void foo() { }
	int delegate() ddd;
	void bar() const {
		static assert(!is(typeof(ddd)));
		foo; // error
		static assert(!is(typeof(foo)));
		static assert(is(typeof(&foo)));
		static assert(is(typeof(&this.foo)));
		static assert(is(typeof(this)));
		void delegate() dg = &this.goo;
		dg=&this.foo; // error
		dg=&foo; // error
		dg();
		pragma(msg, typeof(&goo));
		static assert(is(typeof(&goo)==void delegate()const));
		static assert(is(typeof(&this.goo)==void delegate()const));
	}
	void goo()inout{
		pragma(msg, typeof(&goo));
	}
	void baz()immutable{
		//static assert(is(typeof(&goo)))
		pragma(msg, typeof(&goo));
		// void delegate()immutable dg = &this.goo; // TODO
		void delegate()const inout dg = &this.goo;
	}
}

struct TestMutDelegateFromConstRcvr{
	struct S{
		int delegate() dg;
		int delegate()immutable dg2;
		int delegate()const dg3;
	}
	int test(){
		int x;
		S s; s.dg = ()=>(x=2);
		s.dg3 = s.dg2 = ()immutable=>x;
		const(S) t=s;
		int y=t.dg2()+t.dg3(); // ok
		return t.dg()+y; // error
	}
}

//pragma(msg, is(int delegate()immutable:const(int delegate()immutable)));

const(int delegate()immutable) foofo;
//pragma(msg, typeof(cast()foo));


void foo(alias f,T...)(){
	T[0] t;
}

void main(){
	int x=2;
	struct S{
		int getX(){return x;}
	}
	int f(){return 2;}
	foo!(f,S)();
}

auto loc1(){
	int x = 2;
	struct Loc1{
		int getX(){ return x; } // error // TODO: better message?
	}
	return Loc1();
}
auto loc2(){
	int x = 3;
	struct Loc2{
		int getX(){ return x; }
	}
	return Loc2();
}

static int[] build(A,B)(){
	A a;B b;
	return [a.getX()];
}

pragma(msg, build!(typeof(loc1()), typeof(loc2()))());



int ppccfoo(){ return 1; }
class PP{
	int foo(){ return 2; }
}
class CC: PP{
	int bar(){
		ppccfoo();
		PP.foo();
		CC.foo();
		super.foo();
		this.foo();
		this.bar();
		super.bar();// error
		return foo();
	}
	static int baz(){
		this.foo();// error
		this.bar();// error
		super.foo();// error
/+		ppccfoo();
		PP.ppccfoo(); // error
		CC.ppccfoo(); // error
		PP.foo(); // error
		return foo(); // error+/
	}
	pragma(msg, typeof(this));
	pragma(msg, typeof(super));
	static assert(is(typeof(this)==CC));
	static assert(is(typeof(super)==PP));
}
pragma(msg, typeof(this)); // error

struct NOPP{
	void foo(){
		super.foo();//error
	}
}

/+

class D{
	int x;
	template bar(){
		int foo(){
			return x;
		}
	}
	static class C{
		int foo(){
			return bar!().foo(); // error
		}
	}
}

int intatmodulescope;

void testmodulescoperesolution(){
	double intatmodulescope; // fake
	static assert(is(typeof(.intatmodulescope)==int));
	pragma(msg, typeof(.intatmodulescope));
}


alias typeof((immutable(void[])).length) size_t;

pragma(msg, size_t);


void testpuredollar(){
	int[] x = [1,2,3];
	x[(()pure=>$,$-1)]=2; // must work
}



template Inex(a...){
	alias Inex!(1,a[0..n]) Inex; // error
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
	static void foo(){y[0]++;} // error
}

template TT(int i){
	alias Rest V;
	static if(i) alias TT!(0).V Rest;
	else alias thisiszero Rest;
	static if(i) enum thisisone=true;
	else enum thisiszero = 2;
}

pragma(msg, TT!(0).V);
pragma(msg, TT!(1).V);

template SS(bool i){
	static if(i) alias int V;
	else alias double V;
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
		a(); // error
		b=b; // error
	}
}


struct G {G g; }
struct F(T) { static int f(immutable ref T) {return 2;} }
pragma(msg, F!G.f(G.g)); // just a type error, because the pragma would attempt compile-time lookup of G.g



struct WW{
	void foo(){
		a=2; // error
	}
}

//immutable foo = 2; 
//pragma(msg, a);


struct Foo{
	//static double foo(){}
	static double foo(int){}
	int foo(){}
	static void goo(){
		Foo f;
		auto x=f.foo(2);
		auto y=Foo.foo(); // error
		pragma(msg, "x: ",typeof(x)," y: ",typeof(y));
	}
}

struct Test{
	static inout(int) foo(inout(int)){return 1;}
	double foo(int){return 1.0;}
	static void goo(){
		//foo();
		pragma(msg, typeof(Test.foo(cast(shared)1))); // error

		Test.foo(2); // TODO: should work (?)
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
// +/
// +/