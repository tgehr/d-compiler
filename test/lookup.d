template TypeTuple(T...){ alias T TypeTuple;}


void local(){
	int x;
	//alias x y;
	alias TypeTuple!x y;
	static void foo(){y[0]++;}
}

/+
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

alias TypeTuple!(QQ.x, QQ.y) QQs;
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