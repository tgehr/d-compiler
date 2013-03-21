
auto foo(){
	immutable int y=22;
	auto fooz()(){return y+2;}
	auto x = (){enum a = fooz!()(); return a;};
	pragma(msg, typeof(x));
	return x;
}
pragma(msg, foo()());



/+int testaliasparam(){
	int x;
	template Foo(alias X) { auto p(){return &X;} }
	template Bar(alias T) { alias T!(x) abc; }
	void test() { alias Bar!(Foo) bar; *bar.abc.p() = 3; }
	test();
	return x;
}
pragma(msg, testaliasparam());+/

/+class S{
	int x;
	template foo(){
		int z;
	}
	static void fooz(){
		S s;
		S.foo!().z=2;
		s.foo!(33).z=2;
		foo!().z=2;
	}
	void bar(){
		foo!().z=3;
	}
}+/


/+
T foo(T)(T arg){
	return arg>0?arg+foo!T(arg-1):0;
}
void fooz(){pragma(msg, typeof(foo!int));foo!int(2);}

pragma(msg, foo!double(42.23));


template test(){
	void test(){
		//enum test = 2;
		pragma(msg, test!()());
		pragma(msg, "inner!");
		test!();
	}
}

void main(){
	test!();
}
+/
/+

// TODO: currently, recursive templates are in Omega(N^2)
// TODO: FIX!

template factorial(int n){
	static if(n<=1) enum V = 1.0L;
	else enum V = n*factorial!(n-1).V;
}
template recu1(int n){
	static if(n<=1) int V(){return 1;}
	else int V(){return recu1!(n-1).V();}
}

pragma(msg, recu1!200.V());

template recu2(int n){
	static if(n<=1) int V(){return 1;}
	else auto V(){return recu2!(n-1).V();}
}

pragma(msg, recu2!200.V());


//pragma(msg, factorial!130.V);

auto gen(){
	immutable(char)[] r;
	//for(int i=0;i<=130;i++) r~=`enum e`~toString(i)~`=factorial!`~toString(i)~".V;\n";
	for(int i=0;i<=100;i++) r~=`pragma(msg,factorial!`~toString(i)~".V);\n";
	return r;
}

//pragma(msg, gen());
mixin(gen());
+/

/+
auto gun(alias a)(){
	cast(void)a;
	static if(is(typeof({cast(void)a;}): void delegate())) enum stc = null;
	else enum stc = "static ";
	mixin(stc~q{ref typeof(a) foo(){auto ptr=&a; return *ptr;};});
	return &foo;
}
immutable int x=223;

auto fun(){
	int y;
	static const(int[][]) z=[[2]];
	pragma(msg, typeof(gun!x()));
	pragma(msg, typeof(gun!y()));
	pragma(msg, typeof(gun!(z)()));
	pragma(msg, gun!z()());
	gun!y()()=gun!x()();
	int delegate()ref x = gun!y();
	x()+=2;
	return y;
}
pragma(msg, fun());
+/
//T foo(T)(T arg)=>arg+arg;
//pragma(msg, foo!double(32.2));

/+struct Foo{
	static int foo(){}
	int foo(){}
	void goo(){
		Foo f;
		f.foo();

	}
}+/

/+
struct Test{
	static inout(int) foo(inout(int)){return 1;}
	double foo(int){return 1.0;}
	static void goo(){
		//foo();
		pragma(msg, typeof(Test.foo(cast(shared)1)));

		Test.foo(2);
	}
}

+/
/+
void foo(){
	D d;
	d.test!().foo(2);
}

class D{
	int x;
	static template test(){
		mixin(q{

	int foo(){
			return x;
				}});
	}
	static class C{
		int foo(){
			return test!().foo();
		}
	}
}



void main(){
	auto c = new D.C;
	//c.goo();
}+/

/+
//enum b = is(typeof(a)), a = b;

//pragma(msg, a);
//pragma(msg, b);

template Foo(alias a){
	mixin(a);
}

pragma(msg, Foo!"enum Foo = \"Foo\";");


template A(){
	static if(!is(typeof(B!())==int)) enum A = 2;
	//enum A = 2;
	enum A = B!();
}


template B(){
	static if(!is(typeof(A!())==int)) enum B = 2;
	enum B = 2;
}
//alias B!() b;

//pragma(msg, b);
pragma(msg, A!());
pragma(msg, B!());

//alias int T;
template tmpl(T){
	static if(is(T==double)){
		T[] tmpl(T arg){return [arg, 2*arg];}
	}else{
		T[] tmpl(T arg){return is(T==int)?[arg]:[arg,arg,2*arg];}
	}
	//alias int T;
}
pragma(msg, tmpl!int(2),"\n",tmpl!float(2),"\n",tmpl!double(2),"\n",tmpl!real(22));



pragma(msg, mixin({return ['1'];}()));

auto mxin(const(char)[] s)(){
	mixin(s);
}

pragma(msg, mxin!q{return "asdf";}());
pragma(msg, mxin!"return 123;"()+1);
pragma(msg, mxin!"return \"323\" ~ \"123\";"());

//pragma(msg, 2!2);


template TTT(T){immutable TTT=cast(T)1;}

pragma(msg, TTT!int);
pragma(msg, TTT!float);

template TTTT(T:int){immutable int TTTT=2;}

pragma(msg, TTTT!int);
static assert(!is(typeof(TTTT!float)));

template ttt(immutable(char)[] op : "+"){enum ttt=2;}

pragma(msg, ttt!"+");
static assert(!is(typeof(ttt!"-")));

template tt2(long a : 2){enum tt2=a;}
pragma(msg, tt2!(2));
static assert(!is(typeof(tt2!(1))));
+/

/+struct S{
	immutable foo = "222";
}


auto test(){
	immutable x = "hello, world!";
	auto bar(){return x;}
	auto bar2(){return x;}
	pragma(msg, foo!bar2());
	return foo!bar();
}
pragma(msg, test());+/

/+
auto foo(alias a)(){
	//pragma(msg, typeof(a));
	return a();
}

auto test2(){
	auto x = "hello, world!";
	auto bar(){return x;}
	return foo!bar();
}
pragma(msg, test2());

auto test3(){
	auto x = 22;
	auto foo1(){return x;}
	auto bar(){return foo1();}
	return foo!bar()+foo!foo1();
}
pragma(msg, test3());+/

auto foo2(alias a, alias b)(){
	b++;
	return a(b);
}

/+auto test4(){
	auto x = 2;
	auto foo(int y){
		assert(y==3);
		auto id(int x){return x;}
		auto r=foo2!(id,y)();
		assert(y==4 && r==4);
		return r;
	}
	return foo2!(foo,x)();
}+/

auto get(alias a)(){return a;}

struct S{
	immutable int x=TT!().SS!().TT;
	immutable int a=x;
	template TT(){
		template SS(){
			alias c TT;
		}
	}
	immutable int c=222;
	pragma(msg, a);
	//int a;
	//int foo(){return a+2;}
	//pragma(msg, "get: ", get!a());
	//pragma(msg, "foo: ", foo());
	static int foo(int){
		S s; // TODO: fix
		return s.TT!().SS!().TT;
	}
	pragma(msg, foo(2));
}

/+
auto test4(){
	auto x = 2;
	auto foo(int y){
		assert(y==3);
		auto id(int x){
			assert(x==4);
			return x;
		}
		assert(y==3);
		auto r=foo2!(id,y)();
		assert(y==4);
		return r;
	}
	x++;
	return foo(x);
}
pragma(msg, "test4: ",test4());
+/


/+class C{
	static int x(){return 0;};
	struct S{
		void bar(){
			foo!x();
		}
	}
}+/


//
T identity(T)(T arg){
	return arg;
}
pragma(msg, "identity: ",identity!int(2)," ",identity!float(2.0)," ",identity!real(-2));


/+
struct S{
	//T foo(T)(T arg){return arg;}
	enum foo = 2;
}
pragma(msg, S.foo);

void main(){
	S s;
	s.foo!int(2);
}

//template Mxin(string x,string y){}

//pragma(msg, Tmpl!int.foo());


// hallo timon heeeeeey <--- copyright (C) 2012 Josef Ziegler +/

auto toString(int i){
	immutable(char)[] s;
	do s=(i%10+'0')~s, i/=10; while(i);
	return s;
}
