
static assert(is(int delegate()auto==int delegate()));

void delegateArrayInference() {
	void writeln(string x);
	auto tbl1 = [
		(string x) { writeln(x); },
		(string x) { x ~= 'a'; },
	];
	auto tbl2 = [
		(string x) { x ~= 'a'; },
		(string x) { writeln(x); },
	];
}

struct testLookupConversionError{
	struct S{
		int delegate() dg;
	}
	static int test(){
		S s;
		int x;
		s.dg = ()=>x=2;
		const(S) t=s;
		pragma(msg, typeof(t.dg)); // error
	}
}



class A{}
class B:A{}

auto f(A function() dg){return dg();}

//pragma(msg, f(()=>cast(B)null));

auto testcontextded(){
	auto a = [x=>x+1, y=>2*y, (long z)=>z/2];
	static assert(is(typeof(a[0]): long function(long)));
	auto b = [[(long x)=>x+1],[y=>2*y], [z=>z/2]];
	static assert(is(typeof(b[0][0]): long function(long)));
	auto c = [[x=>x+1],[y=>2*y], [(long z)=>z/2]];
	static assert(is(typeof(c[0][0]): long function(long)));
	auto d = [[[x=>x+1]],[[x=>x]],[[(long x)=>x+1]]];
	auto e = [[[x=>x+1, x=>x, (long x)=>x+1]]];
	return d[0][0][0](1)+d[1][0][0](2)
		+ e[0][0][0](1)+e[0][0][1](2);
}
static assert(testcontextded()==8);

void testinex(){
	void foo(int delegate(int) dg){}
	foo(x=>y); // error: 'y' is undefined
}


pragma(msg, (int x, int y){}()); // error: wrong number of parameters


auto testdederr()=>(x,y,z,w)=>{return y;}(2,"hello",4,5)(); // error: deduction failure
typeof(x=>x) testdederr2; // error: deduction failure

auto testdederr3(){
	auto a=(x=>x(2))(x=>x); // error: deduction failure (no inference)
	auto b=(cast(int function(int function(int)))x=>x(2))(x=>x); // ok
	static assert(is(typeof(b)==int));
}



auto testdedinit(bool b){
	string delegate(int, double, string)[] dgs =
		[(x,y,z)=>toString(x),(x,y,z)=>toString(cast(int)y),(x,y,z)=>z];

	template Seq(T...){ alias T Seq;}

	alias Seq!(int, double, string) P;

	double delegate(P)[] dg2 = b?[(x,y,z)=>x]:[(x,y,z)=>y];

	alias Seq!(1,2,"3") args;

	return dgs[0](args)~dgs[1](args)~dgs[2](args)~(dg2[0](1,2,"3")==2?"2":"?");
}

pragma(msg, "testdedinit 1: ",testdedinit(false));
pragma(msg, "testdedinit 2: ",testdedinit(true));

static assert(testdedinit(false)=="1232" && testdedinit(true)=="123?");


auto deduceparamfromdollar(){
	int[] x=[-1,1,1337,3,0,0,0];
	return x[][][0..$-1][][][1..$-1][][][0..$-1][][]
	[
	 ((x,y,z,w)=>{
		 assert(x==z && y[0]=='$' && z+1==w && w==3 && $==3);
		 return x-1;
	 })($-1,"$-1",$-1,$)()
	];
}
static assert(deduceparamfromdollar()==1337);
pragma(msg, "deduceparamfromdollar: ",deduceparamfromdollar());



shared(typeof(delegate()const{})) x;
pragma(msg,shared(typeof(cast()x)));

//const(const(int)*****) y;
//pragma(msg, typeof(y));


struct AccessibleImmutable{
	immutable int xx=2;
	void foo(){
		static assert(is(typeof(()=>xx):immutable(int) delegate()));
	}
}

auto testdeduction(){
	auto x=(x=>x)(2);
	int function(int) foo0=x=>x;
	auto foo1 = cast(int delegate(int))x=>x;
	int delegate(int) foo2 = cast(int delegate(int))(int x)=>x;
	
	float higho(double delegate(int, double, float) dg){
		return dg(1,2,3);
	}

	return foo0(1)+foo1(2)+foo2(3)+x+higho((x,y,z)=>(x+y+z)/3);
}

static assert(testdeduction()==10.0f);
pragma(msg, "testdeduction: ",testdeduction());


void validconversions(){
	void delegate()const[] x;
	const(void delegate())[] y = x;
}


struct S{
	int a;
	int foo(){return 2;}
	pragma(msg, (()=>foo())()); // error: 'this' is missing
	mixin({ // TODO!
		auto s="enum a0=0;";
		for(int i=1;i<100;i++)
			s~="enum int a"~toString(i)~"=a"~toString(i-1)~"+"~toString(i*2-1)~";";
		return s;
	}());
	pragma(msg, "a5: ", a5); static assert(a5==25); // TODO
}

void testfunctiondeduction(){
	immutable int x = 0;
	static assert(is(typeof((){enum e=x;return e;}):immutable(int)function())); // TODO
}

void main(){
	int sjisjis;
	static pure void main()@safe nothrow pure{sjisjis=2;} // error: context not accessible
	auto x = &main;
	static assert(is(typeof(&main)==void function()pure nothrow @safe));
	static assert(!is(typeof(&x): void function()*));
	auto y = &x;
	static assert(!is(typeof(&y): void function()**));

	//auto _ = main;
	auto a = (){(){}();};
	pragma(msg, typeof(a));
	//auto a = (){};
	//pragma(msg, typeof(a));
	//void function() a;
	//a=&main;
	auto b = (){(){a();}();};
	auto c = delegate(){(){}();};
	static assert(is(typeof(a): void function()));
	static assert(is(typeof(b): void delegate()));
	static assert(!is(typeof(c): void function()));
	static assert(is(void delegate()@safe: void delegate()));
	static assert(is(void delegate()@safe: void delegate()@trusted));
	static assert(is(void delegate()@trusted: void delegate()@safe));
	static assert(is(void function() pure nothrow @safe : void function()));
	static assert(!is(void function() : void function()pure nothrow @safe));
}


// +/
// +/

auto toString(int i){
	immutable(char)[] s;
	do s=(i%10+'0')~s, i/=10; while(i);
	return s;
}

alias immutable(char)[] string;

