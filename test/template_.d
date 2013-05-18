
struct MatchLevels{
	enum foos=[
		q{static int fooN(int x)(int y){ return M; }},
		q{static int fooN(int x)(const int y){ return M; }},
		q{static int fooN(int x)(float y){ return M; }},
		q{static int fooN(const int x)(int y){ return M; }},
		q{static int fooN(const int x)(const int y){ return M; }},
		q{static int fooN(const int x)(const int y){ return M; }},
		q{static int fooN(float x)(int y){ return M; }},
		q{static int fooN(float x)(const int y){ return M; }},
		q{static int fooN(float x)(float y){ return M; }},
		q{static int fooN()(){ return M; }},
	];
	enum assrt=q{static assert(fooN!1(1)==M);};
	static string replace(string s, string a, string b){
		string r;
	Louter:for(ulong i=0;i<=s.length-a.length;){
			for(ulong j=0;j<0+a.length;j++)
				if(s[i+j]!=a[j]){r~=s[i],i++;continue Louter;}
			r~=b;
			i+=a.length;
		}
		return r;
	}
	static string replNM(string s,int i, int j){
		return replace(replace(s,"N",i.toString),"M",(i?i.toString:"")~j.toString);
	}
	static string generate(){
		string r;
		for(int i=0;i<foos.length-1;i++){
			for(int j=i;j<foos.length;j++)
				r~=replNM(foos[j],i,j)~"\n";
			r~=replNM(assrt,i,i)~'\n';
		}
		return r;
	}
	mixin(generate()); // TODO!
}

template toStringNow(ulong v)
{
    static if (v < 10)
        enum toStringNow = "" ~ cast(char)(v + '0');
    else
        enum toStringNow = toStringNow!(v / 10) ~ toStringNow!(v % 10);
}
void unittest_()
{
    static assert(toStringNow!(1uL << 62) == "4611686018427387904");
}
template toStringNow(long v)
{
    static if (v < 0)
        enum toStringNow = "-" ~ toStringNow!(cast(ulong) -v);
    else
        enum toStringNow = toStringNow!(cast(ulong) v);
}

void unittest_()
{
	static assert(toStringNow!(0x100000000) == "4294967296"); // TODO
	static assert(toStringNow!(-138L) == "-138");             // TODO
}

struct TemplatedParserHack(T){
	this(int a[]){}
}
pragma(msg, TemplatedParserHack!int);


template Ambiguous(int a){ enum Ambiguous = "moo"; }
template Ambiguous(int a){enum Ambiguous = "foo"; }

pragma(msg, Ambiguous!2); // TODO


template T(int a) if(!T!a){  // error
	enum a = false;
}
pragma(msg, T!1);            // // TODO: show it here!

template factorial(int n){
	static if(n<=1) enum factorial = 1.0L;
	else enum factorial = n*factorial!(n-1);
}
pragma(msg, factorial!20);


auto gen(){
	immutable(char)[] r;
	//for(int i=0;i<=130;i++) r~=`enum e`~toString(i)~`=factorial!`~toString(i)~".V;\n";
	for(int i=0;i<=100;i++) r~=`pragma(msg,factorial!`~toString(i)~");\n";
	return r;
}

//pragma(msg, gen());
//mixin(gen());


template recu1(int n){
	static if(n<=1) int V(){return 1;}
	else int V(){return recu1!(n-1).V();}
}

pragma(msg, "recu1: ",recu1!20.V());

template recu2(int n){
	static if(n<=1) int recu2(){return 1;}
	else auto recu2(){return recu2!(n-1)()+1;}
}

pragma(msg, "recu2: ",recu2!20());


//pragma(msg, factorial!130.V);



auto testtemplatefunclit(fun...)(){
	static if(!fun.length) return "";
	else{
		alias fun[0] tmpl;
		static if(is(typeof(tmpl!(double,string)))) alias tmpl!(double,string) ff;
		else alias tmpl ff;
		pragma(msg, typeof(ff));
		return ff(0,4.5,"fun ")()~testtemplatefunclit!(fun[1..$])();
	}
}
struct FunContainer{
	static fun(int x,double y,string z)=>()=>z~"hi1";
}
pragma(msg, "testtemplatefunclit 1: ",testtemplatefunclit!(FunContainer.fun)()); // TODO!
pragma(msg, "testtemplatefunclit 2: ",testtemplatefunclit!((int x,double y,string z)=>()=>z~"hi2")());
immutable u = "123";
pragma(msg, "testtemplatefunclit 3: ",testtemplatefunclit!((int x,y,z)=>()=>u~u~" hi3")());
pragma(msg, "testtemplatefunclit 4: ",testtemplatefunclit!((int x,y,z)=>()=>toString(cast(int)y)~z~"hi4")());


template Deflt(T,S=int,R:float=int){
	enum Deflt = "success";
}
pragma(msg, "Deflt: ",Deflt!int);


template CircCirc(a...){
	template F(A){}
	alias F!(CircCirc!(1,2,3)) CircCirc; // error
}
pragma(msg, CircCirc!());


template Test(alias a){
	enum Test = a;
}

//int delegate() fozo(){return ()=>2;}
//pragma(msg,Test!(fozo())() // TODO!



template redefinedparam(T)if(is(typeof(t)==int)){
	void redefinedparam(T t) {}
	enum a = t; // is an error
}
pragma(msg, redefinedparam!int);


template CircularInstantiation(int x){
	enum A = CircularInstantiation!x;
	enum CircularInstantiation = x;
}
pragma(msg, CircularInstantiation!3);



template fc(int x){
	static if(x<=1) enum fc=1;
	else enum fc = x*fc!(x-1);
}
pragma(msg, "fc: ",fc!10);


template tmpl(T){
	static if(is(T==double)){
		T[] tmpl(T arg){return [arg, 2*arg];}
	}else{
		T[] tmpl(T arg){return is(T==int)?[arg]:[arg,arg,2*arg];}
	}
	//alias int T;
}
pragma(msg, tmpl!int(2),"\n",tmpl!float(2),"\n",tmpl!double(2),"\n",tmpl!real(22));





/+
template ttt(int x){
	int ttt(){return 2;}
	pragma(msg, typeof(ttt));
}
mixin ttt!2;
+/

template AA(string xx){
	enum x = mixin(xx);
	static assert(x>0);
	template BB(int y) if(x<y){
		static assert(y<10); // error
		enum BB = "hello world";
	}
}
//pragma(msg, AA!"0".BB!1);
//pragma(msg, AA!"0".BB!0);
pragma(msg, AA!"3".BB!13~' '~AA!"3".BB!4);


auto to(T,F)(F arg){
	static if(is(F==int) && is(T==string)) return toString(arg);
	else static assert(0, "not implemented!"); // error
}

pragma(msg, [to!(string,int)(1337)]);
pragma(msg, [to!(string,uint)(1337u)]);


template Ov(const(int) x){pragma(msg, 1);}
template Ov(uint x){pragma(msg, 2);}

mixin Ov!2u; // TODO

template isInputRange(R){
	enum isInputRange=is(typeof({
		R r;
		if(!r.empty()) r.popFront();
		auto f = r.front();
	}));
}

template ElementType(R) if(isInputRange!R){
	alias typeof({R r; return r.front();}()) ElementType;
}

struct Range{
	bool empty(){return false;}
	void popFront(){}
	int front(){return 10;}
}
struct NonRange{
	auto really(){return -10;}
	bool nota(){return true;}
	void range(){}
}
Range r;

//pragma(msg, ElementType!Range);

auto array(R)(R arg) if(isInputRange!R) {
	ElementType!R[] res;
	for(auto r = arg; !r.empty(); r.popFront()) res~=r.front();
	return res;
}
//pragma(msg, typeof(array!Range(r)));
//pragma(msg, typeof(array!NonRange(r)));


struct PRange(alias a){
	bool empty(){return false;}
	void popFront(){}
	auto front(){return a;}// error
}

PRange!r pr;
PRange!pr ppr;
PRange!ppr pppr;
PRange!pppr ppppr;

pragma(msg, "! ",ElementType!(ElementType!(ElementType!(ElementType!(PRange!(ppr))))));

pragma(msg, ElementType!(PRange!ppr));
pragma(msg, ElementType!(PRange!pr));

pragma(msg, typeof(array!(PRange!pppr)(ppppr)));


pragma(msg, typeof(PRange!pr.front()));

pragma(msg, "!!",typeof(PRange!(PRange!(r)).front()));

struct L(T){
	static if(is(typeof(T.t))) enum t = T.t*2;
	else enum t = 1;
}

static assert(L!(L!(L!(L!(L!(L!(L!(L!int))))))).t == 1<<7);
pragma(msg, "L!L!L!...: ", L!(L!(L!(L!(L!(L!(L!(L!int))))))).t);


//pragma(msg, int*);

pragma(msg, "Range*: ",ElementType!(Range*));


pragma(msg, ElementType!Range);
pragma(msg, ElementType!NonRange); // error
pragma(msg, isInputRange!Range);
pragma(msg, isInputRange!NonRange);


template TT(int x) if(x>22){ immutable int TT = x; }

pragma(msg, TT!21); // error
pragma(msg, TT!23); // ok

bool iloop(){return iloop();}
template LoL(int x) if(x>22&&iloop()){ immutable int LoL=x; }
pragma(msg, LoL!21); // error


auto foo3(){
	immutable int y=22;
	auto fooz()(){return y+2;}
	auto x = (){enum a = fooz!()(); return a;};
	pragma(msg, typeof(x));
	return x();
}
pragma(msg, foo3());


version(DigitalMars){} // TODO
else mixin(q{
int testaliasparam(){
	int x;
	template Foo(alias X) { auto p(){return &X;} }
	template Bar(alias T) { alias T!(x) abc; }
	void test() { alias Bar!(Foo) bar; *bar.abc.p() = 3; }
	test();
	return x;
}
static assert(testaliasparam()==3);
pragma(msg, "testaliasparam: ",testaliasparam());
});


class TemplatedLocalVariable{
	int x;
	template foo(){
		int z; // TODO: error
	}
	static void fooz(){
		TemplatedLocalVariable s;
		TemplatedLocalVariable.foo!().z=2;
		s.foo!(33).z=2; // error
		foo!().z=2;     // TODO (shouldn't show anything)
		s.foo!().z=2;
	}
	void bar(){
		foo!().z=3;
	}
}

template test(){
	void test(){
		//enum test = 2;
		//pragma(msg, test!());
		pragma(msg, "inner!");
		test!();
	}
}
void instantiatetest(){test!();}



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
	immutable int[][] z=[[]];
	pragma(msg, typeof(gun!x()));
	pragma(msg, typeof(gun!y()));
	pragma(msg, typeof(gun!(z)()));
	pragma(msg, gun!z()());
	gun!z()();
	gun!y()()=gun!x()();
	int delegate()ref x = gun!y();
	x()+=2;
	return y;
}
pragma(msg, "fun: ",fun());

T twotimes(T)(T arg)=>arg+arg;
pragma(msg, twotimes!double(32.2));



void foo(){
	D d;
	d.test!().foo(2);
}

class D{
	int x;
	static template test(){
		mixin(q{ // error

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
}


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



static assert(!is(typeof({
	template U(long v){
		static if (v < 0){}
		else enum U = U!(cast(ulong) v);
	}
	void testU(){ U!2; }
})));


auto testImplConvIdentity(){
	template TT(long x){
		int TT = x;
	}
	TT!1=1;
	TT!1L=2;
	return cast(char)(TT!1+'0')~" "~cast(char)(TT!1L+'0');
}
static assert(testImplConvIdentity()=="2 2");
pragma(msg, "testImplConvIdentity: ",testImplConvIdentity());



/+struct S{
	immutable foo = "222";
}+/


auto test(){
	immutable x = "hello, world!";
	auto bar(){return x;}
	auto bar2(){return x;}
	pragma(msg, foo!bar2());
	return foo!bar();
}
pragma(msg, test());


auto foo(alias a)(){
	//pragma(msg, typeof(a));
	return a(); // error
}
T foo123(T)(T arg){
	return arg>0?arg+foo!T(arg-1):0;
}
void fooz(){pragma(msg, typeof(foo123!int));foo123!int(2);} // error

pragma(msg, foo123!double(42.23));


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
pragma(msg, test3());

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

//auto get(alias a)(){return a;}

struct S{
	immutable int x=TT!().SS!().TT;
	immutable int a=x;
	template TT(){
		template SS(){
			alias c TT;
		}
	}
	static immutable int c=222; // // TODO: should it work without static?
	pragma(msg, a);
	//int a;
	//int foo(){return a+2;}
	//pragma(msg, "get: ", get!a());
	//pragma(msg, "foo: ", foo());
	static int foo(int){
		S s;
		return s.TT!().SS!().TT;
	}
	pragma(msg, foo(2),"28282");
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

// +/
// +/
// +/

/+template Sort(Pred,T...){
	template PredC(alias A){ template PredC(alias B){ alias Pred!(A,B) PredC; } }
	static if(!T.length) alias T Sort;
	else alias TypeTuple!(Sort!(Pred,staticFilter!(PredC!(T[0]),T[1..$/2+1])),T[0],Sort!(Pred,staticFilter!(PredC!(T[0]),T[$/2+1..$]))) Sort;
}+/


alias immutable(char)[] string;
auto toString(int i){
	immutable(char)[] s;
	do s=(i%10+'0')~s, i/=10; while(i);
	return s;
}

