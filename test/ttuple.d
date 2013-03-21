
int testZeroArgs(){
	int x;
	int foo(){ return x; }
	return foo((x++,Seq!())); // TODO!
}
pragma(msg, testZeroArgs());


auto seqret(int a, int b){auto x=Seq!(a,b);return x;}

auto seqtak(){auto x = seqret(1,2); return x[0];}
pragma(msg, "seqtak: ", seqtak());
//pragma(msg, seqret(1,2)); // TODO!

auto compose(alias a, alias b,T...)(T args){
	return a(b(args));
}

auto seqid(T...)(T args){
	return args;
}
auto add(int a, int b, int c)=>a+b+c;
pragma(msg, "multiret: ", compose!(add,seqid)(1,2,3));

int testmultirefret(){
	int a, b;
	ref Seq!(int, int) multirefret(){
		return Seq!(a,b); // TODO
	}
	multirefret()=Seq!(1,2); // TODO
	return a+b;
}
pragma(msg, "testmultirefret: ", testmultirefret());

T seq(T...)(T args){ return args; }
pragma(msg, (()=>[seq(1,2,3,4)])());
pragma(msg, [seq(1,2,3,4)]); // TODO

/+

struct Tpl{
	Seq!(int, double) foo;
	int a,b;
	alias Seq!(a,b) c;
}

void checkTpl(){
	void fun(int, double){ }
	Tpl t;
	fun(t.c);   // TODO!
	t.c[0]=2;   // TODO!
	t.foo[0]=2; // TODO!
}

/+
/+
alias Seq Seq;

auto seqparm(A,B,C...)(Seq!(A,B,C) args){
	return args[0]+args[1]+args[2]+args[$-1];
}

static assert(seqparm(1,2,3.0,4,5)==11.0);
pragma(msg, "seqparm: ",seqparm(1,2,3.0,4,5));


pragma(msg, Seq!(1,2,3,4)[1..3]);
Seq!(int,double,float,long)[1..3] xx;
pragma(msg, typeof(xx));
pragma(msg, "length: ",Seq!(1,2,3).length);
pragma(msg, "$ 1: ", Seq!(1,2,3)[$-1]);

pragma(msg, "$ 2: ", Seq!(int,double)[$-1]);

pragma(msg, "$ 3: ", Seq!(1,2,3)[1..$]);
pragma(msg, "$ 4: ", Seq!(int,int,int)[1..$]);

void convErrMsg(){
	Seq!(int, double) a=Seq!(1.0,2);
}

static assert(!is(Seq!(int, double)==int));



template Fst(T...){
	alias T[0] Fst;
}

pragma(msg, "Fst: ",[Seq!(Fst!(Seq!("133",2,3,4)),"2","3","4")]);




/+int main(){
	Seq!(int,int) x = Seq!(1,2);
	x[1]=3;
	x[0]-=11;
	return x[0]+x[1];
}+/
//pragma(msg, main());


auto refe(ref Seq!(int,int,int,int) arg){
	return ++arg[0]+ ++arg[1]+ --arg[2]+ --arg[3];
}

auto testt(ref int a, ref int b, ref int c, ref int d){
	a++; b++; c++; d++;
}
auto testAliasTuple(){
	int a,b,c,d;
	int x;
	//alias Seq!(a,b,c,d) tp;
	//tp=++x;
	Seq!(int,int,int,int) tp=++x;
	//a=1;b=2;c=1;d=3;
	//pragma(msg, typeof({tp;tp[0];}));
	//(){testt(tp);}();

	//alias f_d a_d;
	//static void foo(){tp[0]=2;}

	(){testt(tp);}();
	
	x=333;
	auto r=[tp]~{testt(tp); return [tp];}()~refe(tp)~[tp];
	//return r[1..12];
	return r;
}
static assert(testAliasTuple()==[2,3,4,5,3,4,5,6,18,4,5,4,5]);
pragma(msg, testAliasTuple());

pragma(msg, Seq!(1,2,3));
pragma(msg, typeof(Seq!(1,2,3)));
pragma(msg, Seq!(1,int,3));
pragma(msg, typeof(Seq!(1,int,3)));
pragma(msg, Seq!(float,int,double));

static assert(is(Seq!(int,double)==Seq!(int,double)));
static assert(!is(Seq!(double,int)==Seq!(int,double)));
static assert(is(Seq!(int delegate(int, int[]))==Seq!(int delegate(int,int[]))));

pragma(msg, Seq!(1,Seq!(int,double),2,Seq!(float,real,int[])));

Seq!(1,2,3)[1] aaa; // error

pragma(msg, Seq!(1,2,3,Seq!(1,2,3)));

//pragma(msg, Seq!(int,double)[0]);

Seq!(int,[2])[0] as;
pragma(msg, typeof(as));
//pragma(msg, x);


Alias!(Seq!(int,2)) a; // error

static assert(Seq!(0,"test")); // error

static assert(Seq!(1,""));
void main(){assert(Seq!(1,""));}


mixin(Seq!("int x;"));

int[Seq!(1,2)] ad; // error


alias Seq!(1,2) start;
enum Seq!(int,int) aii = 12;
//pragma(msg, aii[Seq!(start,3,5,11)]);


//Seq!(int,double) aid = Seq!(1,1,2);

void test(){
	//	aid = Seq!(1,1,2);
}

immutable int[2] a2=[1,2];
//pragma(msg, a[1..3]);
pragma(msg, a2[1]);

template StaticMap(alias F, a...){
	static if(a.length) alias Seq!(F!(a[0]), StaticMap!(F,a[1..a.length])) StaticMap;
	else alias Seq!() StaticMap;
}

template StaticFoldr(alias F, a...){
	static if(a.length==2) alias F!(a[0],a[1]) StaticFoldr;
	else alias F!(a[0],StaticFoldr!(F, a[1..a.length])) StaticFoldr;
}


template CommonType(A,B){ alias typeof({A a; B b; return 1?a:b;}()) CommonType; }
pragma(msg, StaticFoldr!(CommonType, int, double, short, real));

template TimesTwo(int x){ enum TimesTwo = x+x; }
template Square(int x){ enum Square = x*x; }


pragma(msg, [StaticMap!(TimesTwo,StaticIota!(1,31))]);
pragma(msg, StaticMap!(Square,StaticIota!(1,31)));


template StaticFilter(alias F, a...){
	static if(!a.length) alias a StaticFilter;
	else static if(F!(a[0])) alias Seq!(a[0], Rest) StaticFilter;
	else alias Rest StaticFilter;
	static if(a.length) alias StaticFilter!(F,a[1..a.length]) Rest;
}

bool any(alias a,R)(R r, int len){// if(is(typeof(a(r[0])) == bool)) {
	for(int i=0;i<len;i++) if(a(r[i])) return true;
	return false;
}
static bool lower(char s) { return 'a'<=s&&s<='z'; }

alias immutable(char)[] string;
template isUppercase(string s) if(is(typeof(s[2]))&&!is(typeof(s[3]))){
	enum isUppercase = {
		static bool lower(char s) { return 'a'<=s&&s<='z'; }
		return !any!(lower, string)(s,3);
	}();
}

//pragma(msg, isUppercase!"123");
//pragma(msg, isUppercase!"aBc");
//pragma(msg, isUppercase!"ABC");
//pragma(msg, isUppercase!"AbC");
//pragma(msg, isUppercase!"DEF");

pragma(msg, StaticFilter!(isUppercase,"123","aBc",Seq!("ABC","AbC"),"DEF"));

template StaticIota(int a, int b) if(a<=b){
	static if(a==b) alias Seq!() StaticIota;
	else alias Seq!(a,StaticIota!(a+1,b)) StaticIota;
}


template Divides(int a){
	template Divides(int b){
		enum Divides = a%b==0;
	}
}

//pragma(msg, (Divides!2)!2);


template IsPrime(int p){
	//enum IsPrime = StaticFilter!(Divides!p, StaticIota!(1,p+1)).length==2;
	enum IsPrime = {
		int r;
		for(int i=1;i<=p;i++) r+=!(p%i);
		return r;
	}()==2;
}

pragma(msg, IsPrime!2);
pragma(msg, IsPrime!4);
pragma(msg, IsPrime!5);
pragma(msg, IsPrime!13);
//pragma(msg, IsPrime!20);

/+pragma(msg, IsPrime!53);
pragma(msg, IsPrime!70);
pragma(msg, IsPrime!103);
pragma(msg, IsPrime!103);+/

pragma(msg, ListPrimes!103);

template Primes(int i){
	alias StaticFilter!(IsPrime, StaticIota!(2,i+1)) Primes;
}

template ListPrimes(int upper){
	enum ListPrimes = H!2;
	template H(int lower){
		enum H = "";
		static if(lower <= upper){
			static if(IsPrime!lower){pragma(msg, lower,H!(lower+1));}
			else enum next=H!(lower+1);
		}
	}
}



pragma(msg, StaticIota!(1,12)," ", Primes!12);

//pragma(msg, StaticIota!(2,100).V);


//pragma(msg, a[0].mangleof);
//pragma(msg, _a_field_0.mangleof);

// +/
// +/
// +/

template Seq(T...){ alias T Seq; }

template Alias(T){ alias T Alias; }
