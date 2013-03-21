/+/+
template Alias(T){ alias T Alias; }

template TypeTuple(T...){ alias T TypeTuple; }

pragma(msg, TypeTuple!(1,2,3,4)[1..3]);
TypeTuple!(int,double,float,long)[1..3] xx;
pragma(msg, typeof(xx));



/+int main(){
	TypeTuple!(int,int) x = TypeTuple!(1,2);
	x[1]=3;
	x[0]-=11;
	return x[0]+x[1];
}+/
//pragma(msg, main());


auto refe(ref TypeTuple!(int,int,int,int) arg){
	return ++arg[0]+ ++arg[1]+ --arg[2]+ --arg[3];
}


auto testt(ref int a, ref int b, ref int c, ref int d){
	a++; b++; c++; d++;
}
auto testAliasTuple(){
	int a,b,c,d;
	int x;
	//alias TypeTuple!(a,b,c,d) tp;
	//tp=++x;
	TypeTuple!(int,int,int,int) tp=++x;
	//a=1;b=2;c=1;d=3;
	//pragma(msg, typeof({tp;tp[0];}));
	//(){testt(tp);}();
	auto r=[tp]~{testt(tp); return [tp];}()~refe(tp)~[tp];
	return r[1..12];
}
static assert(testAliasTuple()==[2,3,4,2,3,4,5,14,3,4,3]);
pragma(msg, testAliasTuple());



pragma(msg, TypeTuple!(1,2,3));
pragma(msg, typeof(TypeTuple!(1,2,3)));
pragma(msg, TypeTuple!(1,int,3));
pragma(msg, typeof(TypeTuple!(1,int,3)));
pragma(msg, TypeTuple!(float,int,double));

static assert(is(TypeTuple!(int,double)==TypeTuple!(int,double)));
static assert(!is(TypeTuple!(double,int)==TypeTuple!(int,double)));
static assert(is(TypeTuple!(int delegate(int, int[]))==TypeTuple!(int delegate(int,int[]))));

pragma(msg, TypeTuple!(1,TypeTuple!(int,double),2,TypeTuple!(float,real,int[])));

TypeTuple!(1,2,3)[1] aaa;

pragma(msg, TypeTuple!(1,2,3,TypeTuple!(1,2,3)));

//pragma(msg, TypeTuple!(int,double)[0]);

TypeTuple!(int,[2])[0] as;
pragma(msg, typeof(as));
//pragma(msg, x);


Alias!(TypeTuple!(int,2)) a;

static assert(TypeTuple!(0,"test"));

static assert(TypeTuple!(1,""));
void main(){assert(TypeTuple!(1,""));}


mixin(TypeTuple!("int x;"));

int[TypeTuple!(1,2)] ad;
+/

template TypeTuple(T...){alias T TypeTuple;}
alias TypeTuple!(1,2) start;
enum TypeTuple!(int,int) aii = 12;
//pragma(msg, aii[TypeTuple!(start,3,5,11)]);


//TypeTuple!(int,double) aid = TypeTuple!(1,1,2);

void test(){
	//	aid = TypeTuple!(1,1,2);
}

immutable int[2] a=[1,2];
//pragma(msg, a[1..3]);

pragma(msg, a[1]);


template StaticMap(alias F, int len, a...){
	static if(len) alias TypeTuple!(F!(a[0]), StaticMap!(F,len-1,a[1..len]).V) V;
	else alias TypeTuple!() V;
}

template StaticFoldr(alias F, int len, a...){
	static if(len==2) alias F!(a[0],a[1]) V;
	else alias F!(a[0],StaticFoldr!(F,len-1,a[1..len]).V) V;
}

template TimesTwo(int x){ enum TimesTwo = x+x; }
template Square(int x){ enum Square = x*x; }

template CommonType(A,B){ alias typeof({A a; B b; return 1?a:b;}()) CommonType; }

pragma(msg, StaticMap!(TimesTwo,5,1,2,3,4,5).V);
pragma(msg, StaticMap!(Square,5,1,2,3,4,5).V);

pragma(msg, StaticFoldr!(CommonType, 4,int, double[], short, real).V);
+/

/+alias S.t a;
struct S{
	int t;
	void foo(){
		a=2;
	}
}+/

/*
  TT!1.V ->
  TT!1.Rest ->
  TT!0.V ->
  


 */

template TypeTuple(T...){alias T TypeTuple;}
template StaticFilter(alias F, int len, a...){
	static if(!len) alias a V;
	else static if(F!(a[0])) alias TypeTuple!(a[0], Rest) V;
	else alias Rest V;
	static if(len) alias StaticFilter!(F,len-1,a[1..len]).V Rest;
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

pragma(msg, StaticFilter!(isUppercase,5,"123","aBc",TypeTuple!("ABC","AbC"),"DEF").V);

template StaticIota(int a, int b) if(a<=b){
	static if(a==b) alias TypeTuple!() V;
	else alias TypeTuple!(a,StaticIota!(a+1,b).V) V;
}

template Divides(int a){
	template Divides(int b){
		enum Divides = a%b==0;
	}
}

template IsPrime(int p){
	enum IsPrime = !is(typeof(StaticFilter!(Divides!p, p, StaticIota!(1,p+1).V).V[2]));
	/+enum IsPrime = {
		int r;
		for(int i=1;i<=p;i++) r+=!(p%i);
		return r;
	}()==2;+/
}

pragma(msg, IsPrime!2);
pragma(msg, IsPrime!4);
pragma(msg, IsPrime!5);
pragma(msg, IsPrime!20);

pragma(msg, IsPrime!53);
pragma(msg, IsPrime!70);
pragma(msg, IsPrime!103);
pragma(msg, IsPrime!103);

pragma(msg, ListPrimes!103);

template Primes(int i){
	alias StaticFilter!(IsPrime, i-1, StaticIota!(2,i+1).V).V V;
}

template ListPrimes(int upper){
	enum ListPrimes = H!2;
	template H(int lower){
		enum H = "";
		static if(lower <= upper){
			/+static if(IsPrime!lower)+/ pragma(msg, lower,H!(lower+1));
			//else pragma(msg, H!(lower+1));
		}
	}
}



//pragma(msg, StaticIota!(1,12).V," ", Primes!12.V);

//pragma(msg, StaticIota!(2,100).V);


//pragma(msg, a[0].mangleof);
//pragma(msg, _a_field_0.mangleof);

// +/