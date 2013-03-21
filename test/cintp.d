
/+
// TODO: do we want deterministic slice aliasing in CTFE?
auto testsetlengthdet(){
	auto x = [1,2,3];
	auto y = x;
	x.length=4;
	y=x;
	x.length=5;
	y[0]=4;	
	return x;
}
static assert(testsetlengthdet()==[1,2,3,0,0]);
pragma(msg, "testsetlengthdet: ",testsetlengthdet());
+/

auto testsetlength(){
	auto x=[1,2,3,4];
	x.length=3;
	int[] y;
	x.length=y.length=4;
	(x.length+=1)++;
	assert(x.length==6);
	x.length=4;
	assert(x.length==4);
	return x~y;
}
static assert(testsetlength()==[1,2,3,0,0,0,0,0]);
pragma(msg, "testsetlength: ",testsetlength());

auto testdollarclosure(){
	int[] x = [1,2,3,4];
	ulong delegate() dg;
	x[(dg=()=>$,$-1)]=1; 
	assert(x[(assert($==4),3)]==1);
	return dg();
}
pragma(msg, "testdollarclosure: ",testdollarclosure());

auto testnulldelegate(){
	int delegate() dg; // =null; // TODO!
	return dg();
}

auto testnullfunpointer(){
	int function() fp=null;
	return fp();
}
pragma(msg, testnulldelegate());
pragma(msg, testnullfunpointer());


bool bsearch(T)(T[] haystack, T needle){
	if(haystack.length<=1) return (haystack~(needle+1))[0]==needle;
	bool b = haystack[$/2]>needle;
	return bsearch!T(haystack[b?0:$/2..b?$/2:$], needle);
}

pragma(msg, "bsearch1: ",bsearch!int([1,2,3],0));
pragma(msg, "bsearch2: ",bsearch!int([0,2,5],2));
pragma(msg, "bsearch3: ",bsearch!int([0,2,5],3));
pragma(msg, "bsearch4: ",bsearch!int([],0));


auto testdollar(){
	int[] x = [1,2,3,4];
	auto ptr=&x[(x~=cast(int)$,x~=cast(int)$,0)];
	assert(x.length==6 && x[$-2]==4 && x[$-1]==4);
	*ptr = 2;
	assert(x[0]==2);
	x[0]=1;
	assert(*ptr==1);
	x=x[0..$-2];
	return x[$-1]~x[$-3..$-1]~x[$-4..$][0];
}
static assert(testdollar()==[4,2,3,1]);
pragma(msg, "testdollar: ",testdollar());

auto loopclosures(int n){
	immutable(int)* delegate()[] a;
	for(int i=0;i<n;i++){
		immutable int j=i;
		a ~= {return &j;};
	}
	int[] r;
	for(int i=0;i<n;i++) r~=*a[i]();
	return r;
}

static assert(loopclosures(10)==[0,1,2,3,4,5,6,7,8,9],"TODO!"); // TODO!

auto testlambda(){
	int x;
	(){(){x++;}();}();
	return x;
}

pragma(msg, "testlambda: ",testlambda());


auto map(alias a,T)(T[] arg) if(is(typeof(a(arg[0]))[])){
	typeof(a(arg[0]))[] r;
	for(int i=0;i<arg.length;i++)
		r~=a(arg[i]);
	return r;
}
pragma(msg, typeof(map!(toString,int)));

int[] iota(int a, int b){ int[] r; for(int i=a;i<b;i++) r~=i; return r; }

bool pred(string s){
	int c=0;
	for(int i=0;i<s.length;i++) c+=s[i]=='2';
	return c>=2;
}

pragma(msg, filter!(pred,string)(map!(toString,int)(iota(0,1000))));

auto filter(alias a,T)(T[] arg) if(is(typeof(cast(bool)a(arg[0])):bool)){
	typeof(arg) r;
	for(int i=0;i<arg.length;i++)
		if(a(arg[i])) r~=arg[i];
	return r;
}

template binaryFun(alias fun,T){
	static if(is(typeof(fun)==string))
		auto binaryFun(T a, T b){
			return mixin(fun);
		}
	else alias fun binaryFun;
}

auto sort(alias p,T)(T[] arg){
	alias binaryFun!(p,T) pred;
	if(arg.length <= 1) return arg;
	bool low(T x){return !!pred(x,arg[0]);}
	bool high(T x){return !pred(x,arg[0]);}
	return sort!(pred,T)(filter!(low,T)(arg))
	~ arg[0] ~ sort!(pred,T)(filter!(high,T)(arg[1..arg.length]));
}



auto mod(int x){return (int y)=>y%x;}


auto mod10(int y){return mod(10)(y);}

enum unsorted = [3,28,1,29,33,828,11,282,34,378,122,122];

pragma(msg, sort!("a<b",int)(map!(mod10,int)(unsorted)));

//pragma(msg, sort!("a",int)(map!(mod10,int)([3,28,1,29,33,828,11,282,34,378,122,122])));

bool less(int a,int b){return a<b;}
pragma(msg, sort!(less,int)(unsorted));
pragma(msg, sort!(less,int)(unsorted));
pragma(msg, sort!("a>b",int)(unsorted));




auto testarrayptrlength(){
	int[] x = [1,2,4];
	assert(x.length==3);

	auto y = x.ptr;
	static assert(is(typeof(*y) == typeof(x[0])));
	assert(*y==1 && y[1]==2 && y[2]==4);

	*y=8;
	assert(x[0]==8);
	(){*(y+2)=1337;}();
	return *(y+x.length-1);
}
static assert(testarrayptrlength()==1337);
pragma(msg, "testarrayptrlength: ", testarrayptrlength());


typeof(null) retnull(){return null;}
pragma(msg, "retnull: ",retnull());

static assert(retnull() is null); // TODO!

static assert([] is null); // TODO!
static assert([] == null); // TODO!

immutable a = "hallo";
immutable b = a;
pragma(msg, a is b);
//pragma(msg, (()=>a is b)());
//pragma(msg, ((immutable(char)[] a, immutable(char)[] b)=>a is b)(a,b));

int retzero(){return 0;}
enum divby0 = 1/retzero();

/+
// TODO: should this be legal code?
struct InterpretImmutableField{
	immutable y=22;
}
static assert(InterpretImmutableField.y==22);
static assert((()=>InterpretImmutableField.y==22)());
+/

mixin(`auto foo1="1.0f";`);
mixin(`float a11=`~foo1~";");

enum short[] x = rngg();
int[] rngg(){return [1,2,3,];}
pragma(msg, "rngg: ", x);

bool testptrcmp(){
	auto x = [0,1];
	auto p = &x[0], q = &x[1];
	assert(*p==0 && *q==1);

	assert(p==p && p is p && p!<>p);
	assert(!(p!=p) && !(p!is p) && !(p<>p));

	assert(p!=q && p !is q && p<>q && p<>=q);
	assert(!(p==q) && !(p is q) && !(p!<>q) && !(p!<>=q));

	assert(p<q && p<=q && p!>q && p!>=q);
	assert(!(p!<q) && !(p!<=q) && !(p>q) && !(p>=q));

	assert(q>p && q>=p && q!<p && q!<=p);
	assert(!(q!>p) && !(q!>=p) && !(q<p) && !(q<=p));

	assert(*p==0 && *q==1);
	return true;
}
static assert(testptrcmp());


bool testrealcmp(){
	real a = 2, b = 3;

	assert(a==a && a is a && a!<>a);
	assert(!(a!=a) && !(a!is a) && !(a<>a));

	assert(a!=b && a !is b && a<>b && a<>=b);
	assert(!(a==b) && !(a is b) && !(a!<>b) && !(a!<>=b));

	assert(a<b && a<=b && a!>b && a!>=b);
	assert(!(a!<b) && !(a!<=b) && !(a>b) && !(a>=b));

	assert(b>a && b>=a && b!<a && b!<=a);
	assert(!(b!>a) && !(b!>=a) && !(b<a) && !(b<=a));

	b = 1.0L/0*0;
	assert(b!=b && b is b && b!<>=b);
	assert(!(b==b) && !(b!is b) && !(b<>=b));

	for(int i=0;i<3;i++){
		assert(a!<b && a!>b && a!<=b && a!>=b && a!<>=b && b!<>=b);
		assert(!(a<b) && !(a>b) && !(a==b) && !(a<=b) && !(a>=b));
		a=b;
		assert(a!=a);
		if(i==3) b=2;
	}
	return cast(bool)b;
}
static assert(testrealcmp());

real[] testreal(real a, real b){
	real[] r;
	r~=a;
	r~=b;
	r~=a+b;
	r~=a-b;
	r~=a/b;
	r~=b%a;
	double d = a, e = b;
	r~=d;
	r~=e;
	r~=d+e;
	r~=d-e;
	r~=d/e;
	r~=e%d;
	double f = a, g = b;
	r~=f;
	r~=g;
	r~=f+g;
	r~=f-g;
	r~=f/g;
	r~=g%f;
	//r~=a&b;
	real[] o;
	for(real* p = &r[0]; p !is &r[0]+18; p++) o~=*p;
	return o;
}
pragma(msg, "testreal: ",testreal(22.2,39.1));


int[] testbitwise(int a, int b){
	int[] r;
	r~=a&b;
	r~=a|b;
	r~=a^b;
	return r;
}
pragma(msg, "testbitwise: ",testbitwise(2883,28291));



int fops(int x){return x;}

//static assert(fops(1/fops(0)));
//static assert(foo(assert(0))); // DMD bug?

//enum x = (fops(),1);


// xP
/+int bug6498(int x)
{
	int n = 0;
	while (n < x)
		n++;
	return n;
}
static assert(bug6498(10_000_000)!=10_000_000);+/


immutable int immu=2;
int refp(ref immutable int x){
	return x;
}
pragma(msg, "refp: ",refp(immu));

int testaddr(){
	immutable int x;
	auto p = &immu;
	immutable(int*) id(immutable int* x){return x;}
	return *id(p);
	//return *(((immutable int* p)=>p)(p));
}
static assert(testaddr()==2);
pragma(msg, "testaddr: ", testaddr());

void testlocal1(){ // (should not compile)
	int x = 2;
	immutable y = x;
	bool tt(){return 2==y;}
	static assert(tt());
}

int testlocal2(){ // (should compile)
	immutable x = 2;
	immutable y = x;
	bool tt(){return 2==y;}
	static assert(tt());
}

int testlazy(){
	int x;
	int foo(lazy int x){return x;}
	foo(++x);
	return x;
}
pragma(msg, "testlazy: ",testlazy());

ref int testrefret(){
	int x;
	ref int foo(){ return x; }
	//ref int bar(){ return 2; }
	foo()=1;
	++foo();
	foo()++;
	foo()+=3;
	assert(x==6 && foo()==6);
	x=0;
	assert(foo()==0);
	foo()+=8;
	return x;
}
pragma(msg, "testrefret: ",testrefret());
static assert(testrefret()==8);

int testrefoutlazy(){
	int x=1;
	void testout(out int x){
		x=2;
	}
	void testref(ref int x){
		(++x)++;
		//x+=2;
	}
	//int testlazy(lazy int x){
	int testlazy(lazy int x){
		return x+x;
	}
	void testptr(int* x){*x+=2; x+=2;}
	testout(x);
	testref(x);
	testptr(&x);
	assert(x==6);
	auto t=testlazy(x++);
	assert(t==6+7);
	return x;
}
pragma(msg, "testrefoutlazy: ",testrefoutlazy());
static assert(testrefoutlazy()==8);



int[] createclosure(){
	int[] x;
	void delegate() foo(int start, int step){
		int i = start;
		return { x~=(i+=step); };
	}
	auto dg = foo(0,1);
	auto dg2 = foo(22,-2);
	for(int i=0;i<20;i++)
		((i&1)?dg:dg2)();
	return x;
}
pragma(msg, "createclosure: ",createclosure());


int casts(){
	int[] a = null;
	immutable(int)[] b = cast(immutable)a; // disallow unsafe cast
	a[0]=2;
	//int* x = &a[0];
	return 0;
}
pragma(msg, casts());



int twiceinterpret(){
	int accessible = 2; // only accessible from 'foo'  on the second invocation
	immutable zero = 0; // always accessible from 'foo'
	int foo(bool first){return first?zero:accessible;}
	enum y = foo(true); // fails
	return foo(false);  // suceeds
}
static assert(twiceinterpret()==2);


void invtest(){
	bool x = false;
	bool foo(){return true&&x;} // cannot access x
	bool ttt(){return foo();}
	static assert(ttt());
}
static assert({invtest(); return true;}());




//enum a = "mixin(a); mixin(a);";
//mixin(a);

int dggg(){
	int x=2;
	int foo(){return x;}
	static int bar(){return 2;}
	auto a = &foo;
	auto b = &bar;
	static assert(is(typeof(a): int delegate()));
	static assert(!is(typeof(a): int function()));
	static assert(is(typeof(b): int function()));
	static assert(!is(typeof(b): int delegate()));
	return a()+b();
}
pragma(msg, "dggg: ",dggg());
static assert(dggg()==4);

int[] testdelegate(){
	void doall(int delegate(int) dg, int[] a, int n){
		for(int i=0;i<n;i++) a[i]=dg(a[i]);
	}
	int t = 100;
	int squareplust(int x){return x*x+t;}
	int[] a = [1,2,3,4,5,2,1928];
	doall(&squareplust, a, 7);
	return a;
	// static assert(testdelegate()==[]);
}
static assert(testdelegate()==[101,104,109,116,125,104,3717284]);
pragma(msg, "testdelegate: ",testdelegate());


int testnested2(){
	int y=3;
	int foo(){
		int x;
		int bar(){
			return x+y--;
		}
		int qux(){
			auto yp = &y;
			int foo(){
				x = 2;
				return ++*yp +bar()+(*yp)++;//*yp++; // ok, but DMD cannot do this
			}
			return foo();
		}
		return qux();
	}
	return foo();
}

pragma(msg, "testnested2: ", testnested2());
static assert(testnested2()==13);



static assert({return rettrue();}());
auto rettrue(){return {return {return true;}();}();}

int testnested(){
	int x,y;
	int *p;
	(){p=&x;}();
	(){*p=3;}();

	(){int a=3;(){int z=--a;(){y=(){return z++;}();}();}();}();
	(){x++;}();
	return (){return (int x){return (int y){return x+y;}(y);}(x);}();
	//return (){return x+y;}();
}
pragma(msg, "testnested: ",testnested());
static assert(testnested()==6);




int* aliasinp(int* x){
	auto y = &x;
	return x;
}
int testalias(){
	int a, b;
	auto p = aliasinp(&a);
	auto q = aliasinp(&b);
	*p=2;
	*q=3;
	return a+b;
}
static assert(testalias()==5);
pragma(msg, "testalias: ",testalias());


int* escapestackref(int x){
	int y = x;
	//return aliasinp(&*&y); // this crashes DMD :o)
	return &y;
}
int testescape(){
	int a = 11;
	int* p = escapestackref(a);
	a = 12;
	int* q = escapestackref(a);
	return *p+*q;
}
static assert(testescape() == 23); // TODO: should this be an error instead?
pragma(msg, "testescape: ", testescape());

int addr(int a){
	int* x;
	int**y = &x;
	int***z = &y;	
	a=2;
	x = &a;
	return a;
}


pragma(msg, "addr: ",addr(3));

int tailcalls(int n, int x){
	if(!n) return x;
	return 1?tailcalls(n-1, x+n):10;
}
int tcfac(int n){
	version(DigitalMars) int loop(int x, int a) {return x>n?a: loop(x+1,x*a);}
	else mixin(q{int loop(int x, int a) => x>n?a: loop(x+1,x*a);});
	return loop(1,1);
}
pragma(msg, "tcfac: ", tcfac(10));


pragma(msg, "tailcalls: ",tailcalls(10000,0));

immutable(char)[] toEngNum(uint i){ // pure
	immutable static a=["zero","one","two","three","four","five","six","seven","eight","nine","ten","eleven",
	                   "twelve","thirteen","fourteen","fifteen","sixteen","seventeen","eighteen","nineteen"];
	immutable static b=[null,"ten","twenty","thirty","forty","fifty","sixty","seventy","eighty","ninety"];
	//static auto foo(int i)
	if(i>=1000000) return (uint i){immutable(char)[] s; while(i) s=(i%10+'0')~s, i/=10; return s;}(i);
	if(i>=1000) return toEngNum(i/1000)~" thousand"~(i%1000?" "~toEngNum(i%1000):"");
	if(i>=100) return toEngNum(i/100)~" hundred"~(i%100?" and "~toEngNum(i%100):"");
	if(i>=10) return i<20?a[i]:b[i/10]~(i%10?"-"~toEngNum(i%10):"");
	return a[i];
}

pragma(msg, "toEngNum: ",toEngNum(123562222));

pragma(msg, "toEngNum in a loop: ",{
		immutable(char)[][] r;
		for(int i=0;i<=1000;i++) r~=toEngNum(i);
		return r;
	}());


auto fun(int x){
	return ""~cast(byte)('0'+x);
}

auto testfuncall(){
	auto r="";
	for(int i=0;i<10;i++) r~=fun(i);
	return r;
}

pragma(msg, testfuncall());


char invass(char a, char b){
	return a~=b;
}
pragma(msg, invass(1,2));



auto generate(){
	auto r = `pragma(msg, "hallo");`;
	for(int i=0;i<20;i++) r~=r;
	return r;
}

//pragma(msg, generate());

enum gen = generate();
//mixin(gen);


int lvalue(){
	int a=2, b=3;
	(a*=b)+=(b*=a);
	int[] c=[1], d=[2];
	(c~=d)=d;
	int*p=&a;
	(p+=a)=p-a;
	return a+c[0]+*p;
}
static assert(lvalue() == 50);
pragma(msg, "lvalue: ",lvalue());


int[] slice(int[] e, int l, int r){
	return (&e[0]+1)[-1+l..r-1];
}

pragma(msg, "slice: ",slice([1,2,3],0,3));


int tt3(){
	//int tt3(){return 2;}
	return 3;
}

pragma(msg, "tt3: ",tt3());


int testbrkcnt(){
	int h=0,i,j=0,k=0,l=11;
	for(i=0;;i++){
		if(i>=10) break;
		else continue;
		i+=1234;
	}
 label:{h++;if(h<10) goto label;}
	do{
		j++;
		if(j>=10) break;
		else continue;
		j+=1234;
	}while(true);

	while(1){
		k++;
		if(k>=10) break;
		else continue;
		k+=1234;
	}

	{ for(;;) for(;;) goto outmost2;}
	i = 112233;
 outmost:for(outmost2:l=0;l<10;l++)
		for(;;){
			for(;;){
			next: for(;;) for(;;)break next;
				continue outmost;
			}
		}

	// TODO: foreach
	return h+i+j+k+l;
}
static assert(testbrkcnt() == 50);

pragma(msg, "testbrkcnt: ", testbrkcnt());


bool strchr(immutable(char)* haystack, immutable(char)* needle){
	if(haystack is null) return needle is null;
	auto p = haystack, q = needle;
	for(;; p++){
		for(auto h=p, n=q;;h++,n++){
			if(!*n) return true;
			if(*h != *n) break;
			else continue;
		}
		if(!*p) break;
	}
	((p))=p;
	return false;
}
pragma(msg, "strchr1: ",strchr(null, null)); 
pragma(msg, "strchr2: ",strchr(null, &"\0"[0])); 
pragma(msg, "strchr3: ", strchr(&"1234"[0],&"232"[0]));
pragma(msg, "strchr4: ", strchr(&"1234"[0],&"23"[0]));
pragma(msg, "strchr5: ", strchr(&"1234"[0],&"023"[0]));
pragma(msg, "strchr6: ", strchr(&"1234"[0],&"123"[0]));
pragma(msg, "strchr7: ", strchr(&"123"[0],&""[0])); // TODO: fix?
pragma(msg, "strchr8: ", strchr(&"\0"[0],&"\0"[0]));


int strcmp(immutable(char)[] a, immutable(char)[] b){
	auto p = &a[0], q = &b[0];
	while(*p && *p == *q){p++,q++;}
	return *p == *q ? 0 : *p < *q ? -1 : 1;
}

pragma(msg, "strcmp: ",strcmp("122","123"));


immutable estr = ["zero","one","two","three","four","five","six","seven","eight","nine","ten","eleven","twelve","thirteen","fourteen","fifteen","sixteen","seventeen","eighteen","nineteen"];

auto toestr(int i){
	//estr[i]="hello"; // TODO: array casting
	auto p = &estr[0];
	//return *(p+i);
	return *(&p[i+1]-1)~" "~*(&p[i-199]+199);
}
static assert(toestr(19)=="nineteen nineteen");
pragma(msg, toestr(19));


long testvoid(){
	long a = 0;
	long b = 0;
	b || function(long*a){*a = 1;}(&a);
	b || {a++;}();
	a && function(long*b){++*b;}(&b);
	a && {b+=2;}();
	return a+b;
}
static assert(testvoid()==5);
pragma(msg, "testvoid: ", testvoid());


int[][] funny(int[] a, int n, int p){
	int[][] l;
	for(int i=0;i<n;i++){
		int x,y;
		auto t=&y;
		auto c=[0,0,0];
		a[i]<p?x:a[i]==p?c[1]:*t=a[i];
		c[0]=x;
		c[2]=y;
		l~=c;
	}
	return l;
	
}

pragma(msg, "funny: ",funny([1,2,3,2,3,1,3,1,2,3,2,1],12,2));

int[][] funny2(int[] a, int n){
	int*[] ptrs;
	int[][] r;
	for(int i=0;i<n;i++) a[i]--, r~=[0,0,0];
	for(int i=0;i<3*n;i+=3) ptrs~=[&r[i/3][0],&r[i/3][1],&r[i/3][2]];
	for(int i=0;i<3*n;i+=3) *ptrs[i+a[i/3]]=a[i/3]+1;

	return r;
}


pragma(msg, "funny2: ",funny2([1,2,3,2,3,1,3,1,2,3,2,1],12));

static assert(funny([1,2,3,2,3,1,3,1,2,3,2,1],12,2)==funny2([1,2,3,2,3,1,3,1,2,3,2,1],12));

int ptrstore(){
	int x = 1;
	int* ptr = &x;
	*ptr = 2;
	return x;
}

pragma(msg, "ptrstore: ",ptrstore());


//static assert(ptrr(4) == 13);


int ptrr(int x){
	int a = x = x+++2;
	x = x--+a;
	auto y = &++--++++--x;
	auto z = &y;
	auto w = &z;
	auto u = &w;
	return *(*(*(*u)));
}
pragma(msg, "ptrr: ", ptrr(4));
static assert(ptrr(4) == 13);


int tttt(int x){
	x=2;
	int y = x++;
	return y;
}
pragma(msg, "tttt: ",tttt(2));

int ptr(int[] x){
	//int x = 222;
	auto p = &x[0];
	p++;
	auto y = p++;
	auto z = &y;
	return **z;
}
//pragma(msg, ptr(33));
pragma(msg, "ptr: ", ptr([1,2,3,4,5,6,7,8,9,10]));


immutable(char[]) acast(immutable(char)[] a){
	auto b = cast(char[])a;
	b[0] = 'b'; // TODO: should this be allowed or not?
	return cast(immutable)b;
}
pragma(msg, "acast: ", acast(`string`));


int div(int a, int b){ return a/b; }
pragma(msg, "div: ", div(1,0));

int index(int[] a, int b){ return a[b]; }
pragma(msg, "index: ", index([1,2,3],4));

ulong shl(long a, int b){ return a<<b; }
pragma(msg, "shl: ", shl(1,32*2));


real ttt(){
	real[][] y=[[]];
	y[0]=[2];
	return y[0][0];
}
pragma(msg, "ttt: ",ttt());

real tt2(){
	real[] y = [1];
	y[0]=2;
	return y[0];
}

pragma(msg, "tt2: ",tt2());


real testindex(){
	real[][] x;// = [[[2,3]],[[4],[5,6]]];
	int y = 3;
	x=[[2]]~[[y+2,y+100]];
	return x[1][1];
}

pragma(msg, "testindex: ",testindex());

real multiindex(){
	real[][][] x = [[[2,3]],[[4],[5,6]]];
	x[0]=[[3,4],[1,2]];
	return x[0][1][1];
}

pragma(msg, "multiindex: ",multiindex());


int[][][] ttlit(int n){
	int[][][] r = [[[1]]];
	for(int i=0;i<n;i++) r~=[[[],[1,2]],[[]]];
	return r;
}

pragma(msg, "ttlit: ", ttlit(4));


int[][][][] arraylit(int n){
	int[][][][] r;
	for(int i=0;i<n;i++) r~=[[[[]]],[[[1,2],[3],[4,5]],[[6],[7]],[[8,9]]],[[[]]]];
	return r;
}

pragma(msg,"arraylit: ",arraylit(4));

//pragma(msg, [[[[]]],[[[1,2],[3],[4,5]],[[6],[7]],[[8,9]]],[[[]]]]);
//pragma(msg, cast(void)1);
//pragma(msg, [[[]],[[2]]]);

real[] foo(int x){
	real[] r;
	for(int i=0;i<x;i++) r~=i*2+3;
	return r;
}

pragma(msg,"foo: ", foo(10));

immutable(char)[] bar(immutable(char)[] input){
	immutable(char)[] r=null;
	for(int x=1;x<3;x++) r~=input;
	return r~r;
}

mixin(bar("pragma(msg,`success!`,bar(\"success!\"));"));
pragma(msg,"bar: ", bar("pragma(msg,`success!`,bar(\"success!\"));"));



int[] dupit(int[] arg, int n){
	int[] r;
	for(int i=0;i<n;i++) r~=arg[i];
	return r;

}

pragma(msg, "dupit: ",dupit([1,2,3,4,5],5));


int[] sqr(int[] arg, int n){
	int[] r;
	for(int i=0;i<n;i++) r~=arg[i], r~=arg[i]*arg[i];
	return r;
}

pragma(msg, "sqr: ",sqr([1,2,3,4,5],5));


auto teststr(){ return "test"; }
pragma(msg, "teststr: ",teststr());

auto tostr(int n){
	immutable(char)[][] r;
	for(int i=0;i<n;i++){
		immutable(char)[] s;
		if(!i) s="0";
		else s="";
		int j=i; 
		while(j) s=(j%10+'0')~s, j/=10;
		r~=s;
	}
	return r;
}

pragma(msg, "tostr: ",tostr(100));

int[] dowhile(){
	int n = 20;
	int[] r;
	do{
		r~=n--*n--;
	}while(n>0);
	return r;
}
pragma(msg, "dowhile: ",dowhile());


int[] incall(int[] arg, int n){
	for(int i=0;i<n;i++) arg[i]++;
	return arg;
}
pragma(msg, "incall: ",incall([1,2,3,4,5],5));


int[] incspec(int[] arg){
	arg[4]=arg[0]++;
	return arg;
}
pragma(msg, "incspec: ",incspec([1,2,3,4,5]));

int sum(int x){
	int y=0;
	while(x){
		y=y+x;
		x--;
	}
	return y;
}
pragma(msg, "sum: ",sum(3));

int factorial(int n){
	uint r=1;
	for(int i=2;-i>=-n;++i) r=r*i;
	return r;
}
pragma(msg, "factorial: ",factorial(12));


int[] erathos(int x){
	bool[] p;
	for(int i=0;i<=x;i++) p~=true;
	for(int i=3;i*i<=x;i+=2){
		if(p[i]) for(int k=i*i;k<=x;k=k+i) p[k]=false;
	}
	int[] r;
	if(x>=2) r~=2;
	for(int i=3;i<=x;i+=2) if(p[i]) r~=i;
	return r;
}

pragma(msg, "erathos: ",erathos(1000));

int[] primes(int x){
	int[] r;
	if(x>=2) r~=2;
	for(int i=3;i<=x;i=i+2){
		int d=0;
		bool isprime = true;
		for(int j=2;(j<i)&&isprime;j=j+1){
			if(!(i%j)){
				isprime = false;
				//break;
			}
		}
		if(isprime) r~=i;
	}
	return r;
}

pragma(msg, "primes: ",primes(100)); // TODO!: array boundschecks (in interpretV?)
/+

//mixin("s");


//pragma(msg, bar("e"));

/+
enum e = (()=>cast(immutable)2)();
pragma(msg, 'j'~"ello");

//pragma(msg, typeof(e+cast(immutable)1));

pragma(msg, [2Li+2]<[2Li+1]);
//pragma(msg, [2i-1]<[2i+1]);

enum immutable(dchar)[] str = 'j'~"ello";
static assert(str == "jello");
pragma(msg, typeof('j'~"ello"));


pragma(msg, (()=>cast(immutable)'j')()~"ello");
pragma(msg, typeof((()=>cast(immutable)'j')()));
pragma(msg, typeof('j'~"ello"));
pragma(msg, typeof(cast(immutable)2));+/
/+auto x = 2;
int bar(){
	return 2;
	//if(auto x = -100) if(x) return (++++x)++;
}
static assert(!is(typeof({enum _ = (assert(!bar()),1);})));

pragma(msg, assert(bar()));+/



immutable int xx = 10;
auto azfoo(int x){
	real y,z;
	z=y=x+xx;
	return z;
}
pragma(msg, "azfoo: ",azfoo(2));

/+
+/

/+immutable int y=2;
immutable foo = [[[2+y]]];
immutable shared int[][][] xxx = [[[2+y]]];

pragma(msg, typeof(xxx[0]));

pragma(msg, typeof(cast(immutable)[1]));

pragma(msg, "oOoOoO: ",xxx);


auto dg = (delegate int(int x) => x)(2);+/



//int x;
//pragma(__p, [2,x]~1);

// +/
// +/

alias immutable(char)[] string;

auto toString(int i){
	immutable(char)[] s;
	do s=(i%10+'0')~s, i/=10; while(i);
	return s;
}
