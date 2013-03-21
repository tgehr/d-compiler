//enum a = "mixin(a); mixin(a);";
//mixin(a);

int tailcalls(int n, int x){
	if(!n) return x;
	return tailcalls(n-1, x+n);
}

pragma(msg, tailcalls(10000,0));


immutable(char)[] toEngNum(uint i){ // pure
	immutable static a=["zero","one","two","three","four","five","six","seven","eight","nine","ten","eleven",
	                   "twelve","thirteen","fourteen","fifteen","sixteen","seventeen","eighteen","nineteen"];
	immutable static b=[null,"ten","twenty","thirty","forty","fifty","sixty","seventy","eighty","ninety"];
	//static auto foo(int i)
	if(i>=1000000) return (uint i){immutable(char)[] s; while(i) s=(i%10+'0')~s, i/=10; return s;}(i);
	if(i>=1000) return toEngNum(i/1000)~" thousand"~(i%100?" "~toEngNum(i%1000):"");
	if(i>=100) return toEngNum(i/100)~" hundred"~(i%100?" and "~toEngNum(i%100):"");
	if(i>=10) return i<20?a[i]:b[i/10]~(i%10?"-"~toEngNum(i%10):"");
	return a[i];
}

pragma(msg, toEngNum(123562222));


pragma(msg, {
		immutable(char)[][] r;
		for(int i=0;i<1000;i++) r~=toEngNum(i);
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

pragma(msg, slice([1,2,3],0,3));


int tt3(){
	//int tt3(){return 2;}
	return 3;
}

pragma(msg, tt3());


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


bool strchr(immutable(char)[] haystack, immutable(char)[] needle){
	auto p = &haystack[0], q = &needle[0];
	for(;; p++){
		for(auto h=p, n=q;;h++,n++){
			if(!*n) return true;
			if(*h != *n) break;
			else continue;
		}
		if(!*p) break;
	}
	return false;
}

pragma(msg, "strchr: ", strchr("1234","232"));
pragma(msg, "strchr: ", strchr("1234","23"));
pragma(msg, "strchr: ", strchr("1234","023"));
pragma(msg, "strchr: ", strchr("1234","123"));
pragma(msg, "strchr: ", strchr("123",""));
pragma(msg, "strchr: ", strchr("",""));


int strcmp(immutable(char)[] a, immutable(char)[] b){
	auto p = &a[0], q = &b[0];
	while(*p && *p == *q){p++,q++;}
	return *p == *q ? 0 : *p < *q ? -1 : 1;
}

pragma(msg, strcmp("122","123"));


immutable estr = ["zero","one","two","three","four","five","six","seven","eight","nine","ten","eleven","twelve","thirteen","fourteen","fifteen","sixteen","seventeen","eighteen","nineteen"];

auto toestr(int i){
	//estr[i]="hello"; // TODO: array casting
	auto p = &estr[0];
	//return *(p+i);
	return *(&p[i+1]-1)~" "~*(&p[i-199]+199);
}

pragma(msg, toestr(19));


long testvoid(){
	long a = 0;
	long b = 0;
	b || (a = 1); // TODO: replace with lambda call
	a && (b = 1); // TODO: replace with lambda call
	return a+b;
}

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


/+int[][][] ttlit(int n){
	int[][][] r = [[[1]]];
	for(int i=0;i<n;i++) r~=[[[],[1,2]],[[]]];
	return r;
}

pragma(msg, "ttlit: ", ttlit(4));+/

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

pragma(msg, "erathos: ",erathos(10000));

/+
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

pragma(msg, primes(10000)); // TODO!: array boundschecks (in interpretV?)
+/

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


/+
immutable int xx = 10;
auto foo(int x){
	real y,z;
	z=y=x+xx;
	return z;
}
pragma(msg, foo(2));+/

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
