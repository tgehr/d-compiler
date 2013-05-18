// ok now

struct DRPF{
	struct DynRange(T){
		DynRange!T delegate() popFrontImpl;
		void popFront(){
			auto u = popFrontImpl();
		}
	}
	pragma(msg, DynRange!int);
}

enum x = (cast(ulong)0x10009 >> 1) == 0x8004;


template filter(alias a){
	auto filter(){
		auto r = Filter();
		assert(r.x==2);
		r.range = dynRange();
		assert(r.x==2);
		r.popFront();
		return r;
	}
	static struct Filter{
		int x=2;
		DynRange!int range;
		void popFront(){
			range.popFront2();
		}
	}
}


struct DynRange(T){
	DynRange!T delegate() popFrontImpl;
	void popFront2(){
		auto u = popFrontImpl();
	}
}


DynRange!int dynRange(){
	DynRange!int result;
	auto retres()=>result;
	result.popFrontImpl = &retres;
	return result;
}

auto crash(){
	auto foo(int a){ return a; }
	auto r=filter!foo();
	return 0;
}
pragma(msg, "crash: ", crash());


auto ttex(){
	int start=2;
	auto exec(alias a)(){return a(2); }
	return exec!(a=>a%start)();
}
static assert(ttex()==0);
pragma(msg, "ttex: ",ttex());


template Seq(T...){alias T Seq;}
template StaticFilter(alias F, a...){
	static if(!a.length) alias a StaticFilter;
	else static if(F!(a[0])) alias Seq!(a[0], Rest) StaticFilter;
		else alias Rest StaticFilter;
	static if(a.length) alias StaticFilter!(F,a[1..a.length]) Rest;
}

template Pred(int x){ enum bool Pred = x&1; }
pragma(msg, StaticFilter!(Pred, 1, 2, 3, 4, 5, 6, 7));

template U2(long v) { static if(true) enum U2 = 2; }
void testU2(){ U2!2; }

auto balancedIndexOf(alias a=(a,b)=>a==b, T, V...)(const(T)[] c, V v){
	auto init = 0;
	template bal(immutable(char)[] s) { auto bal = init; }
	for(typeof(c.length) i=0;i<c.length;i++){
		if(c[i]=='(') bal!"("++;
		else if(c[i]==')') bal!"("--;
		else if(c[i]=='[') bal!"["++;
		else if(c[i]==']') bal!"["--;
		else if(c[i]=='{') bal!"{"++;
		else if(c[i]=='}') bal!"{"--;
		if(bal!"("||bal!"["||bal!"{") continue;
		if(a(c[i],v)) return i;
	}
	return -1;
}
static assert(balancedIndexOf("(,),",',')==3);

string nqueens(int n){
	string r;
	void write(){}
	void write(T...)(T args) { r~=args[0]; write(args[1..$]); }

	write("123");
	return r;
}

static assert(nqueens(2)=="123");


static assert((()=>-1LU)()==-1LU);

int indexOf(alias a=(a,b)=>a==b,T)(const(T)[] c, const(T) v){
	for(int i=0;i<c.length;i++)
		if(a(c[i],v)) return i;
	return -1;
}

static assert(indexOf!()("aba",'b')==1);

static assert(!is(typeof({
				int delegate(int delegate(int delegate(int)) delegate(int)) arg;
				return arg(x=>y=>z=>2);
			})));

auto II(T)(T arg){ return arg; }
static assert(is(typeof(II(cast(const)0))==int));

int* pII;
static assert(is(typeof(II(cast(const)pII))==const(int)*));

struct Foo {
	int[2] bar;
}
const(int[2]) spam() {
	const Foo* x;
	return true ? x.bar : [10, 20];
}
void main() {}

auto fun(){return "a function";}
auto fun(T...)(T args){return 1;}
template fun(a...){auto fun(T...)(T args){return 2;}}
template fun(a...){template fun(b...){auto fun(T...)(T args){return 3;}}}

static assert(!is(typeof(fun!()(0))));
static assert(!is(typeof(fun!()())));
static assert(!is(typeof(fun(0))));
static assert(fun()=="a function");

int a;
struct T{
	static assert(is(typeof(a) == float));
	pragma(msg, typeof(a));
	pragma(msg, typeof(a));
	mixin(`float a=`~bar~";");
	mixin(`const foo=`~c~`;`);
	mixin(`const bar="`~foo~`";`);
	mixin(q{mixin(q{mixin(q{const c = "`1.0`";});});});
}

template MAlias(A,B){ alias A delegate(B) MAlias2; }

auto malias(A,B)(MAlias!(A,B).MAlias2 dg, B arg){ return dg(arg); }
pragma(msg, malias!(int,int)((int x)=>x,3));

int rec(T)(int x){
	if(!x) return 0;
	return 1+rec!T(x-1);
}
pragma(msg, rec!int(2));

int[] rec(int[] arg){
	if(!arg.length) return arg;
	return rec(arg[1..arg.length]);
}
enum unsorted = [1,2];

pragma(msg, rec(unsorted));
pragma(msg, rec(unsorted));

int[][] funny2(int[] a, int n){
	int*[] ptrs;
	int[][] r;
	for(int i=0;i<n;i++) a[i]--, r~=[0,0,0];
	for(int i=0;i<3*n;i+=3) ptrs~=[&r[i/3][0],&r[i/3][1],&r[i/3][2]];
	for(int i=0;i<3*n;i+=3) *ptrs[i+a[i/3]]=a[i/3]+1;

	return r;
}
pragma(msg, "funny2: ",funny2([1,2,3,2,3,1,3,1,2,3,2,1],12));

auto id(A)(A arg) => arg;

pragma(msg, id(1));


static assert(!is(typeof({
				struct S{
					immutable int x=TT!().SS!().TT;
					template TT(){ template SS(){ alias x TT; } }
				}
			})));

auto testtemplatefunclit(alias fun)(){ return fun!int(2); }
pragma(msg, "testtemplatefunclit 3: ",testtemplatefunclit!(x=>2)());

int testlazy(){
	int x;
	void testl(lazy int y){
		assert(y==1&&y==2);
		assert(x==2);
	}
	testl(++x);
	return x;
}
static assert(testlazy()==2);


/+
int k;

typeof(z) x;
typeof(x) y;
typeof(y) z;
+/

static assert(is(typeof({int delegate(int) dg = x=>2;})));

// +/
// +/

alias immutable(char)[] string;
alias typeof((int[]).length) size_t;
