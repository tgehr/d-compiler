

/+
class A { auto foo(){ return "A"; } alias int string; } // TODO: error

template ID(alias a){ alias a ID; }
template P(){ alias ID!(mixin(new C().foo())) P; }
class C : P!(){
	override string foo(){ return x; }
}
enum x = "A";+/

/+

struct Exp(string code, A...){
	A a; 
	auto eval(){ return mixin(code); }
	auto opBinary(string op,B)(B b){
		return Exp!("(a[0].eval()"~op~"a[1].eval())",typeof(this),B)(this,b);
	}
}
auto eval(A)(A a){ return a; }
auto val(A)(A a){ return Exp!("a[0]",A)(a); }
auto var()(string name){ return Exp!("d[a[0]].eval(d)",string)(name); }

//import std.stdio;
void main(){
	//(1.val+2.val*"x".var).eval(["x":22.val]).writeln;
	//1.val;
	Exp!("a[0]",int)(1);
}
+/

/+struct FoFo{
	struct S2{
		void x()(int a) { }
		void y() const {
			x(42); // error
			auto u=&x!(); // error
			pragma(msg, typeof(&x!())); // TODO: ok
		}
	}
}+/
/+
/+int dontTouchThis(alias a)(){

	static struct S{
		int foo(){
			pragma(msg, typeof(a(2)));
			static assert(is(typeof({return a(2);}))); // no access check inside typeof
			a(2); // should be an error
			return 2;
		}
	}
	S s;
	return s.foo();
}

int nanana(){
	int x=3;
	auto goo(T)(T a)=>a+x;
	return dontTouchThis!(a=>a+x)();
}
//pragma(msg, "nanana: ", nanana());
+/
/+
struct TTTTTTTTT{
	static int fun(T)(){
		T s;
		return s.f();
	}
	
	static int main() {
		int x=2;
		void f(){}
		struct R { int f() { return x; } } // should work
		auto m = fun!(R)();
		return m;
	}
	pragma(msg, main());
}
+/
/+template ID(alias d){ alias d ID; }
template boo(){ alias ID!(x=>2) boo;}

pragma(msg, boo!()(2));+/

/+struct ReturnTypeLambdaParameterIfti{
	void foo(T)(T a, T b) { }
	void main() {
		foo((int a)=>a, b=>1.0); // foo!(double function(int))
	}
}
+/

/+struct UndefinedIdentifierError{
	void foo(T)(T delegate(int) arg, T delegate(S) brg){} // TODO: better error message
	pragma(msg, foo(a=>1,a=>1.0));
}
+/

/+
struct TemplatedParserHack(T){
	this(int a[]){}
}
pragma(msg, TemplatedParserHack!int); // TODO: fix assertion failure
+/
/+
struct TemplatedConstructor(T){
	this(T)(T arg){}
	static create(){
		return TemplatedConstructor(2); // TODO: should work
	}
}
pragma(msg, TemplatedConstructor!int);
+/
/+
template forward(args...)
{
	@property forward()(){ return args[0]; }
}

void main()
{
	int a = 1;
	int b = 1;
	assert(a == forward!b); // TODO: should work
}+/


/+template foot(alias a){
	auto foot(){
		return a();
	}
}
int main(){
	int x=2;
	int foo(){ return x; }
	static int bar(){
		return foot!foo();
	}
	return bar();
}
pragma(msg, main());+/


/+
struct Foo(_T) {
	alias _T T;
}
void bar(FooT)(FooT foo, FooT.T x){ // TODO: silence
	pragma(msg, typeof(x));
}
void main() {
	Foo!int foo;
	bar(foo, 1);
}+/


/+
// TODO: make interpretation of partially analyzed functions work
int cdep(){ enum x=cdep2(); return x;}
int cdep2(){ return cdep(); }+/

/+auto intarrlen = int[].length;+/

/+// TODO: this must work! (need notion of potential indirections to support this)
pragma(msg, {
	string x = "123";
	auto y = ['1','2','3'];
	return x~=y;
}());
+/

/+// TODO: better error message
pragma(msg,{
		immutable (int)*[] x;
		int y = 2;
		x~= cast(float*)&y;
		return *x[0];
	}());
+/

/+
template asdf(){}
template Uninstantiable() if(asdf(2)){}
template Instantiable() if(Uninstantiable!()){}
pragma(msg, typeof(Instantiable!())); // show error!
+/

// enum returnVoidArray = delegate void[](){return [2];}();
// enum returnEmptyArray = ((int delegate(int))=>[])(x=>x);

/+
template Seq(T...){ alias T Seq; }
int aMatchError(R)(Seq!R delegate(int) dg){ return dg(2); }
pragma(msg, aMatchError(a=>a)); // TODO: remove reference to matcher type in error message
+/

/+
pragma(msg, ElementType!(int));
template ElementType(T=S,S=T){ alias typeof({T t; return t[0];}()) ElementType; } // display error message
+/

// make compile
/+
auto indexOf3(alias a=(a,b)=>a==b, T, V...)(const(T)[] c, const V v){
	for(typeof(c.length) i=0;i<c.length;i++)
		if(a(c[i],v)) return i;
	return -1;
}

static assert(indexOf3("aba", 'b')==1);
+/
/+
auto indexOf2(alias a=(a,b)=>a==b, T...)(const(T)[] c, const T v){
	for(typeof(c.length) i=0;i<c.length;i++)
		if(c[i]==v) return i;
	return -1;
}
static assert(indexOf2("aba",'b')==1); // spurious error message+/


/+improve error messages!+/

/+template Cont(R,A){ alias R delegate(R delegate(A)) Cont; }

auto ret(R,A)(A arg){ return (R delegate(A) k)=>k(arg); }
auto cat(R,A,B)(Cont!(R,A) me, Cont!(R,B) delegate(A) f){
	return (R delegate(B) k)=>me(r=>f(r)(k));
}

auto callCC(B,R,A,T...)(Cont!(R,A) delegate(Cont!(R,B) delegate(A),T) f, T args){
	1=2;
	return (R delegate(A) k)=>f(a=>_=>k(a), args)(k);
}

auto testcallCC(){
	auto f(Cont!(int,int) delegate(int) cont, int x){
		return cat(x<3?cont(x):ret!int(1),a=>cont(x+a));
	}
	assert(callCC(&f,1)(x=>x)==1);
	assert(callCC(&f,3)(x=>x)==4);
	return callCC(&f,1)(x=>x)+callCC(&f,3)(x=>x);
}+/
/+
// ok now
struct MixinAccessCheck{
	struct S{
		immutable int x = 2;
	}
	pragma(msg, mixin(q{S.x}));

	template ReturnType(func...) if (func.length == 1) {
		alias int ReturnType;
	}
	struct BinaryOperatorX(string _op, rhs_t,C) {
		ReturnType!(mixin("C.opBinary!(_op,rhs_t)")) RET_T;
	}
	class MyClass {
		auto opBinary(string op, T)() { }
	}
	void PydMain() {
		BinaryOperatorX!("+", int, MyClass) foo;
	}
}

struct FOFOFO{
	enum x = undef; // error
	mixin(`float a11=`~foo1~";"); // error
}

struct DRPF{
	struct DynRange(T){
		DynRange!T delegate() popFrontImpl;
		void popFront(){
			auto u = popFrontImpl();
		}
	}
	pragma(msg, DynRange!int);
}


struct TestInheritIsExp{
	class A{ static assert(is(E: A)); }
	class D(): A{}
	class E: D!(){}
	pragma(msg, is(E:A));	
}


void testMemberFunctionTemplate(){
	struct S{
		int x;
		bool g()(){
			return !!x;
		}
		bool f(){return g!()();}
	}
	static assert({S s; s.x=1; return s.f();}());
}

enum x = (cast(ulong)0x10009 >> 1) == 0x8004;

void testOverrideSkip(){
	class P{ int foo(){ return 2; }}
	class C6: P{}
	class C7: C6{ override int foo(){ return 3; }}
}

static assert(!is(typeof({
auto recc2(R)(R foo)=>recc2!R(foo);
pragma(msg, recc2!int);
})));


static assert(!is(typeof({
auto recc(R)(R foo)=>recc(foo);
pragma(msg, recc!int);
})));

struct TupleExpand{
	template Cont(R,A){ alias R delegate(R delegate(A)) Cont; }
	
	auto callCC(T...)(T args){
		Cont!(int,int) delegate(Cont!(int,int) delegate(int),int) f;
		return (int delegate(int) k)=>f(a=>_=>k(a), args)(k);
	}
	
	auto testcallCC(){
		assert(callCC(1)(x=>x)==1);
	}
}


static assert(!is(typeof({
int testStructMemberAliasParam(){
	int x;
	struct S{
		void bar(int x){ foo((a)=>a=x); }
		void foo(alias a)(){ a(x); }
	}
}})));


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
	static assert(toStringNow!(0x100000000) == "4294967296");
    static assert(toStringNow!(-138L) == "-138");
}

static assert(!is(typeof({
	template U(long v){
		static if (v < 0){}
		else enum U = U!(cast(ulong) v);
	}
	void testU(){ U!2; }
})));

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