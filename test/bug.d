/+
int ret(alias x)(){
	return x;
}

struct S{
	int x=0;
	int m(){ return x; }
	void foo(){
		int k(){ return m; }
		ret!x();
		ret!m(); // // TODO: does not work in DMD
		ret!k();
	}
}

void main(){
	
}
+/

/+
auto seq(T...)(T args){
    return args;
}
pragma(msg, seq(1,2,3));
+/
/+
void foo(){
	int j;
	for({j=2; int d = 3; } j+d<7; {j++; d++;}) {
	}
}
+/
/+struct A{
	int i;
	int b;
}
struct S{
	union U{
		A first;
		A second;
	}
	U u;
	this(A val){
		u.second = val;
		assign(val);
	}
	int assign(A val){
		u.first.i = val.i+1;
		return u.first.i;
	}
}

void main(){
    enum a = S({A aa; aa.i=1; return aa;}());
    static assert(a.u.first.i == 2);
}+/



// *****
/+
int main() {
	int sum=0;

	int return1_add9tosum() {
		sum += 9;
		return 1;
	}
    sum += return1_add9tosum();
	return sum;
}

pragma(msg, main());

void main(){
	int x=0;
	assert(3 == ++x + ++x);
}
//pragma(msg, main());+/

/+

template A(alias Arg) {
    enum A = Arg;
    enum Unrelated = ({return A();})(); // TODO
};

void main() {
    enum FnPtr = &asdf;
    enum _ = A!FnPtr;
};

void asdf() {};
+/

// ****

/+
immutable x=[1,2,3];

/+void foo(inout(int)*,inout(int)[]){}

pragma(msg, foo(x.ptr,x));+/



struct S{
	this(inout(int)*)inout{ }
}
pragma(msg, S(x.ptr));
class C{
	this(inout(int)*)inout{ }
}
//pragma(msg, new C(x.ptr));
+/

/+
int testStructMemberAliasParam3(){
	int x;
	struct S{
		int y;
		int bar(){
			return k!(()=>x);
		}
		immutable int k(alias a)=2;
	}
	S s;
	s.k!2=3;
	return s.bar();
}
static assert(testStructMemberAliasParam3()==35);
pragma(msg, "testStructMemberAliasParam3: ", testStructMemberAliasParam3());
+/

//mixin(['i','n','t',' ','f','o','o','a','s','d','f',';']);
//mixin(cast(dchar[])['2','a']~";");
//pragma(msg, cast(immutable(dchar)[])[cast(dchar)'2',cast(dchar)'a']);

/+int f(X...)(){ return X[0]; }
struct T {
	int x=2;
	static int bar(){
		return f!x(); // error
	}
}
+/
/+
auto eval(alias a,T...)(T args){
	return a(args); // TODO: reverse eponymous template lookup for alias parameters
}

T foo(T)(T[] x){
	return eval!foo(x[0]);
}
int foo(int x){
	return x;
}

pragma(msg, foo([1]));
+/


/+
struct S{
	int* a;
	T* b;
	int* c;
}
struct T{
	int x;
	int y;
}

S x(){
	S s;
	s.b=new T();
	s.b.x=3;
	s.a=&s.b.x;
	s.c=&s.b.y;
	s.b.y=2;
	return s;
}
immutable k=x();
pragma(msg, k.a," ",k.c," ",k.b," ",*k.a," ",*k.c); // TODO: move somewhere else, this behaves as expected
+/

/+
struct StrangeInheritance1{
	class A(T) if(is(T: A!T)){} // TODO
	class B: A!B{}
}

struct StrangeInheritanc2{
	class X{}
	class A(T):X if(is(T: X)){} // TODO
	class B: A!B{}
}

struct StrangeInheritance3{
	class X{}
	class A(T):X if(is(T: B!T)){}
	class B(T): A!T if(is(T:X)){} // TODO
	class C: B!C{}
}
+/

/+
class S{
	int s;
}
void foo(T)(T arg){
	pragma(msg,T);
}

void main(){
	S s;
	const(S) t=s; // ok
	S x=t; // error
	foo!()(t); // TODO: ok
}
+/
/+
struct TemplateFunctionLiteralAlias{
	alias id=(a)=>a;
	static assert(id(1)==1 && id(2.5)==2.5);
}

auto foo(){ return foo(0); }
int foo(int x){ return x; }

bool bar(double x){ return true; }
static if(bar(0)){ bool bar(int x){ return false; } }
+/

/+struct DefaultArgsIFTI{
static:
	void previously(T=int)(T t=0){}
	void now(T)(T t=0){}
	alias Seq(T...)=T;
	auto now2(T...)(T args=Seq!(1,2,3)){ return args; }
	auto now3(T)(T[] arg=[1,2,3]){ return arg; }
	auto now4(T)(T a=['h','i'],T b="123"){ }
	auto now5(S,T...)(S delegate(T) dg=(int a,double b)=>"hi"){}
	auto now6(T,R,S,U)(T x,S delegate(R) dg=(T a)=>a,U delegate(S)=x=>x){}
	void main() {
		previously();
		// previously("hi"); // TODO: does it really make sense to error out here?
		now();
		//now2();
		//now3();
		//now4();
		//now4(['h','i']);
		//now5();
		//now6("hi");
	}
}+/

/+struct IFTiOverload{
static:
	template foo(){
		auto foo(int x){}
		auto foo(string y){}
	}
	pragma(msg, foo("hi")); // TODO
}+/

/+
//import std.container;
class RedBlackTree(T,alias less){
	bool foo(int a,int b){
		return less(a,b);
	}
}
class C{
	int[] prio;
	this(int[] prio){
		this.prio=prio;
		tree=new typeof(tree)();
		assert(tree.foo(1,0));
	}
	RedBlackTree!(int, (a,b)=>prio[a]<prio[b]) tree;
} 
void main(){
	auto c=new C([3,1,2]);
	//assert(c.tree.foo(0,2));
}
pragma(msg,main());
+/
/+
struct SPtr(T){
    ptrdiff_t _offset;
    void opAssign(T* orig) { _offset = cast(void*)orig - cast(void*)&this;}
    inout(T)* _get()inout{ return cast(T*)((cast(void*)&this) + _offset);}
    alias _get this;
}

auto sptr(alias init,alias var)(){ return typeof(var)(init.offsetof-var.offsetof); }

struct S{
	int x;
	SPtr!int y=sptr!(x,y);
}
+/


/+ TODO: create a test out of this:
import std.stdio;
struct Test{
    mixin(binOpProxy("+~+-~*--+++----*"));
    void opBinary(string op : "+~+-~*--+++----*", T)(T rhs){
        writeln("+~+-~*--+++----*");
    }
}

void main(){
    Test a,b;
    a +~+-~*--+++----* b;
}

import std.string, std.algorithm, std.range;
int operatorSuffixLength(string s){
	int count(dchar c){ return 2-s.retro.countUntil!(d=>c!=d)%2; }
	if(s.endsWith("++")) return count('+');
	if(s.endsWith("--")) return count('-');
	return 1;
}
struct TheProxy(T,string s){
    T unwrap;
    this(T unwrap){ this.unwrap=unwrap; }
    static if(s.length){
        alias NextType=TheProxy!(T,s[0..$-operatorSuffixLength(s)]);
        alias FullType=NextType.FullType;
		mixin(`
        auto opUnary(string op : "`~s[$-operatorSuffixLength(s)..$]~`")(){
            return NextType(unwrap);
        }`);
    }else{
        alias FullType=typeof(this);
    }
}

string binOpProxy(string s)in{
	assert(s.length>=1+operatorSuffixLength(s));
	assert(!s.startsWith("++"));
	assert(!s.startsWith("--"));
	foreach(dchar c;s)
		assert("+-*~".canFind(c));
}body{
	int len=operatorSuffixLength(s);
    return `
        auto opUnary(string op:"`~s[$-len..$]~`")(){
            return TheProxy!(typeof(this),"`~s[1..$-len]~`")(this);
        }
        auto opBinary(string op:"`~s[0]~`")(TheProxy!(typeof(this),"`~s[1..$-1]~`").FullType t){
            return opBinary!"`~s~`"(t.unwrap);
        }
    `;
}
+/


/+

struct S {
	int delegate(dchar) dg = cast(void delegate(dchar))(dchar) { return 2; };
	// test.d(2): Error: delegate test.S.__lambda2 cannot be class members
}
pragma(msg, S().dg('a'));

import std.stdio;
template log(T...){
	void log(T args);
	int x;
	static if(true) void logf(T args,int x=2){ }
	/+static if(true)+/ 
}

void main(){ log(1,2,3); }
+/


//int x(){ if(foo){ } // TODO: show unmatched paren

/+class Infty{
	int foo(){ return foo(); } // TODO: ok
	pragma(msg, foo()); // TODO; error
}+/


/+class C{
	final int foo(){ return 1; }
	int x;
	void bar(){
		enum e=this.foo();
		//enum e=x; // TODO: improve error message
	}
}+/

/+static void foo(){
	static struct S{ S delegate() dg; }
	S bar(){
		S s;
		s.dg=&bar;
		return s;
	}
	pragma(msg, bar()); // error
	struct T{ int x; }
	T baz(){
		T t;
		t.x=2;
		return T;
	}
	pragma(msg, baz()); // error
	static struct U{ int x; }
	U qux(){
		U u;
		u.x=2;
		return u;
	}
	pragma(msg, qux().x); // ok
}

struct TemplateParameterAccessCheck{
	enum ID1(alias e)=e;
	enum ID2(int delegate() e)=e;
	enum ID3(alias e)=&e; // error
	
	static void foo(){
		static int sbar()=>2;
		static int sbaz()=>ID1!(&sbar)();
		static assert(sbaz()==2);
		int kbar()=>3;
		int kbaz()=>ID2!(&kbar)();
		static assert(kbaz()==3);
		enum e=&kbar, f=&sbar;
		static assert(e()==3 && f()==2);
		int x;
		int kobar()=>x;
		pragma(msg, kobar()); // error
		enum g=&kobar; // error
		int kobaz()=>ID3!kobar;
	}
}+/

/++struct S{
	immutable f = function()pure immutable{}; // TODO: bail out for the correct reason
}+/

/+
struct ComparisonTests{
	alias Seq(T...)=T;
	static:
	auto seq(T...)(T args)=>args;
	enum a=1, b=2, c=3;
	alias Foo(bool b)=Seq!(b?Seq!(a,b,c):seq(a,b,c));
	static assert(Foo!false==Seq!(1,false,3));
	static assert(Foo!true==Seq!(1,true,3));
	static assert(!is(typeof({static assert(Foo!true!=Seq!(1,true,3));})));

	bool cmptest(int a,int b){
		return Seq!(a,b)!=seq(1,2);
	}
	pragma(msg, cmptest(1,2));
}+/

// ref void foo(){ return; } // // TODO: should this fail?

/+alias Seq(T...)=T;
enum ESeq{ foo=Seq!(1,2), bar=Seq!(2,3) } // TODO? (TODO: bug report against DMD?)
pragma(msg, ESeq.foo);+/

//pragma(msg, typeof(CDX.foo));

/+
class C{
	auto _InsertAllBut(int v) {
		int* node = null;
		//enum mutable = is(typeof({node.value;}));
		enum foo = {return ()=>node;}; (DMD stores runtime context pointer in enum constant magically.)
		return 2;//foo()();
	}
}

pragma(msg, (()=>(new C())._InsertAllBut(2))());
+/


/+enum Foo{
	xxx
}

immutable arr = [Foo.xxx]; // TODO+/

/+
immutable int x=2;
immutable int* p = &x + 1; // TODO: error

int y=2;
int* q=&y; // TODO: ok.
+/

/+struct ByteCodeBuilder{
	class Node{}
	private ulong[] byteCode;
	private Node[] errtbl;
	auto getByteCode(){
		enum Instruction{errtbl}
		alias immutable(ulong)[] ByteCode;
		return cast(ByteCode)((byteCode~=Instruction.errtbl)~=cast(ByteCode)errtbl); // BUG (also: bad error message)
	}
}+/

/+@property int bar()=>2;

struct PoorErrorMessage{
static foo(){ return bar(); // TODO: fix error message
}
pragma(msg, foo());
}+/


/+struct ReturnTypeLambdaParameterIfti{
	void foo(T)(T a, T b) { }
	void main() {
		foo((int a)=>a, b=>1.0); // foo!(double function(int))
	}
}+/


/+
// TODO: make interpretation of partially analyzed functions work
int cdep(){ enum x=cdep2(); return x;}
int cdep2(){ return cdep(); }+/

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


/+template asdf(){ }
template Uninstantiable() if(asdf(2)){}
template Instantiable() if(Uninstantiable!()){}
pragma(msg, typeof(Instantiable!())); // show error!+/

/+template asdf(){ enum asdf=(int x)=>true; }
template Uninstantiable() if(asdf(2)){}
template Instantiable() if(Uninstantiable!()){}
pragma(msg, typeof(Instantiable!()));+/

/+
template Seq(T...){ alias T Seq; }
int aMatchError(R)(Seq!R delegate(int) dg){ return dg(2); }
pragma(msg, aMatchError(a=>a)); // TODO: remove reference to matcher type in error message
+/


/+improve error messages!+/

/+pragma(msg, ElementType!(int));
template ElementType(T=S,S=T){ alias typeof({T t; return t[0];}()) ElementType; }
+/

/+
auto testtemplatefunclit(fun...)(){
	static if(!fun.length) return "";
	else{
		alias fun[0] tmpl;
		static if(is(typeof(tmpl!(double,string)))) alias tmpl!(double,string) ff;
		else alias tmpl ff;
		// pragma(msg, typeof(ff));
		return ff(0,4.5,"fun ")()~testtemplatefunclit!(fun[1..$])();
	}
}
struct FunContainer{
	static fun(int x,double y,string z)=>()=>z~"hi1";
}
pragma(msg, "testtemplatefunclit 1: ",testtemplatefunclit!(FunContainer.fun)());
+/

// +/
// +/
// +/

alias immutable(char)[] string;
