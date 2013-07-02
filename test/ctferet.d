
struct FunctionLiterals{
	enum foo = (()=>()=>2)();
	static assert(foo()==2);
	
	static immutable fooi = (()=>()=>3)();
	static assert(fooi()==3);
	
	enum bar = ()=>4;
	static assert(bar()==4);
	
	static immutable bari = ()=>5;
	static assert(bari()==5);
}

struct PointersDirect{
	static immutable x = "this is x";
	enum foo = &x;
	static immutable fooi = &x;
	enum bar = &fooi;
	immutable bari = &fooi;

	static assert(foo is fooi);
	static assert(bar is bari);

	static assert(*bari is fooi);
	static assert(*bar is foo);
	static assert(*fooi == x);
	static assert(&x is fooi);

	static assert(**bari == x);
	static assert(**bar == x);

	static assert(*foo is *fooi);
	static assert(**bar is *foo);
	
	static assert(*foo is x); // TODO: aliasing for strings
}

struct LocalGlobalPointer{
	immutable fooi=2;
	enum ptr=&fooi; // TODO: should this be an error?
}

struct StringAliasing{
	static immutable y = "123";
	static assert((()=>y.ptr == y.ptr)()); // TODO!
	static assert({immutable(char)[] x = y; return x~=x;}()=="123123");
}

/+struct VoidPointer{
	static void*[2] a = { // TODO!
		int x;
		double y;
		void* a=&x;
		void* b=&y;
		return [a,b];
	}();
}+/

struct ClassFieldAliasing{
	class C{
		int[2] x=[1,2];
		int y = 3;
	}
	
	static immutable c=new immutable(C)();
	static immutable ptr3 = (()=>&c.y)();
	static immutable ptr4 = (()=>&c.y)();
	static assert((()=>ptr3 is ptr4)());
	static assert((()=>ptr3 is &c.y)()); // TODO
	static immutable ptr1 = (()=>c.x.ptr+2)();
	static immutable ptr2 = (()=>c.x.ptr+2)();
	static assert((()=>ptr1 is ptr2)());
	static assert((()=>ptr1 is c.x.ptr+2)()); // TODO
	static assert((()=>*(ptr1-1)==2&&*(ptr1-2)==1)());
}

struct StructFieldAliasing{
	struct S{
		int[2] x=[1,2];
		int y = 3;
	}
	
	static immutable s=S();
	static immutable ptr1 = (()=>s.x.ptr+2)();
	static immutable ptr2 = (()=>s.x.ptr+2)();
	static immutable ptr3 = (()=>&s.y)();
	static immutable ptr4 = (()=>&s.y)();
	static assert((()=>ptr1 is ptr2)());
	static assert((()=>ptr1 is s.x.ptr+2)()); // TODO
	static assert((()=>ptr3 is ptr4)());
	static assert((()=>ptr3 is &s.y)()); // TODO
	static assert((()=>*(ptr1-1)==2&&*(ptr1-2)==1)());
}
/+// TODO add test
struct StructEmptyStaticArrayFieldAliasing{
	struct S{ int[0] x=[]; }
	
	static immutable s=new immutable(S)();
	static immutable ptr3 = (()=>&s.x)();
	static assert((()=>ptr3 is &s.x)()); // TODO
	//static assert((()=>&s.y is ptr3)()); // TODO
}+/

immutable dg = (()=>delegate()immutable=>1)();
pragma(msg, (()=>dg())()); // TODO
/+immutable fn = (()=>()immutable=>1)();
pragma(msg, (()=>fn())()); // TODO+/

class Subclass{
	static class Parent{int x=1;int foo()const{ return x; }}
	static class Child : Parent{int y=2;override int foo()const{ return x+y; }}

	static immutable pp = delegate immutable Parent(){
		return new immutable(Child)();
	}();
	
	pragma(msg, typeof(pp)," ",pp," ",pp.foo());
	static assert(pp.foo()==3);
}

struct StaticVariableAliasing{
	static immutable x = 2;
	enum ptr = (()=>&x)();
	
	pragma(msg, (()=>*ptr)());
	static assert((()=>ptr is &x)());
}

class YY{
	int x=2;
}

auto fooo(){
	immutable YY x=new YY;
	auto xx=(&x.x)[0..2]; // error
	return xx[1];
}
pragma(msg, fooo);

struct EmptyStructPointer{
	struct XX{}
	
	static x = (()=>immutable(XX)())();
	static food(){
		auto x = &x;
		return x;
	}
	pragma(msg, food);
}

struct LocalVariableAliasing{
	struct TwoPointers{
		immutable(int)* a, b;
		this(immutable(int)* a,immutable(int)* b){ this.a=a; this.b=b; }
	}
	
	static foo(){
		immutable x=2;
		return TwoPointers(&x,&x);
	}
	static immutable fofo = foo();
	pragma(msg, (()=>fofo.a is fofo.b)());
}

class Pointers{
	immutable int[1] u=[333];
	int x = 123;
	static immutable s = (()=>new immutable(Pointers)())();
	static immutable t = (()=>s)();
	pragma(msg, s is t);
	static assert((()=>&s.x is &t.x)());

	static immutable a = (()=>&s.x)();
	static immutable b = (()=>&t.x)();
	static assert(a is b);


	static void*[2] vpa = {
		void* a;
		void* b;
		a=&b;
		b=&a;
		return [a,b];
	}();


	static assert((()=>s.u.ptr is t.u.ptr)());
	static immutable q = (()=>s.u.ptr)();
	static immutable p = (()=>t.u.ptr)();
	static assert(p is q);
}


struct ConstantArrayLiteralAliasing{
	static foo(){
		auto bar(){
			auto x=[1,2,3];
			return x;
		}
		return bar().ptr == bar().ptr;
	}
	static assert(!foo());
}

int[] allocarr(){
	auto x = new int[5]; // TODO!
	return x;
}
pragma(msg, allocarr());

struct TestVoidArrayVoidPtr{
	enum returnVoidArray = delegate void[](){return [2];}();

	static immutable int x = 2;
	static testvptr(){ void* ptr = cast(void*)&x; return ptr; }
	pragma(msg, "testvptr: ", testvptr());
	static assert(testvptr() is testvptr());

	static test1(){ auto x = [1,2,3]; return cast(immutable(int)[])cast(void[])x; } // error
	pragma(msg, test1()," ",typeof(test1()));

	static test2(){ auto x = [1,2,3]; return cast(const(int)[])cast(void[])x; } // ok
	pragma(msg, test2()," ",typeof(test2()));


	static testVarrayStruct(){
		auto x = [1,2,3,4,5];
		struct S{ void[] f; }
		S s;
		s.f = x;
		return s.f;
	}
	static assert(testVarrayStruct()==[1,2,3,4,5]);
}

struct ArrayLiteralConv{
	static int[2] a2=(()=>[1,2])();
	static immutable a=["zero"];
	enum short x = (()=>1)();
	static void[] v = ["one"];
}

struct Qualified{
	class Foo{
		int[] x=[1,2,3];
	}
	enum foo = (){return new immutable(Foo)();}();
	enum bar = (){return new Foo();}();
	enum baz = (){return new Foo();}();
	static assert((()=>bar.x.ptr==baz.x.ptr)());
	static assert((){return foo.x.ptr != bar.x.ptr;}()); // TODO
}

struct AliasingPreserving{
	static immutable x = [1,2,3];
	static auto foo(){ return x; }
	static immutable a = foo();
	static immutable b = foo();
	static assert(a is b);
	static assert(foo() is foo());
}

struct SliceAliasing{
	static immutable(int[][]) retslices(){
		immutable x = cast(immutable(int[]))[0,1,2,3,4];
		return [x[0..3],x[0..4]];
	}
	static immutable x=retslices();
	static assert(x[0].ptr==x[1].ptr);
	static assert((()=>x[0].ptr==x[1].ptr)()); // ok
}

struct Aliasing{
	struct S{
		int x;
	}
	
	struct ImmutableConversion{
		static S[][] foo(){
			auto x = [S(),S(),S(),S()];
			auto xx = [x[0..2],x[2..4]];
			assert(xxx(xx));
			return xx;
		}
		
		immutable xx = foo();
	}
	
	static immutable(S[][]) foo(){
		immutable x = [S(),S(),S(),S()];
		auto xx = [cast(immutable)x[0..2],cast(immutable)x[2..4]];
		assert(xxx(xx));
		return xx;
	}

	immutable xx = foo();

	static bool xxx(const S[][] xx){ return xx[0].ptr+2 == xx[1].ptr; }
	static assert(xxx(xx));
	
	pragma(msg, foo());
}

struct S{
	int a=2,b=3;
	S* next;
}

immutable s = {auto s=S();s.b=4;s.a++;s.next=new S();return s;}();
static assert(s.b==4);
pragma(msg, "s.b: ",s.b);


class D{
	int x;
	D d = {auto x = new D(); return x;}();
	int y = {return D.x;}(); // error
}

enum x = (()=>new D)();

pragma(msg, (()=>x.d.d.d.d)());

//pragma(msg, (()=>new D().d)());

/+
// TODO: this should error at the appropriate time
class C{
	int x=2;
	C c=null;
	void mutate(){ x = 1; }
	auto toString(){ return x.to!string; }
}
immutable xx = (()=>cast(C)null)();
enum y = (()=>new C)();

pragma(msg, {auto z=y;z.mutate; return z;}().toString());
pragma(msg, y.toString());
static assert(y.toString()=="2");
static assert({auto z=y;z.mutate;return z;}().toString()=="1");

enum z = {auto z=y;z.mutate;return z;}();
static assert(z.toString()=="1");+/

class List(T){
	T value;
	bool empty = true; // // TODO: implement comparison with null!
	List next = null;

	string toString(int x){
		if(!x) return "";
		List nix;
		return to!string(value)~(!empty?","~next.toString(x-1):"");
	}
}

auto buildList(){
	List!int r = null;
	for(int i=0;i<123;i++){
		auto l = new List!int();
		l.value = i;
		l.next = r;
		l.empty = i==0;
		r=l;
	}
	r.next.next.next.next=r;
	return r;
}

enum list = buildList();
pragma(msg, list.toString(40));


enum returnEmptyArray = ((int delegate(int))=>[])(x=>x);

pragma(msg, returnEmptyArray);
pragma(msg, typeof(returnEmptyArray));


// +/
// +/
// +/
// +/
// +/
// +/
// +/
// +/


alias immutable(char)[] string;

auto to(T,S)(S arg)if(is(S==int)&&is(T==string)){
	string r="";
	if(!arg) return "0";
	bool n = arg<0;
	if(n) arg=-arg;
	while(arg) r=('0'+arg%10)~r, arg/=10;
	if(n) r="-"~r;
	return r;
}
