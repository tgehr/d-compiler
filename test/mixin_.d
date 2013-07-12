
mixin template Attribs(){ int foo(int x){ return x+y; } }

struct AttribS{
	int y;
	pure static mixin Attribs;
	static assert(is(typeof(&foo)==int function(int)pure));
	struct X{
		mixin Attribs;
		static assert(is(typeof(&foo)==int delegate(int)));
	}
}

struct S{
	mixin Confl;
	mixin NConfl;

	pragma(msg, "NConfl1: ",conflFoo(1));
	pragma(msg, "NConfl2: ",conflFoo([1,2,3]));
}

mixin template Confl(){
	static conflFoo(int x){ return x; }
}

mixin template NConfl(){
	static conflFoo(int[] x){ return x; }
}
mixin Confl;
mixin Confl;
	
pragma(msg, conflFoo(2)); // error

struct AConfl{
	mixin Confl;
	mixin Confl;
	mixin NConfl;
	pragma(msg, conflFoo(2)); // error
}

mixin template Ambig(immutable(char)[] x){
	mixin("enum "~x~"=1;"); // TODO: error
}

static if(!is(typeof(aax))) mixin Ambig!"bbx";
static if(!is(typeof(bbx))) mixin Ambig!"aax";

mixin template FooZ(){
	int foo(){ return 1; }
}

mixin template OFooZ(){
	override int foo(){ return 2; }
}

class C{
	mixin FooZ;
}

class D: C{
	mixin OFooZ;
}

static assert({C c=new D(); return c;}().foo()==2);

//pragma(msg, new C);

pragma(msg, C.foof); // error

mixin FooZ;

mixin template Bar(int x){
	enum Bar = "Don't do eponymous lookup!";
	enum foo = y+2;
	pragma(msg, foo);
}

void fun(){
	enum y=3;
	mixin Bar!2;
	static assert(foo==5);
}

struct Fun{
	enum y=3;
	mixin Bar!2;
	pragma(msg, Bar);
	static assert(foo==5);
}


mixin template Foo(int x){
	enum bar = x;
}
pragma(msg, Foo!2.bar); // error

mixin Foo!2;
static assert(bar == 2);

mixin bar; // error

// +/
// +/
// +/