struct FOFOFO{
	enum x = undef; // error
	mixin(`float a11=`~foo1~";"); // error
}

enum x = "enum xx = q{int y = 0;};";

struct SS{
	mixin(xx);
	mixin(x); // TODO
}

struct S{
	enum z = y;
	enum x = "enum xx = q{immutable y = 123;};";
	mixin(xx);
	mixin(x);
	static assert(z == 123);
}



struct MixinEvalOrder{
	enum x = "string xx = q{int y = 0;};";
	
	struct S{
		mixin(x);  // TODO: we want this to work (?)
		mixin(xx);
	}
}

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

mixin(q{pragma(msg, is(typeof({immutable(char)[] x=['2'];}())));});
enum immutable(dchar)[] fooz = "hello";
//pragma(msg, "fooz");
pragma(msg, typeof(fooz));

//mixin(`hallo velo();`);

void foo(){
	//mixin(x"abcd"); // TODO: fix utf exception
	mixin("abcd"); // error
	pragma(msg, is(typeof(bar)));
}

mixin(q{ // error
	void main(){
		mixin("pragma(msg,mixin(q{`hooray!`}));pragma(msg,mixin(q{moo}));");
		mixin("2;");
		mixin("22"~"=22;");
		mixin(22);
		mixin(cast(dchar[])['2','a']~";");
		dchar[] x;
		immutable(dchar)[] y=x;
		(){immutable(char)[] x = ['2'];}();

		int oops;
		mixin(`int oops;`);

	}
});

// +/

alias immutable(char)[] string;