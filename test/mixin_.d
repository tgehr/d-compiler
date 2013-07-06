mixin template Bar(int x){
	enum Bar = "Don't do eponymous lookup!";
	enum foo = y+2;
	pragma(msg, foo);
}

void fun(){
	enum y=3;
	mixin Bar!2;
	static assert(foo==5); // TODO
}


mixin template Foo(int x){
	enum bar = x;
}
pragma(msg, Foo!2.bar); // error

mixin Foo!2;
static assert(bar == 2); // TODO

mixin bar; // error

// +/
// +/
// +/