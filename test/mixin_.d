mixin template Bar(int x){
	int foo = y+2;
	pragma(msg, foo);
}

void fun(){
	int y;
	mixin Bar!2;
}

/+
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