

pragma(msg, "\u0041\u030A");

//static if(!is(typeof(x))) enum y = 2;
//static if(!is(typeof(y))) enum x = 2;


immutable float a = 1.0f;

auto xxx(){
	return "static int a;";
}

struct S{
	S s;
	auto x = bar();
	static if({return 1;}()){};
	static if(foo()) mixin(xxx()); // error
	static bool foo(){return 1||bar();}
	static bool bar(){return !!a;} /+ error, picks up static declaration from mixin +/
}

/+template foo(T){
	T foo(T arg){
		return arg;
	}
}

pragma(msg, foo!int.foo(1));+/
