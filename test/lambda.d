
void main(){
	int sjisjis;
	static pure void main()@safe nothrow pure{sjisjis=2;}
	auto x = &main;
	static assert(is(typeof(&main)==void function()pure nothrow @safe));
	static assert(is(typeof(&x): void function()*));

	//auto _ = main;
	auto a = (){(){}();};
	pragma(msg, typeof(a));
	//auto a = (){};
	//pragma(msg, typeof(a));
	//void function() a;
	//a=&main;
	auto b = (){(){a();}();};
	auto c = delegate(){(){}();};
	static assert(is(typeof(a): void function()));
	static assert(is(typeof(b): void delegate()));
	static assert(!is(typeof(c): void function()));
	static assert(is(void delegate()@safe: void delegate()));
	static assert(is(void delegate()@safe: void delegate()@trusted));
	static assert(is(void delegate()@trusted: void delegate()@safe));
	static assert(is(void function() pure nothrow @safe : void function()));
	static assert(!is(void function() : void function()pure nothrow @safe));
}

