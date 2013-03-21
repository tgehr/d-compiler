
void validconversions(){
	void delegate()const[] x;
	const(void delegate())[] y = x;
}


/+

struct S{
	int a;
	int foo(){return 2;}
	pragma(msg, (()=>foo())());
	mixin({
		auto s="enum a0=0;";
		for(int i=1;i<100;i++)
			s~="enum int a"~toString(i)~"=a"~toString(i-1)~"+"~toString(i*2-1)~";";
		return s;
	}());
	pragma(msg, a5);
}

void testdeduction(){
	immutable int x = 0;
	static assert(is(typeof((){enum e=x;return e;}):immutable(int)function()));
}

void main(){
	int sjisjis;
	static pure void main()@safe nothrow pure{sjisjis=2;}
	auto x = &main;
	static assert(is(typeof(&main)==void function()pure nothrow @safe));
	static assert(!is(typeof(&x): void function()*));
	auto y = &x;
	static assert(!is(typeof(&y): void function()**));

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

auto toString(int i){
	immutable(char)[] s;
	do s=(i%10+'0')~s, i/=10; while(i);
	return s;
}
+/