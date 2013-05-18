
struct TemplatedTemplateStructConstructor(T){
	this(T)(T arg){}
	static create(){
		auto flt = TemplatedTemplateStructConstructor!float(2);
		return TemplatedTemplateStructConstructor(2);
	}
}
pragma(msg, TemplatedTemplateStructConstructor!int);

struct TemplatedConstructor{
	this(T)(T arg){}
	static create(){
		return TemplatedConstructor(2);
	}
}
void foo(int){}
void goo(){}
alias goo foo; // TODO: overload


//int ass(){return 0;}
//static if(!is(typeof(ass(1)))) int ass(int){return 0;}


enum E=2;
struct RR{
	//static if(is(typeof(S.S.S))) template B(){enum B = 1;}
	enum S = E;
}

//alias RR.S a;
enum FG = RR.S;



int foo(){return foo();}

class Inaccessible{
	immutable int[] x=[S.y];
	immutable int z=2;

	static if(22==22)struct S{
		enum y=22;
		//int x;
		auto foo(){
			pragma(msg, x);
			return &z; // error
		}
	}
}
//import std.stdio;

void main(){
	immutable int y=2;
	struct S{
		immutable(int) xx = y;
	}
	static assert(S.xx==2);
	Inaccessible.S s;
	pragma(msg, Inaccessible.x);
	//&Inaccessible.z;
	//writeln(s.foo);
}

/+struct S{
	int x;
	union{
		int y,z;
	}
}+/

/+void main(){
	int x;
	static int foo(){
		return x;
	}
}+/



alias int AT;

struct S2{
	AT* foo(AT arg){return &arg;}
	AT[] foo(AT arg){return [arg];}
}

struct IT{
	int i,t;
}

int testStrIntp(){
	IT it;
	it.i=2;
	it.t=3;
	return it.i+it.t;
}

pragma(msg, "testStrIntp: ",testStrIntp());


struct Funny2{
	int x;
	enum foofo=10;
	static foo(){Funny2 f; f.x=2; return x;} // error
	static if(foo())
		int y;
}



void main(){
	F f=f;
	S s;
	auto a = s.x;
	auto b = s.foo;
	auto c = s.bar;
	pragma(msg, typeof(a));
	pragma(msg, typeof(b));
	pragma(msg, typeof(c));
}
struct F{
	int g;
}
struct G{static F g;}

F f;
struct S{
	int x = 2;
	int y;
	G f;
	alias f.g foo; // TODO
	alias x bar;
}


//pragma(msg, S.x);

//int a;



static assert(!is(typeof({
	const int a=2;
	struct Funny{
		// reference to a is ambiguous
		static if(is(typeof({enum x=foo();}))){
			float a;
		}
		static int foo(){return a;}
	}
})));


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

struct Bad1{
	Bad2 bad;
}
struct Bad2{
	Bad1 bad;
}

struct SS{
	typeof(a) x;
	void foo(){
		typeof(a) x;
	}

	struct SSS{
		typeof(a) x;
		//typeof(a) z;
		struct SSSS{
			typeof(a) x;
		}
	}
}




mixin("mixin(`dod`);"); // error

static assert(!is(typeof({
int testStructMemberAliasParam(){
	int x;
	struct S{
		void bar(int x){ foo((a)=>a=x); }
		void foo(alias a)(){ a(x); }
	}
}})));


void main(){
/+	mixin(q{	for(c=2;){return 2;}
	foo=2
		foo=3});+/
}
// +/

// ] <-- copyright (C) 2012 Josef Ziegler
