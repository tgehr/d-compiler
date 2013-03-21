struct SS{
	template T(int x){ }
	template T(alias a){ }
	template S(float x){ }
    float prop()@property{ return 0; }
	static assert(is(typeof(T!prop)));
	static assert(is(typeof(S!prop))); // TODO
}

pragma(msg, "ternary1: ", (true?get2:get2)());
pragma(msg, "ternary2: ", typeof(&(true?get2:get2)));
pragma(msg, "ternary3: ", (&(true?get2:get2))());

pragma(msg, "comma1: ", (1,get2)());
pragma(msg, "comma2: ", typeof(&(1,get2)));
pragma(msg, "comma3: ", (&(1,get2))());


@property int prop(){ return 2; }
template Bar(alias a){ enum Bar = a; }
template Bar(int x){ static assert(0); }
pragma(msg, "Bar: ", Bar!prop);

@property int ufcsProperty(int x){ return x+1;}
@property int ufcsProperty(int x, int y){ return x+y; }

pragma(msg, 1.ufcsProperty);
static assert(!is(typeof(1.ufcsProperty())));
pragma(msg, 1.ufcsProperty = 2); // TODO
static assert(!is(typeof(1.ufcsProperty(2))));
pragma(msg, 1.ufcsProperty(2)); // error // TODO: better error message

template Foo(alias a){ enum Foo = a(); }
template Foo(int a){ static assert(0); }

int get2(){ return 2; }

static assert(Foo!get2==2);
pragma(msg, Foo!get2);

static assert(!is(typeof(Foo!(get2()))));

alias get2 aget2;
static assert(aget2()==2);
pragma(msg, aget2());



struct Ref{
	int x;
	@property ref int foo(){ return x;}
	ref int bar(){ return x; }

	int y;
	@property int baz(){ return y; }
	@property void baz(int x){ y=x; }
}
auto rrr(){
	Ref r;
	r.foo = 2;
	auto p = &r.foo;
	auto u = &r.bar;
	++++*p;
	r.baz=2; // TODO
	return r.x+u()+r.y;
}
static assert(rrr()==8);
pragma(msg, "rrr: ", rrr);



int delegate() tdel1()(){ return ()=>2; }
@property int delegate() tdel2(T=int)(){ return ()=>2; }

static assert(tdel1()()==2);
static assert(tdel2()==2);
pragma(msg, "tdel1: ", tdel1()());
pragma(msg, "tdel2: ", tdel2());

@property int tprop(alias a)(){return a(2);}
@property T tprop(T=int)(){ return 2;}
static assert(tprop==2);
pragma(msg, tprop);
static assert(tprop!(a=>a)==2);
pragma(msg, tprop!(a=>a));
static assert(is(typeof(tprop!(a=>a))==int));
pragma(msg, tprop!(a=>a)()); // TODO: diagnostics improvements
static assert(!is(typeof(tprop())));

/+template A(){ enum b = 3; }
template A(T){ enum c = 3; }

pragma(msg, A!());+/

struct TT{
	int foo(){ return 3; }
	@property int bar(){ return 2; }
}
int mm(){
	TT s;
	static assert(!is(typeof(s.bar())));
	static assert(is(typeof(s.foo)==int));
	static assert(is(typeof(s.bar)==int));
	return s.foo()+s.foo+s.bar;
}
pragma(msg, mm());


int foo(int x){ return x+1; }
static assert(1.foo==2);
pragma(msg, 1.foo);
static assert(1.foo()==2);
pragma(msg, 1.foo());

int foo(int x, int y){ return x+y; }
static assert(1.foo(2)==3);
pragma(msg, 1.foo(2));
static assert(1.foo(3)==4);
pragma(msg, 1.foo(3));

//pragma(msg, &1.foo);
static assert(!is(typeof(&1.foo)));

auto map(alias a, T)(T[] arr){
	typeof(a(arr[0]))[] r;
	for(int i=0;i<arr.length;i++)
		r~=a(arr[i]);
	return r;
}

auto map(T,S)(T[] arr, S delegate(T) dg){ return arr.map!dg; }
auto map(T,S)(S delegate(T) dg, T[] arr){ return arr.map(dg); }
//auto map(T,S)(S delegate(T) dg){ return (T[] arr)=>arr.map(dg); }

//template map(alias a){  } // TODO: investigate

struct S{ this(int[] x){ } }

pragma(msg, [1,2,3].S);
pragma(msg, map!(a=>2*a)([1,2,3]));
pragma(msg, [1,2,3].map!(a=>2*a));
pragma(msg, map([1,2,3],a=>2*a));
pragma(msg, [1,2,3].map(a=>2*a));
pragma(msg, map(a=>2*a,[1,2,3]));
pragma(msg, (a=>2*a).map([1,2,3]));

int bar(){ return 2; }
pragma(msg, typeof(bar));
enum bb = bar;
pragma(msg, typeof(bb));

// +/ // +/