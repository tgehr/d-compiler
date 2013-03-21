
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

//struct S{ this(int[] x){ } }

pragma(msg, [1,2,3].S);
pragma(msg, map!(a=>2*a)([1,2,3]));
pragma(msg, [1,2,3].map!(a=>2*a));
pragma(msg, map([1,2,3],a=>2*a));
pragma(msg, [1,2,3].map(a=>2*a));
pragma(msg, map(a=>2*a,[1,2,3]));
pragma(msg, (a=>2*a).map([1,2,3]));

int bar(){ return 2; }
pragma(msg, typeof(bar));
enum bb = bar; // TODO
pragma(msg, typeof(bb));

// +/ // +/