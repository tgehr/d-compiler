
template StaticFilter(alias F, a...){
	static if(!a.length) alias a StaticFilter;
	else static if(F!(a[0])) alias TypeTuple!(a[0], Rest) StaticFilter;
	else alias Rest StaticFilter;
	static if(a.length) alias StaticFilter!(F,a[1..a.length]) Rest;
}

template Pred(int x){ enum bool Pred = x&1; }
pragma(msg, StaticFilter!(Pred, 1, 2, 3, 4, 5, 6, 7));

/+
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

template MAlias(A,B){ alias A delegate(B) MAlias2; }

auto malias(A,B)(MAlias!(A,B).MAlias2 dg, B arg){ return dg(arg); }
pragma(msg, malias!(int,int)((int x)=>x,3));

int rec(T)(int x){
	if(!x) return 0;
	return 1+rec!T(x-1);
}
pragma(msg, rec!int(2));

int[] rec(int[] arg){
	if(!arg.length) return arg;
	return rec(arg[1..arg.length]);
}
enum unsorted = [1,2];

pragma(msg, rec(unsorted));
pragma(msg, rec(unsorted));



int[][] funny2(int[] a, int n){
	int*[] ptrs;
	int[][] r;
	for(int i=0;i<n;i++) a[i]--, r~=[0,0,0];
	for(int i=0;i<3*n;i+=3) ptrs~=[&r[i/3][0],&r[i/3][1],&r[i/3][2]];
	for(int i=0;i<3*n;i+=3) *ptrs[i+a[i/3]]=a[i/3]+1;

	return r;
}
pragma(msg, "funny2: ",funny2([1,2,3,2,3,1,3,1,2,3,2,1],12));

auto id(A)(A arg) => arg;

pragma(msg, id(1));


static assert(!is(typeof({
	struct S{
		immutable int x=TT!().SS!().TT;
		template TT(){ template SS(){ alias x TT; } }
	}
})));

alias immutable(char)[] string;

auto testtemplatefunclit(alias fun)(){ return fun!int(2); }
pragma(msg, "testtemplatefunclit 3: ",testtemplatefunclit!(x=>2)());

/+
int k;

typeof(z) x;
typeof(x) y;
typeof(y) z;
+/

// +/