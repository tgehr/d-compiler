static assert( (4.0 + 3.0i) * (5 + 7i) ==-1 + 43i  );

static assert(cast(short)cast(ulong)1e10 == -7168);

//pragma(msg, 2*2);
//static assert(0);
immutable(int)[] x = [1];
//immutable(int)[]* p = &x;
//immutable rp=p;
immutable a=2;
//int foo(){*p=[2];return 0;}

int fun(int x){return 1+x;}

int gun(int x){
	if(x) return x+1;
	return x<100?100:1000;
}



void main(){
	enum ass = (assert(1,"foo"),2);
	pragma(msg, ass);
	*cast(int*)&x[0] = 2;
	immutable int x=a;
	//pragma(msg, x);
	enum y = x; // TODO: FIX!

	int[] foo;
	//foo[1]=2;

	//enum zz = cast(dchar[])"hello";
	immutable xx = "hello";
	enum zz = cast(char[])xx;
	enum zzz = "abc";
	//pragma(msg, zz,zzz,zz>['a','b','c'],zz>zzz);
	//enum xxx = ['h','e','l','l','o']<['a','b','c'];
	//void fooz(bool c)(){}
	//fooz!(xxx);

	static assert((4+5i)%3i == 1+2i);
	static assert(cast(cdouble)2i == 2i);

	pragma(msg, zz,zzz,zz!<>zzz);
	pragma(msg, "hell"=="hello");
	pragma(msg, [1,2]!<=[1]);
	enum u = (1/0.0f-1/0.0f);
	static assert(u!<>=u);

	static assert(!is(typeof(mixin(q{mixin(q{mixin(q{mixin})})}))));

	//pragma(msg, fun(10)+10);

	enum immutable(dchar)[] idc = "a"~"b"~"c"~"d";
	pragma(msg, idc);

	enum cic = cast(dchar[][])["test"];
	pragma(msg, cic);

	pragma(msg, []<[1]);
	enum zz2 = [zz];
	pragma(msg, (cast(dchar[])zz)[2]);

	pragma(msg, [zz,zz2[0]],"\n","hallo",zz2,cast(dchar[][])[q{2}]);
	pragma(msg, /*cast(int)*/[][y]);
	pragma(msg, [][y]);
}
mixin("pragma(msg)");

// +/