//pragma(msg, 2*2);

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
	enum ass = (assert(0),2);

	*cast(int*)&x[0] = 2;
	immutable int x=a;
	//pragma(msg, x);
	enum y = x;

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
	pragma(msg, zz,zzz,zz!<>zzz);
	pragma(msg, "hell"=="hello");
	pragma(msg, [1,2]!<=[1]);
	enum u = (1/0.0f-1/0.0f);
	static assert(u!<>=u);

	static assert(!is(typeof(mixin(q{mixin(q{mixin(q{mixin})})}))));
	pragma(msg, fun(10)+10);

	enum immutable(dchar)[] idc = "a"~"b"~"c"~"d";
	pragma(msg, idc);

	enum cic = cast(dchar[][])["test"];
	pragma(msg, cic);

	//pragma(msg, []<[1]);
	//enum zz2 = [zz];
	//pragma(msg, (cast(dchar[])zz)[2]);

	//pragma(msg, [zz,zz2[0]],"\n","hallo",zz2,cast(dchar[][])[q{2}]);
	//pragma(msg, /*cast(int)*/[][y]);
	//pragma(msg, [][y]);
}
//mixin("pragma(msg)");