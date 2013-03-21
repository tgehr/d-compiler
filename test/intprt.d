//pragma(msg, 2*2);

immutable(int)[] x = [1];
//immutable(int)[]* p = &x;
//immutable rp=p;
immutable a=2;
//int foo(){*p=[2];return 0;}
void main(){
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
	pragma(msg, u!<>=u);

	pragma(msg, mixin(q{mixin(q{mixin(q{mixin})})}));
	//pragma(msg, []<[1]);
	//enum zz2 = [zz];
	//pragma(msg, (cast(dchar[])zz)[2]);

	//pragma(msg, [zz,zz2[0]],"\n","hallo",zz2,cast(dchar[][])[q{2}]);
	//pragma(msg, /*cast(int)*/[][y]);
	//pragma(msg, [][y]);
}
mixin("pragma(msg)");