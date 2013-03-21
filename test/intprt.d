
void ttt(){
	int y=0;
	immutable x = [1,y];
	pragma(msg, x.length); // TODO: should this work?
}


pragma(msg, [1,2,3][0..(()=>$)()]);
pragma(msg, [1,2,3][(()=>$-1)()..$]);
pragma(msg, [1,2,3][(()=>$-2)()]);

pragma(msg, [1,2,3,4,5,6][0..(){return ()=>$-[3,1][(()=>()=>$-2)()()];}()()]);
static assert([1,2,3,4,5,6][0..(){return ()=>$-[3,1][(()=>()=>$-2)()()];}()()]==[1,2,3]);

pragma(msg, [1,1337,3][(int delegate() dg){return $-dg()+1;}(()=>cast(int)$)]);


immutable int i = 3;
pragma(msg, [1,2,3][(()=>i)()]); // error
pragma(msg, [1,2,3][$]); // error
pragma(msg, [1,2,3][$-1]);

pragma(msg, [1,2][0..$+1]); // error
pragma(msg, [1,2][$+1..0]); // error
pragma(msg, [0,1][1..0]);   // error


int fail(){int x; return x/x;} // error

pragma(msg, [fail()][$/($-1)]);
pragma(msg, [0][fail()]);

pragma(msg, 2/3);



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

	static assert((4+5i)%3i == 1+2i);
	static assert(cast(cdouble)2i == 2i);

	pragma(msg, zz,zzz,zz!<>zzz);
	pragma(msg, "hell"=="hello");
	pragma(msg, [1,2]!<=[1]);
	enum u = (1/0.0f-1/0.0f);
	static assert(u!<>=u);

	static assert(!is(typeof(mixin(q{mixin(q{mixin(q{mixin})})}))));

	//pragma(msg, fun(10)+10);

	enum immutable(dchar)[] idc = "a"~"b"~"c"~"d"; // TODO!
	pragma(msg, idc);

	enum cic = cast(dchar[][])["test"];
	pragma(msg, cic);

	pragma(msg, []<[1]);
	enum zz2 = [zz];
	pragma(msg, (cast(dchar[])zz)[2]);

	pragma(msg, [zz,zz2[0]],"\n","hallo",zz2,cast(dchar[][])[q{2}]);
	pragma(msg, /*cast(int)*/[][y]); // error
	pragma(msg, [][y]); // error
}
mixin("pragma(msg) //error
");

// +/