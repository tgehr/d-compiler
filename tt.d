//const(inout(shared(int))*)*
inout(int*)* foo(inout(int**) x){//, inout(int*)* y){
	//typeof(foo(x)) y = x;
	//foo(x);
	return x;
}
//auto bar(int x){return 1;}

//auto aa(int x){int y;return bb(1);y=2;}
//auto bb(int x){return aa(1);}

inout(float)* qux(inout(float)* x){return x;}

pragma(msg, typeof(x));
const int x;
//pragma(msg, typeof(x));


string foo1(int x){
	//if(x) return q{return "return ``;";};
	return bar1();
}
string bar1(){
	mixin(foo(1));
}

auto tbaz4(R)(R function() dg) { static assert(is(R == void)); return 1; }
auto tbaz4(R)(R delegate() dg) { static assert(is(R == void)); return 2; }
static assert(0,typeof(tbaz4({})));

void main(){
	string delegate(int, string) dg = (n, int x){};
	int delegate(int) dg = true ? (x => x) : (x => m*2);
	byte b;
	short s = b<<1;
	b = -1+(b*-1);
	pragma(__range, -1+(b*-1));

	long n;
	ubyte bb = n%10;
	pragma(__range, n%10);

	enum a = "abc";
	enum b = "def";

	enum d = (cast(char[])"hello");
	enum e = cast(char[])a;
	
	//enum d = "a">cast(immutable(char)[])['b'];
	pragma(msg, d,e,d>e);
	pragma(msg, a~b);
	enum c = a~b;
	pragma(msg, (b<a?b:a)[]);

	//pragma(msg, ([[[[1]]]~[[[2]]]]~[[[[3]]]])[0][0][0][0]);

	pragma(msg, [[1]]<=[[2]]);

	pragma(msg, ("foo"d~"bar"d)[1..5]);
	pragma(msg, typeof(0.0f&&{}()));
	pragma(msg, !(is(T==int))^^2);
	pragma(msg, (){return 2.0f;}());
	pragma(msg, !false);
	pragma(__p, 1+2+3+4+5+6+true);
	pragma(__p, [1,2,3][1]);
	enum x = 2;
	pragma(msg, [1,2,3][2..x&2]);
	pragma(msg, [100][1+(x|1)]);
	pragma(msg, 1 in [1:0,2:0]);
	pragma(msg, [1,2,3] < [1,2,3]);
	pragma(msg,1L<<63);

	short s = [1,2,3][1+(x&1)];
	
	//pragma(__range, );

	//pragma(msg, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff29293393939);
	char ä='ä';
	auto oo = "ä"[2+(x&1)];
	pragma(msg,"ä"[2]);
	immutable(int)[] a;
	const(int)[] b;
	immutable c = a~b;

	int y;
	y = 1+2+3;
	pragma(__range,cast(byte)((y&252)^2)+1);
	pragma(msg,typeof(cast(byte)((y&252)^2)+1));
	ubyte[] x = [((y&252)^2)+1];
	auto xxxx = y+-127;

	//ubyte[] yx = [-127+(y&1)];
	//ubyte[] x = [cast(byte)y,1];
	//pragma(__range, );
	int x = 2;
	//pragma(msg, typeof(x));

	immutable(int*)* a;
	//immutable(int)** b;
	//pragma(msg, typeof(foo(a)));
	
	int** xxxx = a;

	/*	for({	inout(float)* x = null;
			immutable(float)* y = cast(immutable(float)*)10;
		} x<y;x++){
		//pragma(msg, typeof(foo(x,y)));
		pragma(msg, typeof(qux(1?x:y)));
		}*/
}
