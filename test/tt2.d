int kkk;
//pragma(__range, cast(byte)kkk);
// pragma(__range, ((kkk%1000-500)%600)&0xFFFFFFFF);
// pragma(__range, cast(uint)((kkk%1000-500))&cast(int)0xF0000FFF);

// module tt;

//int x=-1;
//pragma(__range, (!!(x|1)+11)^2902);
//xpragma(__range, x&~(1<<31));

extern(C) int scanf(const(char)* format,...);
extern(C) int printf(const(char)* format,...);

//typeof(x) x = x;

struct S{ int x; }

template XXX(int q, alias r, this This, S, T...){}

template Moo(){int Moo(int x){return x;}}
template Moo(){int Moo(int x){return x;}}

//enum int a=b,b=a;

typeof(z) x; // error
typeof(x) y;
typeof(y) z;


int foo(int x){return x;}
double foo(double x){return x;}
// int foo(int* =null); // TODO: fix constant folding in this case!

int moo(short param, short param2);

int mmo(int x, int y=2){return 1;}
//int mmo(double x){return 2;}
//enum x = param;
void fuz(inout(int)*);

static if(false&&foo||true){}

mixin(`pragma(msg, ["bar"]~["foo"d]);`);

void main(){
	immutable(const(int)) u1;
	const(inout(shared(int))) u2;
	inout(const(shared(int))) u3;
	const(inout(shared(int))) u4;
	inout(shared(const(int))) u5;
	shared(const(inout(int))) u6;
	shared(inout(const(int))) u7;

	fuz(&kkk);
	pragma(msg,mmo(1)); // TODO
	foo(&kkk)+1="bar"; // error
	//A!(a=>b);
	int[] a; immutable int[] b;
	const int[] c;
	immutable(int[]) arrr = [1];
	pragma(msg, typeof(cast(immutable)[[1]]~[1]));
	auto dg = delegate int(int x){int[]a;return a;}; // error
	pragma(msg, typeof(x));
	//pragma(msg, typeof(z));
	moo(1,2000000); // error
	float x;
	foo(&x); // error
	// immutable dchar[] aa,bb=x"AA BB CC DD 32";
	// pragma(msg, typeof(aa~bb)); // TODO: FIX
	pragma(msg, bb); // error
	//int*[] x;
	//const(int)*[] y = x~x;

	int[][] x1;
	int[] x2; pragma(msg, typeof(x2));
	const(short)[] ss;
	auto ttt = ss ~ [1,2,3]; // wrong!
	pragma(msg, typeof(ttt));
	//pragma(msg, typeof(x~y));
	immutable(char)[] cca;
	char[] ica = cca~'s';
	//char[] ica = cca~[];
	pragma(msg, typeof(cca~'s'));
	//ubyte sss = ((kkk&252)^2)+1;
	//ubyte[][][] fl = [[[1,2,3]~[4,5,6,(kkk&252^2)+1]]];
	//S[][] foo = [[{1},{2},{3}]];

	immutable(int**)[] xxx;
	shared(int**)[] yyy;
	pragma(msg, typeof(xxx~yyy));
	immutable(dchar)[][][] xxxx;
	//xxxx = "hello"c "hello" "hello"d;
	pragma(msg, typeof(xxxx));
	//immutable(char)[] ss="";
	//auto x=["a"~"b"]~["c",""d];
	//pragma(msg, typeof(x));
	char ccc;
	//' '~ccc;
	//pragma(msg, typeof(ccc~' '));
	int y=(1);
	pragma(msg, typeof(y));
	//auto mooo = x[];
	immutable(int[]) a; // error
	immutable(int[]) b; // error
	shared(int) sx;
	//(*(&++*cast(int*)&a))++;
	//pragma(msg, typeof(cast(const shared inout)sx));
	pragma(__range, sx?22+((sx>>>2)|1):~(++sx&2));
	auto gogod = (1?a:b)[][0..3][22+((sx>>>2|1)&2)..22];
	pragma(msg, typeof(gogod));

	//auto dkl = (*&*&a)[]++;
	//pragma(msg, typeof((cast(shared)++(*&*&a)[]))[]);
	/+float f;
	++f;
	immutable float*[] x = [cast(immutable)&f];
	auto y = x[0];
	immutable(short) z = 1;
	z = 2;
	pragma(msg,typeof(z = 1));
	//scanf("%d",&x);
	//printf();
	void d(){}
	do{
		int moo = 2;
	}while(x==2);
	void moo(){}
	void moo(int){}
	moo();
	if(auto y=&x){
		//pragma(msg, typeof(y));
		(++y)++;
		//auto y=&x;
		//printf("%d",x);
	}else{
		//printf("%d%d",x,x);
	}+/
}
//pragma(msg) // TODO: message should be at right place!
