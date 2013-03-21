//int xyz;
int xyz();
int xyz(float);

/*class C{
	class D{}
}*/

int[] y;
pragma(msg, "start");

inout(const(int)[]) foo(inout(const(int)[]) x){
	//inout(const(inout(shared(immutable(inout(int)[]))))[]) y;
	//const(immutable(int)) y;
	//pragma(msg, typeof(y));
	immutable(int*)[] p;
	const(inout(int*)[]) q=p;
	pragma(msg, typeof(q));
	
	immutable(float) yy;
	int xx;
	auto zz = 1 ? xx : yy;
	auto ww = 1 ? yy : xx;
	pragma(msg, typeof(zz));
	pragma(msg, typeof(ww));
	

	return x;
}

//x x;
//int x;

void foo(){}
int bar(){ return 1; }
void main(){/*
	//pragma(msg, typeof(q));
	shared(int) x=cast(const(int))1;
	const(shared(int)) xxx=1;
	shared(const(int)) xxy=xxx;
	immutable(const(int)) xxz;
	shared(immutable(int)) xxa;
	immutable(shared(int)) xxb;	
	//const(shared(immutable(int))) xxc;
	const(typeof(xxa)) xxc = xxa;
	immutable(const(int)[]) xxd;
	pragma(msg, typeof(xxx));
	pragma(msg, typeof(xxy));
	pragma(msg, typeof(xxz));
	pragma(msg, typeof(xxa));
	pragma(msg, typeof(xxb));
	pragma(msg, typeof(xxc));
	pragma(msg, typeof(xxd));
	//static assert(is(typeof(xxd) == const(immutable(int)*[])));
	
	/*int yyy=xxx;
	ushort wc=((x&1)+1)+1U; int ii=wc;
	auto arr=[2fi+1L, 1.0L, 2,];
	float sa=1+1; char cb;//=sa;
	int cc;
	//cc=x?arr:cb;
	//auto arr=["moo",[]];
	creal cx,cy;
	//pragma(msg,typeof(cx<cy));
	pragma(msg,typeof(cc,cb,arr));
	ubyte x;
	double y;
	//pragma(msg,typeof(x+y));
	ifloat ix, iy;
	bool a,b;
	int c;
	//struct S{} S rx;
	int rx;
	//rx=2;

	pragma(msg,typeof(null));
	pragma(msg,typeof([]));
	pragma(msg,typeof(1?x:y));
	pragma(msg,typeof(ix+c));
	pragma(msg,typeof(1?ix:iy));
	pragma(msg,typeof(1?ix:x));
	uint j;
	//auto x=delegate uint(dchar i){return i+j;pragma(msg,typeof(i>>j));};
	//pragma(msg,typeof(foo()));
	//auto y=(int i){return i+soasjojsoj;};
	auto xx="hello";
	pragma(msg,typeof(xx));
	//printf("hello"~" "~"world!\n");
	//scanf("%d\n",&x);
	//x++;
	//int x;
	//int i;
	//{int i(){};}
	//C c=new C;
	//C.D d=c.new D;
	//printf("x=%d!\n",x);
	//int i(){}
	for(int i=0;i<100;i++){
		//for(int i=0;i<100;i++){}
		}*/
}
//auto foo(){return bar();return 1;}
//auto bar(){return foo();}


extern(C) int scanf(const(char)*, ...);
extern(C) int printf(const(char)*, ...);

//int x=100;

void fill()(){}
void fill()(){}
