
template NumDim(T){enum NumDim=0;}
template NumDim(T:T[]){enum NumDim=NumDim!T+1;}

static assert(NumDim!int==0);
static assert(NumDim!(int[])==1);
static assert(NumDim!(int[][])==2);
static assert(NumDim!(int[][][])==3);

template Test(int a,int b,int c){}

void main(){
	mixin Test!();
	pragma(msg,NumDim!(int[][][][]));
	//A!B!C!D!E!F!G D;
	//alias immutable(Foo) Y;
	//Y.Goo x;
	//pragma(msg,typeof(x));
}
