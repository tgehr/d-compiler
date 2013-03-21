

static assert({return 2f;}() == 2f);static assert({return 2fi;}() == 2fi);
static assert({return 2.0;}() == 2.0);static assert({return 2.0i;}() == 2.0i);
static assert({return 2.0L;}() == 2.0L);static assert({return 2.0Li;}() == 2.0Li);

static assert({return ' ';}() == ' ');

uint x(float a){return cast(uint)a;}
uint x(double a){return cast(uint)a;}
uint x(real a){return cast(uint)a;}

static assert(x(1.5f) == 1);
static assert(x(1.5)  == 1);
static assert(x(1.5L) == 1);

static assert(x(1e228) == 0);

pragma(msg, ((double x)=>(double y)=>x+y)(2)(3));


static assert((double x){return cast(short)cast(ulong)x;}(1e10) == -7168);
static assert(((double x)=>cast(short)x)(1e10) == -7168);


int y(float a){return cast(int)a;}
int y(double a){return cast(int)a;}
int y(real a){return cast(int)a;}


//static assert((x){return cast(int)x;}(2.0L) == 2);
//static assert({return cast(float)

//pragma(msg, {return 2.0i+1;}());

const(int) constvar = 2;
static assert(constvar==2);

uint foo(int x, real y){
	if(x) return cast(uint)y;

	if(100-100.0) return 2;
	else if(true) return 3;
	else return 0;
}

void main(){
	pragma(msg, foo(10,202.5L+119.6));
}