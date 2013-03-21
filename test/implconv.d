void contextpointerqualimplconv(){

	void delegate()inout w;
	void delegate()immutable i;
	void delegate()const c;
	void delegate() m;
	void delegate()const inout wc;
	
	// The following cases should be disallowed:
	
	i=c; // error: there may be mutable references to context
	c=m; // error: m may modify context
	i=m; // error: m may modify context
	w=i; // error: cannot use immutable as const or mutable
	w=m; // error: cannot use mutable as immutable
	w=c; // error: cannot use const as immutable
	wc=m;// error: cannot use mutable as immutable
	wc=c;// error: wc will access context as const or immutable
	i=w; // error: inout could mean const or mutable
	c=w; // error: inout could mean mutable
	i=wc; // error: inout const could mean const

	// These should be allowed:
	
	c=i; // certainly const if only immutable data accessed
	c=wc;// TODO: certainly const if only const inout data accessed
	m=c; // just loses guarantees to caller
	m=i; // TODO: ditto
	m=w; // TODO: ditto
	m=wc;// TODO: ditto
	w=wc;// m=c, c=c and i=i are valid
	wc=i;// TODO: c=i and i=i are valid
	wc=w;// TODO: c=m is not valid, but can be interpreted as c=c
}

static assert(is(int delegate() immutable : int delegate() const));
static assert(!is(int delegate() : int delegate() const));

static assert(!is(int[2]: int[1]));

enum x = 2i*1; // TODO
pragma(msg, x);
pragma(msg, typeof(x));


static assert(is(typeof(x)==idouble)); // TODO!
/+
static assert(is(typeof([1,1L])==long[]));

//byte b = 0b11110000; // TODO: find a case to prove inconsistency of DMD


enum y = 1i*2;
pragma(msg, typeof(y));
//pragma(msg, typeof(x))
+/

inout(void) foo(inout(int)){
	inout(int)* x1;
	const(int)* x2 = x1;
	inout(const(int))* x3 = x1;
	x2 = x3;

	const(char*) a = "hello";
	immutable(wchar*) b = "hello";
	immutable(dchar*) c = "hello";
	pragma(msg, typeof(a));
}
/+
int[][] a = [[]];
immutable int[][] b = [[]];

pragma(msg, typeof(a~b));

// +/

enum long iii = 2000000000;
enum int[] jjj = [iii];

enum long iii2 = 20000000000;
enum int[] jjj2 = [iii2]; // error

immutable long ciii = 2000000000;
void cj(){ int[] cjjj = [ciii]; }

immutable long ciii2 = 20000000000;
void ci(){ int[] cjjj2 = [ciii2]; }// error


enum int siii = 20000;
enum short[] sjjj = [siii];

enum int siii2 = 200000;
enum short[] sjjj2 = [siii2]; // error

immutable int sciii = 20000;
void cj(){ short[] scjjj = [sciii]; }

immutable int sciii2 = 200000;
void ci(){ short[] cjjj2 = [sciii2]; }// error