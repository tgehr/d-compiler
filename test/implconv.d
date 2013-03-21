/+
static assert(!is(int[2]: int[1]),"TODO"); // TODO!

static assert(is(typeof([1,1L])==long[]));

//byte b = 0b11110000; // TODO: find a case to prove inconsistency of DMD

enum x = 2i*1;
pragma(msg, x);
pragma(msg, typeof(x));


static assert(is(typeof(x)==idouble)); // TODO!


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