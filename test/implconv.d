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