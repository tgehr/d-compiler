int[""] saa; // error

enum x=(()=>5)();
int[(()=>5)()] sa;
pragma(msg, typeof(sa));
static assert(is(typeof(sa)==int[5]));
static assert(!is(typeof(sa)==int[6]));
static assert(!is(typeof(sa)==char[5]));

char[4194303*4+3] sa2;
pragma(msg, typeof(sa2));

pragma(msg, {
		auto r="";
		int i=4194303*4+3;
		int j;
		while(i){
			r='0'+(i&1)~r;
			i/=2;
		}
		return r;
	}());

immutable int[2] i2 = [1,2];
immutable int[4] i3 = [1,2,3,43];
immutable int[5] i5 = i2~i3; // error

pragma(msg, i5);

enum int[$] t = [2,3,4]; // error

pragma(msg, t);