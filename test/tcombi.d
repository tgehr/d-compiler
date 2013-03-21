//pragma(msg, bar());
static assert(is(typeof([[[]],[[1]]]) == int[][][]));
pragma(msg, typeof([[[]],[[1]]]));
static assert(is(typeof(0?[[]]:[[1]]) == int[][]));
pragma(msg, typeof(0?[[]]:[[1]]));
static assert(is(typeof([[[]],[[]],[[1]]]) == int[][][]));
pragma(msg, typeof([[[]],[[]],[[1]]]));
static assert(is(typeof(1?1?[[]]:[[]]:[[1]]) == int[][]));
pragma(msg, typeof(1?1?[[]]:[[]]:[[1]]));

immutable(typeof([])) empty;
static assert(is(typeof([[empty],[[1]]]) == int[][][]));
pragma(msg,typeof([[empty],[[1]]]));

typeof([])[] emptyarr;
static assert(is(typeof([emptyarr,[[1]]])==const(int[])[][]));
pragma(msg, typeof([emptyarr,[[1]]]));

typeof(null)[] nullarray;
int*[]x;
static assert(is(typeof([nullarray,x])==const(int*)[][]));
pragma(msg, typeof([nullarray,x]));

immutable(int)*[]y;
static assert(is(typeof([nullarray,y])==const(immutable(int)*)[][]));
pragma(msg, typeof([nullarray,x]));