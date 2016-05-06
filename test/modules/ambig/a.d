import b;

static if(!is(typeof(foo))) enum bar = 2; // error

enum x = y; // error
enum w = z; // ok