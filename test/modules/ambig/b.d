import a;

static if(!is(typeof(bar))) enum foo = 1; // error

enum z = 2;