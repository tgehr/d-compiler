bool ambig(T)(double x){return true;}
bool ambig()(double x){return false;}

template ambig(T){
	static if(true) bool ambig(double x){return false;}
}

template ambig(T){
	static if(true) bool ambig(double x){return false;}
}

pragma(msg, ambig!int(2)); // error

bool noambig(T)(double x){return true;}
bool noambig()(double x){return false;}

template noambig(T){
	static if(true) bool noambig(int x){return false;}
}

template noambig(T){
	static if(true) bool noambig(double x){return false;}
}

pragma(msg, noambig!int(2));


bool nosfinae()(double x){return false;}
template nosfinae(){
	static if(true) bool nosfinae(int x){return true;}
	enum int x = ""; // error // TODO: show instantiation location
}
pragma(msg, "MOO: ", nosfinae(2));


static assert((nosfinae(2),0)); // not shown
static assert(!is(typeof(nosfinae(2))));
static assert((nosfinae(2),0)); // not shown

template X(){
	double X(double){return 2;}
	float X(float){return 3.0;}
}
static assert(is(typeof(X(2.0))==double));
static assert(is(typeof(X(2.0f))==float)); // TODO
static assert(!is(typeof(X(2)))); // TODO
static assert(is(typeof(X!()(2.0f)) == float));

bool nosfinae3()(double x){return true;}
template nosfinae3(){
	bool nosfinae3(int x){return false;}
	enum int x = 1.0; // error (TODO: show instantiation location)
}
static assert((nosfinae3(1.0),0)); // TODO: not shown


auto nosfinae2(double x){return true;}
auto nosfinae2()(int x){return true;}
auto nosfinae2(T=int)(int x){return 1+"";}

pragma(msg, nosfinae2!()(2));// error
pragma(msg, nosfinae2(2));// TODO: error message

auto sfinae()(int x){return x;}
auto sfinae()(int x = sfinae2()){return false;}
static assert(sfinae(1));

pragma(msg, is(typeof(sfinae2(1))));

T foo(T)(T x){return x;}
T foo()(int x){return x;} // sfinae kicks in
int foo(int x){return x+1;}
auto foo(S...)(S args)if(!is(typeof(args[0])==idouble)){return args[0];}

pragma(msg, foo(2.0));
pragma(msg, foo(2));
pragma(msg, foo("123",456));

// +/