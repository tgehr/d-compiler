
bool nosfinae3()(double x){return true;}
template nosfinae3(){
	bool nosfinae3(int x){return false;}
	enum int x = 1.0; // does not get instantiated
}
static assert(nosfinae3(1.0));

bool nosfinae()(double x){return false;}
template nosfinae(){
	bool nosfinae(int x){return true;}
	enum int x = ""; // error (TODO: show instantiation location, propagate to module)
}
pragma(msg, nosfinae(2)); // does not show up because of errors in instantiation
static assert(!is(typeof(nosfinae(2)))); // TODO: should be ok

auto nosfinae2(double x){return true;}
auto nosfinae2()(int x){return true;}
auto nosfinae2(T=int)(int x){return 1+"";}

//pragma(msg, nosfinae2!()(2));// TODO: error message
pragma(msg, nosfinae2(2));// error, both match

auto sfinae()(int x){return x;}
auto sfinae()(int x = sfinae2()){return false;}
static assert(sfinae(1));

pragma(msg, is(typeof(sfinae2(1))));

T foo(T)(T x){return x;}
T foo()(int x){return x;} // sfinae kicks in
int foo(int x){return x+1;}
auto foo(S...)(S args)if(!is(typeof(args[0])==double)){return args[0];}

pragma(msg, foo(2.0));
pragma(msg, foo(2));
pragma(msg, foo("123",456));

