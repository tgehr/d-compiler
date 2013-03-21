interface I{ }

class C: D{ }

class D: C{ } // error


immutable int u = v; // error
immutable int v = u;

const int cu = cv; // error
const int cv = cu;

int duh(typeof(guh) duh){} // error
typeof(duh)* duh(typeof(duh)* duh){return 1;} // error
int duh(typeof(guh)){return 1;}
int guh(typeof(duh)){return 2;}


int circdep1(){enum x = circdep2(); return x;} // error
int circdep2(){enum y = circdep1(); return y;}

// TODO: investigate error message situation: the tail call in circdep3 loses information
int circdep3(bool b){enum x = circdep4(); return x;}
int circdep4(){auto y=circdep5(0); return y;}
int circdep5(bool b){auto y=circdep3(0); return y;} // error


struct AA{
	typeof(AAA.y) x;
	struct AAA{
		static typeof(AA.x) y; // error
	}
}

// evil!
enum a = b, b = is(typeof(a)); // error
enum c = is(typeof(c)); // error

auto foo(){
	static if(is(typeof(bar())==int)) return 1.0; // error
	else return 1;
}

auto bar(){
	static if(is(typeof(foo())==int)) return foo();
	else return 1.0;
}

template A(){
	enum V=B!().V;
}
template B(){
	enum V=A!().V; // error
}
enum x = A!();


struct Str{
	immutable a = b; // error
	immutable b = a;
	immutable int c = d; // error
	immutable int d = c;
	template TT(){
		immutable int TT=x; // error
	}
	immutable int x=y;
	immutable int y=TT!();
}

// +/







