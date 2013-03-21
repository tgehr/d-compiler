
immutable int u = v;
immutable int v = u;

const int cu = cv;
const int cv = cu;

int circdep1(){enum x = circdep2(); return x;}
int circdep2(){enum y = circdep1(); return y;}

// TODO: investigate error message situation: the tail call in circdep3 loses information
int circdep3(bool b){enum x = circdep4(); return x;}
int circdep4(){auto y=circdep5(0); return y;}
int circdep5(bool b){auto y=circdep3(0); return y;}


struct AA{
	typeof(AAA.y) x;
	struct AAA{
		static typeof(AA.x) y;
	}
}

// evil!
enum a = b, b = is(typeof(a));
enum c = is(typeof(c));

auto foo(){
	static if(is(typeof(bar())==int)) return 1.0;
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
	enum V=A!().V;
}
enum x = A!();


struct Str{
	immutable a = b;
	immutable b = a;
	immutable int c = d;
	immutable int d = c;
	template TT(){
		immutable int TT=x;
	}
	immutable int x=y;
	immutable int y=TT!();
}

