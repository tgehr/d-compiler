
auto goo(){
	void foo(){}
	with(foo()){} // TODO
}


auto boo(){
	int x;
	struct S{ int x; }
	S s;
	with(s){
		s.x++; // ok
	}
	with(s){
		x++; // TODO: error
	}
}

auto foo(){
	struct T{ int u; }
	struct S{ int x; int y; T t; }
	S foo;
	//int x;
	with(foo){
		x=23;
		x++;
		--x;
		y=x;
		y-=3*x;
		with(t) u=1337;
	}
	return [foo.x,foo.y,foo.t.u];
	//writeln(foo.x);
}
pragma(msg, foo());

auto fun(){
	enum E{ A, B, C }
	auto gun(E e){
		final switch(e) with(E){
			case A: return "A";
			case B: return "B";
			case C: return "C";
		}
	}
	with(E) return gun(A)~gun(C)~gun(B);
}
pragma(msg, fun());

auto hun(){
	struct S{ int x; }

	auto foo(alias a)(){a=2;}
	S s;
	with(s){
		foo!x(); // ok
	}
	with(S){
		foo!x(); // error // TODO: better error message
	}
}

mixin template M(){ int foo(){ return x+=2; } int x=2; }
auto gun(){
	struct S{
		mixin M m;
	}
	S s;
	with(s.m){
		x++;
		return [s.m.x++,s.x++,x,foo(),x++,s.x++,s.m.x];
	}
}
static assert(gun()==[3,4,5,7,7,8,9]);

auto iun(){
	struct S{
		mixin M m;
	}
	S s;
	with(s){
		m.x++;
		return [m.x++,s.m.x++,x,foo(),x++,s.m.x++,m.x];
	}
}
pragma(msg, iun());
static assert(gun()==iun());

int builtIn(){
	with(int) return max; // TODO
}
static assert(builtIn()==int.max); // TODO
