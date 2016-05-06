
struct S{
	struct O{
		static immutable int x = 2;
		enum int y = 2;
	}
	O o;
}

int foo(){
	const(S) s;
	s.O x;
	int y = 0;
	return (++y,s).o.x+(++y,s).O.x+(++y,s).o.y+y;
}
static assert(foo()==7);

