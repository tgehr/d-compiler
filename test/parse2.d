struct TestReturn{
	ref TestReturn foo() return {
		return this;
	}
}

//auto A(T);

auto A(T) = true;
@safe enum @safe bool B(T) = false;
enum bool C(T) = true;
static assert(!B!int);
static assert(C!int);
auto X(T)=true, Y(T)=false;

static assert(is(typeof({ A!int=false; X!int=false; Y!int=true; })));

alias K(T)=T, L(T)=T;
//alias M(T)=true, N(T)=true;

struct S{
	int x,y;
	//alias this=x;
	alias x xx;
	alias x k,l;
	//alias int k(T);
}
static assert({
	S s;
	s.k=2;
	assert(s.x==2);
	s.l=3;
	assert(s.x==3);
	return true;
}());


auto enum T{K}


void main(){
	//A!int=false;
}


//enum B(T){ X }
