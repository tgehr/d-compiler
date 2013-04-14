
void container(){
	void proto();
	void proto(T...)(T args){return proto();} // error
	pragma(msg, {proto!()(2);return 1;}());
}


//auto fun(alias T)(T args){return 1;}
auto fun(){return "a function";}
auto fun(T...)(T args){return 1;}
template fun(a...){auto fun(T...)(T args){return 2;}}
template fun(a...){template fun(b...){auto fun(T...)(T args){return 3;}}}
static assert(fun(0)==1); // TODO: should this work?
static assert(fun()=="a function");
//pragma(msg, fun!2);


//pragma(msg, fun!2(1,4));
//pragma(msg, (fun!2));

//template fun(a...){ alias a fun; }
//pragma(msg, fun!2);


template ambiguous(T...){}
template ambiguous(T...){}

pragma(msg, ambiguous!(int, double)); // error


auto notambiguous(T:   int)(T arg){ return true; }
auto notambiguous(T: short)(T arg){ return false; }

alias notambiguous!int ali1;
alias notambiguous!short ali2;
static assert(ali1(1));
static assert(!ali2(2));
static assert(notambiguous(2));
static assert(!notambiguous(cast(short)2));
pragma(msg, ali1(2));
pragma(msg, notambiguous!short(2));

template TT(int x){enum TT = 1;}
template TT(const(int) y){enum TT = 2;}

void nest(){
	const j = 2;
	const i = j+1;
	pragma(msg, "TT: ",TT!i);
	static assert(TT!i == 2);
	static assert(is(typeof(TT!i)));
}

template SS(x : int){ enum SS = 1; }
template SS(y : const(int)){ enum SS = 2; }
static assert(!is(typeof(SS!(const(int)))));

auto uu(T : int)(const(T) arg){ return 1; }
auto uu(T : const(int))(T arg){ return 2; }

static assert(uu(0)==2);

pragma(msg, "uu: ",uu(0));
pragma(msg, "uu: ",uu!int(0));

static assert(uu(cast(const)0)==2); // TODO

// +/