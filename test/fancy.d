
@property int foo()(){ return 2; }
alias foo bar;
//pragma(msg, foo," ",bar);

struct S{
	int foo(){ return 2; }
}

pragma(msg, S.foo()); // error