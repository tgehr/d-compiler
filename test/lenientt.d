/+template _Empty(){}
alias _Empty!() Empty;
template Cons(alias Car, alias Cdr){
	alias Car CAR;
	alias Cdr CDR;
}
template Index(alias L, int i){
	static if(!i) alias L.CAR Index;
	else alias Index!(L.CDR,i) Index;
}
template List(T...){
	static if(!T.length) alias Empty List;
	else alias List!(T,List!(T[1..$])) List;
}

alias Cons!(1,Ones) Ones; // error. TODO: should this work
+/


/+template Fib(int n){
	template FibImpl(alias L, int i, int n){
		static if(i>n) alias Empty FibImpl;
		else alias Cons!(Index!(L,i-1)+Index!(L,i-2),FibIimpl!(L,i+1,n)) FibImpl;
	}
	alias Cons!(0,Cons!(1,FibImpl!(L,2,n))) L; // error.
	alias Index!(L,n) Fib;
}

pragma(msg, Fib!(0));+/