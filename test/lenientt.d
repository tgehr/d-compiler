
template BorkenY(alias F){
	template BorkenY(A...){
		template Lhs(alias X){
			alias X!X Lhs;
		}
		template Rhs(alias X){
			alias F!(X,A) Rhs;
		}
		alias Lhs!Rhs BorkenY;
	}
}
template BorkenAlmostFact(alias BorkenFact, int n){
	static if(n) enum AlmostFact = n*BorkenFact!(n-1); // error
	else enum BorkenAlmostFact=1;
}
alias BorkenY!BorkenAlmostFact BorkenFact;
pragma(msg, BorkenFact!3);

template Y(alias F){
	template Z(alias X){
		template Z(A...){
			alias F!(X!X,A) Z;
		}
	}
	alias Z!Z Y;
}

template AlmostFact(alias Fact, int n){
	static if(n) enum AlmostFact = n*Fact!(n-1);
	else enum AlmostFact=1;
}

template AlmostAck(alias Ack, int n, int m){
	static if(!n) enum AlmostAck = m+1;
	else static if(!m) enum AlmostAck = Ack!(n-1,1);
	else enum AlmostAck = Ack!(n-1,Ack!(n,m-1));
}

template AlmostFib(alias Fib, int n){
	static if(n<2) enum AlmostFib = n;
	else enum AlmostFib = Fib!(n-2)+Fib!(n-1);
}

alias Y!AlmostFact Fact;
pragma(msg, "Fact: ",Fact!5);
static assert(Fact!5==120);

/+
// TODO: restore performance!
alias Y!AlmostAck Ack;
pragma(msg, "Ack: ",Ack!(3,7));
static assert(Ack!(3,7)==1021);
+/

alias Y!AlmostFib Fib;
pragma(msg, "Fib: ",Fib!12);
static assert(Fib!12==144);

/+

template _Empty(){}
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

template Y(alias F){
	template Y(A...){
		template Lhs(alias X){
			alias X!X Lhs;
		}
		template Rhs(alias X){
			alias F!(X,A) Rhs;
		}
		alias Lhs!Rhs Y;
	}
}
template AlmostFact(alias Fact, int n){
	static if(n) enum AlmostFact = n*Fact!(n-1);
	else enum AlmostFact=1;
}
alias Y!AlmostFact Fact;

pragma(msg, Fact!3);


/+template Fib(int n){
	template FibImpl(alias L, int i, int n){
		static if(i>n) alias Empty FibImpl;
		else alias Cons!(Index!(L,i-1)+Index!(L,i-2),FibIimpl!(L,i+1,n)) FibImpl;
	}
	alias Cons!(0,Cons!(1,FibImpl!(L,2,n))) L; // error.
	alias Index!(L,n) Fib;
}

pragma(msg, Fib!(0));+/
// +/