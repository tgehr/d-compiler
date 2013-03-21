pragma(msg, "Hello World!");


/+
static if(!is(typeof(a))) enum c = 2;
static if(is(typeof(c))) enum a = 2;


template Foo(T){
	alias T Foo;
}

pragma(msg, Foo!int);+/


template Seq(T...){ alias T Seq; }

template MessStuffUp(){
	static if(is(C!D:D)) alias Seq!() MessStuffUp;
	else alias D MessStuffUp; // error
}


class C(T): MessStuffUp!(){ // error
	
}

class D{}

void main(){
	D d = new C!D;
}