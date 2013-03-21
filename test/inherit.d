class A(T){
	static assert(is(T: A!T));
}
class C(T) : A!T{
	// static if(is(T==D)) enum x = "success!";
	// static if(is(T:C!T)) enum x = "success!";
}

class D: C!D{
	//pragma(msg, x);
}

//pragma(msg, D);
//pragma(msg, C!D);