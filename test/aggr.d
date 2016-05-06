struct CC{
	static int x;
	static template foo(){
		auto bar(){
			return x;
		}
	}
}

void foo(){
	CC c;
	CC.foo!().bar();
	//CC.x=2;
}

struct A{
	struct B{
		A* c;
	}
}
class B{
	const(B) foo(){return this;}
}
class C{
	void d(C args){
		d(C); // error
	}
}

void foo(int){}
pragma(msg,is(typeof(foo(typeof(0)))));

void main(){}

