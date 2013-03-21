//S s;

//static if(!is(typeof(s.d2))) enum d1=0;

struct S{
	//static if(!is(typeof(d2))) enum d1=0;
	static if(!is(typeof(d1))) enum d2=0;
}

void main(){
	pragma(msg, is(typeof(d1)));
	pragma(msg, is(typeof(S.d1)));
	pragma(msg, is(typeof(S.d2)));
}

