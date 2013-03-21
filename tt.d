//const(inout(shared(int))*)*
/+auto foo(const(inout(shared(int))**) x){//, inout(int*)* y){
	//typeof(foo(x)) y = x;
	foo(x);
	return x;
}+/
auto bar(int x){return 1;}

auto aa(int x){int y;return bb(1);y=2;}
auto bb(int x){return aa(1);}

inout(float)* qux(inout(float)* x){return x;}

void main(){
	immutable(int)** a;
	//immutable(int)** b;
	pragma(msg, typeof(foo(a)));
	
	for({	inout(float)* x = null;
			immutable(float)* y = cast(immutable(float)*)10;
		} x<y;x++){
		//pragma(msg, typeof(foo(x,y)));
		pragma(msg, typeof(qux(1?x:y)));
	}
}
