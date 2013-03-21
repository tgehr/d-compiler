
inout(void) foo(inout(int)){
	inout(int)* x1;
	const(int)* x2 = x1;
	inout(const(int))* x3 = x1;
	x2 = x3;
}

void main(){
}