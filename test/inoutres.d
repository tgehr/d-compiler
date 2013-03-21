

//inout(int)* 
inout(int)* foo(inout int x, inout(int)* y){return y;}
inout(int)* foo(inout int x, inout(int)* y){return y;}
const(int)* foo(immutable int x, immutable(int)* y){return y;}

void main(){
	immutable int x;
	pragma(msg,typeof(foo(x,&x)));
}