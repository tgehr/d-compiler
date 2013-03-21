//int a;
void main(){
	int a;
	pragma(msg, is(typeof(function{a=1;})));
	pragma(msg, is(typeof(1)==int));
	pragma(msg, is(typeof(""): const(shared(char)[])));
	int function(int) fp;
	pragma(msg, is(typeof(*(int x){return x;}) == typeof(*fp)));
	pragma(msg, typeof(*(int x){return x;}));
	pragma(msg, typeof(*fp));
	//pragma(msg, is(typeof(foo)));
}
int foo(){
	return 1=2;
	return 0;
}