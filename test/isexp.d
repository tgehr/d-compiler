//int a;
void main(){
	int a;
	static assert(!is(typeof(function{a=1;})));
	static assert(is(typeof(1)==int));
	static assert(is(typeof(""): const(shared(char)[])));
	int function(int) fp;
	// static assert(!is(typeof(*(int x){return x;}) == typeof(*fp)));
	pragma(msg, typeof(*(int x){return x;}));
	pragma(msg, typeof(*fp));
	pragma(msg, is(typeof(foo)));
}
int foo(){
	return 1=2;
	return 0;
}