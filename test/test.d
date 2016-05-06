

int main(){
	return 3;
}
pragma(msg, typeof(main));
pragma(msg, main());


/+//enum int a = b, b = a;

enum x = "hallo";

auto ref min(S,T)(auto ref S a, auto ref T b){
	return b<a?b:a;
}

void main(){
	int a=2, b=3;
	min(a,b)=4;
	import std.stdio;
	writeln(a," ",b);

	writeln(min(1,2));
}+/