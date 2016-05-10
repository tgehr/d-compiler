enum s="123";

deprecated("a"){
	deprecated("b") int nested(){ return 0; }
}

pragma(msg, nested()); // TODO: error

deprecated(s) int foo(){ return 1;}

pragma(msg, foo()); // TODO: error // TODO: actually show the message

@nogc deprecated("the message") pure int bar(){ return 2; }
pragma(msg, bar()); // TODO: error // TODO: actually show the message

//pragma(msg, cast(deprecated int)2); // TODO: error
void main(){
	foreach(deprecated i;0..2){
		int x=i; // TODO: error
	}
	foreach(deprecated("hi") i;0..2){
		int x=i; // TODO: error // TODO: actually show the message
	}
}
