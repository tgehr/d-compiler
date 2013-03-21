import std.stdio, std.range;

struct S{
	this() @disable;
	int i;
}

class C{
	S s;
	this(){} // Error: constructor tt.C.this field s must be initialized in constructor
}

int a☺

void main(){
	//auto c=new C(0);
}


/*void main(){
string x="h☺☺O↯";
	writeln(x);
	foreach_reverse(dchar c;x) writeln(c);
	foreach(c;retro(x)) writeln(c);
	}*/

