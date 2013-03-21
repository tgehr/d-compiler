import std.stdio, std.range;

void main(){
	string x="h☺☺O↯";
	writeln(x);
	foreach_reverse(dchar c;x) writeln(c);
	foreach(c;retro(x)) writeln(c);
}
