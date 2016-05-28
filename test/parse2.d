void assign(string x, ref string r){ r=x; }
struct ImportExp{
	auto foo(){
		string r;
		import("parse2.d").assign(r); // TODO
		return r;
	}
	pragma(msg,foo()[0..100]);
}



alias string=immutable(char)[];
