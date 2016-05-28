// options: -Jtest

void assign(string x, ref string r){ r=x; }

alias Seq(T...)=T;

struct ImportExp{
	static foo(){
		string r;
		import(Seq!("importexp.d"),("foo",Seq!())).assign(r);
		return r;
	}
	pragma(msg,foo()[0..100]);
}

int x=2;
enum k=import(Seq!("importexp.d"),(x,Seq!())); // error

string s=import("importexp.d");
wstring w=import("importexp.d");
dstring d=import("importexp.d");


alias string=immutable(char)[];
alias wstring=immutable(wchar)[];
alias dstring=immutable(dchar)[];
