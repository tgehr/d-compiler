
/+int main(){
	//float f = float.infinity;
	int i = 0;
	
	assert(0 == 0x80000000);
	return 0;
}+/

//int

/+string toEngNum(uint i){
	if(i>=1000) return toEngNum(i/1000)~" thousand"~(i%100?" "~toEngNum(i%1000):"");
}+/
/+import std.stdio;
import std.string, std.algorithm;

mixin template Mem(string s){
	enum _vars = s.split(",");
	static _lambda(string[] a){
		string[2][] r;
		foreach(x;a){
			auto y = a.split(" ");
			r~=cast(string[2])y;
		}
		return r;
	}
	enum _tn = _lambda(_vars);
	mixin(_vars.join(";")~";");
	
}

class Term{}
class Id: Term{mixin Mem!q{string name};}
class Ap: Term{mixin Mem!q{Term term1,Term term2};}
class Lam: Term{mixin Mem!q{string var,Term term};}



void main(){
	
}+/