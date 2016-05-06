/+
struct S{
	this(int){}
	int opCmp(long rhs){return -1;}
	void opOpAssign(string op)(int i){l+=i;}
	ulong l;
	alias l this;
}+/


void main(){
	//int[][] x=[[],[],[]];
	immutable(char)[] xx;
	auto x=1+"";// error
	//foreach(double i,dchar j; x){
	/+foreach(double i, j; x){ // TODO
		//import std.stdio; writeln(j);
		//pragma(msg, typeof(j[i][0]+i));
	}+/
}