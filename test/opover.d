void testPostFix2(){
	static struct S{
		S opUnary(string op)(){ return this; }
	}
	S s;
	s++--; // TODO: better message
}

int testPostFix(){
	static struct S{
		int x;
		this(int x){ this.x=x; } // // TODO: default construction
		S opUnary(string op)(){mixin(op~"x;");return this;}
	}
	auto s=S(1);
	auto t=s++;
	assert(s.x==2&&t.x==1);
	auto u=s--;
	assert(s.x==1&&u.x==2);
	return s++.x;
}
pragma(msg,"testPostFix: ",testPostFix());
static assert(testPostFix()==1);

struct BinOpUFCS{
}
auto opBinary(string op)(BinOpUFCS lhs,BinOpUFCS rhs){
	//1=2;
	return 2;
}
auto opBinaryRight(string op)(BinOpUFCS rhs, BinOpUFCS lhs){
	//1=2;
	return 3;
}
auto opUnary(dstring op)(){
	return ""+1; // error
}
pragma(msg, BinOpUFCS()+BinOpUFCS()); // error
pragma(msg, ""+1); // error
pragma(msg, +BinOpUFCS());

struct UFCS{this(){}}
int opIndex(UFCS i, int x){
	return x;
}
string opBinary(string s)(UFCS a, UFCS b){
	return s;
}
pragma(msg, "UFCS.opIndex: ",UFCS()[3]);
pragma(msg, "UFCS.opBinary: ",UFCS()>>>UFCS());


struct S{
	int opIndex(int x)const{
		return x;
	}

	auto opIndex(T...)(T indices)const{
		return indices.length;
	}
	
	int[] opSlice(int a,int b)const{
		return [a,b];
	}

	string opUnary(string op)()const{
		return "opUnary: "~op;
	}
	string opBinary(string op)(const S rhs)const{
		return "opBinary: "~op;
	}
	string opOpAssign(string op)(const S rhs)const{
		return "opOpAssign: "~op;
	}
}
immutable S s;
struct T{}
immutable T t;

pragma(msg, "opIndex: ",s.opIndex(1,2,3));


int testIndex(int x){
	S s;
	return s[x];
}

pragma(msg, "opIndex: ",s[53]);
pragma(msg, t[2]); // error

pragma(msg, "opSlice: ",s[3..4]);
pragma(msg, t[3..4]); // error

pragma(msg, "opIndex: ",s[1,2,3]);
pragma(msg, t[1,2,3]); // error

//["-","+","~","*","++","--"]
pragma(msg, -s);
pragma(msg, +s);
pragma(msg, ~s);
pragma(msg, *s);
pragma(msg, ++s);
pragma(msg, --s);

pragma(msg, s+s);
pragma(msg, s-s);
pragma(msg, s*s);
pragma(msg, s/s);
pragma(msg, s%s);
pragma(msg, s^^s);
pragma(msg, s&s);
pragma(msg, s|s); 
pragma(msg, s^s);
pragma(msg, s<<s);
pragma(msg, s>>s);
pragma(msg, s>>>s);
pragma(msg, s~s);
pragma(msg, s in s);
pragma(msg, s !in s); // error

struct SupportNotIn{
	bool opBinaryRight(string op)(int l) if(op=="in"){
		return !l;
	}
}
pragma(msg, "opBinaryRight!\"!in\"(1):", 1 !in SupportNotIn());
pragma(msg, "opBinaryRight!\"!in\"(0):", 0 !in SupportNotIn());

pragma(msg, s+=s);
pragma(msg, s-=s);
pragma(msg, s*=s);
pragma(msg, s/=s);
pragma(msg, s%=s);
pragma(msg, s^^=s);
pragma(msg, s&=s);
pragma(msg, s|=s); 
pragma(msg, s^=s);
pragma(msg, s<<=s);
pragma(msg, s>>=s);
pragma(msg, s>>>s);
pragma(msg, s~s);

// +/
// +/
// +/

alias immutable(char)[] string;
alias immutable(dchar)[] dstring;
