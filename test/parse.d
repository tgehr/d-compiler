
class C: typeof(new C){} // error
class D: immutable(typeof(new D)){} // error
class E: int{} // error

immutable int foo(){}

void main(){
	auto fun = delegate immutable int delegate()()immutable=>()immutable{return 2;};
	//pragma(msg, typeof(fun));
}


//alias void foo(){};
bool match(int matches[]);

pragma(msg, typeof(&match));

void main(){
	auto d = new A().B(); // error

	//auto x = r"\ ";
	//import std.stdio;
	//static assert(2^^2^^3==2^^(2^^3));
	int[]x,y;
	//1 < 2 < 3;
	//@@=;

	static assert(!is(typeof({mixin(`auto dg = (int)@ => 2;`);})));

	auto dg = (int)@safe pure nothrow=> 2;
	//pragma(msg, is(typeof(true&true==true,true==true&true)));
	//int[] a;
	//foreach(x;a){}
	if(true){
		//if(false) if(false) if(false)x="";
		//else{}
	}
	static if (true){
		if (false)
			assert(3);
		else
			assert(4);
	}

	if(false)
		if(false)
			if(false){}
			else if(false){}// if(false){}
			else{}
	//x="";

	void dddx(){
		try{ // TODO
			try{

			}finally{

			}
		}
		catch(Exception e){
		}
	}
	
}

/+

auto tmpl(S...)(S sep) if((S.length==0){ } // TODO: better diagnostic

+/

// +/