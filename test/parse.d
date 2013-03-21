//alias void foo(){};
bool match(Group!DataIndex matches[]);
void main(){
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
		try{
			try{

			}finally{

			}
		}
		catch(Exception e){
		}
	}
	
}