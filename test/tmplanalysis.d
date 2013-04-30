struct IndetCircErr{
	static match(alias a, alias b,T)(T[] t){
		if(t.length==0) return a();
		return b(t[0],t[1..$]);
	}
	
	static getLen(T)(T[] t){ return match!(()=>0,(x,xs)=>1+getLen(xs))(t); } // // TODO: this appears to sometimes fail
	
	pragma(msg, getLen([1,2,3,4]));
	static assert(getLen([1,2,3,4])==4);
	
	void main(){ }
}

template TTT(int i){
	int x = "";
}
static assert(!is(typeof(TTT!2)));


template FF(int i){
	static if(i==0) enum FF=TT!1;
	else enum FF=TT!0;
}

template TT(int i){
	static if(i==0) enum TT=FF!1;
	else enum TT=FF!0;
}
static assert(!is(typeof(TT!0)));
