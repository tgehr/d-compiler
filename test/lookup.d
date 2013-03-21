/+template TT(int i){
	alias Rest V;
	static if(i) alias TT!(0).V Rest;
	static if(i) enum thisisone=true;
}

pragma(msg, TT!(0).V);
pragma(msg, TT!(1).V);

template SS(bool i){
	static if(i) alias int V;
	alias V A;
}

pragma(msg, SS!1.V);
pragma(msg, SS!(0).A);
+/

alias QQ.x a;
alias QQ.y b;

struct QQ{
	int x=2,y=3;
	void foo(){
		a = b;
	}
}

struct WW{
	void foo(){
		a=2;
	}
}

immutable foo = 2; 
//pragma(msg, a);

template TypeTuple(T...){ alias T TypeTuple;}

alias TypeTuple!(QQ.x, QQ.y) QQs;

pragma(msg, QQs);