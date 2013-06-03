
struct S{
	int a=2,b=3;
	S* next;
}

immutable s = {auto s=S();s.b=4;s.a++;s.next=new S();return s;}();
immutable t=s.next[0];

pragma(msg, s.b);


/+

class D{
	int x;
	D d = {auto x = new D(); return x;}();
	//int y = {return D.x;}(); // error
}

enum x = (()=>new D)();

pragma(msg, (()=>x.d.d.d.d)());

//pragma(msg, (()=>new D().d)());


class C{
	int x=2;
	C c=null;
	void mutate(){ x = 1; }
	auto toString(){ return x.to!string; }
}
immutable xx = (()=>cast(C)null)();
enum y = (()=>new C)();

pragma(msg, {auto z=y;z.mutate; return z;}().toString());
pragma(msg, y.toString());
static assert(y.toString()=="2");
static assert({auto z=y;z.mutate;return z;}().toString()=="1");

enum z = {auto z=y;z.mutate;return z;}();
static assert(z.toString()=="1");

class List(T){
	T value;
	bool empty = true; // TODO: implement comparison with null!
	List next = null;

	string toString(int x){
		if(!x) return "";
		List nix;
		return to!string(value)~(!empty?","~next.toString(x-1):"");
	}
}

auto buildList(){
	List!int r = null;
	for(int i=0;i<123;i++){
		auto l = new List!int();
		l.value = i;
		l.next = r;
		l.empty = i==0;
		r=l;
	}
	r.next.next.next=r;
	return r;
}

enum list = buildList();
pragma(msg, list.toString(40));



// +/
// +/
// +/
// +/
// +/
// +/
// +/
// +/


alias immutable(char)[] string;

auto to(T,S)(S arg)if(is(S==int)&&is(T==string)){
	string r="";
	if(!arg) return "0";
	bool n = arg<0;
	if(n) arg=-arg;
	while(arg) r=('0'+arg%10)~r, arg/=10;
	if(n) r="-"~r;
	return r;
}
