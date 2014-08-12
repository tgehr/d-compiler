
bool checkSaveCall(){
	static struct S{
		@property int front(){ return 1; }
		bool empty=true;
		void popFront(){ empty=true; }
		S save(){ empty=false; return this; }
	}
	foreach(x;S()) return !!x;
	return false;
}
static assert(!checkSaveCall());

auto foreachArray(){
	auto arr=[5,2,3,4];
	int[] r=[];
	foreach(i,ref x;arr) r~=[x++,cast(int)i];
	foreach(x;r) r~=x;
	return r~arr;
}
pragma(msg, foreachArray());
static assert(foreachArray()==[5,0,2,1,3,2,4,3,5,0,2,1,3,2,4,3,6,3,4,5]);

int[] foreachReverseToIntMin(){
	int[] r=[];
	foreach_reverse(ref x;int.min..int.min+10){ // TODO
		r~=x;
		x--;
	}
	return r;
}
pragma(msg, foreachReverseToIntMin());

int[] frrngrvShdw(){
	int[] r=[];
	foreach_reverse(ref x;0..21){
		r~=x*x;
		//x-=2;
		int x=2; // error
	}
	for({int l=0,rr=21;}l<rr;){
		--rr;
		auto x=rr;
		r~=x*x;
		int l=0; // error
	}
	return r;
}

int[] frrngrv(){
	int[] r=[];
	foreach_reverse(ref x;0..21){
		r~=x*x;
	}
	for({int l=0,rr=21;}l<rr;){
		--rr;
		auto x=rr;
		r~=x*x;
	}
	return r;
}
enum e=frrngrv();
static assert(e[0..$/2]==e[$/2..$]);
pragma(msg, frrngrv());

int[] frrng(){
	int[] r=[];
   	foreach(ref x;0..20){
		r~=x*x;
		x+=2;
	}
	int y;
	foreach(x;0..10){
		if(x>0){ y=x; break; }
		x=123;
	}
	r~=y;
	return r;
}
pragma(msg, frrng());
static assert(frrng()==[0,9,36,81,144,225,324,1]);

struct Iota{
	size_t s,e;
	this(size_t s,size_t e){ this.s=s; this.e=e; } // // TODO: default constructors
	@property bool empty() => s>=e;
	@property size_t front() => s;
	void popFront(){ s++; }
}
auto iota(size_t s, size_t e){ return Iota(s,e); }
//auto iota(size_t e){ return iota(0,e); } // TODO
auto iota(size_t e){ return Iota(0,e); }

template map(alias a){
	struct Map(R){
		R r;
		this(R r){ this.r=r; }
		@property front(){ return a(r.front); }
		@property bool empty(){ return r.empty; }
		void popFront(){ r.popFront(); }
	}
	auto map(R)(R r){ return Map!R(r); }
}

auto array(R)(R r){
	typeof(r.front)[] a;
	foreach(x;r) a~=x;
	return a;
}
pragma(msg, iota(20).map!(a=>a*a).array);

struct ApWrap(T){
	T r;
	this(T r){ this.r=r; } // // TODO: default initializers
	int opApply(int delegate(size_t) dg){
		foreach(x;r) if(auto r=dg(x)) return r;
		return 0;
	}
}
auto apWrap(T)(T arg){ return ApWrap!T(arg); }

int foo(){
	int j=0;
	foreach(i;0..10){ j+=i; }
	assert(j==45);
	foreach(i;iota(10)){ j+=cast(int)i; }
	assert(j==90);
	int[] foo(size_t[] a){
		int[] r=[];
	Lstart:
		r~=1;
	Lforeach: foreach(x;apWrap(a)){ // TODO
			switch(x){
			case 1: goto Lstart;
			case 2: goto Lend;
			case 3: return r~1337;
			case 4: continue;
			case 5: r~=2; continue;
			case 6: break Lforeach;
			default: break;
			}
			r~=3;
			if(x<1||x>6) break;
		}
		r~=4;
	Lend:
		return r;
	}
	return 3;
}
static assert(foo()==3);


alias size_t = typeof(int[].length);

// +/
// +/
// +/
