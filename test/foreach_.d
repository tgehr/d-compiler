struct RangeStaticForeach{
	static:
	struct Range{
		int x=0;
		this(int x){ this.x=x; } // // TODO: struct default constructors
		@property int front(){ return x; }
		void popFront(){ x += 2; }
		@property bool empty(){ return x>=10; }
	}
	static foreach(i;Range()){
		mixin(`enum x`~cast(char)('0'+i)~"=i;");
	}
	static foreach(i;0..5){
		static assert(mixin(`x`~cast(char)('0'+2*i))==2*i);
	}
	static foreach(i,k;Range()){ // TODO: error
		
	}
}

struct OpApplySingleStaticForeach{
	static:
	struct OpApply{
		int opApply(scope int delegate(int) dg){
			foreach(i;0..10) if(auto r=dg(i)) return r;
			return 0;
		}
	}
	static foreach(b;OpApply()){
		mixin(`enum x`~cast(char)('0'+b)~"=b;");
	}
	static foreach(i;0..10){
		static assert(mixin(`x`~cast(char)('0'+i))==i);
	}
}

struct TypeStaticForeach{
static:
	alias Seq(T...)=T;
	static foreach(i,alias T;Seq!(int,double,char)){
		mixin(`T x`~cast(char)('0'+i)~";");
	}
	pragma(msg, "x0: ",typeof(x0));
	pragma(msg, "x1: ",typeof(x1));
	pragma(msg, "x2: ",typeof(x2));
	static assert(is(typeof(x0)==int));
	static assert(is(typeof(x1)==double));
	static assert(is(typeof(x2)==char));
}

struct AliasForeach{
static:
	alias Seq(T...)=T;
	int[][] test(){
		int a,b,c;
		static foreach(x;Seq!(a,b,c,2)){
			static if(is(typeof({x=2;}))) x=2;
		}
		int x,y,z;
		static foreach(alias x;Seq!(x,y,z,2)){
			static if(is(typeof({x=2;}))) x=2;
		}
		int j,k,l;
		static foreach(ref x;Seq!(j,k,l,2)){ // error
			static if(is(typeof({x=2;}))) x=2;
		}
		return [[a,b,c],[x,y,z]];
	}
	static assert(test()==[[0,0,0],[2,2,2]]);
}

struct EnumForeach{
static:
	alias Seq(T...)=T;
	int a=1;
	int fun(){ return a; } // error
	int gun(){ return 2; }
	int hun(){ return 3;}
	auto test(){
		static foreach(enum x;Seq!(fun,gun,hun)){
		}
	}
}

struct TestUninterpretable{
static:
	alias Seq(T...)=T;
	auto test(){
		int k;
		static foreach(x;[k]){ // error
			
		}
		foreach(enum x;[1,2,3]){} // error // TODO: improve diagnostic
		foreach(enum x;Seq!(1,2,3)){} // ok
		static foreach(enum x;[1,2,3]){} //ok
	}
}

struct StaticForeachAmbiguity{
	static foreach(i;0..!is(typeof(x))) enum y=0; // error
	static foreach(i;0..!is(typeof(y))) enum x=0; // error
}

struct SeqForeachConstant{
static:
	alias Seq(T...)=T;
	void test(){
		foreach(x;Seq!1) x=2; // error
	}
	int test2(){
		int r=0;
		foreach(x;Seq!(1,2,3)){
			enum k=x;
			r+=k;
		}
		return r;
	}
	static assert(test2()==6);
}

struct SeqForeachBreakContinue{
static:
	alias Seq(T...)=T;
	int[] test(){
		int[] r;
		foreach(i;Seq!(0,1,2,3,4,5)){
			if(i==2) continue;
			if(i==4) break;
			r~=i;
		}
		return r;
	}
	static assert(test()==[0,1,3]);
}
struct TestStaticForeach{
static:
	int test(int x){
		int r=0;
		switch(x){
			static foreach(i;0..10){
				case i: r=i; break;
			}
			default: r=-1; break;
		}
		return r;
	}
	static foreach(i;0..15){
		pragma(msg, "test(",i,")→ ",test(i));
		static assert(test(i)==(i<10?i:-1));
	}

	enum x=[1,2,3];

	static foreach(i;x){
		pragma(msg, mixin("x"~cast(char)('0'+i)));
		pragma(msg,x);
	}

	static foreach(i;x){
		mixin("enum x"~cast(char)('0'+i)~"="~cast(char)('0'+i)~";");
	}

	int[] noBreakNoContinue(){
		int[] r;
		static foreach(i;0..1){
			if(i==3) continue; // error
			if(i==7) break; // error
			r~=i;
		}
		return r;
	}

	mixin("enum k=3;");
}

struct VarSeqForeach{
static:
	alias Seq(T...)=T;
	int[] test(){
		int x,y,z;
		foreach(i,ref k;Seq!(x,y,z))
			k=cast(int)i+1;
		return [x,y,z];
	}
	static assert(test()==[1,2,3]);

	int[] test2(){
		int x,y,z;
		foreach(ref i,k;Seq!(x,y,z)){ // error
			k=cast(int)i+1;
		}
		return [x,y,z];
	}
	static assert(test2()==[0,0,0]);
	int[][] test3(){
		auto a=[1,2,3],b=[1,2,3],c=[1,2,3];
		foreach(i;Seq!(a,b,c)){
			i=[10,10,10];
		}
		auto x=1,y=2,z=3;
		foreach(ref i;Seq!(x,y,z)){
			i=10;
		}
		auto l=1,m=2,n=3;
		foreach(i;Seq!(l,m,n)){
			i=10;
		}
		return [a,b,c,[x,y,z],[l,m,n]];
	}
	static assert(test3==[[1,2,3],[1,2,3],[1,2,3],[10,10,10],[1,2,3]]);
}

struct SeqForeach{
static:
	alias Seq(T...)=T;
	int test(){
		int r=0;
		foreach(immutable i,k;Seq!(1,2,3)){
			pragma(msg, typeof(i)," ",typeof(k));
			r += cast(int)i*k; // // TODO: DMD allows this without cast...
			//break;
		}
		return r;
	}
	pragma(msg, test());
}

struct FunPtrForeach{
	static int[] test(){
		int[] r;
		foreach(i;(int delegate(ref int) f){ // error
			foreach(i;0..10) if(auto r=f(i)) return r;
			return 0;
		}){
			//if(i==5) continue;
			//if(i==8) break;
			//r~=i;
		}
		return r;
	}
	static assert(test()==[0,1,2,3,4,6,7]);
}

struct DelegateForeach{
	static int[] test(){
		int[] r;
		foreach(i;delegate(int delegate(int) f){ // // TODO: report DMD bug (it does not work with DMD)
			foreach(i;0..10) if(auto r=f(i)) return r;
			return 0;
		}){
			if(i==5) continue;
			if(i==8) break;
			r~=i;
		}
		return r;
	}
	static assert(test()==[0,1,2,3,4,6,7]);

	static int[] test2(){
		int[] r;
		foreach_reverse(i;delegate(int delegate(int) f){ // error
			foreach(i;0..10) if(auto r=f(i)) return r;
			return 0;
		}){
			if(i==5) continue;
			if(i==8) break;
			r~=i;
		}
		return r;
	}
}

int[] opSlice(UFCSOpSlice x){ return [1,2,3]; }

struct UFCSOpSlice{
	static int test(){
		int r=0;
		foreach(x;UFCSOpSlice()) // TODO: error
			r+=x;
		return r;
	}
	pragma(msg, test());
}

bool empty(ref UFCSForeach x){ return x.x>10; }
int front(ref UFCSForeach x){ return x.x; }
void popFront(ref UFCSForeach x){ x.x += 1; }

struct UFCSForeach{
	int x;
	static int test(){
		int r=0;
		foreach(x;UFCSForeach()) // error
			r+=1;
		return r;
	}
	pragma(msg, test());
}

struct OnlyMembers{
	int opApply(scope int delegate(int) dg){
		return 0;
	}
	struct S{
		bool empty(){ return true; }
		int front(){ return 0; }
		void popFront();
	}
	void test(){
		foreach(x;S()){}
	}
}

struct SliceForeach2{
static:
	struct S{
		bool empty(){ return true; }
		int front(){ return 0; }
		void popFront(){}
		int opSlice(){return 0; }
	}
	void test(){
		foreach(x;S()){} // error
	}
	struct T{
		bool empty(){ return true; }
		int front(){ return 0; }
		void popFront(){}
		int opSlice;
		
	}
	void test2(){
		foreach(x;T()){} // ok
	}
}


struct SliceForeach{
static:
	struct S{
		int x=1;
		bool empty(){ return x>10; }
		int front(){ return x; }
		void popFront(){ x++; }
		S opSlice()(){ S r; r.x=x+1; return r; } // // TODO: default construction
	}
	int foo(){
		int r=0;
		foreach(x;S()) r+=x;
		return r;
	}
	static assert(foo()==54);
}

struct OpApplyIotaTests{
static:
	struct Iota{
		int s,e;
		this(int s,int e){ this.s=s; this.e=e; }
		int opApply(int delegate(int) dg){
			foreach(i;s..e) if(auto r=dg(i)){ return r; }
			return 0;
		}
		int opApplyReverse(int delegate(int) dg){
			foreach_reverse(i;s..e) if(auto r=dg(i)){ return r; }
			return 0;
		}
	}

	string testOpApplyReverse(){
		string r;
		foreach_reverse(i;Iota(0,10)){
			r~=cast(char)('0'+i);
		}
		return r;
	}
	static assert(testOpApplyReverse()=="9876543210");

	int bar(){
		int r=0;
		foreach(x;Iota(1,10)){
			r+=x;
		}
		return r;
	}
	static assert(bar()==45);

	auto testReturnFromOpApply(){
		foreach(x;Iota(0,10)) return "hi from within opApply";
		assert(0);
	}
	pragma(msg, testReturnFromOpApply());
	static assert(testReturnFromOpApply()=="hi from within opApply");

	void errorFoo(){
		foreach(char[] x;Iota(1,100)){} // TODO: improve diagnostic
		foreach(x,y;Iota(1,100)){}      // TODO: ditto
	}


	int labelShadowing(){
		int r=0;
		foreach(x;Iota(1,10)){
			r+=x;
			if(x==4) goto Lfoo;
		Lfoo:;	// TODO: this probably should be an error instead, but DMD allows this
		}
	Lfoo:
		return r;
	}
	static assert(labelShadowing()==45);
	pragma(msg, labelShadowing());


	immutable arr=[[[9]],[[4,5,2,3],[5,0,6],[0,1,2]],[[4,5,1,4],[6,1,6],[0,1,2]],[[0],[1],[2]],[[1],[2],[3]],[[7]],[[8]]];
	auto labeledContinue(){
		int[] r;
	L0:foreach(i;0..arr.length){
		L1:foreach(j;0..arr[i].length){
			L2:foreach(k;0..arr[i][j].length){
					switch(arr[i][j][k]){
					case 0: continue L0;
					case 1: continue L1;
					case 2: continue L2;
					case 7: break L0;
					case 8: return 8~r;
					case 9: goto Lninetynine;
					default: r~=arr[i][j][k];
					}
				}
				continue;
			Lninetynine:
				r~=99;
			}
		}
		return r;
	}
	pragma(msg, labeledContinue());
	static assert(labeledContinue()==[99,4,5,3,5,4,5,6,3]);

	auto opApplyLabeledContinue(){
		int[] r;
	L0:foreach(i;Iota(0,cast(int)arr.length)){
		L1:foreach(j;Iota(0,cast(int)arr[i].length)){
			L2:foreach(k;Iota(0,cast(int)arr[i][j].length)){
					switch(arr[i][j][k]){
					case 0: continue L0;
					case 1: continue L1;
					case 2: continue L2;
					case 7: break L0;
					case 8: return 8~r;
					case 9: goto Lninetynine;
					default: r~=arr[i][j][k];
					}
				}
				continue;
			Lninetynine:
				r~=99;
			}
		}
		return r;
	}
	pragma(msg, opApplyLabeledContinue());
	static assert(labeledContinue()==opApplyLabeledContinue());

	auto gotoBeforeLoop(int x){
		int[] r;
		goto Lfoo;
	Lbar: return 2;
	Lfoo:
		foreach(i;Iota(0,x)){
			goto Lbar;
		}
		return 0;
	}
	static assert(gotoBeforeLoop(1)==2&&gotoBeforeLoop(0)==0);

	int testGotoCaseGotoDefault(int x,int z){
		int y=1;
		switch(z){
		case -1:
			foreach(i;Iota(0,x)){	
				goto case;
			}
			return -1;
		case 0:
			y++;
			foreach(i;Iota(0,x)){
				y++;
				if(i>2) goto case 2;
			}
			goto case;
		case 2:
			foreach(i;Iota(0,x)){
				y++;
				if(i>1) goto default;
			}
		default:
			return x+y;
		}
	}
	pragma(msg, iota(-1,8).fmap!(function(i)=>iota(-1,8).fmap!(j=>testGotoCaseGotoDefault(i,j))));
	static assert(iota(-1,8).fmap!(function(i)=>iota(-1,8).fmap!(j=>testGotoCaseGotoDefault(i,j)))==[-1,1,0,0,0,0,0,0,0,-1,2,1,1,1,1,1,1,1,5,5,2,3,2,2,2,2,2,8,8,3,5,3,3,3,3,3,11,11,4,7,4,4,4,4,4,13,13,5,8,5,5,5,5,5,14,14,6,9,6,6,6,6,6,15,15,7,10,7,7,7,7,7,16,16,8,11,8,8,8,8,8]);
	pragma(msg, iota(-1,8).fmap!(i=>iota(-1,8).fmap!(j=>testGotoCaseGotoDefault(i,j))));

}
int[] iota(int x,int y){ int[] r; foreach(i;x..y) r~=i; return r; }
int[] fmap(alias a)(int[] b){ int[] r; foreach(x;b) r~=a(x); return r; } // TODO: fix 'cannot access this at nesting level' issue.

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

int[] foo(){
	int j=0;
	foreach(i;0..10){ j+=i; }
	assert(j==45);
	foreach(i;iota(10)){ j+=cast(int)i; }
	assert(j==90);
	int[] foo(size_t[] a){
		int[] r=[];
	Lstart:
		r~=1;
		a=a[1..$];
	Lforeach: foreach(x;apWrap(apWrap(apWrap(a)))){
			switch(x){
			case 1: goto Lstart;
			case 2: goto Lend;
			case 3: r~=1337~r;
			case 4: continue;
			case 5: r~=2; continue;
			case 6: break Lforeach;
			case 7: return r;
			default: break;
			}
			r~=3;
			if(x<1||x>6) break;
		}
		r~=4;
	Lend:
		return r;
	}
	return foo([1,3,4,1,3,1,3,1,3,4,5,6,3])~foo([4,5,6,2,1])~foo([4,3,4,5,5,5,7,1,2,3,4,5])~foo([1,5,0]);
}
static assert(foo()==[1,1337,1,1,1,1,1337,1,1337,1,1,1,1,1,1,1337,1,1337,1,1,1,1,1337,1,1337,1,1,1,1,1,1,1,1,1337,1,1337,1,1,1,1,1337,1,1337,1,1,1,1,1,1,1337,1,1337,1,1,1,1,1337,1,1337,1,1,1,1,1,1,1,1,2,4,1,2,4,1,1337,1,2,2,2,1,2,3,4]);
pragma(msg, "foo: ",foo());

alias size_t = typeof(int[].length);
alias string = immutable(char)[];
// +/
// +/
// +/
