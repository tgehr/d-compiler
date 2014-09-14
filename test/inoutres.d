struct InoutOpApply{
	struct S{
		int[] a;
		int opApply(scope int delegate(ref inout int) dg)inout{
			foreach(ref x;a) if(auto r=dg(x)) return r;
			return 0;
		}
	}
	
	int[] testInoutOpApply(){
		int[] r;
		//auto s=S([1,2,3]); // TODO
		S s; s.a=[1,2,3];
		foreach(ref x;s) x++;
		const s2=s;
		foreach(ref x;s2){
			r~=x;
			static assert(!is(typeof(x++)));
		}
		return r;
	}
	pragma(msg, testInoutOpApply());
}

struct HeadUnqualMatching{
	inout(int*) foo(inout int* a){ return a; }
	inout(int*) bar(inout(int*) a){ return a; }
	
	void main(){
		immutable int a;
		static assert(is(typeof(foo(&a))==immutable(int*)));
		static assert(is(typeof(bar(&a))==immutable(int*)));
	}
}

struct InoutScopes{
	int* coerce(inout(int)* x){
		inout(int)* screwUp(inout(int)*){ return x; };
		int* y;
		return coerce(y); // TODO: error
	}
}

struct DelegateInout{
	// // TODO: the spec does not actually indicate how this should work.
	inout(int)* foo(inout(int)* a, inout(int)* delegate(inout(int)*) dg){
		return dg(a);
	}
	inout(int)* bar(inout(int)* a, inout(int)* delegate(inout(int)*) dg){
		auto x = dg(a); // ok
		int* y;
		dg(y); // ok
		return x;
	}	
	void main(){
		immutable int a;
		assert(foo(&a,x=>x) is &a);
		static assert(is(typeof(foo(&a,x=>x))==immutable(int)*));
		assert(foo(&a,(immutable(int)* x)=>x) is &a);
		static assert(!is(typeof(foo(&a,(inout(int)* x)=>x))));
	}
}
/+
auto civc(const(inout(int[])) x){ return x; }
auto civc(const(int[]) x){ return x; }
auto civc(inout(int[]) x){ return x; }

pragma(msg, typeof(civc(cast(const)[1,2,3])));
// pragma(msg, typeof(civc(cast(immutable)[1,2,3]))); // TODO: should this work?
pragma(msg, typeof(((inout int)=>civc(cast(inout)[1,2,3]))(cast(immutable)0)));



inout(int) constinout(const inout int x){ return x; }
static assert(is(typeof(constinout(cast(const)2))==const(int))); // // TODO: ok this way?

inout(int) inoutfun(inout int x){
	static assert(is(typeof((delegate inout double (inout x)=>cast(double)x)(cast(shared const inout)2))==const(inout(double))));
	return x;
}


//inout(int)* 
inout(int)* foo(inout int x, inout(int)* y){return y;}
const(int)* foo(immutable int x, immutable(int)* y){return y;}

inout(int)* bar(inout int x, inout(int)* y){return y;}

void bar();
void main(){
	immutable int x;
	pragma(msg,typeof(foo(x,&x)));
	pragma(msg,typeof(bar(x,&x)));
}


inout(int) ov1(int delegate(int) dg,int x, inout int y){ return y; }
inout(int) ov1(double delegate(int) dg, inout int x, int y){ return x; }
static assert(is(typeof(ov1((x){
			static if(is(typeof(x)==int)) return 1.0;
			else return 1;
		},cast(immutable)2,3))==immutable(int)));

static assert(is(typeof(ov1((x){
			static if(is(typeof(x)==int)) return 1.0;
			else return 1;
		},cast(immutable)2,3))==immutable(int)));

inout(int) ov2(double delegate(int) dg, inout int x, int y){ return x; }
inout(int) ov2(int delegate(int) dg,int x, inout int y){ return y; }
static assert(is(typeof(ov2((x){
			static if(is(typeof(x)==int)) return 1.0;
			else return 1;
		},cast(immutable)2,3))==immutable(int)));

inout(int) ov3(int delegate(int) dg,int x, inout int y){ return y; }
inout(int) ov3(double delegate(int) dg, inout int x, int y){ return x; }
inout(int) ov3(double delegate(int) dg, inout int x, inout int y){ return x; }

pragma(msg,typeof(ov3((x){ // error (quality of match does not imply specialization)
			static if(is(typeof(x)==int)) return 1.0;
			else return 1;
		},cast(immutable)2,3)));

// +/
