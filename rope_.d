// Written in the D programming language
// Author: Timon Gehr
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

module rope_; // underscore to not conflict with the eponymous function

import std.random, std.range, std.algorithm, std.conv;
import util;
// treap-based rope container

auto rope(R)(R arg) if(isInputRange!R){ return arg.array.Rope!(ElementType!R); }
auto ropeCapture(T)(T[] arg){ return arg.Rope!T; } // transfers ownership!

import expression;
auto toTemplArgs(R)(R arg) if(isInputRange!R){ return arg.array.Rope!(ElementType!R,TemplArgInfo); }
auto captureTemplArgs(T)(T[] arg){ return Rope!(T,TemplArgInfo)(arg); } // transfers ownership!

private size_t roundToPwrTwo(size_t v){ for(size_t t=1;t;t<<=1) v|=v>>t; return v+1; }

template Rope(T,S=void)if(is(S==void) || is(typeof((S a,S b)=>a.combine(b)))){
	enum segtree=!is(S==void);
	static if(segtree){
		struct SegTree{
			S[] t;
			@property size_t length(){ return t.length/2; }
			S get(size_t a, size_t b){
				S get(size_t i,size_t l,size_t r){
					if(a<=l&&r<=b) return t[i];
					auto mid=l+(r-l)/2;
					if(b<=mid) return get(2*i,l,mid);
					if(a>mid) return get(2*i+1,mid+1,r);
					return get(2*i,l,mid).combine(get(2*i+1,mid+1,r));
				}
				return get(1,0,length-1);
			}
		}
		auto buildSegTree(R)(R rng){
			alias TemplArgInfo S;
			auto len = roundToPwrTwo(rng.length);
			auto arr = new S[2*len];
			foreach(i,x;rng) arr[len+i]=S(x);
			foreach_reverse(i;1..len) arr[i]=arr[2*i].combine(arr[2*i+1]);
			return SegTree(arr);
		}
		struct SliceSegTree{
			SegTree tree;
			S value;
			size_t a,b;
			this(SegTree tree, size_t a, size_t b){
				this.tree=tree;
				this.a=a;
				this.b=b;
				value=tree.get(a,b);
			}
			@property size_t length(){ return b-a; }
			auto opSlice(size_t a, size_t b)in{assert(this.a+b<=this.b);}body{
				return new SliceSegTree(tree,this.a+a,this.a+b);
			}
		}
	}
	// interface (owns array; can exploit array opAssign)
	static if(segtree) alias Seq!S Info;
	else alias Seq!() Info;
	struct Rope{
		static if(segtree) private SliceSegTree* tree;
		private this(T[] array){
			if(array==[]) return;
			this.array = array;
			static if(segtree){
				tree=new SliceSegTree(buildSegTree(array/+.map!(function(a)=>a.tmplArgToHash().assocHash())+/),0,array.length);
			}
		}

		static if(segtree){
			@property value(){ return isArray()?tree?tree.value:S.init:rope.value; }
			private this(T[] array, SliceSegTree* tree){
				if(array==[]) return;
				this.array = array;
				this.tree = tree;
			}
		}

		private this(RopeImpl* rope){ this.rope = rope; }
		invariant(){ assert(cast(void*)rope is array.ptr); }
		private union{
			T[] array=void;
			struct{
				size_t padding=0;
				RopeImpl* rope=null;
			}
		}
		private @property bool isArray(){ return array.length || rope is null; }
		private RopeImpl* toImpl(){
			if(isArray()){
				static if(segtree) return new RopeImpl(array,tree);
				else return new RopeImpl(array);
			}
			return rope;
		}
		auto generalize(Q)()if(is(Q==class)&&is(T==class)&&is(T:Q)){
			return cast(Rope!(Q,S))this;
		}
		@property size_t length(){ return isArray() ? array.length : rope.length; }
		Rope opBinary(string op:"~")(Rope rhs){
			if(!length) return rhs;
			if(!rhs.length) return this;
			return Rope(*toImpl() ~ rhs.toImpl());
		}
		Rope opBinary(string op:"~")(T rhs){
			return this ~ Rope([rhs]);
		}
		Rope opBinaryRight(string op:"~")(T rhs){
			return Rope([rhs])~toImpl();
		}

		Rope opOpAssign(string op:"~")(Rope rhs){
			return this = this ~ rhs;
		}
		Rope opOpAssign(string op:"~")(T rhs){
			return this = this ~ rhs;
		}
		Rope opSlice(size_t a, size_t b)in{assert(a<=b && b<=length,text(this," ",a," ",b));}body{
			if(a==b) return Rope([]);
			if(isArray()) return Rope(array[a..b],(*tree)[a..b]);
			return Rope((*rope)[a..b]);
		}
		T opIndex(size_t i){
			if(isArray()) return array[i];
			return (*rope)[i];
		}
		Rope opIndexAssign(T t,size_t i){
			return this=this[0..i]~Rope([t])~this[i+1..length];
		}
		Rope opSliceAssign(Rope r, size_t a, size_t b){
			return this=this[0..a]~r~this[b..length]; // TODO: dollar
		}

		int opApply(scope int delegate(T) dg){
			if(isArray()){foreach(x;array) if(auto r=dg(x)) return r; return 0; }
			return rope.opApply(dg);
		}
		int opApply(scope int delegate(size_t,T) dg){
			if(isArray()){foreach(i,x;array) if(auto r=dg(i,x)) return r; return 0; }
			return rope.opApply(dg);
		}

		// TODO: these are slow:
		alias length opDollar;
		@property T front(){ return this[0]; }
		@property T back(){ return this[$-1]; }
		@property bool empty(){ return !length; }
		@property Rope save(){ return this; }
		void popFront(){ this=this[1..length]; }
		void popBack(){ this=this[0..length-1]; }
	}

	// implementation (does not own array.)
	private struct RopeImpl{
		enum Tag : ubyte { Array, Concat, }
		Tag tag;
		static if(segtree){
			S value;
			SliceSegTree* tree;
		}
		this(RopeImpl* l, RopeImpl* r){
			tag=Tag.Concat;
			this.l=l, this.r=r;
			this.length = l.length+r.length;
			static if(segtree) value=l.value.combine(r.value);
		}
		this(T[] array, SliceSegTree* tree){
			this.array=array;
			this.tree=tree;
			value=tree.value;
		}
		union{
			T[] array;
			struct{
				size_t length;
				RopeImpl* l,r; // TODO: can be left unallocated if tag == Array
			}
			invariant(){ assert(array.length==length); }
		}
		// TODO: use treap instead of random balancing
		RopeImpl* opBinary(string op:"~")(RopeImpl* rhs){
			if(tag==Tag.Array&&rhs.tag==Tag.Array){
				// TODO: coalesce?
				return new RopeImpl(&this,rhs);
			}
			if(tag==Tag.Array){
				if(uniform(0,2)) return new RopeImpl(&this,rhs);
				else return new RopeImpl(this~rhs.l,rhs.r);
			}
			if(rhs.tag==Tag.Array){
				if(uniform(0,2)) return new RopeImpl(l,*r~rhs);
				else return new RopeImpl(&this,rhs);
			}
			// TODO: refcount+in-place updates
			if(uniform(0,2)) return new RopeImpl(l,*r~rhs);
			else return new RopeImpl(this~rhs.l,rhs.r);
		}
		T opIndex(size_t i){
			if(tag==Tag.Array) return array[i];
			if(i<l.length) return (*l)[i];
			return (*r)[i-l.length];
		}
		RopeImpl* opSlice(size_t a, size_t b){
			if(a==0&&b==length) return &this;
			if(tag==Tag.Array) return new RopeImpl(array[a..b], (*tree)[a..b]);
			if(b<=l.length) return (*l)[a..b];
			if(l.length<=a) return (*r)[a-l.length..b-l.length];
			return *(*l)[a..l.length]~(*r)[0..b-l.length];
		}

		int opApply(scope int delegate(T) dg){
			if(tag==Tag.Array){foreach(x;array) if(auto r=dg(x)) return r; return 0; }
			if(auto r=l.opApply(dg)) return r;
			return r.opApply(dg);
		}
		int opApply(scope int delegate(size_t,T) dg,size_t start=0){
			if(tag==Tag.Array){foreach(i,x;array) if(auto r=dg(start+i,x)) return r; return 0; }
			if(auto r=l.opApply(dg,start)) return r;
			return r.opApply(dg,start+l.length);
		}

		// in-place update.
		int unsafeByRef(scope int delegate(ref T) dg){
			if(tag==Tag.Array){foreach(ref x;array) if(auto r=dg(x)) return r; return 0; }
			if(auto r=l.unsafeByRef(dg)) return r;
			return r.unsafeByRef(dg);
		}
		int unsafeByRef(scope int delegate(size_t,ref T) dg,size_t start=0){
			if(tag==Tag.Array){foreach(i,ref x;array) if(auto r=dg(start+i,x)) return r; return 0; }
			if(auto r=l.unsafeByRef(dg,start)) return r;
			return r.unsafeByRef(dg,start+l.length);			
		}
	}
}

// in-place update.
struct UnsafeByRef(T,S){
	Rope!(T,S) enc;
	int opApply(scope int delegate(size_t,ref T) dg){
		with(enc){
			if(isArray()){foreach(i,ref x;array) if(auto r=dg(i,x)) return r; return 0; }
			return rope.unsafeByRef(dg);
		}
	}
	int opApply(scope int delegate(ref T) dg){
		with(enc){
			if(isArray()){foreach(ref x;array) if(auto r=dg(x)) return r; return 0; }
			return rope.unsafeByRef(dg);
		}
	}
}
auto unsafeByRef(T,S)(Rope!(T,S) enc){ return UnsafeByRef!(T,S)(enc); }

