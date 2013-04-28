// Written in the D programming language

module rope_; // underscore to not conflict with the eponymous function...

import std.random, std.range, std.algorithm;
import util;
// treap-based rope container

import hashtable; // TODO: is there a good way to separate those better?

auto rope(R)(R arg) if(isInputRange!R){ return arg.array.Rope!(ElementType!R); }
auto ropeCapture(T)(T[] arg){ return arg.Rope!T; } // transfers ownership!

auto hashRope(R)(R arg) if(isInputRange!R){ return arg.array.Rope!(ElementType!R,true); }
auto hashRopeCapture(T)(T[] arg){ return arg.Rope!(T,true); } // transfers ownership!

struct SegTree{//(T,alias combine){// forward reference bug
	alias AssocHash T;
	alias assocHashCombine combine;

	T[] t;
	@property size_t length(){ return t.length/2; }
	T get(size_t a, size_t b){
		T get(size_t i,size_t l,size_t r){
			if(a<=l&&r<=b) return t[i];
			auto mid=l+(r-l)/2;
			if(b<=mid) return get(2*i,l,mid);
			if(a>mid) return get(2*i+1,mid+1,r);
			return combine(get(2*i,l,mid),get(2*i+1,mid+1,r));
		}
		return get(1,0,length-1);
	}
}

private size_t roundToPwrTwo(size_t v){ for(size_t t=1;t;t<<=1) v|=v>>t; return v+1; }

auto buildSegTree(/+alias combine,+/R)(R rng){
	//alias ElementType!R T;
	alias AssocHash T;
	alias assocHashCombine combine;
	auto len = roundToPwrTwo(rng.length)*2;
	auto arr = new T[len];
	//copy(rng, arr[len/2..$]);
	foreach(i,x;rng) arr[len/2+i]=!x?0.assocHash():x.tmplArgToHash().assocHash();
	foreach_reverse(i;1..len/2) arr[i]=combine(arr[2*i],arr[2*i+1]);
	return SegTree/+!(T,combine)+/(arr);
}

struct SliceSegTree{//(T,alias combine){
	alias AssocHash T;
	alias assocHashCombine combine;

	SegTree/+!(T,combine)+/ tree;
	T value;
	size_t a,b;
	this(SegTree/+!(T,combine)+/ tree, size_t a, size_t b){
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

template Rope(T,bool withAssocHash=false){
	// interface (owns array; can exploit array opAssign)
	enum wah=withAssocHash;
	static if(wah) alias Seq!AssocHash Hash;
	else alias Seq!() Hash;
	struct Rope{
		static if(wah) private SliceSegTree/+!(AssocHash,assocHashCombine)+/* tree;
		private this(T[] array){
			if(array==[]) return;
			this.array = array;
			static if(wah){
				tree=new SliceSegTree/+!(AssocHash,assocHashCombine)+/(buildSegTree/+!(assocHashCombine)+/(array/+.map!(function(a)=>a.tmplArgToHash().assocHash())+/),0,array.length);
			}
		}

		static if(wah){
			size_t tmplArgToHash(){
				if(isArray()) return !tree?0:tree.value.toHash();
				return rope.hash.toHash();
			}
			private this(T[] array, SliceSegTree/+!(AssocHash,assocHashCombine)+/* tree){
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
				static if(wah) return new RopeImpl(array,tree);
				else return new RopeImpl(array);
			}
			return rope;
		}
		auto generalize(S)()@trusted if(is(S==class)&&is(T==class)&&is(T:S)){
			return cast(Rope!(S,wah))this;
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
		Rope opSlice(size_t a, size_t b)in{assert(a<=b && b<=length);}body{
			if(a==b) return Rope([]);
			if(isArray()) return Rope(array[a..b],(*tree)[a..b]);
			return Rope((*rope)[a..b]);
		}
		T opIndex(size_t i){
			if(isArray()) return array[i];
			return (*rope)[i];
		}
		Rope opIndexAssign(T t,size_t i){
			if(isArray()) array[i]=t;
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
	}

	// implementation (does not own array.)
	private struct RopeImpl{
		enum Tag : ubyte { Array, Concat, }
		Tag tag;
		static if(wah){
			AssocHash hash;
			SliceSegTree/+!(AssocHash,assocHashCombine)+/* tree;
		}
		this(RopeImpl* l, RopeImpl* r){
			tag=Tag.Concat;
			this.l=l, this.r=r;
			this.length = l.length+r.length;
			static if(wah) hash=assocHashCombine(l.hash,r.hash);
		}
		this(T[] array, SliceSegTree/+!(AssocHash,assocHashCombine)+/* tree){
			this.array=array;
			this.tree=tree;
			hash=tree.value;
		}
		union{
			T[] array;
			struct{
				size_t length;
				RopeImpl* l,r; // TODO: can be left unallocated if tag == Array
			}
			invariant(){ assert(array.length==length); }
		}
		RopeImpl* opBinary(string op:"~")(RopeImpl* rhs){
			if(tag==Tag.Array||rhs.tag==Tag.Array){
				// if(length+rhs.length<128) return new RopeImpl(array~rhs.array);
				return new RopeImpl(&this,rhs);
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
			return new RopeImpl((*l)[a..l.length],(*r)[0..b-l.length]);
		}

		int opApply(scope int delegate(T) dg){
			if(tag==Tag.Array){foreach(x;array) if(auto r=dg(x)) return r; return 0; }
			if(auto r=l.opApply(dg)) return r;
			return r.opApply(dg);
		}
		int opApply(scope int delegate(size_t,T) dg,size_t start=0){
			if(tag==Tag.Array){foreach(i,x;array) if(auto r=dg(start+i,x)) return r; return 0; }
			if(auto r=l.opApply(dg)) return r;
			return r.opApply(dg,l.length);
		}

		// in-place update.
		int unsafeByRef(scope int delegate(ref T) dg,size_t start=0){
			if(tag==Tag.Array){foreach(ref x;array) if(auto r=dg(x)) return r; return 0; }
			if(auto r=l.unsafeByRef(dg)) return r;
			return r.unsafeByRef(dg,l.length);
		}
		int unsafeByRef(scope int delegate(size_t,ref T) dg,size_t start=0){
			if(tag==Tag.Array){foreach(i,ref x;array) if(auto r=dg(start+i,x)) return r; return 0; }
			if(auto r=l.unsafeByRef(dg)) return r;
			return r.unsafeByRef(dg,l.length);			
		}
	}
}

// in-place update.
struct UnsafeByRef(T,bool wah){
	Rope!(T,wah) enc;
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
auto unsafeByRef(T,bool wah)(Rope!(T,wah) enc){ return UnsafeByRef!(T,wah)(enc); }

