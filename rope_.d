// Written in the D programming language

module rope_; // underscore to not conflict with the eponymous function...

import std.random, std.range;
// treap-based rope container

auto rope(R)(R arg) if(isInputRange!R){ return arg.array.Rope!(ElementType!R); }
auto ropeCapture(T)(T[] arg){ return arg.Rope!T; } // transfers ownership!

template Rope(T){
	// interface (owns array; can exploit array opAssign)
	struct Rope{
		private this(T[] array){ if(array==[]) return; this.array = array; }
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
			if(isArray()) return new RopeImpl(array);
			return rope;
		}
		Rope!S generalize(S)()@trusted if(is(S==class)&&is(T==class)&&is(T:S)){
			return cast(Rope!S)this;
		}
		@property size_t length(){ return isArray() ? array.length : rope.length; }
		Rope opBinary(string op:"~")(Rope rhs){
			return Rope(*toImpl() ~ rhs.toImpl());
		}
		Rope opBinary(string op:"~")(T rhs){
			return Rope(*toImpl() ~ new RopeImpl([rhs]));
		}
		Rope opBinaryRight(string op:"~")(T rhs){
			return Rope(*new RopeImpl([rhs])~toImpl());
		}

		Rope opOpAssign(string op:"~")(Rope rhs){
			if(isArray()&&rhs.isArray()) array~=rhs.array;
			return this = this ~ rhs;
		}
		Rope opOpAssign(string op:"~")(T rhs){
			if(isArray()) return Rope(array~=rhs);
			return this = this ~ rhs;
		}
		Rope opSlice(size_t a, size_t b)in{assert(a<=b && b<=length);}body{
			if(a==b) return Rope([]);
			if(isArray()) return Rope(array[a..b]);
			return Rope((*rope)[a..b]);
		}
		T opIndex(size_t i){
			if(isArray()) return array[i];
			return (*rope)[i];
		}
		Rope opIndexAssign(T t,size_t i){
			if(isArray()) array[i]=t;
			return this=this[0..i]~Rope(new RopeImpl([t]))~this[i+1..length];
		}
		Rope opSliceAssign(Rope r, size_t a, size_t b){
			if(isArray()&&r.isArray()){ // TODO: bound on lengths?
				array[a..b]=r.array[];
				return this;
			}
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
		this(RopeImpl* l, RopeImpl* r){
			tag=Tag.Concat;
			this.l=l, this.r=r;
			this.length = l.length+r.length;
		}
		this(T[] array){ this.array=array; }
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
				if(length+rhs.length<128) return new RopeImpl(array~rhs.array);
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
			if(tag==Tag.Array) return new RopeImpl(array[a..b]);
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
struct UnsafeByRef(T){
	Rope!T enc;
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
auto unsafeByRef(T)(Rope!T enc){ return UnsafeByRef!T(enc); }

