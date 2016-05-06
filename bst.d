// Written in the D programming language
// Author: Timon Gehr
// Licence: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

module bst;

import std.random, util;
import std.conv, std.typecons, std.algorithm;

alias TreapSet Set;
alias TreapMap Map;

// TODO: optimize

struct TreapSet(K)if(is(typeof((K a,K b)=>a<b))){
	private Impl* impl;
	private Impl* _begin;
	private Impl* _rbegin;
	private this(Impl* impl){ this.impl = impl; }

	this(this){
		TreapSet r;
		foreach(k;this)
			r.insert(k);
		this=move(r);
	}

	int opCmp()(TreapSet rhs){ return opCmp(rhs); }
	int opCmp()(ref TreapSet rhs){
		return cmp(this[], rhs[]);
	}
	bool opEquals()(TreapSet rhs){ return opEquals(rhs); }
	bool opEquals()(ref TreapSet rhs){
		return equal(this[], rhs[]);
	}
	
	// TODO: operators on sets
	// TODO: track size of set
/+
	TreapSet opBinary(string op: "&")(TreapSet rhs){ return this & rhs; }
	TreapSet opBinary(string op: "&")(ref TreapSet rhs){ } +/
	
	private struct Impl{
		K k; size_t weight;
		this(Impl* p, K k){
			this.p=p;
			this.k=k;
			weight=uniform!"[]"(0,size_t.max);
		}
		Impl* p, l, r;
	}

	struct Iterator{
		private Impl* c;
		private Impl* _rbegin;
		bool isValid(){ return !!_rbegin; }
		bool isEnd(){ return isValid() && !c; }

		private this(Impl* c, Impl* _rbegin){ this.c=c; this._rbegin=_rbegin; }
		
		ref Iterator opUnary(string op:"++")()in{assert(isValid()&&!isEnd());}body{
			if(c.r){
				for(c=c.r;c.l;c=c.l){}
				return this;
			}
			for(;;){
				if(!c.p){ c=null; return this; }
				if(c.p.l is c){ c=c.p; return this; }
				assert(c.p.r is c);
				c=c.p;
            }
		}

		ref Iterator opUnary(string op:"--")()in{assert(isValid());}body{
			if(!c){ c=_rbegin; return this; }
			if(c.l){
				for(c=c.l;c.r;c=c.r){}
				return this;
			}
			for(;;){
				if(!c.p){ c=_rbegin=null; return this; }
				if(c.p.r is c){ c=c.p; return this; }
				assert(c.p.l is c);
				c=c.p;
			}
		}

		@property K item()in{assert(isValid());}body{ return c.k; }
	}

	private Iterator iteratorAt(Impl* impl){ return Iterator(impl, _rbegin); }

	Iterator begin(){ return iteratorAt(_begin); }
	Iterator end(){ return iteratorAt(null); }

	struct Range{
		private Impl* _begin;
		private Impl* _end;
		private Impl* _rbegin;
		
		@property bool isValid(){ return _begin || !_rbegin; }
		@property bool empty()in{assert(isValid());}body{ return !_end; }

		// TODO: once property rewrites work properly, make sure to
		// check that the key still compares equal to itself after mutation
		@property ref K front()in{assert(isValid() && !empty);}body{
			return _begin.k;
		}

		void popFront()in{assert(isValid() && !empty);}body{
			if(_begin is _end){ _end = null; return; }
			auto it=Iterator(_begin, _rbegin);
			it++;
			this=Range(it.c, _end, _rbegin);
		}

		@property ref K back()in{assert(isValid());}body{
			return _end.k;
		}

		void popBack()in{assert(isValid() && !empty);}body{
			if(_begin is _end){ _end = null; return; }
			auto it=Iterator(_end, _rbegin);
			it--;
			this=Range(it.c, _end, _rbegin);
		}

		static if(is(typeof(to!string(k))))
		string toString(){
			if(!isValid()) return "<invalid range>";
			return chain("[",joiner(map!(to!string)(this),", "),"]").array;
		}
	}

	alias range opSlice;

	Range range(){ return Range(_begin, _rbegin, _rbegin); }

	Range upTo(L)(L k){
		auto i=largestLowerBound(k);
		return Range(i.isValid()?_begin:null,i.c,i._rbegin);
	}

	Range below(L)(L k){
		auto i=largestBelow(k);
		return range(i.isValid()?_begin:null,i.c,i._rbegin);
	}

	Range from(L)(L k){
		auto i = leastUpperBound(k);
		return Range(i.c, i._rbegin, i._rbegin);
	}

	Range above(L)(L k){
		auto i=smallestAbove(k);
		return Range(i.c, i._rbegin, i._rbegin);
	}

	private static void rotateR(ref Impl* impl)in{assert(impl&&impl.l);}body{
		// dw("rotating R along edge ",impl.l.k,"-",impl.k);
		/+
		    p              p
		    |              |
		   impl            l
		    /\            / \
		   l  r    ->    a impl
		  / \               / \
		 a   b             b   r
		+/
		auto p = impl.p;
		auto l = impl.l;
		auto b = l.r;
		l.r=impl;
		impl.p=l;
		impl.l=b;
		if(b) b.p=impl;
		l.p=p;
		if(p){
			if(p.l is impl) p.l=l;
			else{ assert(p.r is impl); p.r=l; }
		}
		impl=l;
	}

	private static void rotateL(ref Impl* impl)in{assert(impl&&impl.r);}body{
		// dw("rotating L along edge ",impl.r.k,"-",impl.k);
		/+
		     p              p
		     |              |
		     r             impl
		    / \            / \
		  impl b    <-    l   r
		  / \                / \
		 l   a              a   b
		+/
		auto p = impl.p;
		auto r = impl.r;
		auto a = r.l;
		r.l=impl;
		impl.p=r;
		impl.r=a;
		if(a) a.p=impl;
		r.p=p;
		if(p){
			if(p.l is impl) p.l=r;
			else{ assert(p.r is impl); p.r=r; }
		}
		impl=r;
	}

	bool insert(K k, bool replace=false){
		enum { Smallest=1, Largest=2 }
		bool go(Impl* p, ref Impl* impl, int flags){
			if(!impl){
				impl = new Impl(p, k);
				if(flags&Smallest) _begin=impl;
				if(flags&Largest) _rbegin=impl;
				return false;
			}
			if(k<impl.k){
				bool b=go(impl, impl.l, flags&~Largest);
				if(impl.l.weight<impl.weight) rotateR(impl);
				return b;
			}else if(impl.k<k){
				bool b=go(impl, impl.r, flags&~Smallest);
				if(impl.r.weight<impl.weight) rotateL(impl);
				return b;
			}else{
				if(replace) impl.k=k;
				return true;
			}
		}
		assert(!impl||!impl.p);
		return go(null, impl, Smallest|Largest);
	}

	bool erase(K k){
		bool go(bool check=true)(ref Impl* impl){
			static if(check){
				if(!impl) return false;
				if(k<impl.k) return go(impl.l);
				if(impl.k<k) return go(impl.r);
			}
			auto p=impl.p;
			void updateBounds(){
				if(impl is _begin){
					if(impl !is _rbegin){
						auto it=iteratorAt(_begin);
						it++;
						assert(!!it.isValid());
						_begin=it.c;
					}else _begin=_rbegin=null;
				}else if(impl is _rbegin){
					auto it=iteratorAt(_rbegin);
					it--;
					assert(!!it.isValid());
					_rbegin=it.c;				
				}
			}
			if(!impl.l){
				updateBounds();
				impl=impl.r;
				if(impl) impl.p=p;
				return true;
			}
			if(!impl.r){
				updateBounds();
				impl=impl.l;
				if(impl) impl.p=p;
				return true;
			}
			if(impl.l.weight<impl.r.weight){
				rotateR(impl);
				go!false(impl.r);
			}else{
				rotateL(impl);
				go!false(impl.l);
			}
			return true;
		}
		return go(impl);
	}

	Iterator find(L)(L k){
		Iterator go(Impl* impl){
			if(!impl) return Iterator.init;
			if(k<impl.k) return go(impl.l);
			else if(impl.k<k) return go(impl.r);
			else return Iterator(impl, _rbegin);
		}
		return go(impl);
	}

	private static string genbnd(string cmp, string dir){
		return mixin(X!q{ Iterator go(Impl* impl){
			if(!impl) return Iterator.init;
			if(@(cmp)) return go(impl.@(dir));
			auto r=go(impl.@(dir=="r"?"l":"r"));
			if(r.isValid()) return r;
			return iteratorAt(impl);
		} return go(impl); });
	}

	Iterator leastUpperBound(L)(L k){ mixin(genbnd(q{ impl.k<k }, "r")); }
	Iterator largestLowerBound(L)(L k)out(r){
		if((cast()r).isValid()){
			dw((cast()r).item," ",cast()k);
		}
		assert(!(cast()r).isValid()||(cast()r).item<=cast()k); }body{ mixin(genbnd(q{ k<impl.k }, "l")); }
	Iterator smallestAbove(L)(L k){ mixin(genbnd(q{ impl.k<=k }, "r")); }
	Iterator largestBelow(L)(L k){ mixin(genbnd(q{ k<=impl.k }, "l")); }
	
	bool has(K k){
		bool go(Impl* impl){
			if(!impl) return false;
			if(k<impl.k) return go(impl.l);
			else if(impl.k<k) return go(impl.r);
			else return true;
		}
		return go(impl);
	}

	static if(is(typeof(to!string(K.init)))) string toString(){
		return typeof(this).stringof~`(`~to!string(range)~`)`;
	}
}

mixin template SetToMap(alias Set){
//if(is(typeof((K a,K b)=>a<b)) && is(V)){// TODO: propose enhancement
	static assert(is(typeof((K a, K b)=>a<b)) && is(V));

	private static cmpK(ref K k1, ref K k2){
		static if(is(typeof(k.opCmp(r.k))==int)) return kv[0].opCmp(r.kv[0]);
		else return k1<k2?-1:k2<k1?1:0;		
	}

	private struct KCmp{
		K k;
		int opCmp(ref KV r){ return cmpK(k,r.kv[0]); }
	}
	private struct KV{
		Tuple!(K,V) kv;
		int opCmp(ref KV r){
			// TODO: propose opCmp and other operator member functions for built-in types
			//return k.opCmp(r.k);
			return cmpK(kv[0],r.kv[0]);
		}
		int opCmp(ref KCmp r){
			return cmpK(kv[0], r.k);
		}
		static if(is(typeof(to!string(kv[0])~to!string(kv[1]))==string))
			string toString(){ return to!string((&kv[0])[0..1])[1..$-1]~" : "~to!string((&kv[1])[0..1])[1..$-1]; } // TODO: fix
	}
	private Set!KV impl;
	static if(is(typeof(to!string(KV.kv[0])~to!string(KV.kv[1]))==string))
		string toString(){ return typeof(this).stringof~"("~to!string(impl.range)~")"; }
	else string toString(){ return typeof(this).stringof; }

	private Set!KV.Iterator find(K k){
		return impl.find(KCmp(k));
	}

	private ref V opIndexImpl(K k){
		auto f=find(k);
		assert(!f.isValid(), "key not present");
		return f.item.kv[1];
	}
	
	// TODO: how to accept both ref and non-ref delegates?
	auto ref T get(T)(scope T delegate(ref V) found, lazy T notFound){
		auto f=find(k);
		if(f.isValid()) return found(f.v.v);
		return notFound();
	}

	V get()(lazy V notFound){ // TODO: should not be a template
		auto f=find(k);
		if(f.isValid()) return f.item.kv[1];
		return notFound;
	}

	V opIndex(K k){ return opIndexImpl(k); }
		
	void opIndexAssign(V v, K k){
		impl.insert(KV(tuple(k,v)), true);
	}
	void opIndexOpAssign(string op)(V v, K k){
		mixin(`opIndexImpl(k) `~op~`=v`);
	}

	// TODO: we want those to be private, bug with protection
	/+private +/static ref Tuple!(K,V) _mapper(ref KV kv){ return kv.kv; }
	/+private +/static alias map!_mapper _mapIt;

	auto opSlice(){ return _mapIt(impl[]); }
	auto upTo(L)(L k){ return _mapIt(impl.upTo(KCmp(k))); }
	auto below(L)(L k){ return _mapIt(impl.below(KCmp(k))); }
	auto from(L)(L k){ return _mapIt(impl.from(KCmp(k))); }
	auto above(L)(L k){ return _mapIt(impl.above(KCmp(k))); }
}


struct TreapMap(K,V)if(is(typeof((K a,K b)=>a<b))){
	mixin SetToMap!TreapSet;
}

version(BST_MAIN){
	import std.stdio;
	import std.range, std.random;
	void main(){
		Set!int s;
		writeln(s);
		auto i=iota(30).array;
		randomShuffle(i);
		foreach(x;i){
			assert(!s.has(x));
			s.insert(x);
			assert(s.has(x));
		}
		writeln(s);
		randomShuffle(i);
		foreach(x;i[0..$/2]){
			assert(s.has(x));
			s.erase(x);
			assert(!s.has(x));
		}
		writeln(s);
		foreach(x;i){
			if(x<10) assert(s.has(x)==s.erase(x));
		}
		writeln(s);
		writeln(s.upTo(20));
		writeln(s.from(20));

	
		Map!(int, string) m;

		foreach(x;s.from(20)) m[x]=to!string(x);
		writeln(m); // TODO: report bug
		writeln(m.upTo(25));
		writeln(m.from(25));
		//writeln(s.largestBelow(25).item);
		writeln(s);
		writeln(s.smallestAbove(19).item);

		foreach(x;0..30) s.insert(x);
		auto t=s;
		assert(t==s);
		t.erase(15);
		assert(t>s);
		s.erase(15);
		assert(t==s);
		s.erase(14);
		assert(t<s);
	}
}
