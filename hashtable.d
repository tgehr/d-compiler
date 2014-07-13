// built-in AAs as implemented by Digital Mars are unusable.

import std.typecons, std.typetuple;
import std.functional, std.algorithm;
import std.conv, std.array;

import std.random;

import util;

struct HashMap(K, V, alias eq_ , alias h_){
	alias binaryFun!eq_ eq;
	alias unaryFun!h_ h;
	struct E{ V v; K k; }
	alias E[] B;
	B[] es;
	size_t length;

	enum initialSize = 16;
	enum maxBucketSize = 2;
	enum limitfactor = 32;
	enum incrementFactor = 3;
	enum decrementFactor = 2;
	enum compactLimit = 2;


	private void initialize(){ es = new B[](initialSize); }
	int numrealloc;
	private void realloc(){
		auto ees = es;
		es = new B[](es.length*incrementFactor+uniform(0,incrementFactor));
		length = 0;
		foreach(b;ees) foreach(e;b) insert(e);
	}
	
	private void compact(){
		auto ees = es;
		es = new B[](es.length/decrementFactor);
		length = 0;
		foreach(b;ees) foreach(ref e;b) insert(e);
	}

	bool opBinaryRight(string op: "in")(K k){
		if(length){
			foreach(ref e; es[h(k)%$])
				if(eq(k, e.k)) return true;
		}
		return false;
	}

	V get(K k, lazy V alt){
		if(length){
			foreach(ref e; es[h(k)%$])
				if(eq(k, e.k)) return e.v;
		}
		return alt;
	}

	V opIndex(K k){
		return get(k,(assert(0, "key not found"),V.init));
	}

	void remove(K k){
		if(!es.length) return;
		auto b = &es[h(k)%$];
		foreach(ref e; *b)
			if(eq(k, e.k)){
				swap(e, (*b)[$-1]);
				length--;
				*b=(*b)[0..$-1];
				(*b).assumeSafeAppend();
				return;
			}
	}

	private void insert(E x) /+out{assert(x.k in this, text(es[h(x.k)%$]));}body+/{
		if(!es.length) initialize();
		auto hs=h(x.k);
		auto b = &es[hs%$];
		foreach(ref e; *b)
			if(eq(x.k, e.k)){
				e=x;
				return;
			}
		length++;
		*b~=x;
		if(b.length>maxBucketSize&&hs!=h((*b)[0].k)) realloc();
	}
	
	void opIndexAssign(V v, K k){
		insert(E(v,k));
	}
	void opIndexOpAssign(string op,W)(W w, K k){
		if(length){
			foreach(ref e; es[h(k)%$])
				if(eq(k, e.k)){
					mixin(`e.v `~op~`= w;`);
					return;
				}
		}
		V v; mixin(`v` ~op~`= w;`);
		insert(E(v,k));
	}

	int opApply(scope int delegate(ref V) dg){
		if(es.length>compactLimit*length) compact();
		foreach(b;es) foreach(e;b) if(auto r=dg(e.v)) return r;
		return 0;
	}
	int opApply(scope int delegate(ref K,ref V) dg){
		if(es.length>compactLimit*length) compact();
		foreach(b;es) foreach(e;b) if(auto r=dg(e.k, e.v)) return r;
		return 0;
	}


	void clear(){ es[]=B.init; length=0; }
	HashMap dup(){
		// return HashMap(es.map!(_=>_.dup).array, length); // fu
		auto oes = es.dup;
		foreach(ref e;oes) e=e.dup;
		return HashMap(oes, length);
	}

	static if(is(typeof(text(K.init,V.init))))
	string toString(){
		//return text("[",join(map!(_=>text(_.k,":",_.v))(filter!"a.e"(es)),", "),"]");// wtf
		auto r="[";
		foreach(b;es) foreach(e;b) r~=text(e.k,":",e.v)~", ";
		if(r.length>2) r=r[0..$-2];
		r.assumeSafeAppend();
		r~="]";
		return r;
	}
}

//template CuckooMap(K, V,T...){ alias V[K] CuckooMap; }
struct CuckooMap(K, V, alias eq_, alias h0_, alias h1_){
	//invariant(){ assert(es.length>0); }
	// static opCall(){ return CuckooMap(new E[](10)); } WTF?

	alias binaryFun!eq_ eq;
	alias unaryFun!h0_ h0;
	alias unaryFun!h1_ h1;
	alias Seq!(h0, h1) hs;

	struct E{ V v; K k; bool e; }
	private E[] es; // the only data members
	size_t length;
	
	private void initialize(){ es = new E[](8); }
	private void realloc(){
		auto ees = es;
		es = new E[](es.length*8+uniform(0,10));
		length = 0;
		foreach(e;ees) if(e.e) insert(e);
	}
	private void compact(){
		auto ees = es;
		es = new E[](es.length/4);
		length = 0;
		foreach(e;ees) if(e.e) insert(e);
	}

	bool opBinaryRight(string op: "in")(K k){
		if(es.length){
			foreach(h; hs){
				auto x=&es[h(k)%$];
				if(x.e && eq(k, x.k)) return true;
			}
		}
		return false;
	}

	V get(K k, lazy V alt){
		if(es.length){
			foreach(h; hs){
				auto x=&es[h(k)%$];
				if(x.e && eq(k, x.k)) return x.v;
			}
		}
		return alt;
	}

	V opIndex(K k){
		return get(k,(assert(0, "key not found"),V.init));
	}

	void remove(K k){
		if(!es.length) return;
		foreach(h; hs){
			auto x=&es[h(k)%$];
			if(x.e && eq(k, x.k)){ *x=E.init; length--; return;}
		}
	}

	private void insert(E x){
		if(!es.length) initialize();
		size_t t0,t1;
		alias Seq!(t0,t1) ts;

		foreach(i,ref t; ts){
			t=hs[i](x.k)%es.length;
			if(!es[t].e){
				es[t]=x; // TODO: keys should always be simple, or this is inefficient
				length++;
				return;
			}else if(eq(x.k, es[t].k)){
				es[t]=x;
				return;
			}
		}

		swap(x, es[t0]);
		size_t i = 0, p = t0;

		assert(x.e);
		do{
			// TODO: is caching the hashes more efficient?
			t0 = h0(x.k)%es.length, t1 = h1(x.k)%es.length;
			if(p==t0){swap(x, es[t1]); p=t1;}
			else{assert(p==t1); swap(x, es[t0]); p=t0;}
		}while(x.e && ++i<es.length);
		if(!x.e) { length++; if(length*2>es.length) realloc(); return; }
		assert(i==es.length);

		realloc();
		//dw(this," ",es.length," ", length," ",t0," ",t1);
/+		import expression;
		static if(is(typeof(x.k)==Expression[]))foreach(k, e; es) if(e.e){
				dw(k," ",e.k," ",h0(e.k)," ",h1(e.k)," ",
				   e.k.map!(_=>_.tmplArgToHash()));
		}
		dw();dw();+/

		insert(x);
	}
	
	void opIndexAssign(V v, K k){
		insert(E(v,k,true));
	}
	void opIndexOpAssign(string op,W)(W w, K k){
		if(!es.length) initialize();
		foreach(h; hs){
			auto x=&es[h(k)%$];
			if(x.e && eq(k, x.k)){ mixin( `x.v `~op~`= w;`); return;}
		}
		V v; mixin(`v` ~op~`= w;`);
		insert(E(v,k,true));
	}

	int opApply(scope int delegate(ref V) dg){
		if(es.length>4*length) compact();
		foreach(e; es) if(e.e) if(auto r=dg(e.v)) return r;
		return 0;
	}
	int opApply(scope int delegate(ref K,ref V) dg){
		if(es.length>4*length) compact();
		//writeln(es.length," ",length," ",es.length>4*length);
		
		foreach(e; es) if(e.e) if(auto r=dg(e.k, e.v)) return r;
		return 0;
	}


	void clear(){ es[]=E.init; length=0; }
	CuckooMap dup(){ return CuckooMap(es.dup, length); }

	static if(is(typeof(text(K.init,V.init))))
	string toString(){
		//return text("[",join(map!(_=>text(_.k,":",_.v))(filter!"a.e"(es)),", "),"]");// wtf
		auto r="[";
		foreach(e;es) if(e.e) r~=text(e.k,":",e.v)~", ";
		if(r.length>2) r=r[0..$-2];
		r.assumeSafeAppend();
		r~="]";
		return r;
	}
}

size_t identityHash0(Object o){
	return o.toHash()/16;
}
size_t identityHash1(Object o){
	return FNV(identityHash0(o));
}

private static if(size_t.sizeof==4) enum fnvp = 16777619U, fnvb = 2166136261U;
else static if(size_t.sizeof==8) enum fnvp = 1099511628211LU, fnvb = 14695981039346656037LU;

size_t FNV(size_t data, size_t start=fnvb){
	return (start^data)*fnvp;
}

size_t FNVred(R)(R i){
	if(!i.length) return fnvb;
	auto r = FNV(i[0].tmplArgToHash());
	foreach(x; i[1../*$*/i.length]) r = FNV(x.tmplArgToHash(), r); // TODO: update compiler, then dollar will work for ropes
	return r;
}


// (Dummy implementation!)
struct AssocHash{
	size_t value;
}
auto toHash(AssocHash h){ return h.value; }
auto assocHashCombine(AssocHash a, AssocHash b){ return AssocHash(a.value+b.value); }
int i;
auto assocHash(size_t data){ return AssocHash(data); }
private enum assocb=assocHash(0);
auto assocHashRed(R)(R i){ return reduce!assocHashCombine(assocb, i.map!assocHash); }

alias Seq!(identityHash0, identityHash1) identityHash;

version(none)
void main(){
	import std.math, std.stdio;
	enum x = sqrt(5.0);
	//CuckooMap!(int, double, (a,b)=>a==b, a=>a, a=>cast(int)(a*x)) map;
	CuckooMap!(int, double, (a,b)=>a==b, a=>a, a=>a) map;
	//double[int] map;

	map[0] = 2.0;
	map[1] = 9;
	map[9] = 3.0;
	map[2] = 4.1;
	map[1] = 3.2;
	map[11] = 12;
	map.remove(11);
	writeln(map);
}
/+
	debug V[K] check;
	debug bool disablei;
	debug invariant(){
		if(disablei) return;
		auto p = &disablei;
		*cast(bool*)p=true;
		scope(exit) *cast(bool*)p=false;
		foreach(k,v; cast()check) assert(k in cast()this && (cast()this)[k] == v);
		foreach(i,e;cast(E[])es) if(e.e){
			assert(e.k in cast()check && check[e.k]==e.v);
			assert(i==h0(e.k)%es.length||i==h1(e.k)%es.length);
		}
	}
+/
