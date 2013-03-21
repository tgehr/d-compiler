// built-in AAs as implemented by Digital Mars are unusable.

import std.typecons, std.typetuple;
import std.functional, std.algorithm;
import std.conv, std.array;
alias TypeTuple Seq;

struct CuckooMap(K, V, alias eq_, alias h0_, alias h1_){
	//invariant(){ assert(es.length>0); }
	// static opCall(){ return CuckooMap(new E[](10)); } WTF?

	alias binaryFun!eq_ eq;
	alias unaryFun!h0_ h0;
	alias unaryFun!h1_ h1;
	alias Seq!(h0, h1) hs;

	struct E{ V v; K k; bool e; }
	E[] es;
	
	private void initialize(){ es = new E[](8); }
	private void realloc(){ es.length *= 2; }

	V opIndex(K k){
		if(!es.length) initialize();
		foreach(h; hs){
			auto x=&es[h(k)%es.length];
			if(x.e && eq(k, x.k)) return x.v;
		}
		assert(0, "key not found");
	}

	void remove(K k){
		if(!es.length) initialize();
		foreach(h; hs){
			auto x=&es[h(k)%es.length];
			if(x.e && eq(k, x.k)){ *x=E.init; }
		}
	}

	private void insert(E x){
		if(!es.length) initialize();
		size_t t0,t1;
		alias Seq!(t0,t1) ts;

		foreach(i,t; ts){
			t=hs[i](x.k)%es.length;
			if(!es[t].e || eq(x.k, es[t].k)){
				es[t]=x; // TODO: keys should always be simple, or this is inefficient
				return;
			}
		}


		size_t i = 1, p = t0;

		swap(x, es[t0]);

		do{
			// TODO: is caching the hashes more efficient?
			t0 = h0(x.k)%es.length, t1=h1(x.k)%es.length;
			if(p==t0){swap(x, es[t1]); p=t1;}
			else{assert(p==t1); swap(x, es[t0]); p=t0;}
		}while(x.e && ++i<es.length);
		if(!x.e) return;
		realloc();
		insert(x);
	}

	
	void opIndexAssign(V v, K k){ insert(E(v,k,true)); }

	void clear(){ es[] = E.init; }

	static if(is(typeof(text(K.init,V.init))))
	string toString(){
		return text("[",join(map!(_=>text(_.k,":",_.v))(filter!"a.e"(es)),", "),"]");
	}
}

void main(){
	import std.math, std.stdio;
	enum x = sqrt(5.0);
	CuckooMap!(int, double, (a,b)=>a==b, a=>a, a=>cast(int)(a*x)) map;
	//double[int] map;

	map[0] = 2.0;
	map[9] = 9;
	map[1] = 3.0;
	map[2] = 4.1;
	map[1] = 3.2;
	map[11] = 12;
	map.remove(11);
	writeln(map);
}