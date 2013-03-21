// Written in the D programming language.

import std.stdio, std.conv;
import std.algorithm, std.math;

alias ValueRange!32 IntRange;
alias ValueRange!64 LongRange;

struct ValueRange(int size) if(size==32||size==64){
	static if(size==32){
		private alias uint T;
		private alias  int S;
	}else static if(size==64){
		private alias ulong T;
		private alias  long S;
	}
	private alias ValueRange R;

	T min, max;
	bool signed;
	invariant(){assert(signed&&cast(S)min<=cast(S)max||!signed&&min<=max);}

	string toString(){return signed?text(cast(S)min,"..",cast(S)max):text(min,"..",max);}

	bool contains(R rhs){
		if(signed){
			if(!rhs.signed) rhs = rhs.toSigned();
			return cast(S)min<=cast(S)rhs.min && cast(S)max>=cast(S)rhs.max;
		}else{
			if(rhs.signed) rhs = rhs.toUnsigned();
			return min<=rhs.min && max>=rhs.max;
		}
	}

	bool overlaps(R rhs){
		if(signed){
			if(!rhs.signed) rhs = rhs.toSigned();
			return cast(S)max>=cast(S)rhs.min && cast(S)rhs.max>=cast(S)min;
		}else{
			if(rhs.signed) rhs = rhs.toUnsigned();
			return max>=rhs.min && rhs.max>=min;
		}
	}

	bool gr(R rhs)in{assert(signed == rhs.signed);}body{
		if(signed) return cast(S)min>cast(S)rhs.max;
		return min>rhs.max;
	}
	bool geq(R rhs)in{assert(signed == rhs.signed);}body{
		if(signed) return cast(S)min>=cast(S)rhs.max;
		return min>=rhs.max;
	}
	bool le(R rhs)in{assert(signed == rhs.signed);}body{
		if(signed) return cast(S)max<cast(S)rhs.min;
		return max<rhs.min;
	}
	bool leq(R rhs)in{assert(signed == rhs.signed);}body{
		if(signed) return cast(S)max<=cast(S)rhs.min;
		return max<=rhs.min;
	}

	static R full(bool signed){return signed?R(S.min,S.max,true):R(T.min,T.max,false);}
	R toSigned(){
		if(signed) return this;
		if(cast(S)min<=cast(S)max) return R(min, max, true);
		return full(true);
	}
	R toUnsigned(){
		if(!signed) return this;
		if(min<=max) return R(min, max, false);
		return full(false);
	}
	R getAbs(){
		if(!signed) return this;
		if(cast(S)(min^max)>=0) return max<0?-this:this;
		return R(0,.max(abs(min),max),true);
	}
	R merge(R rhs)in{assert(signed==rhs.signed);}body{
		if(!signed) return R(.min(min, rhs.min), .max(max, rhs.max), 0);
		return R(.min(cast(S)min, cast(S)rhs.min), .max(cast(S)max, cast(S)rhs.max), 1);
	}
	ValueRange!32 narrow(bool sign, int bits)in{assert(0<bits && bits<=32 && bits<size);}body{
		T mask = (cast(T)1<<bits)-1;
		alias ValueRange!32 R;
		static if(size == 32){
			if(!sign) return (this&R(cast(uint)mask,cast(uint)mask,signed)).toSigned();
		}else if(!sign){
			auto r = (this&ValueRange(mask,mask,signed));
			if(bits<32) r=r.toSigned();
			else r=r.toUnsigned();
			return R(cast(uint)r.min, cast(uint)r.max, r.signed);
		}
		T diff = min^max;
		T s = 1<<bits-1;
		assert(diff>max || !(diff&s) || !(min&s) && max&s);
		if(diff>mask || diff&s) return R(cast(uint)-s, cast(uint)s-1, true);
		diff|=diff>>1; diff|=diff>>2; diff|=diff>>4; diff|=diff>>8;
		static if(is(T==long)) diff|=diff>>16;
		T nmin = min&~diff&mask, nmax=max&mask;
		if(nmin&s) nmin |= ~(s-1); if(nmax&s) nmax |= ~(s-1); // sign extend
		return R(cast(uint)nmin, cast(uint)nmax, true);
	}

	R opUnary(string op:"~")(){return R(~max,~min,signed);}
	R opUnary(string op:"-")(){return ~this+R(1,1,signed);}
	
	R opBinary(string op:"^")(R rhs)in{assert(signed==rhs.signed);}body{
		// TODO: build dedicated logic to make this more efficient
		return this&~rhs|~this&rhs;
	}

	R opBinary(string op:"&")(R rhs)in{assert(signed==rhs.signed);}body{
		//if(!signed) return R(minAnd(this,rhs),maxAnd(this,rhs),signed);
		// unsigned or identical sign bits:
		if(!signed || (cast(S)(min^max)>=0 && cast(S)(rhs.min^rhs.max)>=0)){
			return R(minAnd(this,rhs),maxAnd(this,rhs),signed);
		}
		auto l = this, r = rhs;
		S x, y;
		// both intervals span [-1,0]
		if(cast(S)(l.min^l.max)<0 && cast(S)(r.min^r.max)<0){
			// cannot be larger than either l.max or r.max, set the other one to -1
			y=.max(l.max,r.max);
			// only negative numbers for minimum
			l.max=-1; r.max=-1;
			x=minAnd(l,r);
		}else{ // only one interval spans [-1,0]
			if(cast(S)(l.min^l.max)<0) swap(l,r); // r spans [-1,0]
			x = .min(cast(S)minAnd(l,R(r.min, -1, true)), cast(S)minAnd(l,R(0, r.max, true)));
			y = .max(cast(S)maxAnd(l,R(r.min, -1, true)), cast(S)maxAnd(l,R(0, r.max, true)));

		}
		return R(x, y, signed);
	}

	R opBinary(string op:"|")(R rhs)in{assert(signed==rhs.signed);}body{
		// unsigned or identical sign bits:
		if(!signed || (cast(S)(min^max)>=0 && cast(S)(rhs.min^rhs.max)>=0)){
			return R(minOr(this,rhs), maxOr(this,rhs),signed);
		}
		auto l = this, r = rhs;
		S x, y;
		// both intervals span [-1,0]
		if(cast(S)(l.min^l.max)<0 && cast(S)(r.min^r.max)<0){
			// cannot be smaller than either l.min or r.min, set the other one to 0
			x = .min(l.min,r.min);
			// no negative numbers for maximum.
			// TODO: there certainly is a more efficient way to handle this
			l.min = r.min = 0;
			y=maxOr(l,r);
		}else{ // only one interval spans [-1,0]
			if(cast(S)(l.min^l.max)<0) swap(l,r); // r spans [-1,0]
			x = .min(cast(S)minOr(l,R(r.min, -1, true)), cast(S)minOr(l,R(0, r.max, true)));
			y = .max(cast(S)maxOr(l,R(r.min, -1, true)), cast(S)maxOr(l,R(0, r.max, true)));
		}
		return R(x, y, signed);
	}
	R opBinary(string op:"+")(R rhs)in{assert(signed==rhs.signed);}body{
		R r;
		if(!signed){
			if(max>T.max-rhs.max && min<=T.max-rhs.min) return full(false);
			return R(min+rhs.min, max+rhs.max, false);
		}else{
			S x, y;
			bool
				mino = cast(S)min>0 && cast(S)rhs.min>0 && cast(S)min>S.max-cast(S)rhs.min, // min+rhs.min overflows
				maxo = cast(S)max>0 && cast(S)rhs.max>0 && cast(S)max>S.max-cast(S)rhs.max, // max+rhs.max overflows
				minu = cast(S)min<0 && cast(S)rhs.min<0 && cast(S)min<S.min-cast(S)rhs.min, // min+rhs.min underflows
				maxu = cast(S)max<0 && cast(S)rhs.max<0 && cast(S)max<S.min-cast(S)rhs.max; // max+rhs.max underflows
			if(!mino && !maxo && !minu && !maxu || mino && maxo || minu && maxu) return R(min+rhs.min, max+rhs.max, true);
			return full(true);
		}
	}

	R opBinary(string op:"-")(R rhs)in{assert(signed==rhs.signed);}body{
		// return this+-rhs; // (this would work too)
		R r;
		if(!signed){
			if(min<rhs.max && max>=rhs.min) return full(false);
			return R(min-rhs.max, max-rhs.min, false);
		}else{
			S x, y;
			bool
				mino = cast(S)min>0 && cast(S)rhs.max<0 && cast(S)min>S.max+cast(S)rhs.max, // min-rhs.max overflows
				maxo = cast(S)max>0 && cast(S)rhs.min<0 && cast(S)max>S.max+cast(S)rhs.min, // max-rhs.min overflows
				minu = cast(S)min<0 && cast(S)rhs.max>0 && cast(S)min<S.min+cast(S)rhs.max, // min-rhs.max underflows
				maxu = cast(S)max<0 && cast(S)rhs.min>0 && cast(S)max<S.min+cast(S)rhs.min; // max-rhs.min underflows
			if(!mino && !maxo && !minu && !maxu || mino && maxo || minu && maxu) return R(min-rhs.max, max-rhs.min,true);
			return full(true);
		}
	}

	R opBinary(string op:"/")(R rhs)in{assert(signed==rhs.signed);}body{
		if(!rhs.max){
			if(!rhs.min) return full(signed); // ignore divide by zero
			rhs.max--;
		}else if(!rhs.min) rhs.min++;
		if(!signed){
			return R(min/rhs.max, max/rhs.min, false);
		}else{
			S x=S.max, y=S.min;
			if(cast(S)(rhs.min^rhs.max)<0){ // divisor spans [-1, 0, 1]
				x = .min(cast(S)min, -cast(S)min, -cast(S)max);
				y = .max(cast(S)max, -cast(S)max, -cast(S)min);
			}else{
				// TODO: a few branches may be more efficient
				S a = cast(S)min/cast(S)rhs.min,
				  b = cast(S)min/cast(S)rhs.max,
				  c = cast(S)max/cast(S)rhs.min,
				  d = cast(S)max/cast(S)rhs.max;
				x = .min(a,b,c,d);
				y = .max(a,b,c,d);
			}
			return R(x, y, true);
		}
	}

	// multiply is just a conservative approximation in case of overflow.
	R opBinary(string op:"*")(R rhs)in{assert(signed==rhs.signed);}body{
		if(!signed){
			if(max>T.max/rhs.max) return full(false);
			return R(min*rhs.min, max*rhs.max,false);
		}else{
			static S satMul(S a, S b, ref int n){
				if(!a||!b){n++; return 0;}
				if(a==S.min) return b>0 ? S.min : S.max;
				if(b==S.min) return a>0 ? S.min : S.max;
				bool s=(a<0)^(b<0);
				a=abs(a); b=abs(b);
				if(s && S.min/a==-b) return S.min;
				if(a>S.max/b) return s ? S.min : S.max;
				n++;
				return s ? -a*b : a*b;
			}
			int n=0;
			S a = satMul(min, rhs.min,n),
			  b = satMul(min, rhs.max,n),
			  c = satMul(max, rhs.min,n),
			  d = satMul(max, rhs.max,n);
			if(n!=4) return full(true);
			return R(.min(a,b,c,d), .max(a,b,c,d), true);
		}
	}

	R opBinary(string op:"^^")(R rhs)in{assert(signed==rhs.signed);}body{
		// TODO: implement
		assert(0);
	}
	R opBinary(string op:"<<")(R rhs){ // do not care about signedness of rhs!
		if(!signed){
			T diff = min^max;
			if(rhs.max>size-1) return full(false);
			if(rhs.min&&~((cast(T)1<<size-1>>rhs.min-1)-1)&diff){
				return R(0, ~cast(T)0<<rhs.min, false);
			}
			T nmin = min<<rhs.min, nmax = max<<rhs.min;
			for(auto i=rhs.min, xmin=nmin, xmax=nmax; i<=rhs.max; i++, xmin+=xmin, xmax+=xmax, diff+=diff){
				if(xmin<nmin) nmin=xmin;
				if(xmax>nmax) nmax=xmax;
				if(i<rhs.max&&diff&(cast(T)1<<size-1)){
					if(0<nmin) nmin=0;
					xmax=~((cast(T)1<<i-1)-1);
					if(xmax>nmax) nmax=xmax;
					break;
				}
			}
			return R(nmin, nmax, false);
		}
		T diff = min^max;
		if(cast(S)rhs.min<0||cast(S)rhs.max>size-1||rhs.min&&~((cast(T)1<<size-1>>rhs.min)-1)&diff) return full(true);
		S nmin = cast(S)(min<<rhs.min), nmax = cast(S)(max<<rhs.min);
		for(auto i=rhs.min, xmin=nmin, xmax=nmax; i<=rhs.max; i++, xmin+=xmin, xmax+=xmax, diff+=diff){
			if(xmin<nmin) nmin=xmin;
			if(xmax>nmax) nmax=xmax;
			if(diff&(cast(T)1<<size-1)){
				if(0<nmin) nmin=0;
				xmax=~((cast(T)1<<i-1)-1);
				if(xmax>nmax) nmax=xmax;
				break;
			}
		}
		return R(nmin, nmax, true);
	}
	R opBinary(string op:">>")(R rhs)in{assert(signed==rhs.signed);}body{
		if(!signed){
			if(rhs.max>size-1) return full(false);
			return R(min>>rhs.max,max>>rhs.min,false);
		}else if(cast(S)rhs.min<0||cast(S)rhs.max>size-1) return full(true);
		if(cast(S)max>0) return R(cast(S)min>>rhs.max,cast(S)max>>rhs.min,true);
		else return R(cast(S)max>>rhs.min,cast(S)min>>rhs.max,true);
	}
	R opBinary(string op:">>>")(R rhs)in{assert(signed==rhs.signed);}body{
		if(!signed){
			if(rhs.max>size-1) return full(false);
			return R(min>>rhs.max,max>>rhs.min,false);
		}else if(cast(S)rhs.min<0||cast(S)rhs.max>size-1) return full(true);
		if(cast(S)(min^max)<0)
			return R(rhs.min?0:min,rhs.max?cast(T)-1>>rhs.max:max,true);
		return R(min>>>rhs.max,max>>>rhs.min,true);
	}

	// modular arithmethics leads to hard problems => conservative approx.
	R opBinary(string op:"%")(R rhs)in{assert(signed==rhs.signed);}body{
		if(!rhs.max){
			if(!rhs.min) return full(signed); // ignore divide by zero
			rhs.max--;
		}else if(!rhs.min) rhs.min++;
		if(!signed){
			//if(max-min>=rhs.max) return R(0, rhs.max-1, false);
			if(max<rhs.max) return this;
			return R(0, rhs.max-1, false);
		}else{
			auto r = rhs.getAbs();
			r.min=0; r.max--;
			if(cast(S)min<0){
				if(cast(S)max<0) r=-r;
				else r.min=-r.max;
			}
			// mod cannot create a wider range
			if(cast(S)min<0 && cast(S)min>-cast(S)rhs.max){
				r.min=min;
				if(cast(S)max<0) r.max=max;
			}
			if(cast(S)max>=0 && cast(S)max<cast(S)rhs.max){
				r.max=max;
				if(cast(S)min>=0) r.max=max;				
			}
			return r;
		}
	}

private static:
	T maxOr(R lhs, R rhs){
		T x=0;
		auto xor=lhs.max^rhs.max;
		auto and=lhs.max&rhs.max;
		for(T d=1LU<<(8*T.sizeof-1);d;d>>=1){
			if(xor & d){
				x |= d;
				if(lhs.max&d){if(~lhs.min&d) lhs.min=0;}
				else{if(~rhs.min&d) rhs.min=0;}
			}else if(lhs.min&rhs.min&d){
			x |= d;
			}else if(and & d){
				x |= (d<<1)-1;
				break;
			}
		}
		return x;
	}
	
	T minOr(R lhs, R rhs){return ~maxAnd(~lhs,~rhs);}
	
	T maxAnd(R lhs, R rhs){
		T x=0;
		for(T d=1LU<<(8*T.sizeof-1);d;d>>=1){
			if(lhs.max&rhs.max&d){
				x |= d;
				if(~lhs.min&d) lhs.min=0;
				if(~rhs.min&d) rhs.min=0;
			}else if(~lhs.min & d && lhs.max & d){
				lhs.max |= d-1;
			}else if(~rhs.min & d && rhs.max & d){
				rhs.max |= d-1;
			}
		}
		return x;
	}
	
	T minAnd(R lhs, R rhs){return ~maxOr(~lhs,~rhs);}
	
	T maxXor(R lhs, R rhs){return maxOr(lhs&~rhs,~lhs&rhs);}
	T minXor(R lhs, R rhs){return minOr(lhs&~rhs,~lhs&rhs);}
}


import std.random;

unittest{
	alias int S;
	alias uint T;
	alias IntRange R;

	S a,b,c,d;
	for(int t;;t++){
		if(!(t%100)) writeln(t," tests passed!"); 
		//a=uniform(0U,T.max); b=a+uniform(0U,10000);
		//c=uniform(0U,T.max); d=c+uniform(0U,10000);
		a=uniform(-5000,5000); b=a+uniform(0U,10000);
		b=uniform(-5000,5000); d=c+uniform(0U,10000);

		if(a>b) swap(a,b);
		if(c>d) swap(c,d);
		//if(!~scanf("%d %d %d %d",&a,&b,&c,&d)) break;		
		//writefln("%.32b..%.32b\n%.32b..%.32b",a,b,c,d);
		S max=S.min, mi, mj;
		foreach(i;a..b+1)
			foreach(j;c..d+1)
				if((i^j)>max) max = i^j, mi=i, mj=j;
		//writeln(mi," ",mj);
		//writefln("%.32b\n%.32b",mi,mj);
		//writeln(maxAnd(R(a,b),R(c,d)));
		//writeln(a,"..",b," ",c,"..",d,": ",max);
		S omax=(R(a,b,true)^R(c,d,true)).max;
		//writeln(min," =? ",omin);
		if(max!=omax){writeln(a,"..",b," ",c,"..",d); writeln(max,"!=",omax); break;}
		//break;
	}
}
version(unittest){void main(){}}