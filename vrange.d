
import std.traits, std.algorithm;

struct ValueRange{
	union{long a; ulong ua;}
	union{long b; ulong ub;}
	bool signed;
	this(long a, long b){this.a=a; this.b=b; signed=true;}
	this(ulong ua, ulong ub){this.ua=ua; this.ub=ub; signed=false;}
	ValueRange widest(){return signed?ValueRange(long.min, long.max):ValueRange(ulong.min, ulong.max);}

	ValueRange normalize(){
		if(signed){
			if(a>b) return this=widest();
		}else
			if(ua>ub) return this=widest();
		return this;
	}

	ValueRange opBinary(string op: "+")(const ref ValueRange rhs)const{
		if(signed)
			return ValueRange(a+rhs.a, b+rhs.b).normalize();
		else
			return ValueRange(ua+rhs.ua, b+rhs.ub).normalize();
	}

	ValueRange opBinary(string op: "-")(const ref ValueRange rhs)const{
		if(signed)
			return ValueRange(a-rhs.b, b-rhs.a).normalize();
		else
			return ValueRange(ua-rhs.ub, b-rhs.ua).normalize();
	}

	ValueRange opBinary(string op: "*")(const ref ValueRange rhs)const{ // probably wrong
		return widest();
	}

}