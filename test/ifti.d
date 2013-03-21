
bool all(alias a,T)(T[] r){
	pragma(msg, typeof(a!int));
	for(typeof(r.length) i=0;i<r.length;i++)
		if(!a!()(r[i])) return false;
	return true;
}

pragma(msg, "all: ",all!(x=>x&1)([1,3,4,5]));



template tmpl(T){
	static if(is(T==double)){
		T[] tmpl(T arg){return [arg, 2*arg];}
	}else{
		T[] tmpl(T arg){return is(T==int)?[arg]:[arg,arg,2*arg];}
	}
	//alias int T;
}
pragma(msg, tmpl!int(2),"\n",tmpl!float(2),"\n",tmpl!double(2),"\n",tmpl!real(22));


alias immutable(char)[] string;

//T identity(T)(const arg=2) {pragma(msg,T," ",typeof(arg)); return arg; }
T identity(T)(const T arg) {pragma(msg,T," ",typeof(arg)); return arg; }

template NotAFunctionTemplate(){void foo(){}}

//pragma(msg, NotAFunctionTemplate());


pragma(msg, identity!(ulong)(12));
pragma(msg, identity!()(cast(const)1)," ",identity!()("string")," ",identity!()(3.0));

T[] filter(T)(T[] a, bool delegate(T) f){
	T[] r;
	for(int i=0;i<a.length;i++) r~=f(a[i])?[a[i]]:[];
	return r;
}

pragma(msg, filter!()([1,2,3,4,5],x=>x&1));

S[] map(T,S)(T[] a, S delegate(T) f){
	S[] r;
	for(int i=0;i<a.length;i++) r~=f(a[i]);
	return r;
}

//pragma(msg, map!()([1,2,3,4,5],(float x)=>x+2.0));

immutable int y = 2;
pragma(msg, map!()([1,2,3],x=>x+y));

pragma(msg, map!()([1,2,3,4,5], x=>x+2));


R[] map2(T,S,R)(const(T)[] a, S delegate(T) f, R delegate(S) g){
	pragma(msg,"typeof(a): ",typeof(a));
	R[] r;
	for(int i=0;i<a.length;i++) r~=g(f(a[i]));
	return r;
}
immutable(float[]) fa = [1,2,3,4];
pragma(msg, map2!()(fa,x=>cast(int)x*1020304,x=>toString(x)));

auto toString(int i){
	immutable(char)[] s;
	do s=(i%10+'0')~s, i/=10; while(i);
	return s;
}


//T idint(T: int)(T arg){ return arg;}
//pragma(msg, idint!()(1.0); // error
//T idfloat(T : float)(T arg){ return arg;}
//pragma(msg, idfloat!()(1.0));


// +/
