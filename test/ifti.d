
T identity(T...)(T arg) if(is(T[0]==int)){ return arg; }


pragma(msg, identity!(int)(12));
//pragma(msg, identity(1)," ",identity("2")," ",identity(3.0));

T[] filter(T)(T[] a, bool delegate(T) f){
	T[] r;
	for(int i=0;i<a.length;i++) r~=f(a[i])?[a[i]]:[];
	return r;
}

pragma(msg, filter!int([1,2,3,4,5],x=>x&1));