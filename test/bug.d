
template MAlias(A,B){ alias A delegate(B) MAlias2; }

auto malias(A,B)(MAlias!(A,B).MAlias2 dg, B arg){ return dg(arg); }
pragma(msg, malias!(int,int)((int x)=>x,3));


int rec(T)(int x){
	if(!x) return 0;
	return 1+rec!T(x-1);
}
pragma(msg, rec!int(2));

int[] rec(int[] arg){
	if(!arg.length) return arg;
	return rec(arg[1..arg.length]);
}
enum unsorted = [1,2];

pragma(msg, rec(unsorted));
pragma(msg, rec(unsorted));



int[][] funny2(int[] a, int n){
	int*[] ptrs;
	int[][] r;
	for(int i=0;i<n;i++) a[i]--, r~=[0,0,0];
	for(int i=0;i<3*n;i+=3) ptrs~=[&r[i/3][0],&r[i/3][1],&r[i/3][2]];
	for(int i=0;i<3*n;i+=3) *ptrs[i+a[i/3]]=a[i/3]+1;

	return r;
}
pragma(msg, "funny2: ",funny2([1,2,3,2,3,1,3,1,2,3,2,1],12));

auto id(A)(A arg) => arg;

pragma(msg, id(1));



struct S{
	immutable int x=TT!().SS!().TT;
	template TT(){ template SS(){ alias x TT; } }
}

alias immutable(char)[] string;

auto testtemplatefunclit(alias fun)(){ return fun!int(2); }
pragma(msg, "testtemplatefunclit 3: ",testtemplatefunclit!(x=>2)());

/+
int k;

typeof(z) x;
typeof(x) y;
typeof(y) z;
+/

// +/