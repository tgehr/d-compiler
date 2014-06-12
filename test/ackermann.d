ulong ackermann(long n,long m){
	return n?m?ackermann(n-1,ackermann(n,m-1)):ackermann(n-1,1):m+1;
}
enum result = ackermann(3,7);
pragma(msg, result);
static assert(result==1021);

int ack(int n, int m){
	return n?ack(n-1,m?ack(n,m-1):1):m+1;
}
pragma(msg, ack(3,5));

int delegate(int m) ackc(int n){
	static int delegate(int m) iter(int delegate(int m) dg){
		int run(int n){ return n?dg(run(n-1)):dg(1); }
		return &run;
	}
	int delegate(int m) r=x=>x+1;
	for(int i=0;i<n;i++) r=iter(r);
	return r;
}
pragma(msg, ackc(3)(5));

int delegate(int m) ackc2(int n){
	int delegate(int m) r=x=>x+1;
	for(int i=0;i<n;i++){
		auto cr=r;
		int run(int n){ return n?cr(run(n-1)):cr(1); }
		r=&run;
	}
	return r;
}
//pragma(msg, ackc2(3)(5)); // TODO. (proper handling of closures in loops necessary.)
