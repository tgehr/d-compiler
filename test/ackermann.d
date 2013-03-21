ulong ackermann(long n,long m){
	return n?m?ackermann(n-1,ackermann(n,m-1)):ackermann(n-1,1):m+1;
}
enum result = ackermann(3,7);
pragma(msg, result);
static assert(result==1021);
