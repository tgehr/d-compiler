
struct Binary(int depth, int a, B) if(depth!=0){
	enum value = 1 +
		Binary!(depth-1, 0, Binary).value +
		Binary!(depth-1, 1, Binary).value;
}
struct Binary(int depth, int a, B) if(depth==0){
	enum value = 1+"";// TODO: show error message!
}
 
void main(){
	enum N = 13;
	enum instantiations = Binary!(N,0,int).value;
}