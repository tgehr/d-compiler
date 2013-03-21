
struct Binary(int depth, int a, B) if(depth!=0){
	enum value = 1 +
		Binary!(depth-1, 0, Binary).value +
		Binary!(depth-1, 1, Binary).value;
}
struct Binary(int depth, int a, B) if(depth==0){
	enum int value = ""; // error
}
 
void main(){
	enum N = 7;
	enum instantiations = Binary!(N,0,int).value; // TODO: BUG: show error message
}