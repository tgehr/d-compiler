
void main(){
	int y;
	pragma(__range, ((y&252)^2)+1);
	ubyte[] x = [((y&252)^2)+1];
}