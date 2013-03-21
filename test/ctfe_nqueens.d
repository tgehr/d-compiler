alias immutable(char)[] string;

string nqueens(int n){
	string r;
	int[] board;
	board.length=n;

	void write(){}
	void write(T...)(T args){
		static if(is(T[0]==string)){ r~=args[0]; }
		else static if(is(T[0]==char)){ r~=args[0]; }
		else static if(is(T[0]==int)){ r~={string r; if(!args[0]) r="0"; while(args[0]){r=(args[0]%10+'0')~r; args[0]/=10; } return r;}(); }
		else static assert(0,"unsupported type");
		write(args[1..$]);
	}

	void writeln(T...)(T args){
		write(args,"\n");
	}
	
	bool unsafe(in int y){
		static assert(is(typeof(y)==const(int)));
		const x = board[y];
		for(int i=1;i<=y;i++){//foreach(i;1..y+1) {
			int t=board[y-i];
			if(t==x||t==x-i||t==x+i) return true;
		}
		return false;
	}
	
	int s = 1;
	void showBoard(){
		writeln("solution #", s++);
		for(auto y=0;y<n;y++){//foreach(y;0..n) {
			for(auto x=0;x<n;x++)//foreach(x;0..n)
				write(board[y]==x?'*':'.');
			writeln();
		}
		writeln();
	}
	
	void main(){
		int y = 0;
		board[0]--;
		
		do{	do board[y]++;
			while(board[y]<n && unsafe(y));
			
			if(board[y]<n) {
				if(y<n-1) board[++y]=-1;
				else showBoard();
			}else y--;
		}while(y>=0);
	}
	main();
	return r;
}

pragma(msg, nqueens(7));
