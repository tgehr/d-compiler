template TT(string s){enum TT=s;}

void main(){
	mixin({
			string r;
			foreach(i;0..12000) r~=q{{enum x=TT!"";};};
			return r;
		}());
}
