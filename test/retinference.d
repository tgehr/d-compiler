
//auto bar(bool b){return foo(b)+"";}
auto bar(bool b){return foo(b);}
auto foo(bool b){
	//pragma(msg, typeof(foo(1)))foo(2);
	if(b) return 1;
	else{
		return bar(!b);
	}
}

void main(){
	int x;
	pragma(msg, typeof(bar(true)));
	auto y = {
		return 1.0;
	}();
	pragma(msg, typeof(y));
}

