
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


static assert(!is(typeof({
auto recc2(R)(R foo)=>recc2!R(foo);
pragma(msg, recc2!int);
})));


static assert(!is(typeof({
auto recc(R)(R foo)=>recc(foo);
pragma(msg, recc!int);
})));
