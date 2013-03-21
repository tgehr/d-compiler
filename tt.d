//const(inout(shared(int))*)*
inout(int*)* foo(inout(int**) x){//, inout(int*)* y){
	//typeof(foo(x)) y = x;
	//foo(x);
	return x;
}
//auto bar(int x){return 1;}

//auto aa(int x){int y;return bb(1);y=2;}
//auto bb(int x){return aa(1);}

inout(float)* qux(inout(float)* x){return x;}

pragma(msg, typeof(x));
const int x;
//pragma(msg, typeof(x));

void main(){
	pragma(msg, typeof(0.0f&&{}()));
	pragma(msg, !(is(T==int))*2);
	pragma(msg, !false);
	
	char ä='ä';
	immutable(int)[] a;
	const(int)[] b;
	immutable c = a~b;

	int y;
	y = 1;
	pragma(__range,cast(byte)((y&252)^2)+1);
	pragma(msg,typeof(cast(byte)((y&252)^2)+1));
	ubyte[] x = [((y&252)^2)+1];
	ubyte[] yx = [-127+(y&1)];
	//ubyte[] x = [cast(byte)y,1];
	//pragma(__range, );
	int x = 2;
	//pragma(msg, typeof(x));

	immutable(int*)* a;
	//immutable(int)** b;
	//pragma(msg, typeof(foo(a)));
	
	int** xxxx = a;

	/*	for({	inout(float)* x = null;
			immutable(float)* y = cast(immutable(float)*)10;
		} x<y;x++){
		//pragma(msg, typeof(foo(x,y)));
		pragma(msg, typeof(qux(1?x:y)));
		}*/
}
