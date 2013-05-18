
/+@property int bar()=>2;

struct PoorErrorMessage{
static foo(){ return bar(); // TODO: fix error message
}
pragma(msg, foo());
}+/


/+struct ReturnTypeLambdaParameterIfti{
	void foo(T)(T a, T b) { }
	void main() {
		foo((int a)=>a, b=>1.0); // foo!(double function(int))
	}
}+/

/+struct UndefinedIdentifierError{
	void foo(T)(T delegate(int) arg, T delegate(S) brg){} // TODO: better error message
	pragma(msg, foo(a=>1,a=>1.0));
}+/

/+
struct Foo(_T) {
	alias _T T;
}
void bar(FooT)(FooT foo, FooT.T x){ // TODO: silence
	pragma(msg, typeof(x));
}
void main() {
	Foo!int foo;
	bar(foo, 1);
}+/


/+
// TODO: make interpretation of partially analyzed functions work
int cdep(){ enum x=cdep2(); return x;}
int cdep2(){ return cdep(); }+/

/+// TODO: this must work! (need notion of potential indirections to support this)
pragma(msg, {
	string x = "123";
	auto y = ['1','2','3'];
	return x~=y;
}());
+/

/+// TODO: better error message
pragma(msg,{
		immutable (int)*[] x;
		int y = 2;
		x~= cast(float*)&y;
		return *x[0];
	}());
+/

/+
template asdf(){}
template Uninstantiable() if(asdf(2)){}
template Instantiable() if(Uninstantiable!()){}
pragma(msg, typeof(Instantiable!())); // show error!
+/

// enum returnVoidArray = delegate void[](){return [2];}();
// enum returnEmptyArray = ((int delegate(int))=>[])(x=>x);

/+
template Seq(T...){ alias T Seq; }
int aMatchError(R)(Seq!R delegate(int) dg){ return dg(2); }
pragma(msg, aMatchError(a=>a)); // TODO: remove reference to matcher type in error message
+/

/+
pragma(msg, ElementType!(int));
template ElementType(T=S,S=T){ alias typeof({T t; return t[0];}()) ElementType; } // display error message
+/

/+improve error messages!+/

/+template Cont(R,A){ alias R delegate(R delegate(A)) Cont; }

auto ret(R,A)(A arg){ return (R delegate(A) k)=>k(arg); }
auto cat(R,A,B)(Cont!(R,A) me, Cont!(R,B) delegate(A) f){
	return (R delegate(B) k)=>me(r=>f(r)(k));
}

auto callCC(B,R,A,T...)(Cont!(R,A) delegate(Cont!(R,B) delegate(A),T) f, T args){
	1=2;
	return (R delegate(A) k)=>f(a=>_=>k(a), args)(k);
}

auto testcallCC(){
	auto f(Cont!(int,int) delegate(int) cont, int x){
		return cat(x<3?cont(x):ret!int(1),a=>cont(x+a));
	}
	assert(callCC(&f,1)(x=>x)==1);
	assert(callCC(&f,3)(x=>x)==4);
	return callCC(&f,1)(x=>x)+callCC(&f,3)(x=>x);
}+/
