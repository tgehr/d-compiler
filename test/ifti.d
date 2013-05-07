struct TestTypeConstructorMatching{
	static foo(T)(const(T)[] a){
		pragma(msg, T);
		return cast(T)a.length;
	}
	pragma(msg, foo([1,2,3]));
	static assert(is(typeof(foo([1,2,3]))==int));
	pragma(msg, foo(cast(const)cast(shared)[1,2,3]));
	static assert(is(typeof(foo(cast(const)cast(shared)[1,2,3]))==shared(int)));
	pragma(msg, foo(cast(shared)[1,2,3]));
	static assert(is(typeof(foo(cast(shared)[1,2,3]))==shared(int)));

	pragma(msg, foo(cast(immutable)[1,2,3]));
	static assert(is(typeof(foo(cast(immutable)[1,2,3]))==int));

	static bar(T)(inout(T)[] a){
		return cast(T)a.length;
	}
	static assert(is(typeof(bar(cast(immutable)[1,2,3]))==int));
	static assert(is(typeof(bar(cast(shared)[1,2,3]))==shared(int)));
	static assert(is(typeof(bar(cast(const)[1,2,3]))==int));
	static assert(is(typeof(bar(cast(const shared)[1,2,3]))==shared(int)));
	void iiiooo()inout{
		static assert(is(typeof(bar(cast(inout)[1,2,3]))==int));
		static assert(is(typeof(this.bar(cast(inout)[1,2,3]))==int));
		static assert(is(typeof(bar(cast(const)[1,2,3]))==int));
		static assert(is(typeof(bar(cast(const inout)[1,2,3]))==int));
		static assert(is(typeof(bar(cast(immutable)[1,2,3]))==int));
		static assert(is(typeof(bar(cast(shared)[1,2,3]))==shared(int)));
		static assert(is(typeof(bar(cast(const shared)[1,2,3]))==shared(int)));
		static assert(is(typeof(bar(cast(inout shared)[1,2,3]))==shared(int)));
		static assert(is(typeof(bar(cast(const inout shared)[1,2,3]))==shared(int)));
	}
	static baz(T)(T[] a, T[] b){ return cast(T)(a.length+b.length); }
	static assert(is(typeof(baz(cast(immutable)[1],cast(const)[2]))==const(int)));
	static assert(is(typeof(baz(cast(shared)[1],cast(immutable)[2]))==shared(const(int))));
	static assert(!is(typeof(baz(cast(const)[1],cast(shared)[2]))));


	// // TODO: the rules are not so clear for those cases:
	static qux1(T)(const(T)[] a, T[] b){ return cast(T)(a.length+b.length); }
	static assert(is(typeof(qux1(cast(immutable)[1],cast(immutable)[2]))==const(int)));
	static qux2(T)(T[] a, immutable(T)[] b){ return cast(T)(a.length+b.length); }
	static assert(is(typeof(qux2(cast(immutable)[1],cast(immutable)[2]))==const(int)));
}

auto indexOf3(alias a=(a,b)=>a==b, T, V...)(const(T)[] c, const V v){
	for(typeof(c.length) i=0;i<c.length;i++)
		if(a(c[i],v)) return i;
	return -1;
}

static assert(indexOf3("aba", cast(const)'b')==1);


auto indexOf2(alias a=(a,b)=>a==b, T...)(const(T)[] c, const T v){
	for(typeof(c.length) i=0;i<c.length;i++)
		if(c[i]==v) return i;
	return -1;
}
static assert(indexOf2("aba",'b')==1); // error




struct TestAdvancedTupleMatching{
	static foo(A,B,T...)(B z, T a, A b){pragma(msg, "foo: ",B," ",T," ",A);return 1;}
	pragma(msg, foo(1,3));
	pragma(msg, foo(1,2,3));
	pragma(msg, foo(1,2,3,4));

	static bar(A,AA,B,BB,T...)(B delegate(BB) z, T a, A delegate(AA) b){ return z(b(0)); }
	pragma(msg, bar((int x)=>x+1,(int y)=>y+2));
	pragma(msg, bar((int x)=>x+1,1,(int y)=>y+2));
	pragma(msg, bar((int x)=>x+1,1,2,(int y)=>y+2));

	static qux(A...,B,C...)(A a, B b,C c){
		pragma(msg, "qux: ",A," ",B," ",C);
		static assert(!c.length);
		return 333;
	}
	pragma(msg, qux(1));
	pragma(msg, qux(1,2,3,4));
	pragma(msg, qux(1,2));
	pragma(msg, qux(1,2,3));
}

struct TestVoidTemplateParam{
	auto foo(T...)(T a){pragma(msg, B," ",T," ",A);return 1;}
	pragma(msg, foo(cast(void)1)); // error
}

auto foo(A,B,T...)(B z, T a, A b){pragma(msg, B," ",T," ",A);return 1;}
pragma(msg, foo(1,2,3));


template ID(alias d){ alias d ID; }
template boz(int a){ alias ID!(x=>x+a) boz; }
template boo(){ alias boz!2 boo; }
static assert(boo(2)==4 && boo!()(3)==5);
pragma(msg, "callthroughalias: ", boo(2)+boo!()(3));

int ambigtmplfun(double a)(int b){ return 1; }
int ambigtmplfun(int a)(double b){ return 2; }

void main(){ pragma(msg, "ambigtmplfun: ", ambigtmplfun!1(1)); } // TODO: error


auto func(T)(T[2] arg){ return arg; }
static assert(is(typeof(func([1,2]))==int[2]));
auto deduceLengthFromLit(T,int n)(T[n] a){ return a; }
pragma(msg, typeof(deduceLengthFromLit([1,2,3]))); // TODO (?)



template G(S,T){ alias T delegate(S) G; }

C foo(A,B,C)(A x, G!(A,B) a, G!(B,C) b){
	pragma(msg, A," ",B," ",C);
	return b(a(x));
}
pragma(msg, foo(1, x=>2.0*x, x=>toString(cast(int)x)));

auto testTupleExpandIFTI(T...)(Seq!(int,int) a,T args){ return a[0]+args[0]; }
static assert(testTupleExpandIFTI(1,2,3,4)==4);

/+ TODO: match template instantiations +/
struct TestMatchTemplateInstantiations{
	struct A(T, int N){ }
	
	struct B(T, int N, int M){ alias B!(T, N, 1) C; }
	
	alias B!(int, 2, 2) b_t;
	
	static void foo(T, int N)(in A!(T,N), in B!(T,N,1)){}
	
	static void matchTemplateInstantiation(){
		A!(int,2) a;
		B!(int,2,1) b;
		foo(a, b); // TODO!
	}
}


struct DefaultParamsNo{
	auto exec(T)(T arg){
		pragma(msg, T);
		return arg(); // TODO: strip default params
	}
	pragma(msg, exec((int x=2)=>x));
	pragma(msg, exec((int x=3)=>x));
}


/+// TODO: should this work?
string myAssert(Args...)(lazy bool condition, lazy Args args, int line = 12, string file = "file.d"){
	if(!condition) return "Assertion failed @ "~file~":"~toString(line)~"\n"~args[0];
	return "";
}
pragma(msg, myAssert(false, "hello"));+/


/+// TODO: should this work?
bool queueDG(S,T,R=T)(S x, R delegate(T) delegate(S) dg, T y){
	return dg(x)(y);
}
pragma(msg, "queueDG: ", queueDG(2, a=>b=>b&&a==2,true));+/


template FooDg(Z,A,B...) { alias Delegate!(Z,A) delegate(B) FooDg; }

bool instFooDg(S,T,R=T)(S x, FooDg!(T,T,S) dg, T y){
	return dg(x)(y);
}
pragma(msg, "instFooDg: ", instFooDg(2, a=>b=>b&&a==2,true));

bool instFooDgTODO(S,T,R=T)(S x, FooDg!(R,T,S) dg, T y){
	return dg(x)(y);
}
pragma(msg, "instFooDgTODO: ", instFooDgTODO(2, a=>b=>b&&a==2,true)); // TODO!



template ElementType(T){ alias typeof({T t; return t[0];}()) ElementType; } // display e

template Seq(T...){ alias T Seq; }
template Delegate(R,T...){ alias Seq!(R, R)[1] delegate(Seq!T) Delegate; }

void transform(IR,OR,I=ElementType!IR,O)(IR input, OR output, scope Delegate!(O,I) dg){
//void transform(IR,OR,O)(IR input, OR output, scope O delegate(ElementType!IR) dg){
	for(auto i = input.length-input.length; i<input.length; i++)
		output[i] = dg(input[i]);
}

pragma(msg, "transform: ",{
	auto a = [1,2,3];
	auto r = [0,0,0];
	transform(a,r,a=>a+1);
	return r;
}());

template MAlias(A,B){ alias A delegate(B) MAlias; }

auto malias(A,B)(MAlias!(A,B) dg, B arg){ return dg(arg); }
pragma(msg, malias((int x)=>x,3));

auto combine(T)(T a, T b, T c){return [a,b,c];}

pragma(msg, "combine: ", combine([],[],[1,2,3]));
pragma(msg, "typeof(combine): ",typeof(combine([],[],[1,2,3])));


auto nomatch(T,S,R)(T t, S s, R r){ return t; }
pragma(msg, nomatch!int(1.0,2,"3")); // error



template tmpl(T){
	static if(is(T==double)){
		T[] tmpl(T arg){return [arg, 2*arg];}
	}else{
		T[] tmpl(T arg){return is(T==int)?[arg]:[arg,arg,2*arg];}
	}
	//alias int T;
}
pragma(msg, "tmpl!int: ",tmpl!int(2),"\ntmpl!float: ",tmpl!float(2),"\ntmpl!double",tmpl!double(2),"\ntmpl!real: ",tmpl!real(22));

auto potentiallyambiguous3(R,A...)(R delegate(A) a, R delegate(A) b){}
pragma(msg, potentiallyambiguous3!()(y=>2.0*y, (long z)=>z/2)); // error // TODO: should it work?

auto potentiallyambiguous2(R)(R delegate(int) a, R b){
	pragma(msg,"notambiguous21R: ", R);
	return true;
}
pragma(msg, "notambiguous2: ",potentiallyambiguous2!()(x=>1.0,1));


auto potentiallyambiguous(R)(R delegate(int) a, R delegate(int) b){
	pragma(msg,"notambiguousR: ", R);
	return true;
}
immutable string mxinx = "x";
pragma(msg, potentiallyambiguous!()(x=>toString(x), x=>mixin(mxinx))); // error. TODO: show it!
pragma(msg, "notambiguous: ",potentiallyambiguous!()(x=>1.0,x=>1.0L));

auto qux(S,T...)(S s, T arg){
	pragma(msg, S, " ", T);
	return s+arg.length;
}

//pragma(msg, qux!(int)(2,"1",1.0));

template deducetwotuples(R){
	R deducetwotuples(T1...,T2...)(R delegate(T1) dg1, R delegate(T2) dg2){
		pragma(msg, T1," ",T2);
		return dg1(StaticIota!(1,T1.length+1))~" "~dg2(StaticIota!(1,T2.length+1));
	}
}
pragma(msg, (deducetwotuples!string)!(int,double,float)((int x, double y, float z)=>toString(x), (int y, int x)=>toString(x)~" "~toString(y)));


template TypeTuple(T...){ alias T TypeTuple; }
template StaticIota(int a, int b) if(a<=b){
	static if(a==b) alias TypeTuple!() StaticIota;
	else alias TypeTuple!(a,StaticIota!(a+1,b)) StaticIota;
}

template StaticAll(string _pred, _A...){
	static if(!_A.length) enum StaticAll = true;
	else{
		alias _A[0] a;
		enum StaticAll = mixin(_pred) && StaticAll!(_pred,_A[1..$]);
	}
}

auto exec(R,A1,A...)(R delegate(A1,A) dg) if(is(A1==int) && StaticAll!("is(a:int)",A)){
	return dg(StaticIota!(1,A.length+2));
}

pragma(msg, exec!()((int x,short y)=>toString(x)~" "~toString(y)));
pragma(msg, exec!()((int x,short y,byte z)=>toString(x)~" "~toString(y)~" "~toString(z)));

pragma(msg, mixin(exec!()((int x,short y,byte z)=>toString(x)~"+"~toString(y)~"*"~toString(z))));

pragma(msg, exec!()((int x,int y,int z)=>toString(x)~" "~toString(y)~" "~toString(z)));


static assert(mixin(exec!()((int x,short y,byte z)=>toString(x)~"+"~toString(y)~"*"~toString(z)))==7);


//auto foo()(int a, int b){return a;}
//pragma(msg, foo!()(1));

auto inexistentparamtype(T...)(S arg){ }
auto inexistentparamtype(T...)(S arg) if(T.length){
	return arg.length;
}
pragma(msg, inexistentparamtype!()(2)); // error

bool all(alias a,T)(T[] r){
	pragma(msg, typeof(a!int));
	for(typeof(r.length) i=0;i<r.length;i++)
		if(!a!()(r[i])) return false;
	return true;
}

pragma(msg, "all: ",all!(x=>x&1)([1,3,4,5]));


//T identity(T)(const arg=2) {pragma(msg,T," ",typeof(arg)); return arg; }
T identity(T)(const T arg) {pragma(msg,T," ",typeof(arg)); return arg; }

template NotAFunctionTemplate(){void foo(){}}

//pragma(msg, NotAFunctionTemplate());


pragma(msg, identity!(ulong)(12));
pragma(msg, identity!()(cast(const)1)," ",identity!()("string")," ",identity!()(3.0));

T[] filter(T)(T[] a, bool delegate(T) f){
	T[] r;
	for(int i=0;i<a.length;i++) r~=f(a[i])?[a[i]]:[];
	return r;
}

pragma(msg, filter!()([1,2,3,4,5],x=>x&1));

S[] map(T,S)(T[] a, S delegate(T) f){
	S[] r;
	for(int i=0;i<a.length;i++) r~=f(a[i]);
	return r;
}

//pragma(msg, map!()([1,2,3,4,5],(float x)=>x+2.0));

immutable int y = 2;
pragma(msg, map!()([1,2,3],x=>x+y));

pragma(msg, map!()([1,2,3,4,5], x=>x+2));


R[] map2(T,S,R)(const(T)[] a, S delegate(T) f, R delegate(S) g){
	pragma(msg,"typeof(a): ",typeof(a));
	R[] r;
	for(int i=0;i<a.length;i++) r~=g(f(a[i]));
	return r;
}
immutable(float[]) fa = [1,2,3,4];
pragma(msg, map2!()(fa,x=>cast(int)x*1020304,x=>toString(x)));

/+ TODO: should this work?
int test(int delegate(int) dg){
	return dg(2);
}
int test2(alias a)(){ return test(&a); }

pragma(msg, test2!(x=>x)());+/

T idint(T: int)(T arg){ return arg;}
pragma(msg, "idint: ",idint!()(1.0)); // TODO: error
//T idfloat(T : float)(T arg){ return arg;}
//pragma(msg, idfloat!()(1.0));


// +/
alias immutable(char)[] string;

auto toString(int i){
	immutable(char)[] s;
	do s=(i%10+'0')~s, i/=10; while(i);
	return s;
}
