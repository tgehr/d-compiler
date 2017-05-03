struct AliasSeqOf{
	static:
	alias Seq(T...)=T;
	
	auto iota(int a,int b){
		static struct Iota{
			int a,b;
			this(int a,int b){
				this.a=a;
				this.b=b;
			}
			bool empty(){
				return a>=b;
			}
			void popFront(){
			++a;
			}
			@property int front(){
				return a;
			}
		}
		return Iota(a,b);
	}
	
	auto rest(T)(T arg){
		arg.popFront();
		return arg;
	}
	
	template aliasSeqOf(alias x,T...){
		static if(x.empty) alias aliasSeqOf=T;
		else{
			enum front=x.front;
			alias aliasSeqOf=aliasSeqOf!(rest(x),T,front);
		}
	}	
	static assert(aliasSeqOf!(iota(0,10))==Seq!(0,1,2,3,4,5,6,7,8,9));
}

struct TestSeqAccessCheck2{
	static:
	alias Seq(T...)=T;
	struct S{
		Seq!int x;
		static void foo(int y){
			x,y=y; // ok
			x=Seq!y; // error
		}
		pragma(msg, typeof(x=x)); // ok
	}
	pragma(msg, typeof(S.x=S.x)); // ok
}

auto testSeqAccessCheck(){
	alias Seq(T...)=T;
	Seq!(int) tp;
	function(){return [tp];}(); // error
	function(){return tp;}(); // error
	return 0;
}

struct TestByRefSeq{
	static:
	ref Seq!(int, int) byrefseq(ref int x, ref int y){
		//pragma(msg, typeof(Seq!(x,y)));
		return Seq!(x, y);
	}
	auto fail(){
		int x,y;
		byrefseq(x,y)+=Seq!(2,3); // error // TODO: do we want to allow this?
	}
	auto test(){
		int x,y;
		byrefseq(x,y)=Seq!(3,4); // ok

		//return [x,y];
		byrefseq(x,y)[1]++;
		return [byrefseq(x,y)];
	}
	pragma(msg, test());
	static assert(test()==[3,5]);

	ref foo(ref int x, ref int y, int z){
		return Seq!(x,y);
	}
	void inc(T...)(ref T x)if(T.length==2){
		x[0]++;
		x[1]++;
	}
	auto fail2(){
		int a=-1,b=-1;
		inc(foo(Seq!(a,b,a)=Seq!(1,2,3))); // error
	}

	auto test2(bool x){
		int a,b;
		alias aba=Seq!(a,b,a);
		alias bab=Seq!(b,a,b);
		aba=Seq!(1,2,3);
		inc(foo(aba));
		auto incx(ref int u, ref int v){
			u+=v;
			v*=u;
		}
		incx((x?aba:bab)[0..2]);
		return [aba,x?foo(aba):foo(bab)];
	}
	static assert(test2(true)==[7,21,7,7,21]);
	pragma(msg, test2(true));
	static assert(test2(false)==[28,7,28,7,28]);
	pragma(msg, test2(false));

	struct Tuple(T...){
		int i=0;
		T expand;
		ref inc(){ i++; return this; }
	}

	auto test3(){
		Tuple!(int,int,int) t;
		t.expand[0]=1;
		t.expand[1]=2;
		t.expand[2]=3;
		auto u=t.inc().expand=Seq!(4,5,6);
		void multiply(ref int a, ref int b, ref int c){
			a*=2;
			b*=3;
			c*=4;
		}
		multiply(t.expand);
		return [t.i,t.expand,u];
	}
	pragma(msg, test3());
	static assert(test3()==[1,8,15,24,4,5,6]);

	auto ternarytest(bool x){
		int a,b,c;
		(2,x?Seq!(a,b):Seq!(b,c))=Seq!(1,2);
		return [a,b,c];
	}
	static assert(ternarytest(true)==[1,2,0]);
	static assert(ternarytest(false)==[0,1,2]);

	auto otherternarytest(bool x, bool y){
		int a,b,c,d,e;
		alias all=Seq!(a,b,c,d,e);
		alias ab=Seq!(a,b);
		alias cdex=Seq!(all[2..4],e,x);
		ref seq(T...)(ref T args){ return args; }
		x?y?Seq!(ab):seq(all[1..$-1])[0..2]:y?seq(cdex[0..2])[]:Seq!(d,e)=Seq!(1,2);
		return [all];
	}
	static assert(otherternarytest(true,true)==[1,2,0,0,0]);
	static assert(otherternarytest(true,false)==[0,1,2,0,0]);
	static assert(otherternarytest(false,true)==[0,0,1,2,0]);
	static assert(otherternarytest(false,false)==[0,0,0,1,2]);

}

struct TupleAndSeqExpansionTests{
	static:
	struct Tuple(T...){
		T expand;
	}

	auto test1(){
		Tuple!(int,double) t;
		t.expand[0]=2;
		t.expand[1]=4;
		Seq!(int,double) a=(()=>t.expand)();
		auto x = t.expand;
		auto b = x[1..2];
		static assert(is(typeof(b)==Seq!(double)));
		auto c = t.expand[1..2];
		a[0]++;
		return [t.expand[0],b[0],c[0],a,t.expand];
	}
	static assert(test1()==[2,4,4,3,4,2,4]);

	auto vdLeftover(){
		Tuple!() tp;
		int x;
		auto y = (x++,tp.expand);
		return x;
	}
	static assert(vdLeftover()==1);

	auto alLeftover(){
		Tuple!() tp;
		int x;
		int[][] y=[[(x++,tp.expand)],[x]];
		pragma(msg, typeof(y));
		return y;
		//return x;
	}
	pragma(msg, "al: ",alLeftover());
	static assert(alLeftover()==[[],[1]]);
	static int x;
	enum a=[[(x++,Seq!())],[0]]; // error
	enum int y=2;
	enum b=[[(y,Seq!())],[y]]; // ok
	static assert(b==[[],[2]]);

	auto ceLeftover(){
		int x=1;
		int foo(){ return ++x; }
		return foo((x*=3,Seq!()));
	}
	pragma(msg, "ce: ",ceLeftover());
	static assert(ceLeftover()==4);

	auto neLeftover(){
		int x=1;
		class C{
			this(){ x++; }
			this(int y){ x*=y; }
		}
		C d;
		auto c=new C(++x+1,(d=new C((x++,Seq!())),Seq!()));
		assert(d !is null);
		// assert(d); // TODO
		return x;
	}
	pragma(msg, "ne: ",neLeftover());
	static assert(neLeftover()==12);

	auto asLeftover(){
		int x=1;
		assert(true,"foo",(x++,Seq!()));
		return x;
	}
	pragma(msg, "as: ",asLeftover());
	static assert(asLeftover()==2);

	enum yy=2;
	enum zz=(assert(yy,"foo",(yy,Seq!())),yy); // ok
	int xx;
	enum ww=(assert(yy,"foo",(xx++,Seq!())),yy); // error
	string str="foo";
	enum hh=(assert(false,str),yy); // error
	enum gg=(assert(true,str),yy); // ok

	auto ieLeftover(){
		int x=0;
		int[] y=[x];
		y~=y[x,(x++,Seq!())];
		y~=x;
		int[] z=[1,2,3];
		//z[(x++,Seq!())]=y[(x*=2,Seq!())]; // TODO
		//y~=z;
		// // TODO: eliminate the need for casting?
		y~=z[(x++,Seq!())]~x~(cast(int[])[(x*=2,Seq!())])[(x++,Seq!())]~x;
		return y;
	}
	pragma(msg, "ie: ",ieLeftover());
	static assert(ieLeftover()==[0,0,1,1,2,3,2,5]);

	enum ii=[1,2,3];
	enum jj=ii[1,(x++,Seq!())]; // error
	pragma(msg, "jj: ",jj);

	int csLeftover(int x){
		enum y=2;
		switch(x){
			case 0,(x++,Seq!()): return 1; // error
			case 1,(y,Seq!()): return 2; // ok
			default: return 3;
		}
	}
	static assert(csLeftover(0)==1&&csLeftover(1)==2&&csLeftover(csLeftover(1))==3);

	int csExpand(int x){
		alias R1=Seq!(1,2,3,4,5);
		alias R2=Seq!(7,8);
		switch(x){
			case R1: return 0;
			case 6,R2,9: return 1;
			default: return 2;
		}
	}
	int[] testCsExpand(){
		int[] r;
		for(int i=0;i<12;i++){
			r~=csExpand(i);
		}
		return r;
	}
	static assert(testCsExpand()==[2,0,0,0,0,0,1,1,1,1,2,2]);
	pragma(msg, "testCsExpand: ",testCsExpand());

	void switchOnTuple(Seq!(int,string) x){
		switch(x){ default: break; } // error
	}

	int seLeftover(){
		int x=1;
		struct S{ this(int y){x*=y;} }
		auto s=S(2,(x++,Seq!()));
		return x;
	}
	pragma(msg, "se: ",seLeftover());
	static assert(seLeftover()==4);

	void toStrings(){
		int x;
		[(x++,Seq!())]=[x];// error
		int foo(){ return 2; }
		foo((x++,Seq!()))=x;// error
		class C{}
		(new C((x++,Seq!())))=x; // error
		assert(true,(x++,Seq!()))=x; // error
		int[] y;
		(y[(x++,Seq!())],x++)=x; // error
		struct S{ this(int x){} }
		S(2,(x++,Seq!()))=x; // error
	}
}

struct TestCallSliceIndexTuple{
	alias Seq(T...)=T;
static:
	auto foo(){
		return Seq!(1,2,3);
	}
	auto bar(){
		return [foo()[1..$]];
	}
	static assert(bar()==[2,3]);
	auto baz(){
		return foo()[1];
	}
	static assert(baz()==2);
}

struct DollarAndConstFolderExpansionTests{
	alias Seq(T...)=T;
	static:
	enum e1=(()=>[1][(assert($==1),Seq!())])(); // ok
	enum e2=(()=>[2,1][(assert($==3),Seq!())])(); // error
	enum f1=[3,2,1][(assert($==3),Seq!())]; // ok
	enum f2=[4,3,2,1][(assert($==3),Seq!())]; // error
	enum g1=[3,2,1][(()=>(assert($==3),Seq!()))()]; // ok
	enum g2=[4,3,2,1][(()=>(assert($==3),Seq!()))()]; // error

	enum x1=[1,2,(assert(true),Seq!())]; // ok
	enum x2=[1,2,(assert(false),Seq!())]; // error
	enum y1=[1,2,(()=>(assert(true),Seq!()))()]; // ok
	enum y2=[1,2,(()=>(assert(false),Seq!()))()]; // error

	pragma(msg, assert(true,"fo",(assert(true),Seq!()))); // ok
	pragma(msg, assert(true,"fo",(assert(false),Seq!()))); // error
}

struct TestSeqTemplateArgument{
	alias Seq(T...)=T;
	static:
	struct Tuple(T...)if(T.length==2){
		T expand;
		this(T args){
			expand[0]=args[0];
			expand[1]=args[1];
		}
	}
	int x=0;
	alias y = Seq!(int,(x++,Seq!())); // error
	enum tpl=Tuple!(int,int)(1,2);
	enum w=Seq!(1,2,tpl.expand);
	pragma(msg, [w],[tpl.expand]);
	static assert([w]==[1,2,1,2]); // // TODO: comparing sequences
	void foo(){
		Seq!(int, int) bar(){ return Seq!(1,2); }//return Seq!(1,2); }
		pragma(msg, bar());
		enum z = Seq!(1,2,bar());
		static assert([z]==[1,2,1,2]); // // TODO: comparing sequences
		enum w=(()=>bar())();
		static assert([w]==[1,2]); // // TODO: comparing sequences
	}
	struct S{
		Seq!int x;
		this(); // ok
		this(int y,int z){ return x[0]=y; } // error
		this(int y){ x[0]=y; }
		this(int y,string z){ x=Seq!y; }
	}
	static assert(S(2).x[0]==2);
	static assert([S(3).x]==[3]);
	static assert([S(4,"").x]==[4]);
	auto bar(){
		Seq!int x=3;
		void bar(int y){ x=Seq!y; }
		bar(4);
		return x;
	}
	pragma(msg, foo());
	static assert([bar()]==[4]);

	// static assert(S(4).x==Seq!4); // TODO
}

struct ConstantFolderExpansionTests{
	static assert(is(typeof(quz)==int));
	static:
	alias Seq(T...)=T;
	auto bar(){ return Seq!(1,2); }
	static assert([bar()]==[1,2]);

	pragma(msg, (1,bar()));
	auto foo(){ return (1,bar()); }
	pragma(msg, foo());
	
	Seq!(bool, string) qux(){ return Seq!(false, "int quz;"); }
	pragma(msg, assert(qux())); // error (but just one)
	pragma(msg, (()=>assert(0))()); // error (but no note)
	
	mixin(Seq!(),qux()[1..2],Seq!());
}

struct SeqBehaviourWithBuiltInTypeConstructors{
	static:
	alias f=Seq!(int,double);
	void foo(){
		f* g; // error
	}
	
	const(Seq!(int,double)) x=Seq!(1,2.0);
	pragma(msg, typeof(x));
	static assert(is(const(Seq!(int,double))[]==Seq!(const(int),const(double))));
	static assert(is(immutable(typeof(x))[]==Seq!(immutable(int),immutable(double))));
}

struct TestExpansionForStaticConstructs{
	static int x;
	enum y=2;
	static assert(true,(x++,Seq!())); // ok
	static assert(Seq!(),Seq!(),Seq!(),Seq!(),true,Seq!()); // ok
	static assert(Seq!(),Seq!(),Seq!(),Seq!(),true,Seq!(),Seq!()); // error
	static assert(Seq!(),Seq!(),Seq!(),Seq!(),false,"false!"); // error
	static assert(Seq!(),Seq!(),Seq!(),Seq!()); // error
	mixin("",(x++,Seq!())); // error
	mixin("",(y,Seq!())); // ok
	static assert(Seq!((x++,Seq!()),true)); // error
	static assert(Seq!((y,Seq!()),true));
}

struct Tuple(T...){
	T expand;
}
auto test0(){
	Tuple!(int,double) t;
	t.expand[0]=2;
	int x;
	Seq!(int,double) a=Seq!(x+2); // error
	return a[0];
}

auto test1(){
	Tuple!(int,double) t;
	Seq!(int,double) a=(()=>t.expand)();
	a[0]=2;
	return a[0];
}

pragma(msg, test1());

auto test2(){
	Tuple!(int,double) t;
	t.expand[0]=2;
	alias t.expand[0] xx;
	alias t.expand[1] yy;
	Seq!(int,double) a=Seq!(xx,yy);
	return xx+a[0]+a[1];
}
static assert(test2()==4.0);

struct TestMemberTuple1(A...){
	A a; 
	auto foo()const{
		static assert(is(typeof(a[0])==const(int)));
		return a[0];
	}
}
int testMemberTuple1(){
	TestMemberTuple1!int a;
}

int testZeroArgs(){
	int x;
	int foo(){ return x; }
	return foo((x++,Seq!()));
}
pragma(msg, "za: ",testZeroArgs());


auto seqret(int a, int b){auto x=Seq!(a,b);return x;}

auto seqtak(){auto x = seqret(1,2); return x[0];}
pragma(msg, "seqtak: ", seqtak());
pragma(msg, "seqret: ", seqret(1,2)); // // TODO: show values instead

auto compose(alias a, alias b,T...)(T args){
	return a(b(args));
}

auto seqid(T...)(T args){
	return args;
}
auto add(int a, int b, int c)=>a+b+c;
pragma(msg, "multiret: ", compose!(add,seqid)(1,2,3));

int testmultirefret(){
	int a, b;
	ref Seq!(int, int) multirefret(){
		return Seq!(a,b);
	}
	multirefret()=Seq!(1,2);
	return a+b;
}
pragma(msg, "testmultirefret: ", testmultirefret());

T seq(T...)(T args){ return args; }
pragma(msg, (()=>[seq(1,2,3,4)])());
pragma(msg, [seq(1,2,3,4)]);


struct TupleExpand{
	template Cont(R,A){ alias R delegate(R delegate(A)) Cont; }
	
	auto callCC(T...)(T args){
		Cont!(int,int) delegate(Cont!(int,int) delegate(int),int) f;
		return (int delegate(int) k)=>f(a=>_=>k(a), args)(k);
	}
	
	auto testcallCC(){
		assert(callCC(1)(x=>x)==1);
	}
}

struct Tpl{
	Seq!(int, double) foo;
	int a,b;
	alias Seq!(a,b) c;
}

auto checkTpl(){
	void fun(int, double){ }
	Tpl t;
	fun(t.c);
	t.c[0]=2;
	t.foo[0]=2;
	return t;
}
enum tpl=checkTpl();
pragma(msg, tpl," ",tpl.a," ",tpl.b," ",tpl.c," ",tpl.foo); // // TODO: show values instead


// alias Seq Seq;

auto seqparm(A,B,C...)(Seq!(A,B,C) args){
	return args[0]+args[1]+args[2]+args[$-1];
}

static assert(seqparm(1,2,3.0,4,5)==11.0);
pragma(msg, "seqparm: ",seqparm(1,2,3.0,4,5));


pragma(msg, Seq!(1,2,3,4)[1..3]);
Seq!(int,double,float,long)[1..3] xx;
pragma(msg, typeof(xx));
pragma(msg, "length: ",Seq!(1,2,3).length);
pragma(msg, "$ 1: ", Seq!(1,2,3)[$-1]);

pragma(msg, "$ 2: ", Seq!(int,double)[$-1]);

pragma(msg, "$ 3: ", Seq!(1,2,3)[1..$]);
pragma(msg, "$ 4: ", Seq!(int,int,int)[1..$]);

void convErrMsg(){
	Seq!(int, double) a=Seq!(1.0,2); // error
}

static assert(!is(Seq!(int, double)==int));



template Fst(T...){
	alias T[0] Fst;
}

pragma(msg, "Fst: ",[Seq!(Fst!(Seq!("133",2,3,4)),"2","3","4")]);




/+int main(){
	Seq!(int,int) x = Seq!(1,2);
	x[1]=3;
	x[0]-=11;
	return x[0]+x[1];
}+/
//pragma(msg, main());


auto refe(ref Seq!(int,int,int,int) arg){
	return ++arg[0]+ ++arg[1]+ --arg[2]+ --arg[3];
}

auto testt(ref int a, ref int b, ref int c, ref int d){
	a++; b++; c++; d++;
}
auto testAliasTuple(){
	int a,b,c,d;
	int x;
	//alias Seq!(a,b,c,d) tp;
	//tp=++x;
	Seq!(int,int,int,int) tp=++x;
	//a=1;b=2;c=1;d=3;
	//pragma(msg, typeof({tp;tp[0];}));
	//(){testt(tp);}();

	//alias f_d a_d;
	//static void foo(){tp[0]=2;}

	(){testt(tp);}();
	
	x=333;
	auto r=[tp]~{testt(tp); return [tp];}()~refe(tp)~[tp];
	//return r[1..12];
	return r;
}
static assert(testAliasTuple()==[2,3,4,5,3,4,5,6,18,4,5,4,5]);
pragma(msg, testAliasTuple());

pragma(msg, Seq!(1,2,3));
pragma(msg, typeof(Seq!(1,2,3)));
pragma(msg, Seq!(1,int,3));
pragma(msg, typeof(Seq!(1,int,3)));
pragma(msg, Seq!(float,int,double));

static assert(is(Seq!(int,double)==Seq!(int,double)));
static assert(!is(Seq!(double,int)==Seq!(int,double)));
static assert(is(Seq!(int delegate(int, int[]))==Seq!(int delegate(int,int[]))));

pragma(msg, Seq!(1,Seq!(int,double),2,Seq!(float,real,int[])));

Seq!(1,2,3)[1] aaa; // error

pragma(msg, Seq!(1,2,3,Seq!(1,2,3)));

//pragma(msg, Seq!(int,double)[0]);

Seq!(int,[2])[0] as;
pragma(msg, typeof(as));
//pragma(msg, x);


Alias!(Seq!(int,2)) a; // error

static assert(Seq!(0,"test")); // error

static assert(Seq!(1,""));
void main(){assert(Seq!(1,""));}


mixin(Seq!("int x;"));

int[Seq!(1,2)] ad; // error


alias Seq!(1,2) start;
enum Seq!(int,int) aii = 12;
//pragma(msg, aii[Seq!(start,3,5,11)]);


//Seq!(int,double) aid = Seq!(1,1,2);

void test(){
	//	aid = Seq!(1,1,2);
}

immutable int[2] a2=[1,2];
//pragma(msg, a[1..3]);
pragma(msg, a2[1]);

template StaticMap(alias F, a...){
	static if(a.length) alias Seq!(F!(a[0]), StaticMap!(F,a[1..a.length])) StaticMap;
	else alias Seq!() StaticMap;
}

template StaticFoldr(alias F, a...){
	static if(a.length==2) alias F!(a[0],a[1]) StaticFoldr;
	else alias F!(a[0],StaticFoldr!(F, a[1..a.length])) StaticFoldr;
}


template CommonType(A,B){ alias typeof({A a; B b; return 1?a:b;}()) CommonType; }
pragma(msg, StaticFoldr!(CommonType, int, double, short, real));

template TimesTwo(int x){ enum TimesTwo = x+x; }
template Square(int x){ enum Square = x*x; }


pragma(msg, [StaticMap!(TimesTwo,StaticIota!(1,31))]);
pragma(msg, StaticMap!(Square,StaticIota!(1,31)));


template StaticFilter(alias F, a...){
	static if(!a.length) alias a StaticFilter;
	else static if(F!(a[0])) alias Seq!(a[0], Rest) StaticFilter;
	else alias Rest StaticFilter;
	static if(a.length) alias StaticFilter!(F,a[1..a.length]) Rest;
}

bool any(alias a,R)(R r, int len){// if(is(typeof(a(r[0])) == bool)) {
	for(int i=0;i<len;i++) if(a(r[i])) return true;
	return false;
}
static bool lower(char s) { return 'a'<=s&&s<='z'; }

alias immutable(char)[] string;
template isUppercase(string s) if(is(typeof(s[2]))&&!is(typeof(s[3]))){
	enum isUppercase = {
		static bool lower(char s) { return 'a'<=s&&s<='z'; }
		return !any!(lower, string)(s,3);
	}();
}

//pragma(msg, isUppercase!"123");
//pragma(msg, isUppercase!"aBc");
//pragma(msg, isUppercase!"ABC");
//pragma(msg, isUppercase!"AbC");
//pragma(msg, isUppercase!"DEF");

pragma(msg, StaticFilter!(isUppercase,"123","aBc",Seq!("ABC","AbC"),"DEF"));

template StaticIota(int a, int b) if(a<=b){
	static if(a==b) alias Seq!() StaticIota;
	else alias Seq!(a,StaticIota!(a+1,b)) StaticIota;
}


template Divides(int a){
	template Divides(int b){
		enum Divides = a%b==0;
	}
}

//pragma(msg, (Divides!2)!2);


template IsPrime(int p){
	//enum IsPrime = StaticFilter!(Divides!p, StaticIota!(1,p+1)).length==2;
	enum IsPrime = {
		int r;
		for(int i=1;i<=p;i++) r+=!(p%i);
		return r;
	}()==2;
}

pragma(msg, IsPrime!2);
pragma(msg, IsPrime!4);
pragma(msg, IsPrime!5);
pragma(msg, IsPrime!13);
//pragma(msg, IsPrime!20);

/+pragma(msg, IsPrime!53);
pragma(msg, IsPrime!70);
pragma(msg, IsPrime!103);
pragma(msg, IsPrime!103);+/

pragma(msg, ListPrimes!103);

template Primes(int i){
	alias StaticFilter!(IsPrime, StaticIota!(2,i+1)) Primes;
}

template ListPrimes(int upper){
	enum ListPrimes = H!2;
	template H(int lower){
		enum H = "";
		static if(lower <= upper){
			static if(IsPrime!lower){pragma(msg, lower,H!(lower+1));}
			else enum next=H!(lower+1);
		}
	}
}



pragma(msg, StaticIota!(1,12)," ", Primes!12);

//pragma(msg, StaticIota!(2,100).V);


//pragma(msg, a[0].mangleof);
//pragma(msg, _a_field_0.mangleof);

// +/
// +/
// +/

template Seq(T...){ alias T Seq; }

template Alias(T){ alias T Alias; }
