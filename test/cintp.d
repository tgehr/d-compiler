
string execLenses(){
	string r;
	void write(T...)(T x){
		static if(x.length){
			r~=to!string(x[0]);
			write(x[1..$]);
		}
	}

	struct Lens(A,T){
		auto compose(T,S)(Lens!(T,S) rhs){
			Lens!(A,S) l;
			l.mod = (a,s)=>mod(a,x=>rhs.mod(x,s));
			l.get = a=>rhs.get(get(a));
			return l;
		}
		A delegate(A,T delegate(T)) mod;
		T delegate(A) get;
	}
	auto id(S)(){
		Lens!(S,S) id;
		id.mod=(a,s)=>s(a);
		id.get=a=>a;
		return id;
	}
	auto getLens(A,T)(T delegate(ref A)ref dg){
		Lens!(A,T) l;
		l.mod=(a,s){auto y=&dg(a);*y=s(*y);return a;};
		l.get=a=>dg(a);
		return l;
	}

	struct Q{ int x=2; }
	struct S{ Q x; }

	void main(){
		auto xlens = getLens((ref S s)ref=>s.x);
		//auto ylens = xlens.compose!(Q,int)(getLens((ref Q q)ref=>q.x));
		//auto lens = ylens.compose!(int,int)(id!int());
		auto lens = xlens.compose!(Q,int)(getLens((ref Q q)ref=>q.x)).compose!(int,int)(id!int());
		auto add13(S x)=>lens.mod(x,x=>x+13);
		auto mul23(S x)=>lens.mod(x,x=>x*23);
		write(add13(mul23(add13(S()))).x.x);
	}
	main();
	return r;
}
pragma(msg, "execLenses: ",execLenses());

/+
struct TestPartialEvaluation{
	static foo(string f){
		if(f[0] == 's')
			return "got somestring";
		return bar!(foo("somestring"));
	}
	static template bar(string s){
		enum bar = s;
	}

	// TODO: could work, but requires out-of-order function body
	// analysis and scope cloning
	static assert(!is(typeof({
		static string nofoo(string f){
			if(f[0] == 'n') return bar!(nofoo("somestring"));
			return "not somestring";
		}
	})));
}
static assert(TestPartialEvaluation.foo("3")=="got somestring");+/

int testClassConstructor(){
	class C{
		int x;
		this(int a, int b){
			x = a + b;
		}
	}
	auto d = new C(2,4);
	assert(d.x == 6);
	return new C(2,3).x;
}
static assert(testClassConstructor()==5);
pragma(msg, "testClassConstructor: ", testClassConstructor());

int testParentFieldAccess(){
	class P{ int x = 2; int foo(){ return x; }}
	class C1: P{ }
	class C2: P{ override int foo(){ return ++x; }}
	
	class C3: P{
		int y;
		this(int x, int y){
			this.x=x;
			this.y=y;
		}
		override int foo(){ return x+y; }
	}

	assert(new C3(2,3).foo()==5);

	P x = new C1, y = new C2;
	return x.foo()+y.foo();
}
static assert(testParentFieldAccess()==5);
pragma(msg, "testParentFieldAccess: ", testParentFieldAccess());

int[] testQualifiedNonVirtual(){
	class P{ int foo(){ return 1; }}
	class C1: P{ override int foo(){ return P.foo(); }}
	class C2: C1{ override int foo(){ return C1.foo()+P.foo(); }}
	class C3: C2{ override int foo(){ return C2.foo()+C1.foo(); }}
	class C4: C3{ override int foo(){ return C3.foo()+C2.foo(); }}
	class C5: C4{ override int foo(){ return C4.foo()+C3.foo(); }}

	P x = new C1, y = new C2, z = new C3, w = new C4, q = new C5;
	return [x.foo(), y.foo(), z.foo(), w.foo(), q.foo()];
}
static assert(testQualifiedNonVirtual()==[1,2,3,5,8]);
pragma(msg, "testQualifiedNonVirtual: ", testQualifiedNonVirtual());

int testVirtual(){
	class P{ int foo(){ return 2; }}
	class C1: P{ override int foo(){ return 1; }}
	class C2: P{ override int foo(){ return 2; }}
	class C3: P{ }
	class C4: P{ int bar(){ return foo(); } }
	class C5: C4{ override int foo(){ return 3; }}
	P x = new C1, y = new C2, z = new C3;
	auto w = new C4(), q = new C5();
	assert(w.foo()==2 && w.bar()==2);
	assert(q.foo()==3 && q.bar()==3);

	class C6: P{ int bar(){ return super.foo(); }}
	class C7: C6{ override int foo(){ return 3; }}
	auto dd = new C7();
	assert(dd.bar()==2 && dd.foo()==3);

	class C8: P{ int bar(){ return C8.foo(); }}
	class C9: C8{ override int foo(){ return 3; }}
	auto ee = new C9();
	assert(ee.bar()==2 && ee.foo()==3);


	return x.foo()+y.foo()+z.foo();
}
static assert(testVirtual()==5);
pragma(msg, "testVirtual: ", testVirtual());


int testNew(){
	struct S{ int x; }
	class C{ int x; }
	auto s = new S, c = new C;
	s.x = 2; c.x = 3;
	return s.x+c.x;
}
static assert(testNew()==5);
pragma(msg, "testNew: ", testNew());

auto transferContext() {
	int x = 2;
    struct Foo {
        size_t data;
	    this(size_t data){ this.data = data; }
        @property
        auto clone() {
            return Foo(data);
        }
	    @property int xx(){ return x; }
    }

    return Foo(0).clone.clone;
}
pragma(msg, "transferContext: ", transferContext().clone.xx);
static assert(transferContext().clone.xx==2);

int testInvalidContext(){
	auto s(){ int x=2; struct S{ int foo(){ return x; }} return S(); } // error
	typeof(s()) ss;
	return ss.foo();
}
pragma(msg, testInvalidContext());

int testThis(){
	struct S{
		int x;
		this(int u){
			x = u;
		}
		S foo(){ return this; }
		ref S goo(){ return this; }
		void repl(S other){ this = other; }
	}
	S s = S(4);
	S g = s.foo();
	S moo;
	moo.repl(g.foo());
	moo.goo().x++;
	return moo.foo().goo().goo().foo().x;
}
static assert(testThis()==5);
pragma(msg, "testThis: ", testThis());

int testConstructor(){
	struct S{
		int x;
		this(int x){
			this.x=x;
		}
		this(int a, int b){
			x = a+b;
		}
	}
	auto g=S(2);
	return S(1,2).x+g.x;
}
static assert(testConstructor()==5);
pragma(msg, "testConstructor: ", testConstructor());


int testStructMemberAliasParam(){
	int x;
	struct S{
		int y;
		void bar(int x){ foo!((ref a)=>a=x)(); }
		void foo(alias a)(){ a(x); } // TODO
		void baz(alias a)(){ a(y); }
	}
	S s;
	s.bar(2);
	s.baz!(function(ref a)=>a=3)();
	s.baz!((ref a)=>a=3)();
	return x+s.y;
}
static assert(testStructMemberAliasParam()==5);
pragma(msg, "testStructMemberAliasParam: ", testStructMemberAliasParam());


int testMutate3(){
	static struct Cell{
		int x=1335;
		void foo(int u){
			x = u;
		}
	}
	auto c=Cell(), d=Cell();
	c.foo(2), d.foo(3);
	assert(c.x==2 && d.x==3);
	c.foo(3);
	return c.x;
}
static assert(testMutate3()==3);

int testMutate2(){
	static struct Cell{
		int x=1335;
	}
	auto c=Cell(), d=Cell();
	auto p=&c, q=&d;
	p.x=2; q.x=3;
	assert(c.x==2 && d.x==3);
	assert(p.x==2 && q.x==3);
	p.x=3;
	assert(p.x==3);
	return q.x;
}
static assert(testMutate2()==3);

int testMutate(){
	static struct Cell{
		int x=1335;
	}
	auto c=Cell(), d=Cell();
	c.x=2; d.x=3;
	assert(c.x==2 && d.x==3);
	c.x=3;
	return c.x;
}
static assert(testMutate()==3);

struct Dynamic{
	// (tests how the interpreter deals with memory layout changes)
	mixin(foo(Dynamic()));
	static string foo(Dynamic d){
		return d.s;
	}
	string s = "int b = 2;";
	static assert({
		Dynamic d;
		return d.b==2?foo(d):"fail";
	}() == "int b = 2;");
}

struct TestStaticImmutableAndEnumFields{
	static immutable int c=222; // // TODO: should it work without static?
	enum x = 333;
	static int foo(int){
		TestStaticImmutableAndEnumFields s;
		return c+x;
	}
}
static assert(TestStaticImmutableAndEnumFields.foo(3)==555);
pragma(msg, "TestStaticImmutableAndEnumFields.foo: ", TestStaticImmutableAndEnumFields.foo(3));

auto testStruct2(){
	static struct S{
		int x=1;
		int y=2;
		int z=4;
		int w=8;
	}
	S s;
	S* q = &s;
	return s.x+q.y+(()=>s.z)()+(()=>(()=>s.w)())();
}
static assert(testStruct2()==15);
pragma(msg, "testStruct2: ", testStruct2());

auto testStruct(){
	static struct S{
		int x=1;
		int y=2;
		int z=3;
	}
	S s;
	return s.x+s.y+s.z;
}

static assert(testStruct()==6);
pragma(msg, "testStruct: ", testStruct());


int[] evalord(){
	int[] a=[1,2,3], b=[1,2,3];
	int c = 1;
	a[c]=b[++c];
	return a;
}

pragma(msg, "evalord: ", evalord());
static assert(evalord()==[1,3,3]); // evaluation from left to right

template CommonType(T...){
	enum e = q{{ T bar(T)(T[]); T t; auto ts = [t]; return bar(ts); }()};
	static if(is(typeof(mixin(e)))) alias typeof(mixin(e)) CommonType;
	else alias void CommonType;
}

pragma(msg, "CommonType: ",CommonType!()," ",CommonType!(int,double,real));

int[] bigInt(string s){ /+ TODO: in contracts +/
	int[] r;
	for(size_t i=0;i<s.length;i++) assert('0'<=s[i] && s[i] <='9');
	for({size_t i=s.length;while(i>1&&s[--i]=='0'){}};){
		r~=s[i]-'0';
		if(!i--) break;
	}
	return r;
}

string biToString(int[] bi){
	string r;
	for({size_t i = bi.length;while(i>1&&!bi[--i]){}};){
		r~=cast(char)(bi[i]+'0');
		if(!i--) break;
	}
	return r;
}

pragma(msg, biToString(bigInt("00123453388338838")));


auto memoizer(T,S)(T[] memo, T delegate(T delegate(S), S) formula){
	bool[] e;
	e.length = memo.length;
	for(int i=0;i<e.length;i++) e[i]=true;

	T recur(S arg){
		while(memo.length<=arg) memo.length*=2;
		e.length = memo.length;
		if(!e[arg]){
			memo[arg] = formula(&recur, arg);
			e[arg] = true;
		}
		return memo[arg];
	}
	return &recur;
}

auto memfactorial(int n) => memoizer([1, 1L], (recur, int n) => n*recur(n-1))(n);
auto memfibonacci(int n) => memoizer([0, 1 ], (recur, int n) => recur(n-2)+recur(n-1))(n);
pragma(msg, "memfactorial: ", map!memfactorial(iota(0,19)));
pragma(msg, "memfibonacci: ", map!memfibonacci(iota(0,29)));
pragma(msg,typeof(memoizer([], (int delegate(int) recur, int n) => n*recur(n-1))));


// Haskell-Like CPS //
template Cont(R,A){ alias R delegate(R delegate(A)) Cont; }

auto ret(R=A,A)(A arg){ return (R delegate(A) k)=>k(arg); }
auto bind(R,A,B)(Cont!(R,A) me, Cont!(R,B) delegate(A) f){
	return (R delegate(B) k)=>me(r=>f(r)(k));
}

// ((A -> (B -> R) -> R) -> (A -> R) -> R) -> (A -> R) -> R

auto callCC(R,A,B,T...)(Cont!(R,A) delegate(Cont!(R,B) delegate(A),T) f, T args){
	return (R delegate(A) k)=>f(a=>_=>k(a), args)(k);
}

/+pragma(msg, typeof(&callCC!(R,A,B)));
auto testselfapp(){
	return callCC(&callCC!(),);
}+/

auto testcallCC(){
	auto f(Cont!(int,int) delegate(int) cont, int x){
		return bind(x<3?cont(x):ret!int(1),a=>cont(x+a));
	}
	assert(callCC(&f,1)(x=>x)==1);
	assert(callCC(&f,3)(x=>x)==4);
	return callCC(&f,1)(x=>x)+callCC(&f,3)(x=>x);
	//pragma(msg, typeof(&f));
}
static assert(testcallCC()==5);
pragma(msg, "testcallCC: ", testcallCC());


pragma(msg, "callCC: ",callCC!(int,int,int)(ret=>ret(2))(x=>callCC!(int,int,int)(ret=>ret(x+1))(x=>x)));

auto testcallCC2(){
	auto f(Cont!(int,int) delegate(int) cont, int x){
		return cont(1+x);
	}
	// pragma(msg, typeof(&f));
	auto g(Cont!(int,int) delegate(Cont!(int, int) delegate(int)) arg){
		return callCC(arg);
	}
	assert(g(x=>f(x,3))(x=>x) == 4);

	alias Cont!(int,int) delegate(int) R;
	alias Cont!(int,int) delegate(int) A;
	alias Cont!(int,int) delegate(int) B;

	Cont!(R,A) callCCBack(Cont!(R,B) delegate(A) arg){
		//return callCC(arg);
		//return arg(x=>y=>z=>callCC(&f, x(2)(x=>x)+y(2)(3)(x=>x)+z));
		//return callCC(arg);
		return arg(x=>callCC(&f,x));
	}
	return callCC(&callCCBack)(x=>x)(1337);
/+	auto callCCBack(Cont!(Cont!(int, int) delegate(int),int) delegate(Cont!(Cont!(int, int) delegate(int), int) delegate(Cont!(int, int) delegate(int))) arg){
		//return callCC(arg);
		return arg(x=>y=>z=>callCC(&f, x(2)(x=>x)+y(2)(3)(x=>x)+z));
	}
	return callCC!(int,Cont!(int, int) delegate(int),Cont!(int, int) delegate(int))(&callCCBack);+/

	//return callCC(&f, 4);
	//return callCC(&g, callCC(&f, 2));
}
static assert(testcallCC2()(x=>x)==1338);
pragma(msg, "testcallCC2: ", testcallCC2()(x=>x));

auto testcps()
=>	bind(1.ret, a =>
	bind(2.ret, b =>
	bind(3.ret, c =>
	ret!int(a+b+c))))
	(x=>x);


static assert(testcps()==6);
pragma(msg, "testcps: ", testcps());

Cont!(int,int) factcps(Cont!(int,int) delegate(int) cont, int n){
	return 
		bind!(int,int,int)(n<1 ? cont(1) : ret!int(n-1),
		                  a => cont(callCC!(int,int,int)((x,y)=>factcps(x,y), a)(x=>x)*n));
}

pragma(msg, "factcps: ", map!(a=>callCC!(int,int,int)((x,y)=>factcps(x,y),a)((int x)=>x))(iota(1,10)));

alias Seq!(void,bool) vb;
alias Seq!(void,bool,bool) vbb;

Cont!vb isprimecps(Cont!vb delegate(bool) cont, int p){
	Cont!vb loop(int i){
		return
			bind!vbb(i > p  ? cont(false) : ret!vb(false), a=>
			        i == p ? cont(true) :
			        p % i  ? loop(i+1) :
			        cont(a));
	}
	return loop(2);
}

T escapeCont(T)(Cont!(void, T) cont){
	T r;
	// cont((x){r=x;});
	cont(x=>cast(void)(r=x));
	return r;
}

// pragma(msg, escapeCont(callCC!vbb((x,y)=>isprimecps(x,y),4)));
pragma(msg, "isprimecps: ",filter!(a=>escapeCont(callCC!vbb((x,y)=>isprimecps(x,y),a)))(iota(1,100)));

Cont!(S,T) arrayToCont(S,T)(T[] a){
	return (S delegate(T) dg){
		S r;
		//foreach(x;a) r~=dg(x);
		for(int i=0;i<a.length;i++)
			r~=dg(a[i]);
		return r;
	};
}


auto cartprodcps(T)(T[] a, T[] b){
	alias arrayToCont i; alias T[][] R;
	return bind(i!R(a),x=>bind(i!R(b),y=>ret!R([[x,y]])));
}

pragma(msg, cartprodcps([1,2,3],[4,5,6])(x=>x));

enum cprod = cartprodcps([1,2,3],[4,5,6])(x=>x);
enum cprod2 = cartprodcps(cprod,cprod)(x=>x);

//enum cprod3 = cartprodcps(cprod2, cprod2)(x=>x);

pragma(msg, "cartprodcps: ",cprod2);
//pragma(msg, cartprodcps(cprod2,cprod2)(x=>x));

auto expCps(T)(T[] a, T[] b){
	alias arrayToCont i;
	alias Seq!(T[],T,T) iaii;
	alias Seq!(T[][],T[],T[]) iaaiaia;
	
	alias Seq!(T[][],T,T) iaaii;
	alias Seq!(T[][],T[],T) iaaiai;

	//return bind!iaii(i!T(a),x=>bind!iaii(i!T(b),y=>i!T([x,y])));
	//return bind!iaaiaia(i!(T[])(a),x=>bind!iaaiaia(i!(T[])(b),y=>i!(T[])([[x,y]])));
	//return bind!(T[],T,T)(i!(T)(a), x=>ret!(T[])(x*2));
	//return bind!iaaiaia(i!(T[])([a]), x=>ret!(T[][])(x));

	//return bind!iaaii(i!(T[])(a),x=>bind!iaaii(i!(T[])(b),y=>ret!(T[][])(x)));
}

size_t indexOf(alias a=(a,b)=>a==b, T, V...)(const(T)[] c, V v){
	for(size_t i=0;i<c.length;i++)
		if(a(c[i],v)) return i;
	return -1;
}
static assert(indexOf("abc",'d')==-1LU);

/+size_t balancedIndexOf(alias a=(a,b)=>a==b, T, V...)(const(T)[] c, V v){
	// TODO: this probably is not supposed to work
	template bal(string s){ size_t bal = 0; }
	for(size_t i=0;i<c.length;i++){
		if(!bal!"'"&&!bal!"\""&&!bal!"("&&!bal!"["&&!bal!"{"&&a(c[i],v)) return i;

		if(c[i]=='"') bal!"\""=!bal!"\"";
		else if(c[i]=='\'') bal!"'"=!bal!"'";
		else if(!bal!"\""&&!bal!"'"){
			if(c[i]=='(') bal!"("++;
			else if(c[i]==')') bal!"("--;
			else if(c[i]=='[') bal!"["++;
			else if(c[i]==']') bal!"["--;
			else if(c[i]=='{') bal!"{"++;
			else if(c[i]=='}') bal!"{"--;
		}
	}
	return -1;
}+/

size_t balancedIndexOf(alias a=(a,b)=>a==b, T, V...)(const(T)[] c, V v){
	size_t bal1 = 0, bal2 = 0, bal3 = 0, bal4 = 0, bal5 = 0;
	for(size_t i=0;i<c.length;i++){
		if(!bal1&&!bal2&&!bal3&&!bal4&&!bal5&&a(c[i],v)) return i;

		if(c[i]=='"') bal2=!bal2;
		else if(c[i]=='\'') bal1=!bal1;
		else if(!bal2&&!bal1){
			if(c[i]=='(') bal3++;
			else if(c[i]==')') bal3--;
			else if(c[i]=='[') bal4++;
			else if(c[i]==']') bal4--;
			else if(c[i]=='{') bal5++;
			else if(c[i]=='}') bal5--;
		}
	}
	return -1;
}

string[] splitIdent(string str){
	if('0'<=str[0]&&str[0]<='9') return ["",str];
	for(int i=0;i<str.length;i++)
		if(('a'>str[i]||str[i]>'z')&&('A'>str[i]||str[i]>'Z')&&('0'>str[i]||str[i]>'9')&&str[i]!='_')
			return [str[0..i], str[i..$]];
	return [str,""];
}

string trimLeft(string str){
	while(str.length&&(str[0]==' '||str[0]=='\t'||str[0]=='\v'))
		str = str[1..$];
	return str;
}

private string Ximpl(string x){
	string r=`"`;
	//foreach(i;0..x.length){
	for(size_t i=0;i<x.length;i++){
		if(x[i]=='@'&&i+1<x.length&&x[i+1]=='('){
			auto start = i+1;
			i+=2;
			auto inc = balancedIndexOf(x[i..$],')');
			assert(~inc, x[i..$]);
			i += inc;
			r~=`"~`~x[start..i+1]~`~"`;
		}else{
			if(x[i]=='"'||x[i]=='\\') r~="\\";
			r~=x[i];
		}
	}
	return r~`"`;
}

template X(string x){
	enum X = Ximpl(x);
}

template compr(string c){
	auto computeCompr(){
		auto c=c;
		c = trimLeft(c);
		auto barp = balancedIndexOf(c,'|');
		assert(barp!=-1,"'|' is missing");
		auto exp = c[0..barp];
		c=trimLeft(c[barp+1..$]);
		string[] idents;
		string[] exprs;
		string[] conditions;
		for(;;){
			auto s = splitIdent(c);
			if(!s[0].length) goto parseCondition;
			//assert(s[0].length, "expected identifier at "~s[1]);
			auto rmd = trimLeft(s[1]);
			if(rmd.length<2 || rmd[0]!='<' || rmd[1]!='-') goto parseCondition;
			c = rmd;
			idents ~= s[0];
			assert(s[0][0]!='_',"leading underscore identifiers are reserved");
			//assert(c[0]=='<' && c[1]=='-', c);
			c=c[2..$];
			auto cp = balancedIndexOf(c,',');
			exprs ~= c[0..~cp?cp:$];
			conditions~="true";
			c = c[exprs[$-1].length..$];
			if(!c.length) break;
			c = trimLeft(c[1..$]);
			continue;
		parseCondition:
			assert(conditions.length>0);
			cp = balancedIndexOf(c,',');
			conditions[$-1]~="&&("~c[0..~cp?cp:$]~")";
			c = c[~cp?cp:$..$];
				
			if(!c.length) break;
			c = trimLeft(c[1..$]);
		}
		string[] types = map!(x=>"typeof(_"~x~"[0])")(idents);
		
		string rtype = "typeof({";
		for(size_t i=0;i<idents.length;i++)
			rtype~=types[i]~" "~idents[i]~";";
		rtype ~= "return "~exp~";}())[]";
		return mixin(X!q{
			//
			(@({string r;
				for(size_t i=0;i<idents.length;i++)
					r~="typeof("~exprs[i]~") _"~idents[i]~", ";
				return r;
			}())){
				alias arrayToCont i; alias @(rtype) R;
				return @({
					string r;
					for(int i=0;i<idents.length;i++)
						r~="bind(i!R(_"~idents[i]~"),"~idents[i]~"=>!("~conditions[i]~")?ret!(R,R)([]):";
					r~="ret!R(["~exp~"])";
					for(int i=0;i<idents.length;i++) r~=')';
					return r;
				}());
				
			}(@(join(exprs,',')))
		});
	}
	enum compr = mixin(computeCompr())(x=>x);
}

pragma(msg, "compr: ", compr!q{ [x|1,y] | x <- [1,2,3], y <- [4,5,6], x==y-4});

pragma(msg, "compr2: ", compr!q{ [x<y,y<x] | x <- [1,2,3], y <- [1,2,3], x!=y });

pragma(msg, "compr3: ", compr!q{ [a,b,c].map!toString.join("o") | a<-[1,2], b<-[2,3], c<-[3,4] });

pragma(msg, "compr4: ", compr!q{ [x,y,z] | x <- [1,2,3], x&1, y <- [1,2,3,4], z <-[1,2,3], x+y+z==7 });

//pragma(msg, callCC!(int,int,int)(k=>k(2))(x=>x));

/////////
string templatednested(){
	string r;
	void write(T)(T arg) { r~=arg; }
	write("success!!!");
	return r;
}
pragma(msg, "templatednested: ",templatednested());
static assert(templatednested() == "success!!!");



/+
// TODO: do we want deterministic slice aliasing in CTFE?
auto testsetlengthdet(){
	auto x = [1,2,3];
	auto y = x;
	x.length=4;
	y=x;
	x.length=5;
	y[0]=4;	
	return x;
}
static assert(testsetlengthdet()==[1,2,3,0,0]);
pragma(msg, "testsetlengthdet: ",testsetlengthdet());
+/


auto testsetlength(){
	auto x=[1,2,3,4];
	x.length=3;
	int[] y;
	x.length=y.length=4;
	(x.length+=1)++;
	assert(x.length==6);
	assert(x[5]==0);
	x.length=4;
	assert(x.length==4);
	return x~y;
}
static assert(testsetlength()==[1,2,3,0,0,0,0,0]);
pragma(msg, "testsetlength: ",testsetlength());

auto testdollarclosure(){
	int[] x = [1,2,3,4];
	ulong delegate() dg;
	x[(dg=()=>$,$-1)]=1; 
	assert(x[(assert($==4),3)]==1);
	return dg();
}
pragma(msg, "testdollarclosure: ",testdollarclosure());

auto testnulldelegate(){
	int delegate() dg; // =null; // TODO!
	return dg(); // error
}

auto testnullfunpointer(){
	int function() fp=null;
	return fp(); // error
}
pragma(msg, testnulldelegate());
pragma(msg, testnullfunpointer());


bool bsearch(T)(T[] haystack, T needle){
	if(haystack.length<=1) return (haystack~(needle+1))[0]==needle;
	bool b = haystack[$/2]>needle;
	return bsearch!T(haystack[b?0:$/2..b?$/2:$], needle);
}

pragma(msg, "bsearch1: ",bsearch!int([1,2,3],0));
pragma(msg, "bsearch2: ",bsearch!float([0,2,5],2));
pragma(msg, "bsearch3: ",bsearch!int([0,2,5],3));
pragma(msg, "bsearch4: ",bsearch!real([],0));

 
auto testdollar(){
	int[] x = [1,2,3,4];
	auto ptr=&x[(x~=cast(int)$,x~=cast(int)$,0)];
	assert(x.length==6 && x[$-2]==4 && x[$-1]==4);
	*ptr = 2;
	assert(x[0]==2);
	x[0]=1;
	assert(*ptr==1);
	x=x[0..$-2];
	return x[$-1]~x[$-3..$-1]~x[$-4..$][0];
}
static assert(testdollar()==[4,2,3,1]);
pragma(msg, "testdollar: ",testdollar());

auto loopclosures(int n){
	immutable(int)* delegate()[] a;
	for(int i=0;i<n;i++){
		immutable int j=i;
		a ~= {return &j;};
	}
	int[] r;
	for(int i=0;i<n;i++) r~=*a[i]();
	return r;
}

static assert(loopclosures(10)==[0,1,2,3,4,5,6,7,8,9],"TODO!"); // TODO!

auto testlambda(){
	int x;
	(){(){x++;}();}();
	return x;
}

pragma(msg, "testlambda: ",testlambda());


pragma(msg, typeof(&map!(toString,int)));



bool pred(string s){
	int c=0;
	for(int i=0;i<s.length;i++) c+=s[i]=='2';
	return c>=2;
}

//pragma(msg, filter!(pred,string)(map!(toString,int)(iota(0,1000))));

template binaryFun(alias fun,T){
	static if(is(typeof(fun)==string))
		auto binaryFun(T a, T b){
			return mixin(fun);
		}
	else alias fun binaryFun;
}

auto sort(alias p,T)(T[] arg){
	alias binaryFun!(p,T) pred;
	if(arg.length <= 1) return arg;
	bool low(T x)=>!!pred(x,arg[0]);
	bool high(T x)=>!pred(x,arg[0]);
	return sort!(pred,T)(filter!(low,T)(arg))
	~ arg[0] ~ sort!(pred,T)(filter!(high,T)(arg[1..arg.length]));
}


auto mod(int x)=>(int y)=>y%x;


auto mod10(int y)=>mod(10)(y);

enum unsorted = [3,28,1,29,33,828,11,282,34,378,122,122];

bool less(int a,int b)=>a<b;
pragma(msg, "sort1: ", sort!(less,int)(unsorted));

pragma(msg, "sort2: ",sort!less(unsorted));
pragma(msg, "sort3: ",sort!"a>b"(unsorted));

pragma(msg, "sort4: ",sort!"a<b"(map!mod10(unsorted)));
//pragma(msg, sort!("a",int)(map!(mod10,int)([3,28,1,29,33,828,11,282,34,378,122,122])));

auto testStaticArrayValueType(T)(T[2] x){
	int[2] y=x;
	x[0]=2;
	x[0]++;
	y[1]++;
	assert(x[0]==3 && x[1]==2);
	x=(()=>y)();
	assert(x[0]==1 && x[1]==3);
	y[0]++;
	return y;
}
static assert(testStaticArrayValueType([1,2])==[2,3]);
pragma(msg, "testStaticArrayValueType: ", testStaticArrayValueType([1,2]));


auto testarrayptrlength(){
	int[] x = [1,2,4];
	assert(x.length==3);

	auto y = x.ptr;
	static assert(is(typeof(*y) == typeof(x[0])));
	assert(*y==1 && y[1]==2 && y[2]==4);

	*y=8;
	assert(x[0]==8);
	(){*(y+2)=1337;}();
	return *(y+x.length-1);
}
static assert(testarrayptrlength()==1337);
pragma(msg, "testarrayptrlength: ", testarrayptrlength());


typeof(null) retnull(){return null;}
pragma(msg, "retnull: ",retnull());

static assert(retnull() is null); // TODO!

static assert([] is null); // TODO!
static assert([] == null);

immutable a = "hallo";
immutable b = a;
pragma(msg, a is b); // TODO (?)
//pragma(msg, (()=>a is b)());
//pragma(msg, ((immutable(char)[] a, immutable(char)[] b)=>a is b)(a,b));

int retzero(){return 0;}
enum divby0 = 1/retzero(); // error

/+
// TODO: should this be legal code?
struct InterpretImmutableField{
	immutable y=22;
}
static assert(InterpretImmutableField.y==22);
static assert((()=>InterpretImmutableField.y==22)());
+/


mixin(`auto foo1="1.0f";`);
mixin(`float a11=`~foo1~";"); // error

enum short[] x = rngg();
int[] rngg(){return [1,2,3,];}
pragma(msg, "rngg: ", x);

bool testptrcmp(){
	auto x = [0,1];
	auto p = &x[0], q = &x[1];
	assert(*p==0 && *q==1);

	assert(p==p && p is p && p!<>p);
	assert(!(p!=p) && !(p!is p) && !(p<>p));

	assert(p!=q && p !is q && p<>q && p<>=q);
	assert(!(p==q) && !(p is q) && !(p!<>q) && !(p!<>=q));

	assert(p<q && p<=q && p!>q && p!>=q);
	assert(!(p!<q) && !(p!<=q) && !(p>q) && !(p>=q));

	assert(q>p && q>=p && q!<p && q!<=p);
	assert(!(q!>p) && !(q!>=p) && !(q<p) && !(q<=p));

	assert(*p==0 && *q==1);
	return true;
}
static assert(testptrcmp());


bool testrealcmp(){
	real a = 2, b = 3;

	assert(a==a && a is a && a!<>a);
	assert(!(a!=a) && !(a!is a) && !(a<>a));

	assert(a!=b && a !is b && a<>b && a<>=b);
	assert(!(a==b) && !(a is b) && !(a!<>b) && !(a!<>=b));

	assert(a<b && a<=b && a!>b && a!>=b);
	assert(!(a!<b) && !(a!<=b) && !(a>b) && !(a>=b));

	assert(b>a && b>=a && b!<a && b!<=a);
	assert(!(b!>a) && !(b!>=a) && !(b<a) && !(b<=a));

	b = 1.0L/0*0;
	assert(b!=b && b is b && b!<>=b);
	assert(!(b==b) && !(b!is b) && !(b<>=b));

	for(int i=0;i<3;i++){
		assert(a!<b && a!>b && a!<=b && a!>=b && a!<>=b && b!<>=b);
		assert(!(a<b) && !(a>b) && !(a==b) && !(a<=b) && !(a>=b));
		a=b;
		assert(a!=a);
		if(i==3) b=2;
	}
	return cast(bool)b;
}
static assert(testrealcmp());

real[] testreal(real a, real b){
	real[] r;
	r~=a;
	r~=b;
	r~=a+b;
	r~=a-b;
	r~=a/b;
	r~=b%a;
	double d = a, e = b;
	r~=d;
	r~=e;
	r~=d+e;
	r~=d-e;
	r~=d/e;
	r~=e%d;
	double f = a, g = b;
	r~=f;
	r~=g;
	r~=f+g;
	r~=f-g;
	r~=f/g;
	r~=g%f;
	//r~=a&b;
	real[] o;
	for(real* p = &r[0]; p !is &r[0]+18; p++) o~=*p;
	return o;
}
pragma(msg, "testreal: ",testreal(22.2,39.1));


int[] testbitwise(int a, int b){
	int[] r;
	r~=a&b;
	r~=a|b;
	r~=a^b;
	return r;
}
pragma(msg, "testbitwise: ",testbitwise(2883,28291));



int fops(int x){return x;}

//static assert(fops(1/fops(0)));
//static assert(foo(assert(0))); // DMD bug?

//enum x = (fops(),1);


// xP
/+int bug6498(int x)
{
	int n = 0;
	while (n < x)
		n++;
	return n;
}
static assert(bug6498(10_000_000)!=10_000_000);+/


immutable int immu=2;
int refp(ref immutable int x){
	return x;
}
pragma(msg, "refp: ",refp(immu));

int testaddr(){
	immutable int x;
	auto p = &immu;
	immutable(int*) id(immutable int* x){return x;}
	return *id(p);
	//return *(((immutable int* p)=>p)(p));
}
static assert(testaddr()==2);
pragma(msg, "testaddr: ", testaddr());

void testlocal1(){ // (should not compile)
	int x = 2;
	immutable y = x; // error
	bool tt(){return 2==y;}
	static assert(tt());
}

int testlocal2(){ // (should compile)
	immutable x = 2;
	immutable y = x;
	bool tt(){return 2==y;}
	static assert(tt());
}

int testlazy(){
	int x;
	int foo(lazy int x){return x;}
	foo(++x);
	return x;
}
pragma(msg, "testlazy: ",testlazy());

ref int testrefret(){
	int x;
	ref int foo(){ return x; }
	//ref int bar(){ return 2; }
	foo()=1;
	++foo();
	foo()++;
	foo()+=3;
	assert(x==6 && foo()==6);
	x=0;
	assert(foo()==0);
	foo()+=8;
	return x;
}
pragma(msg, "testrefret: ",testrefret());
static assert(testrefret()==8);

ref int testrefret2(){
	//auto x = delegate(ref int x)ref{ return x; };
	//auto y = delegate(ref int y)ref{ return x(y); };
	//auto z = delegate(ref int z)ref{ return x(y(z)); };
	ref int x(ref int x){ return x; }
	ref int y(ref int y){ return x(y); }
	ref int z(ref int z){ return x(y(z)); }
	int i;
	x(i)++;
	y(i)+=++z(i);
	assert(i==3); // DMD disagrees, but strict left-to-right evaluation results in this
	x(x(y(y(z(z(i))))))++;
	return x(y(z(i)));
}
static assert(testrefret2()==4);
pragma(msg, "testrefret: ", testrefret2());

int testrefoutlazy(){
	int x=1;
	void testout(out int x){
		x=2;
	}
	void testref(ref int x){
		(++x)++;
		//x+=2;
	}
	//int testlazy(lazy int x){
	int testlazy(lazy int x){
		return x+x;
	}
	void testptr(int* x){*x+=2; x+=2;}
	testout(x);
	testref(x);
	testptr(&x);
	assert(x==6);
	auto t=testlazy(x++);
	assert(t==6+7);
	return x;
}
pragma(msg, "testrefoutlazy: ",testrefoutlazy());

static assert(testrefoutlazy()==8);

int[] createclosure(){
	int[] x;
	void delegate() foo(int start, int step){
		int i = start;
		return { x~=(i+=step); };
	}
	auto dg = foo(0,1);
	auto dg2 = foo(22,-2);
	for(int i=0;i<20;i++)
		((i&1)?dg:dg2)();
	return x;
}
pragma(msg, "createclosure: ",createclosure());


int casts(){
	int[] a = null;
	immutable(int)[] b = cast(immutable)a; // error: disallow unsafe cast
	a[0]=2;
	//int* x = &a[0];
	return 0;
}
pragma(msg, casts());

int threetimes(){
	auto twiceinterprt()(){
		int x=3;
		int foo()(bool b){ return b?x:2;}
		// pragma(msg, foo(false));
		static assert(foo(false)==2);
		return &foo!();
	}
	static assert(twiceinterprt()(true)==3);
	return twiceinterprt()(true)+twiceinterprt()(false);
}
static assert(threetimes() == 5);


int twiceinterpret(){
	int accessible = 2; // only accessible from 'foo'  on the second invocation
	immutable zero = 0; // always accessible from 'foo'
	int foo(bool first){return first?zero:accessible;}
	enum y = foo(true); 
	return foo(false);
}
static assert(twiceinterpret()==2);


void invtest(){
	bool x = false;
	bool foo(){return true&&x;} // error: cannot access x
	bool ttt(){return foo();}
	static assert(ttt());
}
static assert({invtest(); return true;}()); // error




//enum a = "mixin(a); mixin(a);";
//mixin(a);

int dggg(){
	int x=2;
	int foo(){return x;}
	static int bar(){return 2;}
	auto a = &foo;
	auto b = &bar;
	static assert(is(typeof(a): int delegate()));
	static assert(!is(typeof(a): int function()));
	static assert(is(typeof(b): int function()));
	static assert(!is(typeof(b): int delegate()));
	return a()+b();
}
pragma(msg, "dggg: ",dggg());
static assert(dggg()==4);

int[] testdelegate(){
	void doall(int delegate(int) dg, int[] a, int n){
		for(int i=0;i<n;i++) a[i]=dg(a[i]);
	}
	int t = 100;
	int squareplust(int x){return x*x+t;}
	int[] a = [1,2,3,4,5,2,1928];
	doall(&squareplust, a, 7);
	return a;
	// static assert(testdelegate()==[]);
}
static assert(testdelegate()==[101,104,109,116,125,104,3717284]);
pragma(msg, "testdelegate: ",testdelegate());


int testnested2(){
	int y=3;
	int foo(){
		int x;
		int bar(){
			return x+y--;
		}
		int qux(){
			auto yp = &y;
			int foo(){
				x = 2;
				return ++*yp +bar()+(*yp)++;//*yp++; // ok, but DMD cannot do this
			}
			return foo();
		}
		return qux();
	}
	return foo();
}

pragma(msg, "testnested2: ", testnested2());
static assert(testnested2()==13);



static assert({return rettrue();}());
auto rettrue(){return {return {return true;}();}();}

int testnested(){
	int x,y;
	int *p;
	(){p=&x;}();
	(){*p=3;}();

	(){int a=3;(){int z=--a;(){y=(){return z++;}();}();}();}();
	(){x++;}();
	return (){return (int x){return (int y){return x+y;}(y);}(x);}();
	//return (){return x+y;}();
}
pragma(msg, "testnested: ",testnested());
static assert(testnested()==6);


int* aliasinp(int* x){
	auto y = &x;
	return x;
}
int testalias(){
	int a, b;
	auto p = aliasinp(&a);
	auto q = aliasinp(&b);
	*p=2;
	*q=3;
	return a+b;
}
static assert(testalias()==5);
pragma(msg, "testalias: ",testalias());


int* escapestackref(int x){
	int y = x;
	return aliasinp(&*&y);
}
int testescape(){
	int a = 11;
	int* p = escapestackref(a);
	a = 12;
	int* q = escapestackref(a);
	return *p+*q;
}
static assert(testescape() == 23); // TODO: should this be an error instead?
pragma(msg, "testescape: ", testescape());

int addr(int a){
	int* x;
	int**y = &x;
	int***z = &y;	
	a=2;
	x = &a;
	return a;
}


pragma(msg, "addr: ",addr(3));

int tailcalls(int n, int x){
	if(!n) return x;
	return 1?tailcalls(n-1, x+n):10;
}
int tcfac(int n){
	int loop(int x, int a) => x>n?a: loop(x+1,x*a);
	return loop(1,1);
}
pragma(msg, "tcfac: ", tcfac(10));


pragma(msg, "tailcalls: ",tailcalls(10000,0));

immutable(char)[] toEngNum(uint i){ // pure
	immutable static a=["zero","one","two","three","four","five","six","seven","eight","nine","ten","eleven",
	                   "twelve","thirteen","fourteen","fifteen","sixteen","seventeen","eighteen","nineteen"];
	immutable static b=[null,"ten","twenty","thirty","forty","fifty","sixty","seventy","eighty","ninety"];
	//static auto foo(int i)
	if(i>=1000000) return (uint i){immutable(char)[] s; while(i) s=(i%10+'0')~s, i/=10; return s;}(i);
	if(i>=1000) return toEngNum(i/1000)~" thousand"~(i%1000?" "~toEngNum(i%1000):"");
	if(i>=100) return toEngNum(i/100)~" hundred"~(i%100?" and "~toEngNum(i%100):"");
	if(i>=10) return i<20?a[i]:b[i/10]~(i%10?"-"~toEngNum(i%10):"");
	return a[i];
}

pragma(msg, "toEngNum: ",toEngNum(123562222));

pragma(msg, "toEngNum in a loop: ",{
		immutable(char)[][] r;
		for(int i=0;i<=1000;i++) r~=toEngNum(i);
		return r;
	}());


auto fun(int x){
	return ""~cast(byte)('0'+x);
}

auto testfuncall(){
	auto r="";
	for(int i=0;i<10;i++) r~=fun(i);
	return r;
}

pragma(msg, testfuncall());


char invass(char a, char b){
	return a~=b; // error
}
pragma(msg, invass(1,2));



auto generate(){
	auto r = `pragma(msg, "hallo");`;
	for(int i=0;i<20;i++) r~=r;
	return r;
}

//pragma(msg, generate());

enum gen = generate();
//mixin(gen);


int lvalue(){
	int a=2, b=3;
	(a*=b)+=(b*=a);
	int[] c=[1], d=[2];
	(c~=d)=d;
	int*p=&a;
	(p+=a)=p-a;
	return a+c[0]+*p;
}
static assert(lvalue() == 50);
pragma(msg, "lvalue: ",lvalue());


int[] slice(int[] e, int l, int r){
	return (&e[0]+1)[-1+l..r-1];
}

pragma(msg, "slice: ",slice([1,2,3],0,3));


int tt3(){
	//int tt3(){return 2;}
	return 3;
}

pragma(msg, "tt3: ",tt3());


int testbrkcnt(){
	int h=0,i,j=0,k=0,l=11;
	for(i=0;;i++){
		if(i>=10) break;
		else continue;
		i+=1234;
	}
 label:{h++;if(h<10) goto label;}
	do{
		j++;
		if(j>=10) break;
		else continue;
		j+=1234;
	}while(true);

	while(1){
		k++;
		if(k>=10) break;
		else continue;
		k+=1234;
	}

	{ for(;;) for(;;) goto outmost2;}
	i = 112233;
 outmost:for(outmost2:l=0;l<10;l++)
		for(;;){
			for(;;){
			next: for(;;) for(;;)break next;
				continue outmost;
			}
		}

	/+ TODO: foreach +/
	return h+i+j+k+l;
}
static assert(testbrkcnt() == 50);

pragma(msg, "testbrkcnt: ", testbrkcnt());

string testimplconv2ptr(){
	const char* x     = "hello world";
	immutable char* y = "world hello";
	immutable(char)* z= " ";
	return x[0..5]~z[0..1]~y[0..5];
}
static assert(testimplconv2ptr()=="hello world");
pragma(msg, "testimplconv2ptr: ",testimplconv2ptr());

static assert({auto x="hello"; return cast(char[])x~cast(char[])x;}()=="hellohello"); // TODO error: should this be invalid?

static assert({char[] x = cast(char[])"123"; return x~=cast(char[])x;}()=="123123"); // TODO error: cast(char[])"123" currently creates an array literal, should probably be invalid during ctfe instead. if directly assigned to an enum, creates an actual reference to read-only memory

bool strchr(immutable(char)* haystack, immutable(char)* needle){
	if(haystack is null) return needle is null;
	auto p = haystack, q = needle;
	for(;; p++){
		for(auto h=p, n=q;;h++,n++){
			if(!*n) return true;
			if(*h != *n) break;
			else continue;
		}
		if(!*p) break;
	}
	((p))=p;
	return false;
}
pragma(msg, "strchr1: ",strchr(null, null)); 
pragma(msg, "strchr2: ",strchr(null, &"\0"[0])); 
pragma(msg, "strchr3: ", strchr(&"1234"[0],&"232"[0]));
pragma(msg, "strchr4: ", strchr(&"1234"[0],&"23"[0]));
pragma(msg, "strchr5: ", strchr(&"1234"[0],&"023"[0]));
pragma(msg, "strchr6: ", strchr(&"1234"[0],&"123"[0]));
pragma(msg, "strchr7: ", strchr(&"123"[0],&""[0])); // TODO: fix?
pragma(msg, "strchr8: ", strchr("",""));


int strcmp(immutable(char)[] a, immutable(char)[] b){
	auto p = &a[0], q = &b[0];
	while(*p && *p == *q){p++,q++;}
	return *p == *q ? 0 : *p < *q ? -1 : 1;
}

pragma(msg, "strcmp: ",strcmp("122","123"));


immutable estr = ["zero","one","two","three","four","five","six","seven","eight","nine","ten","eleven","twelve","thirteen","fourteen","fifteen","sixteen","seventeen","eighteen","nineteen"];

auto toestr(int i){
	//estr[i]="hello"; // TODO: array casting
	auto p = &estr[0];
	//return *(p+i);
	return *(&p[i+1]-1)~" "~*(&p[i-199]+199);
}
static assert(toestr(19)=="nineteen nineteen");
pragma(msg, toestr(19));


long testvoid(){
	long a = 0;
	long b = 0;
	b || function(long*a){*a = 1;}(&a);
	b || {a++;}();
	a && function(long*b){++*b;}(&b);
	a && {b+=2;}();
	1 ? {a+=4;}() : ({b+=8;}(),(()=>2)());
	0 ? ({a+=16;}(),(()=>2)()) : {b+=32;}();
	return a+b;
}
static assert(testvoid()==41);
pragma(msg, "testvoid: ", testvoid());


int[][] funny(int[] a, int n, int p){
	int[][] l;
	for(int i=0;i<n;i++){
		int x,y;
		auto t=&y;
		auto c=[0,0,0];
		a[i]<p?x:a[i]==p?c[1]:*t=a[i];
		c[0]=x;
		c[2]=y;
		l~=c;
	}
	return l;
	
}

pragma(msg, "funny: ",funny([1,2,3,2,3,1,3,1,2,3,2,1],12,2));

int[][] funny2(int[] a, int n){
	int*[] ptrs;
	int[][] r;
	for(int i=0;i<n;i++) a[i]--, r~=[0,0,0];
	for(int i=0;i<3*n;i+=3) ptrs~=[&r[i/3][0],&r[i/3][1],&r[i/3][2]];
	for(int i=0;i<3*n;i+=3) *ptrs[i+a[i/3]]=a[i/3]+1;

	return r;
}


pragma(msg, "funny2: ",funny2([1,2,3,2,3,1,3,1,2,3,2,1],12));

static assert(funny([1,2,3,2,3,1,3,1,2,3,2,1],12,2)==funny2([1,2,3,2,3,1,3,1,2,3,2,1],12));

int ptrstore(){
	int x = 1;
	int* ptr = &x;
	*ptr = 2;
	return x;
}

pragma(msg, "ptrstore: ",ptrstore());


//static assert(ptrr(4) == 13);


int ptrr(int x){
	int a = x = x+++2;
	x = x--+a;
	auto y = &++--++++--x;
	auto z = &y;
	auto w = &z;
	auto u = &w;
	return *(*(*(*u)));
}
pragma(msg, "ptrr: ", ptrr(4));
static assert(ptrr(4) == 13);


int tttt(int x){
	x=2;
	int y = x++;
	return y;
}
pragma(msg, "tttt: ",tttt(2));

int ptr(int[] x){
	//int x = 222;
	auto p = &x[0];
	p++;
	auto y = p++;
	auto z = &y;
	return **z;
}
//pragma(msg, ptr(33));
pragma(msg, "ptr: ", ptr([1,2,3,4,5,6,7,8,9,10]));


immutable(char[]) acast(immutable(char)[] a){
	auto b = cast(char[])a; // error
	b[0] = 'b'; // TODO: should this be allowed or not? (error)
	return cast(immutable)b;
}
pragma(msg, "acast: ", acast(`string`));


int div(int a, int b){ return a/b; } // error
pragma(msg, "div: ", div(1,0));

int index(int[] a, int b){ return a[b]; } // error
pragma(msg, "index: ", index([1,2,3],4));

ulong shl(long a, int b){ return a<<b; } // error
pragma(msg, "shl: ", shl(1,32*2));


real ttt(){
	real[][] y=[[]];
	y[0]=[2];
	return y[0][0];
}
pragma(msg, "ttt: ",ttt());

real tt2(){
	real[] y = [1];
	y[0]=2;
	return y[0];
}

pragma(msg, "tt2: ",tt2());


real testindex(){
	real[][] x;// = [[[2,3]],[[4],[5,6]]];
	int y = 3;
	x=[[2]]~[[y+2,y+100]];
	return x[1][1];
}

pragma(msg, "testindex: ",testindex());


int[] errCastConcat(){
	float[] a = [1,2,3,4];
	return cast(int[])a~cast(int[])a; // error
}
pragma(msg, errCastConcat());


real multiindex(){
	real[][][] x = [[[2,3]],[[4],[5,6]]];
	x[0]=[[3,4],[1,2]];
	return x[0][1][1];
}

pragma(msg, "multiindex: ",multiindex());


int[][][] ttlit(int n){
	int[][][] r = [[[1]]];
	for(int i=0;i<n;i++) r~=[[[],[1,2]],[[]]];
	return r;
}

pragma(msg, "ttlit: ", ttlit(4));


int[][][][] arraylit(int n){
	int[][][][] r;
	for(int i=0;i<n;i++) r~=[[[[]]],[[[1,2],[3],[4,5]],[[6],[7]],[[8,9]]],[[[]]]];
	return r;
}

pragma(msg,"arraylit: ",arraylit(4));

//pragma(msg, [[[[]]],[[[1,2],[3],[4,5]],[[6],[7]],[[8,9]]],[[[]]]]);
//pragma(msg, cast(void)1);
//pragma(msg, [[[]],[[2]]]);

real[] foo(int x){
	real[] r;
	for(int i=0;i<x;i++) r~=i*2+3;
	return r;
}

pragma(msg,"foo: ", foo(10));

immutable(char)[] bar(immutable(char)[] input){
	immutable(char)[] r=null;
	for(int x=1;x<3;x++) r~=input;
	return r~r;
}

mixin(bar("pragma(msg,`success!`,bar(\"success!\"));"));
pragma(msg,"bar: ", bar("pragma(msg,`success!`,bar(\"success!\"));"));



int[] dupit(int[] arg, int n){
	int[] r;
	for(int i=0;i<n;i++) r~=arg[i];
	return r;

}

pragma(msg, "dupit: ",dupit([1,2,3,4,5],5));


int[] sqr(int[] arg, int n){
	int[] r;
	for(int i=0;i<n;i++) r~=arg[i], r~=arg[i]*arg[i];
	return r;
}

pragma(msg, "sqr: ",sqr([1,2,3,4,5],5));


auto teststr(){ return "test"; }
pragma(msg, "teststr: ",teststr());

auto tostr(int n){
	immutable(char)[][] r;
	for(int i=0;i<n;i++){
		immutable(char)[] s;
		if(!i) s="0";
		else s="";
		int j=i; 
		while(j) s=(j%10+'0')~s, j/=10;
		r~=s;
	}
	return r;
}

pragma(msg, "tostr: ",tostr(100));

int[] dowhile(){
	int n = 20;
	int[] r;
	do{
		r~=n--*n--;
	}while(n>0);
	return r;
}
pragma(msg, "dowhile: ",dowhile());


int[] incall(int[] arg, int n){
	for(int i=0;i<n;i++) arg[i]++;
	return arg;
}
pragma(msg, "incall: ",incall([1,2,3,4,5],5));


int[] incspec(int[] arg){
	arg[4]=arg[0]++;
	return arg;
}
pragma(msg, "incspec: ",incspec([1,2,3,4,5]));

int sum(int x){
	int y=0;
	while(x){
		y=y+x;
		x--;
	}
	return y;
}
pragma(msg, "sum: ",sum(3));

int factorial(int n){
	uint r=1;
	for(int i=2;-i>=-n;++i) r=r*i;
	return r;
}
pragma(msg, "factorial: ",factorial(12));


int[] erathos(int x){
	bool[] p;
	for(int i=0;i<=x;i++) p~=true;
	for(int i=3;i*i<=x;i+=2){
		if(p[i]) for(int k=i*i;k<=x;k=k+i) p[k]=false;
	}
	int[] r;
	if(x>=2) r~=2;
	for(int i=3;i<=x;i+=2) if(p[i]) r~=i;
	return r;
}

pragma(msg, "erathos: ",erathos(40000));
pragma(msg, "erathos2: ", erathos(100).map!toEngNum);

int[] primes(int x){
	int[] r;
	if(x>=2) r~=2;
	for(int i=3;i<=x;i=i+2){
		int d=0;
		bool isprime = true;
		for(int j=2;(j<i)&&isprime;j=j+1){
			if(!(i%j)){
				isprime = false;
				//break;
			}
		}
		if(isprime) r~=i;
	}
	return r;
}

pragma(msg, "primes: ",primes(100));

/+

//mixin("s");


//pragma(msg, bar("e"));

/+
enum e = (()=>cast(immutable)2)();
pragma(msg, 'j'~"ello");

//pragma(msg, typeof(e+cast(immutable)1));

pragma(msg, [2Li+2]<[2Li+1]);
//pragma(msg, [2i-1]<[2i+1]);

enum immutable(dchar)[] str = 'j'~"ello";
static assert(str == "jello");
pragma(msg, typeof('j'~"ello"));


pragma(msg, (()=>cast(immutable)'j')()~"ello");
pragma(msg, typeof((()=>cast(immutable)'j')()));
pragma(msg, typeof('j'~"ello"));
pragma(msg, typeof(cast(immutable)2));+/
/+auto x = 2;
int bar(){
	return 2;
	//if(auto x = -100) if(x) return (++++x)++;
}
static assert(!is(typeof({enum _ = (assert(!bar()),1);})));

pragma(msg, assert(bar()));+/



immutable int xx = 10;
auto azfoo(int x){
	real y,z;
	z=y=x+xx;
	return z;
}
pragma(msg, "azfoo: ",azfoo(2));

/+
+/

/+immutable int y=2;
immutable foo = [[[2+y]]];
immutable shared int[][][] xxx = [[[2+y]]];

pragma(msg, typeof(xxx[0]));

pragma(msg, typeof(cast(immutable)[1]));

pragma(msg, "oOoOoO: ",xxx);


auto dg = (delegate int(int x) => x)(2);+/

+/

//int x;
//pragma(__p, [2,x]~1);

// +/
// +/
// +/
alias immutable(char)[] string;
alias typeof({int[] r; return r;}().length) size_t;

auto toString(int i){
	immutable(char)[] s;
	do s=(i%10+'0')~s, i/=10; while(i);
	return s;
}
T[] iota(T)(T a, T b){ T[] r; for(T i=a;i<b;i++) r~=i; return r; }

auto map(alias a,T)(T[] arg) if(is(typeof(a(arg[0]))[])){
	typeof(a(arg[0]))[] r;
	for(int i=0;i<arg.length;i++)
		r~=a(arg[i]);
	return r;
}
auto filter(alias a,T)(T[] arg) if(is(typeof(cast(bool)a(arg[0])):bool)){
	typeof(arg) r;
	for(int i=0;i<arg.length;i++)
		if(a(arg[i])) r~=arg[i];
	return r;
}
auto join(T,S)(T[] arg, S sep){
	T r;
	for(size_t i=0;i+1<arg.length;i++)
		r~=arg[i]~sep;
	r~=arg[$-1];
	return r;
}

auto to(T,S)(S arg)if(is(S==int)&&is(T==string)){
	string r="";
	if(!arg) return "0";
	bool n = arg<0;
	if(n) arg=-arg;
	while(arg) r=('0'+arg%10)~r, arg/=10;
	if(n) r="-"~r;
	return r;
}
auto to(T,S)(S arg)if(is(S==string)&&is(T==string)){
	return arg;
}


template Seq(T...){alias T Seq;}