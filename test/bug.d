struct S{
	void foo(){ bar(); }
	void bar(){ foo(); }
}

/+class C{
	final int foo(){ return 1; }
	int x;
	void bar(){
		enum e=this.foo();
		//enum e=x; // TODO: improve error message
	}
}+/

/+static void foo(){
	static struct S{ S delegate() dg; }
	S bar(){
		S s;
		s.dg=&bar;
		return s;
	}
	pragma(msg, bar()); // error
	struct T{ int x; }
	T baz(){
		T t;
		t.x=2;
		return T;
	}
	pragma(msg, baz()); // error
	static struct U{ int x; }
	U qux(){
		U u;
		u.x=2;
		return u;
	}
	pragma(msg, qux().x); // ok
}

struct TemplateParameterAccessCheck{
	enum ID1(alias e)=e;
	enum ID2(int delegate() e)=e;
	enum ID3(alias e)=&e; // error
	
	static void foo(){
		static int sbar()=>2;
		static int sbaz()=>ID1!(&sbar)();
		static assert(sbaz()==2);
		int kbar()=>3;
		int kbaz()=>ID2!(&kbar)();
		static assert(kbaz()==3);
		enum e=&kbar, f=&sbar;
		static assert(e()==3 && f()==2);
		int x;
		int kobar()=>x;
		pragma(msg, kobar()); // error
		enum g=&kobar; // error
		int kobaz()=>ID3!kobar;
	}
}+/

/++struct S{
	immutable f = function()pure immutable{}; // TODO: bail out for the correct reason
}+/

/+
struct ComparisonTests{
	alias Seq(T...)=T;
	static:
	auto seq(T...)(T args)=>args;
	enum a=1, b=2, c=3;
	alias Foo(bool b)=Seq!(b?Seq!(a,b,c):seq(a,b,c));
	static assert(Foo!false==Seq!(1,false,3));
	static assert(Foo!true==Seq!(1,true,3));
	static assert(!is(typeof({static assert(Foo!true!=Seq!(1,true,3));})));

	bool cmptest(int a,int b){
		return Seq!(a,b)!=seq(1,2);
	}
	//pragma(msg, cmptest(1,2));
}
+/

// ref void foo(){ return; } // // TODO: should this fail?

/+alias Seq(T...)=T;
enum ESeq{ foo=Seq!(1,2), bar=Seq!(2,3) } // TODO? (TODO: bug report against DMD?)
pragma(msg, ESeq.foo);+/

//pragma(msg, typeof(CDX.foo));

/+
class C{
	auto _InsertAllBut(int v) {
		int* node = null;
		//enum mutable = is(typeof({node.value;}));
		enum foo = {return ()=>node;}; (DMD stores runtime context pointer in enum constant magically.)
		return 2;//foo()();
	}
}

pragma(msg, (()=>(new C())._InsertAllBut(2))());
+/


/+enum Foo{
	xxx
}

immutable arr = [Foo.xxx]; // TODO+/

/+
immutable int x=2;
immutable int* p = &x + 1; // TODO: error

int y=2;
int* q=&y; // TODO: ok.
+/

/+struct ByteCodeBuilder{
	class Node{}
	private ulong[] byteCode;
	private Node[] errtbl;
	auto getByteCode(){
		enum Instruction{errtbl}
		alias immutable(ulong)[] ByteCode;
		return cast(ByteCode)((byteCode~=Instruction.errtbl)~=cast(ByteCode)errtbl); // BUG (also: bad error message)
	}
}+/

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


/+template asdf(){ }
template Uninstantiable() if(asdf(2)){}
template Instantiable() if(Uninstantiable!()){}
pragma(msg, typeof(Instantiable!())); // show error!+/

/+template asdf(){ enum asdf=(int x)=>true; }
template Uninstantiable() if(asdf(2)){}
template Instantiable() if(Uninstantiable!()){}
pragma(msg, typeof(Instantiable!()));+/

/+
template Seq(T...){ alias T Seq; }
int aMatchError(R)(Seq!R delegate(int) dg){ return dg(2); }
pragma(msg, aMatchError(a=>a)); // TODO: remove reference to matcher type in error message
+/


/+improve error messages!+/

/+pragma(msg, ElementType!(int));
template ElementType(T=S,S=T){ alias typeof({T t; return t[0];}()) ElementType; }
+/

/+
auto testtemplatefunclit(fun...)(){
	static if(!fun.length) return "";
	else{
		alias fun[0] tmpl;
		static if(is(typeof(tmpl!(double,string)))) alias tmpl!(double,string) ff;
		else alias tmpl ff;
		// pragma(msg, typeof(ff));
		return ff(0,4.5,"fun ")()~testtemplatefunclit!(fun[1..$])();
	}
}
struct FunContainer{
	static fun(int x,double y,string z)=>()=>z~"hi1";
}
pragma(msg, "testtemplatefunclit 1: ",testtemplatefunclit!(FunContainer.fun)());
+/

// +/
// +/
// +/

alias immutable(char)[] string;
