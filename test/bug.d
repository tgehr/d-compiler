
/+
class C{
	auto _InsertAllBut(int v) {
		int* node = null;
		//enum mutable = is(typeof({node.value;}));
		enum foo = {return ()=>node;};
		return 2;//foo()();
	}
}

pragma(msg, (()=>(new C())._InsertAllBut(2))());
+/


/+alias immutable(char)[] string;

void main(){
	string delegate(string, double) dg = (n, int x){return "";};
	import std.stdio; writeln(dg("2",2));
}+/


/+enum Foo{
	xxx
}

immutable arr = [Foo.xxx]; // TODO+/


/+auto foo(){
	void[][] x = [["1","2","3"],cast(void[])[1,2,3]];
	x[0]=x[1];
	return x;
}
pragma(msg, foo());
+/

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
