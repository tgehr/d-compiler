
//immutable(int delegate()) dg;
//pragma(msg, typeof(cast()dg));

//pragma(msg, is(int delegate(): int delegate()const));


template ID(alias T){ alias T ID; }
template GetParent(T){
	alias ID!(mixin((()=>(new T).foo())())) GetParent;
}
class B{ auto foo(){ return "A"; }}
class A: GetParent!A{
	override foo(){ return "B"; }
}

/+

	mixin("int a;");
class A{
	int a;
	this(){
		a = 10;
	}
}

enum x = (()=>(new A()).a)();
pragma(msg, x);+/
/+
template ID(alias T){ alias T ID; }
template GetParent(T){
	alias ID!(mixin((()=>(new T).foo())())) GetParent;
}
class B{ auto foo(){ return "A"; }}
class A: GetParent!C{
	override foo(){ return "C"; }
}
class C: GetParent!B{
	override foo(){ return "B"; }
}
class D: GetParent!A{
	override foo(){ return "D"; }
}
static assert(is(A:B) && is(C:A) && is(D:C));


alias immutable(char)[] string;


+/