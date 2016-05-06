/+
void circ1()(){ circ2(); }
void circ2()(){ circ1(); }
pragma(msg, typeof(&circ1!()));

void foo()(){
	//pragma(msg, typeof(&foo!()));
	bar();
	baz();
}

void bar()()pure @safe{
	return foo();
}
void baz()pure @safe{}

alias a=foo!();
pragma(msg, typeof(&a));
+/
/+void foo(){
	immutable int x=2;
	pragma(msg, typeof(()=>x));
}+/
/+struct S(){
	void foo(){ bar(); }
	void bar(){ foo(); }
}
S!() s;

pragma(msg, typeof(&s.bar));+/
