/+void foo(int, int){}
void foo(double, int){}

void bar(const int){}
void bar(shared int){}

void qux(double){}
void qux(int,double=2){} // this one should be called

void qux2(int){} // this one should be called
void qux2(int,double=2.0){}

void baz(int x, double y){}
void baz(immutable(int) x, double y){}+/

//auto lol(){return lol(1);}
//int lol(typeof(lol()) x){return lol();}
//int lol(int){return 1;}

//int bar(typeof(lol)*x){pragma(msg,typeof(x));return 2;}

//int duh(typeof(guh) duh){} // no error, investigate
//typeof(duh)* duh(typeof(duh)* duh){return 1;}
//int duh(typeof(guh)){return 1;}
//int guh(typeof(duh)){return 2;}

//auto a(){return a(1);}
//auto a(int){return a();}

int foo(immutable(char)[] s){return 0;}
//double foo(immutable(dchar)[] s){return 0;}
//double foo(immutable(dchar)[] d){return 0;}


void main(){
	pragma(msg, typeof("hello"));
	pragma(msg, typeof(foo("hello")));
	/+qux(1);
	qux2(2);

	//duh(guh);
	//duh(1);
	//duh(duh);+/
	//pragma(msg,typeof(lol()));
/+
	foo(1,1);
	foo(1.0,1);
	foo(1,1L);

	bar(1);
+/
	//baz(1,1);
}