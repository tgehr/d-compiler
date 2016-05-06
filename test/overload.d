

bool testFwdDecl(int x);
static assert(testFwdDecl(2) && !testFwdDecl(3));
bool testFwdDecl(int x)=>x==2;

template iftioverload(T){
	T iftioverload(T a, float b){return a;}
	int iftioverload(int a, double b){return a;}
}

void testiftioverload(){
	iftioverload!()(2,2); // TODO: how should this behave?
}


alias immutable(char)[] string;

int fun(int delegate(int,int) a){return a(1,2);}
auto fun(string delegate(int,string) b){return b(1,"2");}

pragma(msg, fun((a,b){static if(is(typeof(b)==string)) return ""; else return 2;})); // error: ambiguous



int fun(int delegate(int,int) a, string delegate(int,string) b){return a(1,2);}
int fun(string delegate(int,string) b, int delegate(int,int) a){return a(1,2);}

pragma(msg, fun((a,b){static if(is(typeof(b)==string)) return 1; else return "";}, (a,b)=>b));// error: no match



bool isLvalue(ref int x){return true;}
bool isLvalue(int x){return false;}

static assert(!isLvalue(1));
static assert({int x;return isLvalue(x);}());

bool testRefOv(ref int x, double y){return true;}
bool testRefOv(int x, int y){return false;}

static assert(!testRefOv(1,1));
static assert(!{int x;return testRefOv(x,1);}());
static assert({int x;return testRefOv(x,1.0);}());
static assert(!is(typeof({return testRefOv(1,1.0);})));

bool testRefOv2(const ref int){ return true; }
bool testRefOv2(ref immutable(int)){ return false; }

static assert(is(typeof({immutable int x; return testRefOv2(x);})));
static assert(!{immutable int x; return testRefOv2(x);}());



int foo(typeof(foo(2,3)) x){return x;} // TODO
int foo(int,int){return 2;}


bool foo(undef){return 1;} // error
bool foo(undef a,undef b){return e;} // error
pragma(msg, foo("asdf","asdf"));

void foo(int, int){}
void foo(double, int){}

void bar(const int){}
void bar(shared int){}

void qux(double){}
void qux(int,double=2){} // this one should be called

void qux2(int){} // this one should be called
void qux2(int,double=2.0){}

void baz(int x, double y){}
void baz(immutable(int) x, double y){}

//auto lol(){return lol(1);}
//int lol(typeof(lol()) x){return lol();}
//int lol(int){return 1;}

//int bar(typeof(lol)*x){pragma(msg,typeof(x));return 2;}

//auto a(){return a(1);}
//auto a(int){return a();}

int foo(immutable(char)[] s){return 0;}
double foo(immutable(wchar)[] d){return 0;}
double foo(immutable(dchar)[] s){return 0;}

void testref(int y){}
void testref(out int x){const(int) d=x;testref(d);}
void testref(ref immutable int y){}


immutable str = "hello";
void main(){
	enum str=str;
	pragma(msg, typeof("hello"));
	pragma(msg, typeof(foo("hello"d)));
	pragma(msg, typeof(foo(str)));
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

// +/