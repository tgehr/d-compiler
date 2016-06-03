struct TestContextInference{
	static:
	int f(alias x)(){ return 0; }
	int g(alias x)(){ return x; }
	int h(A...)(){ return A[0]; }
	struct S{
		int x;
		enum a = f!x(); // ok
		enum b = g!x(); // error
		enum c = h!x(); // error
	}
	struct T {
		int x=2;
		static int foo(){
			auto a = f!x(); // ok
			auto b = g!x(); // error
			auto c = h!x(); // error
			return a;
		}
		static int bar(){
			return f!x();
		}
		static assert(bar()==0);
	}
}

struct I12286{
	class A { int i; }
	class B: A { int j; }
	template copy(alias a, alias b){
		void copy(){ a = b; } // TODO
	}
	class C: B{
		alias copyIJ = copy!(i, j);
	}
}

struct Test{
	int x=2;
	int foo(){ return x; }
	int call(alias a)(){ return a(); }
	pragma(msg,Test().call!foo);
}

struct I11533{
	struct S{
		void put(alias fun)(){ fun!int(); }
	}
	void main(){
		static void foo(T)(){}
		S s;
		s.put!foo();
		static void bar(alias fun)(){ fun(); }
		void nested(){}
		bar!nested();
	}
}

struct I12305a{
	static:
	struct A{
		int x;
		this(int x){ this.x=x; }
		int fun(){ return x;}
		int[] caller(T)(T t){
			int[] r;
			r~=T.fun();
			r~=(x++,t).fun();
			return r;
		}
	}
	struct B{
		alias fun = A.fun;
	}
	void main(){
		A a; B b;
		a.caller(b);
	}
	static assert(A(2).caller(A(10))==[2,10]);
	static assert(A(2).caller(B())==[2,3]);
}

struct I12305b{
	class A{
		void fun(){ }
		class B{
			alias fun = A.fun;
		}
	}
	void main(){
		A a = new A;
		A.B b = a.new B; // TODO
		b.fun(); // TODO
	}
}

struct I12230{
static:
	int[] test(){
		int[] r;
		void writeln(int arg){
			r~=arg;
		}
		template T(alias a){
			void foo(){ writeln(a); }
		}
		struct S{
			int i = 1;
			@property int p(){ return 2; }
			alias ti = T!i; // OK
			alias tp = T!p; // Error
		}
		S s;
		s.ti.foo();
		s.tp.foo();
		return r;
	}
	static assert(test()==[1,2]);
	pragma(msg, "I12230: ",test());
}

struct I12285{
	static:
	struct S{
		int a, c;
		template toA(alias s){
			void copy(){
				a = s;
			}
		}
		alias cToA = toA!c;
	}

	bool test(){
		S s;
		s.c = 42;
		s.cToA.copy();
		assert(s.a == 42);
		return true;
	}
	static assert(test());
}

// +/// +/// +/// +/// +/// +/
