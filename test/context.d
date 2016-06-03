
struct I12305a{
	static:
	struct A{
		int x;
		this(int x){ this.x=x; }
		int fun(){ return x;}
		int[] caller(T)(T t){
			int[] r;
			r~=T.callee();
			r~=(x++,t).callee();
			return r;
		}
	}
	struct B{
		alias callee = A.fun;
	}
	void main(){
		A a; B b;
		a.caller(b);
	}
	pragma(msg, A(2).caller(B()));
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

// +///+///+/
