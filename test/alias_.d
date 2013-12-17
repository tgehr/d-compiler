
struct AliasToNonOverloadable{
	static:
	int x;
	int foo(){ return 2; }
	alias foo = x; // error
	alias foo = 2; // error
	alias foo=foo; // TODO
	static assert(foo()==2);
}

struct OverloadAliasToMemberOfMember{
	struct S{
		int foo(){ return 0; }
		//int foo(){ return 0; }
		struct T{
			int foo(int){ return 1; }
		}
		T t;
		alias t.foo foo; // TODO
	}
	enum s=S();
	pragma(msg, "foo: ",s.foo()," ",s.foo(1)); // TODO
}
/+
struct TemplateFunctionLiteralAlias{
	alias id = (a)=>a;
	alias plus = (a,b)=>a+b;
	static assert(id(1)==1 && id(2.5)==2.5);
	static assert(plus(1,2)==3 && plus(1,2.5)==3.5 &&
	              plus(1.5,2)==3.5 && plus(1.25,2.25)==3.5);
}

struct AliasToSuperMember{
	alias intp = int*;

	class A{
		int foo(){ return 0; }
		alias self=typeof(this);
	}
	class B: A{
		override int foo(){ return 1; }
		template ID(alias a){ alias ID = a; }
		alias typeof(this).foo bar;
		// alias typeof(this).foo bar; // TODO
		alias super.foo baz;
	}
	static assert((()=>(new B()).bar()==1)());
	//static assert(new B().baz()==0);
	static assert((()=>(new B()).baz()==1)());// // TODO: what is the right behaviour here? (DMD agrees)
}

struct AliasToOwnMember{
	struct S{
		int x;
		struct T{
			int x;
		}
		T t,tt;
		alias t.x y;
	}
	static foo1(){
		S s;
		s.t.x=2;
		return s.y+s.x;
	}

	static foo2(){
		S s;
		s.y=2;
		return s.t.x+s.x;
	}
	static foo3(){
		S s,t;
		s.y=2;
		return t.y;
	}

	static assert(foo1()==2 && foo2()==2 && foo3()==0);

	static baz(alias z)(){ return z; }
	
	static bar1(){
		S s;
		s.y=2;
		return baz!(s.y)();
	}
	static bar2(){
		S s;
		s.t.x=2;
		return baz!(s.y)();
	}
	static bar3(){
		S s;
		s.y=2;
		return baz!(s.t.x)();
	}
	static bar4(){
		S s,t;
		s.tt.x=2;
		return baz!(s.t.x)();
	}

	static assert(bar1()==2 && bar2()==2 && bar3()==2 && bar4()==0);
	pragma(msg, bar1());
}

struct AliasToMemberReloaded{
	// // TODO: DMD does not seem to allow this?
	struct S{
		int x;
		alias x y;
	}
	static fun(alias a)(){ return a; }
	static foo(){
		S s;
		s.y=2;
		return fun!(s.x)();
	}
	static assert(foo()==2);
}

struct AliasToMember{
	struct S{
		int x;

		template ID(alias a){ alias a ID; }
		int bar(){
			alias x y;
			alias ID!x yy;
			alias ID!(this.x) yyy;
			return y+++yy+ ++yyy;
		}
	}

	static foo(){
		S s;
		s.x=2;
		alias s.x y;
		return s.bar()+y;
	}

	static assert(foo()==13);
}

//alias int foooo;
void foooo(){}
void goooo(int){}
alias goooo foooo; // TODO: fix
//alias double foooo;

pragma(msg, foooo); // error




alias int y;
alias y[] x;
alias y* z;
alias x* w;
pragma(msg, z," ",w);


static assert(!is(typeof({
				int[] i;
				alias i[] j;
			})));

pragma(msg, typeof(cast(immutable)true~a));

immutable typeof(*{z v;return v;}()) a = [1,2,3]; // error
pragma(msg, a);

void main(){
	z x;
	const typeof(*{typeof(x) v;return v;}()) a = [2,3,4]; // error
	pragma(msg, a);
}

alias aa bb; // error
alias bb cc;
alias cc aa;

// +/