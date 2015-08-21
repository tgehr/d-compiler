
struct DefaultArgumentsWithContext{
	struct S{
		int x;
		int foo(int y=(()=>x)(),int z=bar()){ return y+bar(); } // TODO
		int bar(){ return 1337; }
	}
	struct T{
		int test(){
			S s;
			s.x=3;
			int bar(S k=s){
				return k.foo();
			}
			return bar();
		}
		pragma(msg, test());
		
		pragma(msg, S().foo());
	}
}


alias immutable(char)[] string;

void foo(int a, string b){}

void main(){
	foo(1,2); // error
	foo("1",2); // error
	foo("1","2"); // error
	auto bar = &foo;
	bar(1,2); // error
	bar("1",2); // error
	bar("1","2"); // error
}


class InternetAddress{
	this(string host, ushort port){
		/* ... */
	}
	this(){ /* ... */ }
}

struct Socket{
	void connect(InternetAddress addr){ /*...*/ }
}

void main(){
	Socket socket;
	struct Foo{
		this(string host, uint port){
			socket.connect(new InternetAddress(host, port)); // error
		}
	}
}
