
auto ret(){
	typeof(return) x; // error
	return x;
}

typeof(return) x=2; // error

int foo(){
	typeof(return)[] x=[1,2,3];
	return x[1];
}

auto bar(){
	return 2;
	//typeof(return)[] x=[1,2,3];
	pragma(msg, typeof(return));
	return 2.0; // error
	pragma(msg, typeof(return));
}


class S{
	template s(){
		int s = 2; // TODO: error
	}
	int x;
	void foo(){
		s!()=3;
	}
	class G{
		//pragma(msg, typeof(s));
		void foo(){
			// pragma(msg, S.s!());
			x = 2; // TODO
		}
	}
	static void foo(){
		//typeof(s) y;
	}
}

//alias S.G.foo a;
//pragma(msg, typeof(a()));

