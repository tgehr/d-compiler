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