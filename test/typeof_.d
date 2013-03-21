struct S{
	template s(){
		int s = 2;
	}
	struct G{
		//pragma(msg, typeof(s));
		void foo(){
			pragma(msg, S.s!());// TODO
			s!();
		}
	}
	static void foo(){
		//typeof(s) y;
	}
}

//alias S.G.foo a;
//pragma(msg, typeof(a()));