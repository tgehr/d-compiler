struct S{
	int s;
	static struct G{
		//pragma(msg, typeof(s));
		void foo(){
			typeof(s) x;
			static assert(!is(typeof({cast(void)s;})));
		}
	}
}
