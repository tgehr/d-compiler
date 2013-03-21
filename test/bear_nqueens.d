template State(ulong Cols=0, ulong Diag135=0, ulong Diag45=0, ulong Solution=0) {
	enum ulong cols = Cols;
	enum ulong diag135 = Diag135;
	enum ulong diag45 = Diag45;
	enum ulong solution = Solution;
}

template Test(int k, int j, alias state) {
	enum bool Test = ((state.cols	 & (1UL << j)) +
	                  (state.diag135 & (1UL << (j + k))) +
	                  (state.diag45	 & (1UL << (32 + j - k)))) == 0;
}

template Mark(int k, int j, alias state) {
	alias State!(state.cols	   ^ (1UL << j),
	             state.diag135 ^ (1UL << (j + k)),
	             state.diag45  ^ (1UL << (32 + j - k)),
	             state.solution
	) Mark;
}

template AccumulateResult(int startValue, int times, alias state) {
	static if (times == 0)
		alias state AccumulateResult;
	else
	alias AccumulateResult!(startValue + 1,
	                        times - 1,
	                        State!(state.cols,
	                               state.diag135,
	                               state.diag45,
	                               state.solution + Test!(0, startValue, state))
	) AccumulateResult;
}

template ResultFromTest(bool condition, alias state, int current, int niv, int dx) {
	static if (condition == 0)
		alias state ResultFromTest;
	else
	alias Mark!(niv,
	            current,
	            Solve!(niv - 1,
	                   dx,
	                   Mark!(niv, current, state))
	) ResultFromTest;
}

template ProcessQueens(int begin, int times, alias state, int niv, int dx) {
	static if (times == 0)
		alias state ProcessQueens;
	else
	alias ProcessQueens!(begin + 1,
	                     times - 1,
	                     ResultFromTest!(Test!(niv, begin, state), state, begin, niv, dx),
	                     niv,
	                     dx
	) ProcessQueens;
}

template Solve(int niv, int dx, alias state=State!()) {
	static if (niv == 0)
		alias AccumulateResult!(0, dx, state) Solve;
	else
	alias ProcessQueens!(0, dx, state, niv, dx) Solve;
}

template MetaNQueens(int dx) {
	enum ulong MetaNQueens = Solve!(dx - 1, dx).solution;
}


static assert(MetaNQueens!(1)==1);pragma(msg,"1:", MetaNQueens!1);
static assert(MetaNQueens!(2)==0);pragma(msg,"2:", MetaNQueens!2);
static assert(MetaNQueens!(3)==0);pragma(msg,"3:", MetaNQueens!3);
static assert(MetaNQueens!(4)==2);pragma(msg,"4:", MetaNQueens!4);
//static assert(MetaNQueens!(5)==10);pragma(msg,"5:", MetaNQueens!5);
//static assert(MetaNQueens!(6)==4);pragma(msg,"6:", MetaNQueens!6);
//static assert(MetaNQueens!(7)==40);pragma(msg,"7:", MetaNQueens!7);

