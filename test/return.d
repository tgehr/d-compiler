ref foo(return ref int x)@safe{ return x; } // ok
ref bar(ref int x){ return x; } // TODO: error
