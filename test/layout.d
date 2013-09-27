struct PartialInitialization{
	struct S{
		int x;
		int y;
	}
	union U{
		int y;
		S x;
	}
	static test(){
		U u;
		u.x.x=2; // error
		return true;
	}
	pragma(msg, "test: ", test());

	static test2(){
		U u;
		u.y=3;
		return u.x.x; // error
	}
	pragma(msg, "test2: ", test2());

	static test3(){
		U u;
		u.y=3;
		S s;
		s.x=2;
		s.y=3;
		u.x=s;
		return u.x;
	}
	pragma(msg, "test3: S(",(()=>test3().x)(),",",(()=>test3().y)(),")");

	static test4(){
		U u;
		S s;s.x=2;s.y=3; // // TODO: struct default constructors
		u.x=s;
		return u.y; // error
	}
	pragma(msg, "test4: ",test4());

	struct S1{
		int x;
	}
	union U2{
		int x;
		double y;
	}
	static ttest1(){
		union G{
			S1 x;
			U2 u;
		}
		G g;
		g.x.x=2; // ok
		g.u.y=2.0; // ok
		return g.x.x; // error
	}
	pragma(msg, "ttest1: ", ttest1());

	static ttest2(){
		union G{
			U2 u1;
			U2 u2;
		}
		G g;
		auto x=g.u1.x;
		g.u2.y=3;
		return g.u1.y;
	}
	pragma(msg, "ttest2: ", ttest2());

	static ttest3(){
		union U1{
			int x;
			double y;
		}

		union U2{
			int x;
			double y;
			U1 u1;
		}
		union G{
			U2 u1;
			U2 u2;
		}
		G g;
		g.u2.y=3.0;
		assert(g.u1.y==3.0);
		assert(g.u2.y==3.0);
		U1 u; u.y=3.0;
		U2 uu; uu.u1=u;
		g.u2=uu;
		123;
		return g.u1.u1.y;
	}
	pragma(msg, "ttest3: ", ttest3());

}

struct UnionImplicitStatic{
	static x(){
		int bar=2;
		union U{
			int a;
			float b;
			int foo(){
				return bar; // error
			}
		}
		U u;
		u.a=0;
		u.b=2;
		return u.foo();
	}
	pragma(msg, x());
}

struct UnionLimitations{
	union U{
		int x=2;
		double y;
		int z;
		immutable(int) w;
	}
	union G{
		int x=2;
		union{ // TODO
			int y=0; // TODO: error
		}
	}
	union H{
		int x=2;
		union U{
			int y=0;
		}
		U y; // ok
	}
	static y(){
		U u;
		return u.x; // ok
	}
	static assert(y()==2); // TODO
	static z(){
		U u;
		return u.y; // error
	}
	pragma(msg, "z: ",z());
	static w(){
		U u;
		u.y=2;
		return u.x; // error
	}
	pragma(msg, "w: ",w());
	static uu(){
		U u;
		u.x=2;
		return u.y; // error
	}
	pragma(msg, "uu: ",uu());
	static uw(){
		U u;
		u.x=3;
		return u.z; // ok
	}
	pragma(msg, "uw: ", uw());
	static assert(uw()==3);
	static ux(){
		U u;
		u.x=2;
		return u.w; // error
	}
	pragma(msg, "ux: ",ux());
	static uxx(){
		U u;
		return &u.w; // error // TODO: make it error for the right reason?
	}
	pragma(msg, "uxx: ", uxx());

	static uyy(){
		U u;
		u.y=2.0;
		auto x = &u.y; // TODO
		u.x=2;
		return *x; // TODO: error
	}
	pragma(msg, "uyy: ", uyy());

	static uzz(){
		U u;
		u.y=2.0;
		auto x = &u.y; // TODO
		u.x=2;
		u.y=123.0;
		return *x; // ok
	}
	static assert(uzz()==123.0);
	pragma(msg, "uzz: ", uzz());
	
	static uww(){
		U u;
		u.y=2.0;
		auto x=u.y;
		u.x=3;
		x+=u.x++;
		return x+u.z;
	}
	pragma(msg, "uww: ", uww());
	static assert(uww()==9.0);
}


// +/
// +/
// +/
// +/