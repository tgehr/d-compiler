class OVIC{
	mixin(q{int foo()immutable{ return 2; }});
	int foo()        const    { return 2; }
}
class OVIbICSC: OVIC{
	override int foo()immutable           { return 2; }
	mixin(q{override int foo()const shared{ return 2; }}); // error
	override int foo()const               { return 2;}
	//int foo()inout{ return 2; }
}

class OVIbCCS: OVIC{
	mixin(q{override int foo()const{ return 2; }});
	override int foo()const shared { return 2; }
}

/+
int global;
class Container{
	int cont;
	class C{
		void foo()const{
			static assert(is(typeof(global)==int));
			static assert(is(typeof(cont)==const(int)));
			static assert(is(typeof(d)==const(D)));
			static assert(is(typeof(d.u)==const(int)));
			static assert(is(typeof(Container2.y)==int));
		}
		void foo()const shared{
			static assert(is(typeof(global)==int));
			static assert(is(typeof(cont)==const(shared(int))));
			static assert(is(typeof(d)==const(D)));
			static assert(is(typeof(d.u)==shared(const(int))));
			static assert(is(typeof(Container2.y)==int));
		}
		static void foo(){
			static assert(is(typeof(cont)==int));
			static assert(is(typeof(d.u)==int));
		}
	}
	class D{
		int u;
	}
	D d;
}
class Container2{
	static int y;
}

class DisjointDecls{
	int foo(){ return 2; }
	int foo()immutable{ return 2;}
	int bar(){ return 2; }
	int bar()shared{ return 2; }
}

class DisjointOverrides: DisjointDecls{
	override int foo(){ return 2; }
	override int foo()immutable{ return 2; }
	override int bar(){ return 2; }
	override int bar()shared{ return 2; }
}

class IHazAllFoo{
	int[] x = [1,2,3];
	int[] foo(){
		static assert(is(typeof(this)==IHazAllFoo));
		static assert(is(typeof(x)==int[]));
		return x;
	}
	const(int[]) foo()const{
		static assert(is(typeof(this)==const(IHazAllFoo)));
		static assert(is(typeof(x)==const(int[])));
		return x;
	}
	immutable(int[]) foo()immutable{
		static assert(is(typeof(this)==immutable(IHazAllFoo)));
		static assert(is(typeof(x)==immutable(int[])));
		return x;
	}
	shared(int[]) foo()shared{
		static assert(is(typeof(this)==shared(IHazAllFoo)));
		static assert(is(typeof(x)==shared(int[])));
		return x;
	}
}

class OverrideAllFoo: IHazAllFoo{
	override int[] foo(){
		static assert(is(typeof(super)==IHazAllFoo));
		static assert(is(typeof(x)==int[]));
		return super.foo(); // TODO!
	}
	override const(int[]) foo()const{
		static assert(is(typeof(super)==const(IHazAllFoo)));
		static assert(is(typeof(x)==const(int[])));
		return super.foo(); // TODO!
	}
	override immutable(int[]) foo()immutable{
		static assert(is(typeof(super)==immutable(IHazAllFoo)));
		static assert(is(typeof(x)==immutable(int[])));
		return super.foo(); // TODO!
	}
	override shared(int[]) foo()shared{
		static assert(is(typeof(super)==shared(IHazAllFoo)));
		static assert(is(typeof(x)==shared(int[])));
		return super.foo(); // TODO!
	}
}

class IHazFoo{
	final int x(){ return 2;}
	int foo(){ return x(); }
}
class IHazFoo2: IHazFoo{
	override int foo(){ return super.foo(); }
	int foo()const{ return x(); }
}

class ConstOverride: IHazFoo2{
	override int foo(){ return x(); }
	override int foo()const{ return x(); }
}

class ConstOverride2: IHazFoo{
	override int foo()const{ return x(); }
}

class ConstOverride3: ConstOverride2{
	override int foo(){ return x(); } // error
}

class ConstOverride4: IHazFoo2{
	override int foo(){ return super.foo(); } // TODO
	override int foo()inout{ return x(); }
}

class CircOverride1: CircOverride2{
	override int foo(int x){ return x; }// ok (hidden by circular inheritance)
	override int bar(int x){ return x; }// ok (hidden by circular inheritance)
}
class CircOverride2: CircOverride1{
	override int foo(int x){ return x; }// ok (hidden by circular inheritance)
}

class HasFoo{
	auto foo(HasFoo x){ return x; }
}
class OverridesFoo: HasFoo{
	override HasFoo foo(HasFoo x){ return this; } // ok
	override auto foo(HasFoo x){ return this; } // error
	override void foo(HasFoo x){ } // error
	override auto foo(OverridesFoo x){ return this; } // error
	HasFoo foo(HasFoo x){ return this; } // ok, additional overload
}
class HidesFoo: HasFoo{
	final HidesFoo foo(HasFoo x){ return this; } // error
}

class HasFooOverloads{
	auto foo(HasFooOverloads x){ return x; }
	int foo(int x){ return x; }
}
class OverridesFoo2: HasFooOverloads{
	override foo(int x){ return x; } // error
}
class OverridesFoo3: HasFooOverloads{
	final override foo(int x){ return x; } // ok
	override foo(HasFooOverloads x){ return x; } // ok
}
class OverridesFoo4: OverridesFoo3{
	override foo(int x){ return x; } // error (final in base class)
	override foo(HasFooOverloads x){ return x; } // error (shadows the final method)
}

class OverridesFoo5: HasFooOverloads{
	private int foo(int x){ return x; } // ok (TODO: should private even overload against public?, should functions with the same argument types even be allowed to coexist?)
	override int foo(int x){ return x; } // ok
	override auto foo(HasFooOverloads x){ return x; } // ok
}
class OverridesFoo6: HasFooOverloads{
	package int foo(int x){ return x; } // ok
}

class HasFinalFoo{
	final int foo(int x) { return x; }
}
class HidesFinalFoo: HasFinalFoo{
	final int foo(int x) { return x; }// ok
}


class GG{ enum gg = "gg"; }
class HH: GG{ enum hh = "hh"; }
class II: HH{ enum ii = "ii"; }
class IIHH:II{ enum iihh = ii~hh; }
class GGHH:HH{ enum gghh = gg~hh; }
class GGHHII: II{ enum gghhii = gg~hh~ii; }
pragma(msg, GG.gg,HH.hh,HH.gg,II.ii,II.hh,II.gg,IIHH.iihh,IIHH.ii,IIHH.hh,IIHH.gg,GGHH.gghh,GGHH.gg,GGHH.hh,GGHHII.gghhii,GGHHII.gg,GGHHII.hh,GGHHII.ii);
static assert(GG.gg~HH.hh~HH.gg~II.ii~II.hh~II.gg~IIHH.iihh~IIHH.ii~IIHH.hh~IIHH.gg~GGHH.gghh~GGHH.gg~GGHH.hh~GGHHII.gghhii~GGHHII.gg~GGHHII.hh~GGHHII.ii=="gghhggiihhggiihhiihhgggghhgghhgghhiigghhii");


class PP{
	enum x = "success!";
}
interface I{
	enum y = "success!!";
	enum x = 2;
}
class CC : PP,I{
	pragma(msg, x," ",y);
	static assert(x=="success!"&&y=="success!!");
}

interface HasX{ int x(); }

// (TODO: traits getMember)
template IfDoesNotHaveMemberX(alias from, alias A){
	static if(is(typeof(from.x))) alias Seq!() IfDoesNotHaveMemberX;
	else alias A IfDoesNotHaveMemberX;
}
template IfDoesNotHaveMemberY(alias from, alias A){
	static if(is(typeof(from.y))) alias Seq!() IfDoesNotHaveMemberY;
	else alias A IfDoesNotHaveMemberY;
}

//class NoContradict2: IfDoesNotHaveMemberY!(NoContradict2, HasX){} // TODO: should this work?

static assert(!is(typeof({
	class Contradict2: IfDoesNotHaveMemberX!(Contradict2, HasX){}
})));


//static if(!is(typeof(a))) enum b = 2;
//static if(!is(typeof(b))) enum a = 2;


template Test(bool x){
	static if(x) enum Test = false;
	else enum Test = true;
}

pragma(msg, Test!false);

//static if(!is(typeof(b))) enum a = 2;
//static if(!is(typeof(a))) enum b = 2;
//pragma(msg, a);


template IfNotConvertible(alias From, alias To, alias A){
	static if(is(From:To)) alias Seq!() IfNotConvertible;
	else alias A IfNotConvertible;
}
class AClass{}

static assert(!is(typeof({
	class Contradict: IfNotConvertible!(Contradict, AClass, AClass){}
})));

class NoContradict: AClass, IfNotConvertible!(NoContradict, AClass, AClass){}


int test(){
	NoContradict c;
	AClass b = c;
	return 2;
}
//pragma(msg, test());



class X{}
class Y:X{}
class Z:Y{}

static assert(is(Y:X));
static assert(is(Z:Y));
static assert(is(Z:X));

void test(){
	X x;
	Y y;
	Z z;
	x=z;
	x=y;
	y=z;
	static assert(!is(typeof(z=x)));
	static assert(!is(typeof(y=x)));
	static assert(!is(typeof(z=y)));

	auto a = [y,z];
	static assert(is(typeof(a)==Y[]));
}

class U: X{}
class V: Y{}


void test2(){
	U u;
	V v;
	const(U) cu;
	const(V) cv;
	auto a = [u,v];
	static assert(is(typeof(a)==X[]));

	auto b = [cu,cv];
	pragma(msg, typeof(b));
	static assert(is(typeof(b)==const(X)[])); // TODO!
}

alias Seq!int P;
interface W{}
class TT:Seq!(X,W){}

static assert(!is(typeof({class Foo:X,X{}})));

static assert(!is(typeof({
	struct S{
		class I4:G{}
		class I3:I1{}
		class I2:I3{}
		class I1:I2{}
		class G:I1{}
	}
})));



static assert(!is(typeof({
	interface FI{}
	class F{
		class C:Seq!(B!C,FI){int x;}
	}
})));
class B(T){
	static assert(is(T: B!T));
	static assert(is(IN:B!IN));
}

class A(T){
	pragma(msg, T);
	static assert(is(T: A!T),T);
	pragma(msg, "1 of ",T,":", is(T: A!T));
	pragma(msg, "2 of ",T,":", is(A!T: T));
	static assert(is(E:A!E));
}

static assert(!is(typeof({pragma(msg, "is(A!int): ",is(A!int)," ",A!int);})));

pragma(msg, is(A!E));

class C : A!C{}

class D(T) : A!T{
	// static if(is(T==D)) enum x = "success!";
	// static if(is(T:C!T)) enum x = "success!";
}


class E: D!E{
	//pragma(msg, x);
}

//pragma(msg, D);
//pragma(msg, C!D);



// +/
// +/
// +/

template Seq(T...){alias T Seq;}
alias immutable(char)[] string;