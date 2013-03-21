
struct TestVirtualCall{
	class A{ string foo(){ return "B"; }}
	class B: A{ override string foo(){ return "A"; }}
	template Mixin(string s){
		mixin("alias "~s~" Mixin;");
	}
	class C: Mixin!({A a = new B; return a.foo();}()){
		static assert( is(typeof(this): A));
		static assert(!is(typeof(this): B));
		int bar(){ return 123; }
	}

	template X(){
		alias Mixin!({D d = new E; return d.foo();}()) X;
	}
	class D: X!(){
		int foo(int x){ X!() y=new X!(); return x+y.bar();}
		override .string foo(){ /+ TODO: make work without the '.'+/
			return "B";
		}
	}
	class E: D{
		override .string foo(){
			return "C";
		}
		override foo(int x){ return super.foo(x); }
	}
	static assert(is(E: C));
	static assert(!is(E: B));
	static assert({D e = new E; return e.foo(2);}()==125);
}

class Ino{
	this(inout int x)inout{
		static assert(is(typeof(this) == inout(Ino)));
	}
}
void testIno(){
	auto ino1 = new Ino(1);
	auto ino2 = new const(Ino)(2);
	auto ino3 = new immutable(Ino)(3);
	(inout int){auto ino4 = new inout(Ino)(3);}(0);
}

struct TEst{
	enum x = { auto x = new C; return x.foo(); }();
	template Foo2(){
		static if(x) alias D Foo22;
		else alias C Foo22;
		alias D Foo2;
	}
	enum a = {auto x = new D; return x.s();}();
	class D{ int x=1337; string s(){ return q{int foo()const{ return 2; }};}}
	class C: Foo2!(){
		int foo(){ return 2; }
		int bar(){
			// mixin(this.D.s()); // TODO!
			mixin(D.s());
		}
	}
}

int testHide(){
	class A{
		final int foo(int){return 1;}
		final int foo(double){return 2;}
	}
	class B: A{
		final int foo(int){return 3;} // TODO: error
		//final int
	}
}

auto testLocalClass(){
	class L{}
	return new L;
}

auto testLocalStruct(){
	int a;
	struct S{
		int foo(){
			return a;
		}
		enum x = 2;
	}
	static int foo(){
		S s; // TODO: error
		return s.foo();
	}
	S s; // ok
	//import std.stdio;
	//writeln(s.foo);
	return s;
}

void lclmain(){
	auto x=testLocalStruct();
	x = *new typeof(x); // error

	typeof(x) s = void; // ok

	auto y=testLocalClass();
	y = new typeof(y); // error
	typeof(y) t; // ok

	//import std.stdio;
	//writeln(x.foo);
}

class ConstrDeflt{
	this(int x = 2){}
}

void testDeflt(){
	auto c = new ConstrDeflt(); // TODO
}

struct OvStatic{
	static void foo(int x){}
	int foo(int x){ return x+1; }
}

void testOvStatic(){
	OvStatic ov;
	ov.foo(2);
	OvStatic.foo(2);
}

class ConstructorP{
	this(int x){}
}
class ConstructorC: ConstructorP{ // error TODO!
	
}

void testConsC(){
	auto c = new ConstructorC(2); // error
	auto x = new int(2);
	auto y = new int(3.0f); // error
}


static class Foo{
	static class HazConstructor{
		int x;
		this(int x){
			this.x = x;
		}
	}
	static class HazConstructorOverload{
		int x;
		this(int x)immutable{
			this.x = x; // TODO: relax type checking in constructors
		}
		this(int x){
			this.x = 2;
		}
	}
	static class HazImmutableConstructor{
		this(int x)immutable{}
	}
	static class CanBuildQualified{
		this(int x)inout{}
	}

	class NonStatic{
		this(int x){}
		static class Static{
			this(int x){}
		}
		class NStatic{}
	}
}

void testConstructor(){
	auto x = new Foo.HazConstructor(2);
	auto z = new Foo.HazConstructor(2,3); // error
	auto y = new immutable(Foo.HazConstructorOverload)(3);
	auto w = new Foo.HazImmutableConstructor(2); // error
	auto s = new Foo.NonStatic.Static(2);

	auto fo1 = new Foo;
	auto q = fo1.new NonStatic(2); // TODO

	/// // TODO
	auto fo2 = new immutable(Foo);
	auto qq = fo2.new NonStatic; // error
	auto qqq = fo2.new const(NonStatic)(2); // TODO: ok
	auto qq2 = fo2.new immutable(NonStatic)(2); // TODO: ok
	auto qq3 = fo2.new const(HazConstructor); // error
	auto qq4 = fo2.new immutable(NonStatic.Static)(2); // error
	auto qq5 = fo2.new immutable(NonStatic.NStatic)(); // error
	///
	new Foo().new NonStatic; // TODO

	auto a = new int[2];
	auto b = new int[](2);
	auto c = new int[](1,2); // error
	auto d = new int[][](1,2);
	auto e = new int[][](2);
	struct S{}
	auto ss = new S;
	pragma(msg, typeof(ss));
}

struct FooS{
	int foo()const{ return 2; }
	int foo()immutable{ return 2; }
	int foo(){ return 1; }
	int foo()inout{ return 2; }
	int foo()shared{ return 2; }
	int foo()const shared{ return 2; }
	// int foo()const inout{ return 3; }
}

void testFooS(inout int){
	FooS s1;
	s1.foo();
	const(FooS) s2;
	s2.foo();
	immutable(FooS) s3;
	s3.foo();
	shared(FooS) s4;
	s4.foo();
	inout(FooS) s5;
	s5.foo();
	const(shared(FooS)) s6;
	s6.foo();
	const(inout(FooS)) s7;
	s7.foo();
}

class Infty{
	int foo()const{ return foo()+this.foo(); }
	int foo(){ return foo()+this.foo(); }
	int bar(){ return foo()+this.foo(); }
	int bar()shared{ return foo()+this.foo(); } // error

	auto buz()inout{ return this; }
	auto bbz()const inout{
		buz();
		static assert(is(typeof(buz())==inout(const(Infty))));
		static assert(is(typeof(this.buz())==inout(const(Infty))));
	}
	auto bbz()immutable{
		static assert(is(typeof(buz())==immutable(Infty)));
		static assert(is(typeof(this.buz())==immutable(Infty)));
	}
	auto bbz() const shared{
		buz(); // error
		this.buz(); // error
	}
	auto bbz(){
		static assert(is(typeof(buz())==Infty));
		static assert(is(typeof(this.buz())==Infty));
	}
	auto bbz()const{
		static assert(is(typeof(buz())==const(Infty)));
		static assert(is(typeof(this.buz())==const(Infty)));
	}
	auto bbz()inout{
		static assert(is(typeof(buz())==inout(Infty)));
		static assert(is(typeof(this.buz())==inout(Infty)));
	}

	auto bzz(inout(int[]) x)inout{ return this; }
	auto bbz(int[] x){
		static assert(is(typeof(bzz(x))==Infty));
		static assert(is(typeof(this.bzz(x))==Infty));
	}
	auto bbz(inout(int[])x)immutable{
		static assert(is(typeof(bzz(x))==inout(const(Infty))));
		static assert(is(typeof(this.bzz(x))==inout(const(Infty))));
		static assert(is(typeof(bzz(x))==const(inout(Infty))));
		static assert(is(typeof(this.bzz(x))==const(inout(Infty))));
	}
	auto bbz(inout(int[])x)inout{
		static assert(is(typeof(bzz(x))==inout(Infty)));
		static assert(is(typeof(this.bzz(x))==inout(Infty)));
	}
	auto bbz(immutable(int[]) x)immutable{
		static assert(is(typeof(bzz(x))==immutable(Infty)));
		static assert(is(typeof(this.bzz(x))==immutable(Infty)));
	}
}


class OVIC{
	mixin(q{int foo()immutable{ return 2; }});
	int foo()        const    { return 2; }
}
class OVIbICSC: OVIC{
	override int foo()immutable           { return 2; }
	mixin(q{override int foo()const shared{ return 2; } // error
});
	override int foo()const               { return 2;}
	//int foo()inout{ return 2; }
}

class OVIbCCS: OVIC{
	mixin(q{override int foo()const{ return 2; }});
	override int foo()const shared { return 2; }
}

int global;
class Container{
	int cont;
	static int cont2;
	enum cont3=3;
	class C{
		void foo()const{
			static assert(is(typeof(global)==int));
			static assert(is(typeof(cont)==const(int)));
			static assert(is(typeof(cont2)==int));
			static assert(is(typeof(cont3)==int));
			static assert(is(typeof(d)==const(D)));
			static assert(is(typeof(d.u)==const(int)));
			static assert(is(typeof(Container2.y)==int));
		}
		void foo()const shared{
			static assert(is(typeof(global)==int));
			static assert(is(typeof(cont)==const(shared(int))));
			static assert(is(typeof(cont2)==int));
			static assert(is(typeof(cont3)==int));
			static assert(is(typeof(d)==const(shared(D))));
			static assert(is(typeof(d.u)==shared(const(int))));
			static assert(is(typeof(Container2.y)==int));
			pragma(msg, typeof(Container2.y));
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

class SomeDecl{
	int foo(){}
	int foo()immutable{}
}
class AmbigOverride: SomeDecl{
	override int foo()const{ return 2; } // error: // TODO: should it guess from the context?
	override int foo()immutable{ return 2; }
}
class CertainlyAmbigOverride: SomeDecl{
	override int foo()const{ return 2; } // error
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
		return super.foo();
	}
	override const(int[]) foo()const{
		static assert(is(typeof(super)==const(IHazAllFoo)));
		static assert(is(typeof(x)==const(int[])));
		return super.foo();
	}
	override immutable(int[]) foo()immutable{
		static assert(is(typeof(super)==immutable(IHazAllFoo)));
		static assert(is(typeof(x)==immutable(int[])));
		return super.foo();
	}
	override shared(int[]) foo()shared{
		static assert(is(typeof(super)==shared(IHazAllFoo)));
		static assert(is(typeof(x)==shared(int[])));
		return super.foo();
	}
}

class IHazFoo{
	final int x()const{ return 2;}
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
	override int foo(){ return super.foo(); } // TODO (?)
	override int foo()inout{ return x(); } // TODO: DMD says this is legal...
}

class CircOverride1: CircOverride2{
	override int foo(int x){ return x; }// ok (hidden by circular inheritance)
	override int bar(int x){ return x; }// ok (hidden by circular inheritance)
}
class CircOverride2: CircOverride1{ // error
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
	override foo(HasFooOverloads x){ return x; } // TODO: error (shadows the final method)
}

class OverridesFoo5: HasFooOverloads{
	private int foo(int x){ return x; } // ok (// TODO: should private even overload against public?, should functions with the same argument types even be allowed to coexist?)
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

// (// TODO: traits getMember)
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
	//static if(is(T:C!T)) enum x = "success!";
}

class E: D!E{
	// pragma(msg, x);
}

//pragma(msg, D);
//pragma(msg, C!D);



// +/
// +/
// +/

template Seq(T...){alias T Seq;}
alias immutable(char)[] string;