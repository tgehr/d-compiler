
// // TODO: wait until semantics of the following is clarified by spec
// // (I currently assume the spec is not implementable.)
/+string bb(string x, string y){ return x~y; }
enum E { foo = bb(cast(string)bar, cast(string)baz), bar="1", baz="2" }

enum CDX {foo=bar, bar="123"}

pragma(msg, CDX.foo);
pragma(msg, typeof(CDX.foo));

enum Incompat { foo = qux, bar = 1, baz = "12", qux=bar+baz }


enum Test{ foo = ((int b)=>"hello")(cast(int)bar), bar=2 }
pragma(msg, typeof(Test.foo));+/

enum Weekdays{
	Monday,
	Tuesday,
	Wednesday,
	Thursday,
	Friday,
	Saturday,
	Sunday,
}

enum testcast=((Weekdays x)=>cast(double)x)(Weekdays.Tuesday);
pragma(msg, "testcast: ",testcast);
static assert(testcast==1.0);

pragma(msg, cast(Weekdays)2);
pragma(msg, cast(int)Weekdays.Friday);
static assert(Weekdays.Friday==4);
static assert(Weekdays.Sunday is 6);

static assert(!!Weekdays.Tuesday&&!Weekdays.Monday);

pragma(msg, Weekdays.Monday+1);
pragma(msg, Weekdays.Tuesday+1);
pragma(msg, cast(const)Weekdays.Monday+cast(const)Weekdays.Tuesday);

static assert(is(typeof(cast(const)Weekdays.Monday+cast(const)Weekdays.Tuesday)==const(Weekdays)));
static assert(Weekdays.Monday+Weekdays.Tuesday==Weekdays.Tuesday);

pragma(msg, ~Weekdays.Monday);
static assert(is(typeof(~Weekdays.Monday)==Weekdays));
static assert(~Weekdays.Monday==-1);

enum Aa : Bb { X=Bb.Y }
enum Bb : Aa { Y } // error // TODO: improve error message

enum Wrong:immutable(char)[]{Agh} // error // TODO: improve error message
enum:immutable(char)[]{A="",B,C} // error // TODO: improve error message

enum NoCircDep : int{foo=bar,bar=0}
enum ACircDep : int{foo=bar,bar} // error
enum AnotherCircDep {foo=bar,bar=0} // TODO?: DMD now allows this


enum {circdep0=circdep1, circdep1} // error
enum CDX {foo=bar, bar="123"} // TODO?

pragma(msg, CDX.bar);

enum AXX{a="2",b=["123"]} // error

template Show(alias x){
	pragma(msg, typeof(x));
	enum Show = x;
}

auto fooz(T)(T r){ return "23"; }

enum XX : immutable(char)[] {a=fooz(b),b="123"}

immutable char[] foo=XX.a;

pragma(msg, typeof(XX.a)," ",typeof(foo)," ",foo);

pragma(msg, XX.a);
pragma(msg, XX.b);
pragma(msg, typeof(XX.b));


enum{ int ano1=2, ano2="hi", double ano3=123.123 }
pragma(msg, "Anonymous enums 1: ",ano1, " ", ano2, " ", ano3);

enum{aa0,aa1,aa2,aa3}
pragma(msg, "Anonymous enums 2: ", aa0, " ",aa1, " ", aa2, " ",aa3);

static assert(aa0==0&&aa1==1&&aa2==2&&aa3==3);

enum Empty{ } // error
enum NamedExplicit{int X} // error
enum:int{AaA, int BbB, CcC  } // error


enum X{A, B, C}

enum X a = X.A;
enum X b = X.B;
enum c = X.C;

static assert(is(typeof(c)==X));


// +/
// +/
// +/