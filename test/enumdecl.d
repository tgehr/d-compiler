
enum Weekdays{
	Monday,
	Tuesday,
	Wednesday,
	Thursday,
	Friday,
	Saturday,
	Sunday,
}

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
enum AnotherCircDep {foo=bar,bar=0} // error // TODO: determine if this should be supported


enum {circdep0=circdep1, circdep1} // error
enum CDX {foo=bar, bar="123"} // error

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