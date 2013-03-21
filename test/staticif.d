
static if(!is(typeof(bb))) enum xx = false;
static if(!is(typeof(xx))) enum bb = true; // error
static if(!is(typeof(aa))) enum bb = true; // ok

static if(!is(typeof(bbb))) enum xxx = false;
static if(!is(typeof(aaa))) enum bbb = true; // ok
static if(!is(typeof(xxx))) enum bbb = true; // error


static if(!is(typeof(ffff))) enum gggg = 2; // error
static if(!is(typeof(gggg))) enum ffff = 2; // error


// void bazz(){}
// static if(!is(typeof(bazz(2)))) void bazz(int){} // TODO!

static if(!is(typeof(c))) enum a = 1;
static if(is(typeof(b))) enum c = 1;
enum b = 2;

static assert(!is(typeof(a)));
static assert(is(typeof(c)));

//enum x = ajoiaj;
/+static if(!is(typeof(theOther))){
	enum foo=2;
	pragma(msg, "foo");
}+/
//static if(!is(typeof(theOne))){
//	enum theOther = 1;
//}
static if(!is(typeof(theOther))){
	enum theOne = 1337;
	pragma(msg, "theOne");
	static if(!is(typeof(asdf))) enum theOther=2;
}

//static if(!is(typeof(theOne))) enum asdfg=2; // TODO: this should be OK

static if((0&&foo)^1){pragma(msg, "Fofofo");}
static if(!!(1||foo)){pragma(msg, "fdofo");}
int loop(){return loop();}
enum andshortcuts = 0&&loop();
enum orshortcuts = 1||loop();

pragma(msg, is(typeof(theOne))," ", is(typeof(theOther)));

//pragma(msg, typeof(theOther));

pragma(msg, "a ",is(typeof(a)));
pragma(msg, "b ",is(typeof(b)));
pragma(msg, "c ",is(typeof(c)));

//pragma(msg, 2 !is 1);
auto test(){return theOne;}
static if(test()){pragma(msg, test(), "!!!");} 

static assert(test()==1337);

//static if(!is(typeof(asdf)))
void main(){
	//int asdf=2;
	static if(!is(typeof(theOther))) asdf=2;

	static if(true){
		int x = 2;
		x=3;
		x-=2;
		pragma(msg, x); // error
	}
}

static if(!is(typeof(theOther))){
	static asdf=2;
	mixin("void the(){enum theOther=2;}");
}

//else enum a=1;


/+//S s;

//static if(!is(typeof(s.d2))) enum d1=0;

struct S{
	//static if(!is(typeof(d2))) enum d1=0;
	static if(!is(typeof(d1))) enum d2=0;
}

void main(){
	pragma(msg, is(typeof(d1)));
	pragma(msg, is(typeof(S.d1)));
	pragma(msg, is(typeof(S.d2)));
}


// +/
