
int unsigned(int x){
	switch(cast(uint)x){
		case 0:..case -1: return 1;
		default: return -1;
	}
}
static assert(unsigned(-1)==1);
static assert(unsigned(1)==1);

void finalSwitch(){
	enum E{
		X=1,
		Y=3,
		Z=4,
	}
	E e;
	final switch(e){ case E.X:..case E.Z: break;} // error
	final switch(e){ case E.X: break; case E.Y: break; case E.Z: break;} // ok
	final switch(e){ case E.X, E.Y, E.Z: break; } // ok
	final switch(e){ case E.X, E.Y, E.Z: break; default: break; } // error

	final switch(e){ case E.X, E.Y: break; } // error
	final switch(e){ case E.X, E.Z: break; } // error
	final switch(e){ case E.Y, E.Z: break; } // error
	final switch(e){ case E.X: break; } // error
	final switch(e){ case E.Y: break; } // error
	final switch(e){ case E.Z: break; } // error
	final switch(e){ case E.X: break; case E.Y: break; } // error
	final switch(e){ case E.X: break; case E.Z: break; } // error
	final switch(e){ case E.Y: break; case E.Z: break; } // error
	final switch(e){ case E.X: break; } // error
	final switch(e){ case E.Y: break; } // error
	final switch(e){ case E.Z: break; } // error
}

void overlapping(int x){
	switch(x){
		case 1: break;
		case 2: break;
		case 1: break; // error
		default: break;
	}
	switch(x){
		case 1025:..case 2048: break;
		case 256:..case 1024: break;
		case 0:..case 255: break;
		case 100:..case 2000: break; // error
		default: break;
	}
	switch(x){
		case 0:..case 255: break;
		case 256: break;
		case 245: break; // error
		default: break;
	}
	switch(x){
		case 1:..case 2: break;
		case 2:..case 4: break; // error
		default: break;
	}
	switch(x){
		case 2:..case 4: break;
		case 1:..case 2: break; // error
		default: break;		
	}
}

void main(){
	struct S{}
	switch(S()){ default: break;} // error

	switch(0){ default: } // ok
	switch(""){ default: } // ok
	int x = 3;
	switch(x){
		case 0: break;
		case 1: break;
		case "2": break; // error
		case '2': break; // ok
		case "3",'3': break; // error
		case '3',"3": break; // error
		case '4','4': break; // error
		case '5','6': break; // ok
		case 3: break;
		default: break;
	}
}

int nonCtfeAble(int x){
	int y;
	switch(x){
		case 0: return 0;
		case y: return 1; // error
		default: return 2;
	}
}

void multipleDefaults(){
	switch(0){
		default:
		default: // error
	}
}

void caseOverflow(int x){
	auto foo(){ return 1; }
	switch(x){
		case foo()+1: return; // ok
		case foo():..case 0: return; // error
		default: return;
	}
}

string convert(int x){
	switch(x){
		case 0: return "zero";
		case 1: return "one";
		case 2: return "two";
		case 3: return "three";
		default: return "many";
	}
}

static assert(convert(0)=="zero");
static assert(convert(1)=="one");
static assert(convert(2)=="two");
static assert(convert(3)=="three");
static assert(convert(4)=="many");
static assert(convert(5)=="many");

int convertBack(string s){
	switch(s){
		case "zero": return 0;
		case "one": return 1;
		case "two": return 2;
		case "three": return 3;
		default: assert(0, "cannot convert back");
	}
}

static assert(convertBack("zero")==0);
static assert(convertBack("one")==1);
static assert(convertBack("two")==2);
static assert(convertBack("three")==3);
static assert(!is(typeof({enum e = convertBack("many"); })));
static assert(!is(typeof({enum e = convertBack("asdf"); })));

enum Tag{
	t1,
	t2,
	t3,
}

string tts(Tag s){
	final switch(s){
		case Tag.t1: return "t1";
		case Tag.t2: return "t2";
		case Tag.t3: return "t3";
	}
}

static assert(tts(Tag.t2)=="t2");

string tts2(Tag s){
	final switch(s){
		case Tag.t1: return "t1";
		case Tag.t3: return "t3";
		case Tag.t2: return "t2";
	}
}

static assert(tts2(Tag.t2)=="t2");

string tts3(Tag s){ final switch(s){ } } // error
string tts4(Tag s){ final switch(s){ case Tag.t1: return "t1"; } } // error
string tts5(Tag s){
	final switch(s){ // error
		case Tag.t1: return "t1";
	}
}
string tts6(Tag s){
	final switch(s){ // error
		case Tag.t1: return "t1";
		case Tag.t2: return "t2";
	}
}

string tts6(Tag s){
	final switch(s){ // error
		case Tag.t1: return "t1";
		case Tag.t2: return "t2";
		default: return "t3"; // error
	}
}

string tts7(Tag s){
	switch(s){
		case Tag.t1: return "t1";
		case Tag.t2: return "t2";
		default: return "t3";
	}
}

static assert(tts7(Tag.t1)=="t1");
static assert(tts7(Tag.t2)=="t2");
static assert(tts7(Tag.t3)=="t3");

int caseRange(int x){
	switch(x){
		case 0:..case 255: return 0;
		case 256:..case 1024: return 1;
		case 1025:..case 4097: return 2;
		case 4099:..case ~0U>>1: return 3;
		default: return -1;
		case -1337: return 1337;
	}
}

static assert(caseRange(-23737)==-1);
static assert(caseRange(-1337)==1337);
static assert(caseRange(-1)==-1);

static assert(caseRange(0)==0);
static assert(caseRange(54)==0);
static assert(caseRange(255)==0);

static assert(caseRange(256)==1);
static assert(caseRange(678)==1);
static assert(caseRange(1024)==1);

static assert(caseRange(1025)==2);
static assert(caseRange(3456)==2);
static assert(caseRange(4097)==2);

static assert(caseRange(4098)==-1);

static assert(caseRange(4099)==3);
static assert(caseRange(387373738)==3);
static assert(caseRange(~0U>>1)==3);

string[] generateStrings(int n, int seed){
	uint next(){ return (seed*=16777619)+=21661361; }
	string[] r;
	for(int i=0;i<n;i++){
		string s;
		int l=next()%23+8;
		for(int j=0;j<l;j++) s~=cast(char)('a'+next()%3);
		r~=s;
	}
	return r;
}

string generateSwitch(const string[] strings){
	string r="switch(x){\n";
	for(int i=0;i<strings.length;i++)
		r~=`	case "`~strings[i]~`": return `~to!string(i)~";\n";
	r~="	default: return -1;\n";
	r~=`}`;
	return r;
}

pragma(msg, generateSwitch(generateStrings(26,5)));

int[] testHugeStringSwitch(){
	// // TODO: speed up generation of the switch byte code in some way
	// (the actual matching seems to actually be quite fast.)
	static immutable strings = generateStrings(1000,9);
	int fun(string x){
		mixin(generateSwitch(strings));
	}
	int[] r;
	for(int i=0;i<strings.length;i++){
		r~=fun(strings[i]);
		assert(r[i]==i);
	}
	auto ostrings = generateStrings(1000,7);

	int cmp(string a, string b){
		for(int i=0;i<a.length;i++){
			if(i>=b.length||a[i]>b[i]) return 1;
			if(a[i]<b[i]) return -1;
		}
		return a.length<b.length?-1:0;
	}
	for(int i=0;i<ostrings.length;i++){
		r~=fun(ostrings[i][0..2]~strings[i][2..$]);
		assert(r[$-1]==-1||!cmp(strings[r[$-1]],ostrings[i][0..2]~strings[i][2..$]));
		r~=fun(strings[i][0..2]~ostrings[i][2..$]);
		assert(r[$-1]==-1||!cmp(strings[r[$-1]],strings[i][0..2]~ostrings[i][2..$]));
	}
	return r;
}

pragma(msg, testHugeStringSwitch());

// +/
// +/
// +/
// +/

alias immutable(char)[] string;

auto to(T,S)(S arg)if(is(S==int)&&is(T==string)){
	string r="";
	if(!arg) return "0";
	bool n = arg<0;
	if(n) arg=-arg;
	while(arg) r=('0'+arg%10)~r, arg/=10;
	if(n) r="-"~r;
	return r;
}
