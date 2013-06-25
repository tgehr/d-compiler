/+ // TODO!

//mixin(adt(q{ ListI: NilI | Cons int ListI }));
mixin(adt(q{ Pair(T,S): PP T S }));

pragma(msg, adt(q{ Pair(T,S): PP T S }));

void main(){
	Pair!(int,int) p;
	p=PP(1,2);
}
/+
pragma(msg, adt(q{
 List(T):
 | Nil
 | Cons T List!T
}));
+/
/+mixin(adt(q{
 List(T):
 | Nil
 | Cons T List!T
}));

mixin(adt(q{ Tree(T): Leaf | Node Tree!T T Tree!T }));
mixin(adt(q{
 DayOfWeek:
 | Monday
 | Tuesday
 | Wednesday
 | Thursday
 | Friday
 | Saturday
 | Sunday
}));+/

auto list(R)(R r){
	if(r.empty) return Nil!(ElementType!R);
	auto f = r.front;
	r.popFront();
	return Cons(f,list(r));
}

size_t length(T)(List!T l){ return
	l.match!(
		()=>0,
		(x,xs)=>1+length(xs)
	);
}

template Seq(T...){ alias T Seq; }

void white(ref string s){
	while(!s.empty && isWhite(s.front)) s.popFront();
}

string ident(ref string s){
	string r;
	s.white();
	while(isAlpha(s.front)){
		r~=s.front;
		s.popFront();
	}
	return r;
}

string nonwhite(ref string s){
	string r;
	s.white();
	while(!isWhite(s.front)){
		r~=s.front;
		s.popFront();
	}
	return r;
}

void expect(ref string s, dchar c){
	s.white();
	if(s.front != c) assert(0); //throw new Exception(""); // TODO
	s.popFront();
}

struct Sum{
	string name;
	string[] types;
}

Sum sum(ref string s){
	Sum r;
	r.name = s.ident();
	s.white();
	while(!s.empty && s.front != '|'){
		r.types~=s.nonwhite();
		s.white();
	}
	return r;
}

string create(string s){
	auto name = s.ident;
	string params;
	bool hasparams = false;
	if(s.front=='('){
		hasparams = true;
		s.expect('(');
		while(s.front!=')'){
			params~=s.front;
			s.popFront();
		}
		s.expect(')');
	}
	s.expect(':');
	string r;
	r~="struct "~name;
	if(hasparams) r~="("~params~")";
	r~="{";

	Sum[] sums;
	
	s.white();
	if(s.front!='|') sums~=s.sum();
	while(!s.empty && s.front=='|'){
		s.popFront();
		sums~=s.sum();
	}
	if(sums.length>1) r~="\n\tprivate{\n\t\tsize_t tag;\n\t\tunion{";
	else r~="\n\t";
	r~="Seq!(";
	//foreach(sum;sums){
	for(size_t i=0;i<sums.length;i++){ auto sum=sums[i];
		r~="Tuple!(";
		//foreach(tt;sum.types) r~=tt~",";
		for(size_t j=0;j<sum.types.length;j++) r~=sum.types[j]~",";
		r~=")*,";
	}
	r~=") data;";
	if(sums.length>1) r~=" }\n\t}\n";
	else r~="\n";
	r~="\tprivate static make(size_t x,T...)(T args){\n";
	r~="\t\t"~name~" v;\n";
	if(sums.length>1) r~="\t\tv.tag=x;\n";
	r~="\t\tv.data[x]=[tuple(args)].ptr;\n";
	r~="\t\treturn v;\n";
	r~="\t}\n";
/+
	r~="\tstring toString(){\n";
	r~="\t\tstring display(T)(T args){\n";
	r~="\t\t\tstring r;\n";
	r~="\t\t\tforeach(i,a;args.expand) r~=to!string(args[i])~(i+1==args.length?\"\":\",\");\n";
	r~="\t\t\treturn r;\n";
	r~="\t\t}\n";

	auto genret(size_t i=0){
		return "return \""~sums[i].name~(sums[i].types.length?"(\"~display(*data["~i.to!string~"])~\")":"")~"\";\n";
	}

	if(sums.length>1){
		r~="\t\tswitch(tag){\n\t\t\tdefault: assert(0);\n";
		//foreach(i;0..sums.length){
		for(size_t i=0;i<sums.length;i++){
			r~="\t\t\tcase "~i.to!string~": "~genret(i);
		}
		r~="\t\t}\n";
	}else if(sums.length) r~=genret(0); // // TODO: default parameters
	r~="\t}\n";
	+/
	r~="}\n\n";
	//foreach(i,sum;sums){
	for(size_t i=0;i<sums.length;i++){ auto sum=sums[i];
		r~="auto "~sum.name;
		if(hasparams) r~="("~params~")";
		r~="(";
		//foreach(j,tt;sum.types) r~=tt~" param"~to!string(j)~",";
		for(size_t j=0;j<sum.types.length;j++) r~=sum.types[j]~" param"~to!string(j)~",";
		r~="){ return "~name~(hasparams?"!("~params~")":"")~".make!"~i.to!string~"("~
			iota(sum.types.length).map!(a=>"param"~a.to!string).join(",")~"); }\n";
	}

	r~="auto match(";
	//foreach(sum;sums) r~="alias "~sum.name~"case,";
	for(size_t i=0;i<sums.length;i++) r~="alias "~sums[i].name~"case,";
	if(hasparams) r~=params;
	r~=")("~name~(hasparams?"!("~params~")":"")~" arg){\n";
	r~="\tswitch(arg.tag){\n\t\t\tdefault: assert(0);\n";
	//foreach(i,sum;sums){
	for(size_t i=0;i<sums.length;i++){ auto sum=sums[i];
		r~="\t\t\tcase "~to!string(i)~": auto v=*arg.data["~to!string(i)~"]; return "~sum.name~"case(";
		//foreach(j,tt;sum.types) r~="v["~to!string(j)~"],";
		for(size_t j=0;j<sum.types.length;j++) r~="v["~to!string(j)~"],";
		r~=");\n";
	}
	r~="\t}\n}\n";

	return r;//~"\n\npragma(msg,`"~r~"`);";
}
//template ADT(string s){ mixin(create(s)); }
alias create adt;


// +/
// +/

alias immutable(char)[] string;
alias typeof(int[].length) size_t;


T to(T)(T arg){ return arg; }

T to(T,S)(S arg)if(is(T==string)&&is(typeof(arg==0))&&!is(S==bool)){
	string r="";
	if(!arg) return "0";
	while(arg) r=arg%10+'0'~r, arg/=10;
	return r;
}
T to(T)(bool arg)if(is(T==string)){
	return arg?"true":"false";
}

T to(T,S)(S[] arg)if(!is(S==immutable(char))){
	string r="[";
	if(arg.length){
		r~=to!string(arg[0]);
		for(size_t i=1;i<arg.length;i++){
			r~=", "~to!string(arg[i]);
		}
	}
	r~="]";
	return r;
}

bool isAlpha(dchar c){
	return 'a'<=c&&c<='z'||'A'<=c&&c<='Z';
}
bool isWhite(dchar c){
	return c=='\n'||c=='\r'||c==' '||c=='\t'||c=='\v';
}
@property front(T)(T[] arr){ return arr[0]; }
@property empty(T)(T[] arr){ return !arr.length; }
void popFront(T)(ref T[] arr){ arr=arr[1..$]; }

auto iota(T)(T arg){
	static struct Iota{
		T cur, arg;
		@property front(){ return cur; }
		@property empty(){ return cur==arg; }
		void popFront(){ cur++; }
	}
	Iota r;
	r.arg=arg;
	return r;
}

auto map(alias a,R)(R arg){
	static struct Map(alias a){
		R arg;
		@property front(){return a(arg.front); }
		@property empty(){return arg.empty; }
		void popFront(){ arg.popFront(); }
	}
	Map!a r;
	r.arg=arg;
	return r;
}

auto join(R,S)(R arg,S sep){
	typeof(arg.front.front)[] r;
	if(arg.empty) return r;
	r~=arg.front;
	arg.popFront();
	for(;!arg.empty;arg.popFront()){
		r~=sep~arg.front;
	}
	return r;
}

struct Tuple(T...){
	T expand;
}

auto tuple(T...)(T args){
	Tuple!T x;
	x.expand=args;
	return x;
}