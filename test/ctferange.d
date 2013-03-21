
struct List(T){
	private struct Node{
		T payload;
		Node* next;
		Node* prev;
	}
	Node* head;
	Node* back;

	void add(T arg){
		if(back !is null){
			back.next = new Node();
			back.next.prev=back;
			back=back.next;
		}else head = back = new Node();
		back.payload=arg;
	}

	auto range(){
		struct Range{
			private Node* current;
			T front()=>current.payload;
			bool empty()=>current is null;
			void popFront(){ current=current.next; }
		}
		Range range;
		range.current = head;
		return range;
	}
	auto brange(){
		struct Range{
			private Node* current;
			T front()=>current.payload;
			bool empty()=>current is null;
			void popFront(){ current=current.prev; }
		}
		Range range;
		range.current = back;
		return range;
	}
}

auto testList(){
	List!int list;
	for(int i=0;i<100;i++)
		list.add(i);
	return list;
}
pragma(msg, "testList: ", testList().range().array);
pragma(msg, "testList2: ", testList().brange().map!(a=>a*2).array);

auto map(alias a, R)(R range) if(isInputRange!R && is(typeof(a(range.front())))){
	static struct Map{
		R range;
		@property auto front()    => a(range.front);
		@property auto empty()    => range.empty;
		auto popFront() => range.popFront();
		//static if(isForwardRange!R){}
	}
	//return Map(range); // TODO!
	Map map; map.range = range;
	return map;
}

template filter(alias a, R){// if(isInputRange!R && is(typeof(cast(bool)a(R.front())))){
	auto filter(R range){
		// auto r = Filter(range); // TODO!
		auto r = Filter(); r.range = range;
		if(!range.empty && !a(range.front)) r.popFront();
		return r;
	}
	struct Filter{
		R range;
		auto front()=>range.front;
		auto empty()=>range.empty;
		void popFront(){
			do range.popFront();
			while(!range.empty&&!a(range.front));
		}
	}
}

auto take(R)(R range, size_t num){
	static struct Take{
		R range;
		size_t num;
		auto front()=>range.front;
		auto empty()=>!num||range.empty;
		auto popFront()=>(num--,range.popFront());
	}
	// return Take(range, num); // TODO!
	auto tk = Take(); tk.range = range; tk.num = num;
	return tk;
}

auto reduce(alias a, R)(R range) if(isInputRange!R && is(typeof(a(range.front(), range.front())):typeof(range.front())))=>reduce!a(range.front(),(range.popFront(),range));
auto reduce(alias a, T, R)(T start, R range) if(isInputRange!R && is(typeof(a(start, range.front())):T)){
	T result = start; 
	for(; !range.empty(); range.popFront())
		result = a(result, range.front());
	return result;
}

auto joiner(RR, S...)(RR r, S sep)
if(isInputRange!RR && isInputRange!(ElementType!RR) &&
   S.length<=1 && (S.length==0 || isForwardRange!(S[0]) && 
   is(typeof(sep[0].empty?r.front.front:sep[0].front))))
{
	static struct Result{
		@property auto ref front(){
			static if(S.length) return c.empty ? cs.front : c.front;
			else return c.front;
		}
		@property bool empty(){ return rr.empty && c.empty; }
		void popFront(){
			static if(S.length){
				if(c.empty) cs.popFront();
				else{ c.popFront(); if(!c.empty) return; }
				if(!cs.empty) return;
				else cs=s.save;
			}else{ c.popFront(); if(!c.empty) return; }
			do{
				if(rr.empty) return;
				static if(isForwardRange!(typeof(this))) c=rr.front.save;
				else{
					static assert(!isForwardRange!RR || !isForwardRange!(ElementType!RR));
					c=rr.front;
				}
				rr.popFront();
				static if(S.length) if(!cs.empty) break;
			}while(c.empty);
		}
		static if(isForwardRange!RR && isForwardRange!(ElementType!RR)) @property Result save(){
			/+static if(S.length) return Result(rr.save,c.save,s,cs.save);
			else return Result(rr.save,c.save); // TODO +/
			Result res;
			static if(S.length){
				res.rr = rr.save;
				res.c = c.save;
				res.s = s;
				res.cs = cs.save;
			}else{
				res.rr = rr.save;
				res.c = c.save;
			}
			return res;
		}
	//private: // TODO
		RR rr;
		ElementType!RR c;
		static if(S.length) S[0] s, cs;
	}
	//auto res = Result(r);// TODO
	Result res;
	res.rr = r;
	// with(res) // TODO
	do{
		if(res.rr.empty) break;
		res.c=res.rr.front;
		res.rr.popFront();
	}while(res.c.empty);
	// with(res) // TODO
	static if(S.length){
		res.s = sep[0];
		res.cs = sep[0].save;
	}
	return res;
}

static assert([[1,2,3],[1,2,3]].joiner.array==[1,2,3,1,2,3]);
pragma(msg, "joiner: ", [[1,2,3],[1,2,3]].joiner.array);
static assert([[1,2,3],[1,2,3]].joiner([0,8]).array==[1,2,3,0,8,1,2,3]);
pragma(msg, "joiner2: ", [[1,2,3],[1,2,3]].joiner([0,8]).array);
static assert([[1,2,3],[1,2,3]].joiner([0.8]).array==[1,2,3,0.8,1,2,3]);
pragma(msg, "joiner3: ", [[1,2,3],[1,2,3]].joiner([0.8]).array);

static assert([[[[1],[2,3]],[[2]],[[1],[3,3,4]]]].joiner.joiner.joiner.array==
              [1,2,3,2,1,3,3,4]);
pragma(msg, "joiner4: ", [[[[1],[2,3]],[[2]],[[1],[3,3,4]]],[[[1]]]].joiner.joiner.joiner.array);

static assert([[[[1],[2,3]],[[2]],[[1],[3,3,4]]],[[[1]]]].joiner([[[0]]]).joiner([[5]]).joiner([10]).array==[1,10,2,3,10,5,10,2,10,5,10,1,10,3,3,4,10,5,10,0,10,5,10,1]);
pragma(msg, "joiner5: ", [[[[1],[2,3]],[[2]],[[1],[3,3,4]]],[[[1]]]].joiner([[[0]]]).joiner([[5]]).joiner([10]).array);


static assert(array(iota(0,100)) == [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99]);
pragma(msg, "iota:   ", array(iota(0,100)));
static assert(array(map!(a=>a*2)(iota(0,26))) == [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50]);
pragma(msg, "map:    ", array(map!(a=>a*2)(iota(0,26))));
static assert(array(filter!(a=>a&1)(iota(0,100))) == [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,57,59,61,63,65,67,69,71,73,75,77,79,81,83,85,87,89,91,93,95,97,99]);
pragma(msg, "filter: ", iota(0,100).filter!(a=>a&1).array);
static assert(array(take(iota(0,20),10)) == [0,1,2,3,4,5,6,7,8,9]);
pragma(msg, "take: ", array(take(iota(0,20),10)));
static assert(reduce!((a,b)=>a+b)(iota(1,101)) == 5050);
pragma(msg, "reduce: ", reduce!((a,b)=>a+b)(iota(1,101)));


auto valueTypeRanges(){
	auto x = map!(a=>a*a)(iota(0,100));
	auto y = filter!(a=>a&1)(x);
	auto z = filter!(b=>b&4)(x);
	return [array(y), array(z)];
}

static assert(valueTypeRanges()==[[1,9,25,49,81,121,169,225,289,361,441,529,625,729,841,961,1089,1225,1369,1521,1681,1849,2025,2209,2401,2601,2809,3025,3249,3481,3721,3969,4225,4489,4761,5041,5329,5625,5929,6241,6561,6889,7225,7569,7921,8281,8649,9025,9409,9801],[4,36,100,196,324,484,676,900,1156,1444,1764,2116,2500,2916,3364,3844,4356,4900,5476,6084,6724,7396,8100,8836,9604]]);
pragma(msg, "valueTypeRanges: ", valueTypeRanges());


struct DynRange(T){
	T delegate() frontImpl;
	bool delegate() emptyImpl;
	DynRange!T delegate() popFrontImpl;
	@property T front(){ return frontImpl(); }
	@property bool empty(){ return emptyImpl(); }
	void popFront(){ this = popFrontImpl(); }
}

DynRange!(typeof(R.front())) dynRange(R)(R range)if(isInputRange!R){
	DynRange!(typeof(range.front())) result;
	result.frontImpl = ()=>range.front;
	result.emptyImpl = ()=>range.empty;
	result.popFrontImpl = (){
		static if(is(typeof(range.tail())) && isInputRange!(typeof(range.tail()))){
			auto newRange = range.tail();
		}else{
			auto newRange = range;
			newRange.popFront();
		}
		return dynRange(newRange);
	};
	return result;
}

auto testDynRange(){
	auto rng=dynRange(iota(0,20));
	return [array(rng), array(rng)];
}
static assert(testDynRange() == [[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]]);
//pragma(msg, "testDynRange: ",testDynRange());


auto empty(T=int)(){
	static struct Empty{
		//T front()=>assert(0); // TODO!
		T front(){assert(0); T t; return t;}
		bool empty()=>true;
		void popFront()=>assert(0);
	}
	return Empty();
}
auto cons(E,R)(E e,R range)if(isInputRange!R && is(typeof(1?e:range.front()))){
	static struct Cons{
		bool first = true;
		E e; R range;
		auto front()=>first?e:range.front();
		auto empty()=>!first&&range.empty();
		void popFront(){
			if(first) first = false;
			else range.popFront();
		}
		auto tail(){
			auto r=range;
			if(!first) r.popFront();
			return r;
		}
	}
	// return Cons(e,range); // TODO!
	auto cn = Cons(); cn.e=e; cn.range=range;
	return cn;
}

struct Delay(R){
	R delegate() dg;
	R range;
	bool init = false;
	auto front()=>(check(), range.front());
	auto empty()=>(check(), range.empty());
	auto popFront()=>(check(), range.popFront());
	//private:
	void check(){
		// if(dg) range = dg(); // TODO!
		// if(dg == dg); // TODO!
		// dg = null; // TODO!
		if(!init) range = dg();
		init = true;
	}
}
auto delay(R)(R delegate() dg)if(isInputRange!R){
	//return Delay!R(dg); // TODO
	Delay!R r; r.dg = dg;
	return r;
}

template DDR(R){ alias Delay!(DynRange!R) DDR; }


auto dynRangePrimes(){
	DynRange!int impl(int start)=>
		start.cons(delay(()=>impl(start+1).filter!(a=>a%start))).dynRange;
	return impl(2);
}

pragma(msg, "dynRangePrimes: ", dynRangePrimes().take(20).array);
/+// TODO: be as fast as haskell :)
dynRangePrimes: [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541]

real	1m41.491s
user	1m41.222s
sys	0m0.032s
+/
template All(alias pred, T...){
	static if(!T.length) enum All = true;
	else static if(pred!(T[0])) enum All = All!(pred,T[1..$]);
	else enum All = false;
}

/+struct Tuple(T...){
	T expand;
	this(T args){
		expand = args; // TODO!
	}
}
auto tuple(T...)(T args){ return Tuple!T(args); }+/

/+template ID(alias a){ alias a ID; }
template naryFun(size_t n, alias a)if(n<=26){
	static if(isCallable!a) alias a fun;
	else{
		mixin("alias ID!(("~iota(0,n)
		      .map!(i=>cast(char)('a'+i)~",")
		      .join~")=>"~a~") naryFun;");
	}
}

struct Zip(alias a, R...){
	R inputs;
	auto front(){
		return mixin("naryFun!(R.length,a)("~iota(0,R.length)
		             .map!(i=>"inputs["~to!string(i)~"].front,")()
		             .join()~")");
	}
	bool empty(){
/+		foreach(ref r;inputs) // TODO!
			if(r.empty) return true;
		return false;+/
		return mixin(iota(0,R.length)
		             .map!(i=>"inputs["~to!string(i)~"].empty()")()
		             .join("||"));
	}
	@property void popFront(){
		foreach(ref r;inputs) //TODO!
			r.popFront();
	}
	static if(allSatisfy!(isForwardRange,R)){
		@property Zip save(){
			return mixin("Zip("~iota(0,R.length)
			             .map!(i=>"inputs["~to!string(i)~"].save,")
			             .join~")");
		}
	}
}
auto zip(alias a = tuple, R...)(R ranges){
	return Zip!(a,R)(ranges);
}

pragma(msg, "zip: ", zip!q{a + b}([1,2,3],[2,3,4,5]));+/


/+
template zip(R...)if(All!(isInputRange, R)){
	auto zip(R r){
		static struct Zip{
			R ranges;
			bool empty()=>anyEmpty!ranges();
			auto front(){ return fronts!ranges(); }
			void popFront(){ popFrontAll!ranges(); }
		}
		//return Zip(ranges); // TODO
		auto zw = Zip();
		// zw.ranges = r; // TODO!
		void assign(size_t i)(){
			static if(i<r.length){
				zw.ranges[i] = r[i];
				assign!(i+1)();
			}
		}
		assign!0();
		return zw;
	}
	void popFrontAll()(){}
	void popFrontAll(r...)()=>(r[0].popFront(), popFrontAll!(r[1..$])());
	bool anyEmpty()()=>false;
	bool anyEmpty(r...)()=>r[0].empty()?true:anyEmpty!(r[1..$])();
	auto fronts()()=>tuple();
	auto fronts(r...)(){ return tuple(r[0].front(), fronts!(r[1..$])().expand); }
}

auto zipWith(alias a, R...)(R r)if(All!(isInputRange, R)){// TODO: constraint for a
	return map!(x=>a(x.expand))(zip(r));
}

pragma(msg, "zipWith: ", array(zipWith!((a,b)=>a+b)(wrap([1,2,3]),wrap([4,5,6]))));



// +/
// +/
// +/

alias immutable(char)[] string;

pragma(msg, "wrap: ", array(wrap([1,2,3,4,5])));
static assert(array(wrap([1,2,3,4,5]))==[1,2,3,4,5]);


auto array(R)(R range){
	typeof(R.front)[] arr;
	for(; !range.empty; range.popFront())
		arr ~= range.front;
	return arr;
}

auto wrap(T)(T[] arr){
	static struct Wrap{
		T[] arr;
		T front(){ return arr[0]; }
		bool empty(){ return !arr.length; }
		void popFront(){ arr = arr[1..$]; }
	}
	//return Wrap(arr); // TODO!
	auto wrp = Wrap(); wrp.arr = arr;
	return wrp;
}

// pragma(msg, "diota: ", array(iota(0,10.0))); // TODO!

auto iota(T)(T start, T end){
	static struct Iota{
		T start, end;
		T front(){ return start; }
		bool empty(){ return start == end; }
		void popFront(){ start++; }
	}
	assert(isInputRange!Iota);
	// return Iota(start, end); // TODO!
	Iota io; io.start = start; io.end = end;
	return io;
}

alias typeof(int[].length) size_t;
//pragma(msg, size_t);

template isInputRange(R){
	enum isInputRange=is(typeof({
		R r;
		if(!r.empty) r.popFront();
		auto f = r.front;
	}));
}

template isForwardRange(R){
	enum isForwardRange=isInputRange!R&&is(typeof({
		R r;
		r=r.save;
	}));
}

template ElementType(R)if(isInputRange!R){
	// alias typeof({foreach(x;r)return x;}()) ElementType // TODO (also adapt constraint)
	alias typeof({R r; return r.front; }()) ElementType;
}

@property auto front(T)(T[] a){ return a[0]; }
@property bool empty(T)(T[] a){ return !a.length; }
void popFront(T)(ref T[] a){ a=a[1..$]; }
@property T[] save(T)(T[] a){ return a; }



string trace(){
	string r;
	void write(string s){ r~=s; }
	void writeln(string s){ write(s); write("\n"); }
	struct LoggingRange(R)if(isInputRange!R){
		R rng;
		string name;
		@property front(){ writeln(name~": front"); return rng.front; }
		@property empty(){ writeln(name~": empty"); return rng.empty; }
		void popFront(){ writeln(name~": popFront"); return rng.popFront(); }
		static if(isForwardRange!R){
			@property save(){
				writeln(name~": save");
				// return LoggingRange(rng.save,name); // TODO
				LoggingRange res;
				res.rng=rng.save;
				res.name=name~"'";
				return res;
			}
		}
	}
	auto mkLog(T)(string name, T rng)if(isInputRange!T){
		// return LoggingRange(rng, name); // TODO
		LoggingRange!T res;
		res.rng=rng;
		res.name=name;
		return res;
	}
	int[] x = mkLog("joined",[mkLog("e0",[1,2,3]),mkLog("e1",[4,5,6]),mkLog("e2",[1,2,3])]).joiner(mkLog("sep",[1,2,3])).array;
	return r;
}
static assert(trace()==
"joined: empty
joined: front
joined: popFront
e0: empty
sep: save
joined: empty
e0: empty
e0: front
e0: empty
e0: popFront
e0: empty
joined: empty
e0: empty
e0: front
e0: empty
e0: popFront
e0: empty
joined: empty
e0: empty
e0: front
e0: empty
e0: popFront
e0: empty
sep': empty
joined: empty
e0: empty
sep': front
e0: empty
sep': popFront
sep': empty
joined: empty
e0: empty
sep': front
e0: empty
sep': popFront
sep': empty
joined: empty
e0: empty
sep': front
e0: empty
sep': popFront
sep': empty
sep: save
joined: empty
joined: front
e1: save
joined: popFront
sep': empty
joined: empty
e1': empty
e1': front
e1': empty
e1': popFront
e1': empty
joined: empty
e1': empty
e1': front
e1': empty
e1': popFront
e1': empty
joined: empty
e1': empty
e1': front
e1': empty
e1': popFront
e1': empty
sep': empty
joined: empty
e1': empty
sep': front
e1': empty
sep': popFront
sep': empty
joined: empty
e1': empty
sep': front
e1': empty
sep': popFront
sep': empty
joined: empty
e1': empty
sep': front
e1': empty
sep': popFront
sep': empty
sep: save
joined: empty
joined: front
e2: save
joined: popFront
sep': empty
joined: empty
e2': empty
e2': empty
e2': front
e2': empty
e2': popFront
e2': empty
joined: empty
e2': empty
e2': empty
e2': front
e2': empty
e2': popFront
e2': empty
joined: empty
e2': empty
e2': empty
e2': front
e2': empty
e2': popFront
e2': empty
sep': empty
joined: empty
e2': empty
");
