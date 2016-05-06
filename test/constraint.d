
alias immutable(char)[] string;

template Greek(alias h)if(h=="Plato"||h=="Sokrates"||h=="Zeus"){ }
template God(alias h)if(h=="Zeus"){ }
template Human(alias h)if(is(typeof(Greek!h)) && !is(typeof(God!h))){ }
template Fallible(alias h)if(is(typeof(Human!h))){ }
template Fallible(alias h)if(is(typeof(Greek!h))&&is(typeof(God!h))){ }
template Mortal(alias h)if(is(typeof(Human!h))){ }
template Address(alias h, string a: "Olympus")if(is(typeof(Greek!h))&&is(typeof(God!h))){ }

template Perfect(alias h)if(!is(typeof(Mortal!h)) && !is(typeof(Fallible!h))){}

static assert(is(typeof(Address!("Zeus","Olympus"))));
static assert(!is(typeof(Address!("Plato","Olympus"))));
static assert(!is(typeof(Perfect!"Zeus")));
static assert(is(typeof(Fallible!"Plato")));
static assert(!is(typeof(Human!"Zeus")));
static assert(!is(typeof(God!"Sokrates")));
static assert(is(typeof(Mortal!"Sokrates")));
static assert(!is(typeof(Mortal!"Zeus")));
static assert(is(typeof(Fallible!"Zeus")));

template MergesTo(alias a, alias b, alias c) if(a==[]&&b.length&&b==c){}
template MergesTo(alias a, alias b, alias c) if(a==c&&b==[]){}
template MergesTo(alias a, alias b, alias c) if(a.length&&b.length&&c.length&&a[0]<b[0]&&c[0]==a[0]&&is(typeof(MergesTo!(a[1..$],b,c[1..$])))){}
template MergesTo(alias a, alias b, alias c) if(a.length&&b.length&&c.length&&a[0]>=b[0]&&c[0]==b[0]&&is(typeof(MergesTo!(a,b[1..$],c[1..$])))){}

static assert(is(typeof(MergesTo!([1,2,3],[4,5,6],[1,2,3,4,5,6]))));
static assert(is(typeof(MergesTo!([1,3],[2,4,5,6],[1,2,3,4,5,6]))));

static assert(is(typeof(MergesTo!([1,2,3],[1,2,3],[1,1,2,2,3,3]))));
static assert(!is(typeof(MergesTo!([1,2,3],[1,2,3],[1,1,2,2,3,4]))));

static assert(!is(typeof(!MergesTo!([1,2,4],[1,2,3],[1,1,2,2,3,3]))));
static assert(is(typeof(MergesTo!([1,2,4],[1,2,3],[1,1,2,2,3,4]))));
static assert(is(typeof(MergesTo!([1,2,3],[1,2,4],[1,1,2,2,3,4]))));

static assert(is(typeof(MergesTo!([1,3,5],[0,4,5,6],[0,1,3,4,5,5,6]))));
static assert(is(typeof(MergesTo!([0,4,5,6],[1,3,5],[0,1,3,4,5,5,6]))));

static assert(!is(typeof(MergesTo!([0,4,5,6],[1,3,5],[0,1,3,3,5,5,6]))));
