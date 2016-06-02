interface I;
class C : I; // error
interface J{}
class D: J;

class E: S; // error

struct S;
union U;

void main(){
	S s; // error
	U u; // error
	D d; // ok
	d.x=2; // error
	auto t=new S; // error
	auto v=new U; // error
	auto e=new D; // error
}

enum D x=null;
enum y={ D d=null; return d; }();
static assert(x is y);
