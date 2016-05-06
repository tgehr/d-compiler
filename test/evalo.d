int[] foo(){
    int a=1;
    int[] r;
    a=(a=a*2)+(a=a+=2);
    r~=a,a=0;
    alias string=immutable(char)[];
    static struct S{
        int a;
        this(int a){ this.a=a; }
        S opBinary(string op)(S t){ return S(mixin("a "~op~" t.a")); }
        ref S opUnary(string op:"++")(){ ++a; return this; }
    }
    static struct T{
        int a;
        this(int a){ this.a=a; }
        T opBinaryRight(string op)(T s){ return T(mixin("s.a "~op~" a")); }
        ref T opUnary(string op:"++")(){ ++a; return this; }
    }
    auto s=S(1);
    auto t=T(1);
    s=(s=s*S(2))+(s=s+S(2));
    t=(t=t*T(2))+(t=t+T(2));
    r~=s.a,r~=t.a;
    return r;
}
pragma(msg, foo());
static assert(foo()==[6,8,8]); // 6,6,6 would be nicer
