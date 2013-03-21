template ID(alias a){alias a ID;}
alias ID!(g=>(x=>x(x))(x=>a=>g(x(x),a))) Y;

pragma(msg, Y( (int delegate(int) rec, int n) => n*rec(n-1) ));