int circdep1(){enum x = circdep2(); return x;}
int circdep2(){enum y = circdep1(); return y;}


// TODO: better error message
int circdep3(bool b){enum x = circdep4(); return x;}
int circdep4(){auto y=circdep3(0); return y;}
