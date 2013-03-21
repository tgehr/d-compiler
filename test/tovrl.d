auto fun(T)(T arg){return arg;}
auto fun(int x)(int arg){return arg;}

pragma(msg, fun!int(2)," ",fun!2());