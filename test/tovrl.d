auto fun(T)(T arg){return arg;}
auto fun(int x)(int arg){return arg+2;}

pragma(msg, fun!int(2)," ",fun!2(2));
pragma(msg, fun!int(2)," ",fun!2()); // error