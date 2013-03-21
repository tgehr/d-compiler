
int fun(int x){return x+1;}
int hun(int x){return x+2;}

int gun(){return (0?fun:&hun)(2);} // error


pragma(msg, gun());

@property int function() iun(){return ()=>2;}
pragma(msg, typeof(&iun)); // error


@property int ovr(){return 2;}
@property int ovr(int x){return 3;}

pragma(msg, "ovr: ",ovr=2); // TODO

