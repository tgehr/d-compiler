

void main(){
	int x = 222228298292; // error
	auto y = 1<<(32+(x&1)); // error
    //pragma(__range,1L<=1L+(1&x));
    pragma(__range,((x&7)+23)&((x&6)+10));
    pragma(__range,((x&252)^2)+1);
    ubyte z = ((x&252)^2)+1;
    //pragma(msg, 1<<32);
    //pragma(__range, 1<<32);
}