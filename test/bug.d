
alias immutable(char)[] string;

auto testtemplatefunclit(alias fun)(){ return fun!int(2); }
pragma(msg, "testtemplatefunclit 3: ",testtemplatefunclit!(x=>2)());

int[] rec(int[] arg){
	if(!arg.length) return arg;
	return rec(arg[1..arg.length]);
}
enum unsorted = [1,2];
pragma(msg, rec(unsorted));
pragma(msg, rec(unsorted));



/+
int k;

typeof(z) x;
typeof(x) y;
typeof(y) z;
+/

// +/