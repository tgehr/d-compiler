

//alias int foooo;
void foooo(){}
void goooo(int){}
alias goooo foooo; // TODO: fix
//alias double foooo;

pragma(msg, foooo); // error




alias int y;
alias y[] x;
alias y* z;
alias x* w;
pragma(msg, z," ",w);


static assert(!is(typeof({
				int[] i;
				alias i[] j;
			})));

pragma(msg, typeof(cast(immutable)true~a));

immutable typeof(*{z v;return v;}()) a = [1,2,3]; // error
pragma(msg, a);

void main(){
	z x;
	const typeof(*{typeof(x) v;return v;}()) a = [2,3,4]; // error
	pragma(msg, a);
}

alias aa bb; // error
alias bb cc;
alias cc aa;

// +/