
alias immutable(char)[] string;

void foo(int a, string b){}

void main(){
	foo(1,2); // error
	foo("1",2); // error
	foo("1","2"); // error
	auto bar = &foo;
	bar(1,2); // error
	bar("1",2); // error
	bar("1","2"); // error
}
