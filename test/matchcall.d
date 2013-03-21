
alias immutable(char)[] string;

void foo(int a, string b){}

void main(){
	foo(1,2);
	foo("1",2);
	foo("1","2");
	auto bar = &foo;
	bar(1,2);
	bar("1",2);
	bar("1","2");
}
