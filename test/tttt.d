

/+enum s = "int s;";
struct S{
	mixin(s);
}+/


auto map(T, S)(T[] array, S delegate(T) dg){
	S[] result;
	for(int i=0;i<array.length;i++)
		result ~= dg(array[i]);
	return result;
}

pragma(msg, map([1,2,3],(float x)=>2+x));



alias immutable(char)[] string;


