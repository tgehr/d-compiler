
import std.c.stdlib;
import std.c.string;

import std.traits;
import utf=std.utf;

struct MallocAppender(T:T[]){ // NO RAII
	static MallocAppender create(size_t initial=1){
		MallocAppender app;
		app._length=initial;
		app._data=cast(Unqual!T*)malloc(T.sizeof*app._length);
		app._clength=0;
		return app;
	}
	void put(const(Unqual!T) x){
		_clength++;
		if(_clength>=_length){
			_length*=2;
			_data=cast(Unqual!T*)realloc(cast(void*)_data, T.sizeof*_length);
		}
		_data[_clength-1]=x;
	}
	static if(is(Unqual!T==char)){
		void put(const(dchar) x){
			Unqual!T[4] encoded;
			auto len = utf.encode(encoded, x);
			put(encoded[0..len]);
		}
	}
	void put(const(Unqual!T)[] x){
		_clength+=x.length;
		if(_clength>=_length){
			do _length*=2; while(_clength>_length);
			_data=cast(Unqual!T*)realloc(cast(void*)_data, T.sizeof*_length);
		}
		memcpy(_data+_clength-x.length, x.ptr, T.sizeof*x.length);
	}
	@property T[] data(){return (cast(T*)_data)[0.._clength];}
private:
	Unqual!T* _data;
	size_t _length;
	size_t _clength;
}


MallocAppender!T mallocAppender(T)(){
	return MallocAppender!T.create();
}


string toEngNum(uint i)in{assert(i<1000000);}body{
	static string[] a=["zero","one","two","three","four","five","six","seven","eight","nine","ten","eleven",
	                   "twelve","thirteen","fourteen","fifteen","sixteen","seventeen","eighteen","nineteen"];
	static string[] b=[null,"ten","twenty","thirty","forty","fifty","sixty","seventy","eighty","ninety"];
	if(i>=1000) return toEngNum(i/1000)~" thousand"~(i%100?" "~toEngNum(i%1000):"");
	if(i>=100) return toEngNum(i/100)~" hundred"~(i%100?" and "~toEngNum(i%100):"");
	if(i>=10) return i<20?a[i]:b[i/10]~(i%10?"-"~toEngNum(i%10):"");
	return a[i];
}

// a really fast downcast. only works if the argument is of final class type
T fastCast(T,R)(R x) if(isFinal!T){return typeid(x) is typeid(T)?cast(T)cast(void*)x:null;}