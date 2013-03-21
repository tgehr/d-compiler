
import lexer, parser, error, scope_, util;

import core.memory;
import std.stdio;

class Module{
	Declaration[] decls;
	Scope sc;
	this(string path){
		GC.disable();
		auto f=File(path); // TODO: handle exceptions
		auto app=mallocAppender!(char[]);
		foreach(r;f.byChunk(1024)){app.put(cast(char[])r);}
		app.put("\0\0\0\0"); // insert 4 padding zero bytes
		string code=cast(string)app.data;
		sc=new Scope(new FormattingErrorHandler(path, code));
		decls=parse(code,sc.handler);
		GC.enable();
	}
	void semantic(){
		foreach(ref x;decls) x=x.presemantic(sc); // add all to symbol table
		foreach(ref x;decls) x=x.semantic(sc); // do the heavy processing. TODO: mixins should be processed before other declarations
	}
}