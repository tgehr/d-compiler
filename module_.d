
import lexer, parser, error, scope_, semantic, util;

import core.memory;
import std.stdio, std.algorithm;

class Module: Node{
	Declaration[] decls;
	Scope sc;
	this(string path){
		GC.disable(); scope(exit) GC.enable();
		//auto f=File(path); // TODO: handle exceptions
		File f; if(path=="-") f=stdin; else f=File(path);
		auto app=mallocAppender!(char[])();
		foreach(r;f.byChunk(1024)){app.put(cast(char[])r);}
		app.put("\n\0\0\0\0"); // insert 4 padding zero bytes
		string code=cast(string)app.data;
		sc=new Scope(new FormattingErrorHandler(path, code));
		//sc=new Scope(new SimpleErrorHandler(path, code));
		decls=parse(code,sc.handler);
		sstate = SemState.pre;
		if(sc.handler.nerrors) sstate = SemState.error;
	}
	Module semantic(){
		mixin(SemPrlg);
		if(sstate == SemState.pre) foreach(ref x;decls) x=x.presemantic(sc); // add all to symbol table
		do{
			gRetryAgain = false; // TODO: fix this
			//mixin(SemChld!q{decls});
			foreach(ref x;decls) x = x.semantic(sc);
			//import std.stdio;writeln("round complete!");
		}while(gRetryAgain);
		mixin(SemEplg);
	}

	override @property string kind(){return "module";}
	override string toString(){return "some module";} // TODO
}