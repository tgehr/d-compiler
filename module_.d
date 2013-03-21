// Written in the D programming language.

import lexer, parser, error, scope_, semantic, util;

import analyze;

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
		app.put("\0\0\0\0"); // insert 4 padding zero bytes
		string code=cast(string)app.data;
		sc=new Scope(new FormattingErrorHandler());
		//sc=new Scope(new SimpleErrorHandler(path, code));
		//auto lexer = lex(code);
		// int count=0; foreach(tk;lexer){count++;}writeln(count);
		auto src = new Source(path, code);
		decls=parse(src,sc.handler);
		sstate = SemState.pre;
		if(sc.handler.nerrors) sstate = SemState.error;
	}
	Module semantic(){
		// return null;
		mixin(SemPrlg);
		if(sstate == SemState.pre) foreach(ref x;decls){
			x.stc|=STCstatic;
			x=x.presemantic(sc); // add all to symbol table
		}
		do{
			gRetryAgain = false; // TODO: fix this
			//mixin(SemChld!q{decls});
			foreach(ref x;decls){
				x = x.semantic(sc);
			}
			// import std.stdio;writeln("round complete!");
		}while(gRetryAgain);
		mixin(PropErr!q{decls});
		mixin(SemEplg);
	}

	mixin Analyze;

	override @property string kind(){return "module";}
	override string toString(){return "some module";} // TODO
}