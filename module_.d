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

	static Module current = null;

	Module buildInterface(){
		mixin(Configure!q{Module.current = this});
		mixin(Configure!q{Identifier.tryAgain = true});
		mixin(Configure!q{Identifier.allowDelay = true});
		if(sstate == SemState.pre) foreach(ref x;decls){
			x.stc|=STCstatic;
			x=x.presemantic(sc); // add all to symbol table
		}
		while(Identifier.tryAgain){
			while(Identifier.tryAgain){
				while(Identifier.tryAgain){
					Identifier.tryAgain = false;
					foreach(ref x;decls) x = x.buildInterface();
					foreach(x;templateDecls) x.updateInstances(_=>_.buildInterface());
				}
				Identifier.allowDelay = false;
				foreach(ref x;decls) x = x.buildInterface();
				foreach(x;templateDecls) x.updateInstances(_=>_.buildInterface());
				Identifier.allowDelay = true;
			}
		}
		// import std.stdio; writeln("built interface!");
		return this;
	}
	Module semantic(){
		mixin(SemPrlg);
		mixin(Configure!q{Module.current = this});
		mixin(Configure!q{Identifier.tryAgain = true});
		mixin(Configure!q{Identifier.allowDelay = true});
		auto me = buildInterface();
		assert(me is this);
		foreach(ref x;decls) x = x.semantic(sc);
		foreach(x;templateDecls) x.updateInstances(_=>_.semantic(sc));
		int num = 0;
		while(Identifier.tryAgain){
			// TODO: this is a hack to order declarations before references
			buildInterface();
			// TODO: replace by comprehensive ordering of non-existence decisions
			while(Identifier.tryAgain){
				Identifier.tryAgain = false;
				foreach(ref x;decls) x = x.semantic(sc);
				foreach(x;templateDecls) x.updateInstances(_=>_.semantic(sc));
			}
			Identifier.allowDelay=false;
			foreach(ref x;decls) x = x.semantic(sc);
			foreach(x;templateDecls) x.updateInstances(_=>_.semantic(sc));
			Identifier.allowDelay=true;
		}
		assert({foreach(x; decls) assert(!x.needRetry, x.toString()~" "~to!string(x.needRetry));return 1;}());
		mixin(PropErr!q{decls});
		mixin(SemEplg);
	}

	private TemplateDecl[] templateDecls;
	void addTemplateDecl(TemplateDecl decl){
		templateDecls~=decl;
	}


	mixin Analyze;
	import visitors;
	mixin DeepDup!Module;

	override @property string kind(){return "module";}
	override string toString(){return "some module";} // TODO
}