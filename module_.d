// Written in the D programming language.

import lexer, parser, error, scope_, semantic, util;

import analyze;

import core.memory;
import std.stdio, std.algorithm;

class Module: Declaration{
	Declaration[] decls;
	Scope sc;
	this(string path){
		super(STC.init,New!Identifier(path)); // TODO: fix name
		GC.disable(); scope(exit) GC.enable();
		//auto f=File(path); // TODO: handle exceptions
		File f; if(path=="-") f=stdin; else f=File(path);
		auto app=mallocAppender!(char[])();
		foreach(r;f.byChunk(1024)){app.put(cast(char[])r);}
		app.put("\0\0\0\0"); // insert 4 padding zero bytes
		string code=cast(string)app.data;
		sc=new ModuleScope(new FormattingErrorHandler(), this);
		//sc=new Scope(new SimpleErrorHandler(path, code));
		//auto lexer = lex(code);
		// int count=0; foreach(tk;lexer){count++;}writeln(count);
		auto src = new Source(path, code);
		decls=parse(src,sc.handler);
		sstate = SemState.pre;
		if(sc.handler.nerrors) sstate = SemState.error;
	}

	override void presemantic(Scope=null){
		if(sstate == SemState.pre){
			foreach(ref x;decls){
				x.stc|=STCstatic;
				x.presemantic(sc); // add all to symbol table
				Scheduler().add(x, sc);
			}
			scope_ = sc;
			sstate = SemState.begin;
		}
	}

	override void buildInterface(){
		mixin(SemPrlg);
		if(sstate == SemState.pre) presemantic();
		foreach(ref x;decls){x.buildInterface();mixin(Rewrite!q{x});}
	}

	override void semantic(Scope=null){
		mixin(SemPrlg);
		if(sstate == SemState.pre) presemantic();
		foreach(ref x; decls){
			x.semantic(sc);
			mixin(Rewrite!q{x});
		}
		foreach(x; decls) mixin(SemProp!q{x});
		assert(sstate==SemState.error||{foreach(x; decls) assert(x.sstate == SemState.completed && !x.needRetry, x.toString()~" "~to!string(x.needRetry));return 1;}());
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