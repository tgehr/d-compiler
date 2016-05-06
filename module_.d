// Written in the D programming language
// Author: Timon Gehr
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import lexer, parser, error, scope_, semantic, util;

import analyze;

import core.memory;
import std.stdio, std.algorithm, std.conv;

import std.path;
import file=std.file;

string readCode(File f){
	// TODO: use memory-mapped file with 4 padding zero bytes
	auto app=mallocAppender!(char[])();
	foreach(r;f.byChunk(1024)){app.put(cast(char[])r);}
	app.put("\0\0\0\0"); // insert 4 padding zero bytes
	return cast(string)app.data;	
}
string readCode(string path){ return readCode(File(path)); }

class ModuleRepository{
	void addPath(string path)in{
		debug assert(!searchPathFrozen);
	}body{
		searchPath~=path;
	}

	private string getActualPath(string path,bool package_){
		auto spath = path;
		auto ext = spath.extension;
		if(ext=="") spath=spath.setExtension("d");
		if(file.exists(spath)) return spath;
		foreach(s;searchPath){
			auto cand=buildPath(s,spath);
			if(file.exists(cand))
				return cand;
		}
		if(package_){
			foreach(s;searchPath){
				auto cand=buildPath(s,path,"package.d");
				if(file.exists(cand))
					return cand;
			}
		}
		return path;
	}

	Module getModule(string path, bool package_, out string err){
		debug searchPathFrozen=true;
		path = getActualPath(path,package_);
		auto ext = path.extension;
		if(ext != ".d" && ext != ".di"){
			err = path~": unrecognized extension: "~ext;
			return null;
		}
		err = null;
		string code;
		if(path in modules) return modules[path];
		try code=readCode(path);
		catch(Exception){
			if(!file.exists(path)) err = path ~ ": no such file";
			else err = path ~ ": error reading file";
			return modules[path]=null;
		}
		auto name=New!Identifier(path);
		auto r=modules[path]=new Module(name, path, code, this);
		r.presemantic(r.sc);
		return r;
	}

	bool hasErrors(){
		foreach(_,m;modules) if(!m || m.sstate == SemState.error) return true;
		return false;
	}

private:
	Module[string] modules;
	string[] searchPath;
	debug bool searchPathFrozen;
}

class Module: Declaration{
	Declaration[] decls;
	Scope sc;
	ModuleRepository repository;

	private this(Identifier name, string path, string code, ModuleRepository repository){
		super(STC.init,name); // TODO: fix name
		this.repository = repository;
		GC.disable(); scope(exit) GC.enable();
		sc=new ModuleScope(new FormattingErrorHandler(), this);
		//sc=new Scope(new SimpleErrorHandler(path, code));;
		auto src = new Source(path, code);
		//auto lexer = lex(src);
		//int count=0; foreach(tk;lexer){count++;}writeln(count);
		decls=parse(src,sc.handler);
		sstate = SemState.pre;
		if(sc.handler.nerrors) sstate = SemState.error;
	}

	override void presemantic(Scope=null){
		if(sstate == SemState.pre){
			foreach(ref x;decls){
				if(!x.isImportDecl()) x.stc|=STCstatic;
				x.presemantic(sc); // add all to symbol table
				Scheduler().add(x, sc);
			}
			scope_ = sc;
			sstate = SemState.begin;
		}
	}

	override void semantic(Scope=null){
		mixin(SemPrlg);
		if(sstate == SemState.pre) presemantic();
		foreach(ref x; decls){
			x.semantic(sc);
			mixin(Rewrite!q{x});
		}
		foreach(x; decls) mixin(SemProp!q{x});
		assert(sstate==SemState.error||{foreach(x; decls) assert(x.sstate == SemState.completed && !x.needRetry, text(x," ", x.sstate, " ", x.needRetry));return 1;}());
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
	override string toString(){return "module "~name.name~";";}
}
