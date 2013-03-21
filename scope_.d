
import std.algorithm, std.array, std.string, std.conv;

import lexer, parser, expression, declaration, util, error;


alias GCAlloc.New New; // maybe replace with better allocator if it is a problem

class OverloadSet: Declaration{ // purely semantic node
	this(FunctionDecl[] args...)in{assert(args.length);}body{
		super(STC.init,args[0].name);
		foreach(d;args) add(d);
	}
	this(Identifier name){super(STC.init,name);}
	void add(FunctionDecl decl){decls~=decl;}
	override string toString(){return join(map!(to!string)(decls),"\n");}
	override OverloadSet isOverloadSet(){return this;}
private:
	FunctionDecl[] decls; // TODO: use more efficient data structure
}

class FwdRef: Declaration{ // Forward reference. Dummy node for identifier that has not yet been resolved
	this(Identifier name){super(STC.init, name);}
	Declaration resolved = null;
	Declaration semantic(Scope sc){
		if(resolved) return resolved;
		return sc.lookup(name, this);
	}
	override FwdRef isFwdRef(){return this;}
}

class MutableAliasRef: Declaration{ // used if a declaration references another declaration, eg mixin Template;
	Declaration other;
	bool canShadow = true;
	this(Declaration other){this.other=other; super(other.stc, other.name);}
	Declaration semantic(Scope sc){
		canShadow = false;
		return other.semantic(sc);
	}
	void shadow(Scope sc, Declaration newDecl){
		if(canShadow){ other = newDecl; canShadow = false; return; }
		sc.error(format("cannot shadow declaration '%s' which has already been used", other.name), newDecl.loc);
	}
	MutableAliasRef isMutableAliasRef(){return this;}
}


class Scope{ // TOP LEVEL (MODULE) SCOPE
	this(ErrorHandler handler){this.handler=handler;}

	ErrorHandler handler;

	void insert(Declaration decl)in{assert(decl.name.ptr);}body{
		if(auto d=symtab.get(decl.name.ptr,null)){
			if(auto fw=decl.isFwdRef()){ // forward references can be resolved, so no error
				
			}else if(auto fd=decl.isFunctionDecl()){ // functions can be overloaded, so no error
				if(auto os=d.isOverloadSet()){
					os.add(fd);
					return;
				}else if(auto ofd=d.isFunctionDecl()){
					symtab[decl.name.ptr]=New!OverloadSet(fd,ofd);
					return;
				}
			}
			handler.error(format("redefinition of '%s'",decl.name), decl.name.loc);
			handler.note("previous definition was here",d.name.loc);	             
			return;
		}
		return symtab[decl.name.ptr]=decl;
	}
	
	Declaration lookup(Identifier ident, lazy Declaration alt){
		return symtab.get(ident.ptr, alt);
	}
	Declaration lookup(Identifier ident){
		return lookup(ident, New!FwdRef(ident));  // the allocation is lazy
	}
	
	
	T push(T:NestedScope)(R sc){ return New!T(this); }
	Scope pop(){assert(0,"tried to pop module scope");}
	void error(string err, Location loc){handler.error(err,loc);}

private:
	Declaration[const(char)*] symtab;
	FwdRef[] FwdRefs; // TODO: maybe use more efficient datastructure
}

abstract class NestedScope: Scope{
	Scope parent;
	override Scope pop(){return parent;}
	this(Scope parent){
		super(parent.handler);
		this.parent=parent;
	}
	override Declaration lookup(Identifier ident){
		return lookup(ident, New!MutableAliasRef(parent.lookup(ident)));
	}
	alias Scope.lookup lookup; // overload lookup
}

class FunctionScope: NestedScope{ // Forward references don't get resolved
	this(Scope parent){
		super(parent);
	}
	override Declaration lookup(Identifier ident){
		if(auto lk = symtab.get(ident.ptr, parent.lookup(ident, null))) return lk;
		error(format("undefined identifier '%s'",ident.name), ident.loc);
		return New!ErrorDecl();
	}
	alias Scope.lookup lookup; // overload lookup
}
