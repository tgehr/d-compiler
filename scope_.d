
import std.algorithm, std.array, std.string, std.conv;

import lexer, parser, expression, declaration, semantic, util, error;



/*class FwdRef: Declaration{ // Forward reference. Dummy node for identifier that has not yet been resolved
	this(Identifier name){
		sstate=SemState.fwdRefs;
		super(STC.init, name);
	}
	Declaration resolved = null;
	override Declaration semantic(Scope sc){
		if(resolved) return resolved;
		return sc.lookup(name, this);
	}
	override FwdRef isFwdRef(){return this;}
}*/

class MutableAliasRef: Declaration{ // used if a declaration references another declaration, eg mixin Template;
	Declaration other;
	bool canShadow = true;
	this(Declaration other){this.other=other; super(other.stc, other.name);}
	override Declaration semantic(Scope sc){
		canShadow = false;
		return other.semantic(sc);
	}
	void shadow(Scope sc, Declaration newDecl){
		if(canShadow){ other = newDecl; canShadow = false; return; }
		sc.error(format("cannot shadow declaration '%s' which has already been used", other.name), newDecl.loc);
	}
	override MutableAliasRef isMutableAliasRef(){return this;}
}


class Scope{ // TOP LEVEL (MODULE) SCOPE
	this(ErrorHandler handler){this.handler=handler;}

	ErrorHandler handler;

	bool insert(Declaration decl)in{assert(decl.name.ptr);}body{
		if(auto d=symtab.get(decl.name.ptr,null)){
			if(auto fd=decl.isOverloadableDecl()){ // some declarations can be overloaded, so no error
				if(auto os=d.isOverloadSet()){
					os.add(fd);
					return true;
				}else if(auto ofd=d.isOverloadableDecl()){
					symtab[decl.name.ptr]=New!OverloadSet(fd,ofd);
					return true;
				}
			}
			if(d.sstate != SemState.error){ // TODO: is this always desirable?
				error(format("redefinition of '%s'",decl.name), decl.name.loc);
				note("previous definition was here",d.name.loc);	             
			}
			return false;
		}
		symtab[decl.name.ptr]=decl;
		return true;
	}
	
	Declaration lookup(Identifier ident, lazy Declaration alt){
		return symtab.get(ident.ptr, alt);
	}
	Declaration lookup(Identifier ident){
		if(auto lk = lookup(ident, null)) return lk;
		error(format("undefined identifier '%s'",ident.name), ident.loc);
		return New!ErrorDecl();
	}
	
	
	T push(T:NestedScope)(R sc){ return New!T(this); }
	Scope pop(){assert(0,"tried to pop module scope");}
	void error(string err, Location loc){handler.error(err,loc);}
	void note(string err, Location loc){handler.note(err,loc);}

protected:
	bool canDeclareNested(Declaration decl){return true;} // for BlockScope
private:
	Declaration[const(char)*] symtab;
	//FwdRef[] FwdRefs; // TODO: maybe use more efficient datastructure
}

abstract class NestedScope: Scope{
	Scope parent;
	override Scope pop(){return parent;}
	this(Scope parent){
		super(parent.handler);
		this.parent=parent;
	}
	alias Scope.lookup lookup;
	override Declaration lookup(Identifier ident){
		return lookup(ident, parent.lookup(ident));
	}
}

class FunctionScope: NestedScope{ // Forward references don't get resolved
	this(Scope parent){
		super(parent);
	}
	Declaration lookup(Identifier ident, lazy Declaration alt){
		return symtab.get(ident.ptr, parent.lookup(ident));
	}
	alias Scope.lookup lookup; // overload lookup
protected:
	bool canDeclareNested(Declaration decl){ // for BlockScope
		return !(decl.name.ptr in symtab); // TODO: More complicated stuff.
	}
}

class BlockScope: FunctionScope{ // No shadowing of declarations in the enclosing function.
	this(Scope parent){
		super(parent);
	}
	override bool insert(Declaration decl){
		if(!parent.canDeclareNested(decl)){
			auto confl=parent.lookup(decl.name);
			error(format("declaration '%s' shadows a %s%s",decl.name,confl.kind=="parameter"?"":"local ",confl.kind), decl.name.loc);
			note("previous declaration is here",confl.name.loc);
			return false;
		}
		super.insert(decl); // overload lookup
		return true;
	}
protected:
	override bool canDeclareNested(Declaration decl){
		return super.canDeclareNested(decl) && parent.canDeclareNested(decl);
	}
}