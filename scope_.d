// Written in the D programming language.

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

	bool insert(Declaration decl)in{
		assert(decl.name&&decl.name.ptr&&!decl.scope_, decl.toString()~" "~(decl.scope_ is null?" null scope":"non-null scope"));
	}out(result){
		assert(!result||decl.scope_ is this);
	}body{
		if(auto d=symtab.get(decl.name.ptr,null)){
			if(auto fd=decl.isOverloadableDecl()){ // some declarations can be overloaded, so no error
				if(auto os=d.isOverloadSet()){
					fd.scope_ = this;
					os.add(fd);
					return true;
				}else if(auto ofd=d.isOverloadableDecl()){
					auto os = New!OverloadSet(fd,ofd);
					decl.scope_ = os.scope_ = this;
					symtab[decl.name.ptr]=os;
					return true;
				}
			}
			error(format("redefinition of '%s'",decl.name), decl.name.loc);
			note("previous definition was here",d.name.loc);	             
			// d.sstate = SemState.error;
			return false;
		}
		symtab[decl.name.ptr]=decl;
		decl.scope_=this;
		return true;
	}

	// TODO: useful or just unnecessarily convenient?
	Declaration lookup(Identifier ident, lazy Declaration alt){
		return symtab.get(ident.ptr, alt);
	}
	Declaration lookup(Identifier ident){
		if(auto lk = lookup(ident, null)) return lk;
		error(format("undefined identifier '%s'",ident.name), ident.loc);
		return New!ErrorDecl();
	}


	FunctionDef getFunction(){return null;}
	// control flow structures:
	BreakableStm getBreakableStm(){return null;}
	LoopingStm getLoopingStm(){return null;}
	SwitchStm getSwitchStm(){return null;}
	bool isEnclosing(BreakableStm){return false;}

	bool insertLabel(LabeledStm stm){ assert(0); }
	LabeledStm lookupLabel(Identifier lbl){ assert(0); }	
	void registerForLabel(GotoStm stm, Identifier l)in{
		assert(stm.t==WhichGoto.identifier);
	}body{ assert(0); }
	int unresolvedLabels(scope int delegate(GotoStm) dg){return 0;}
	void error(lazy string err, Location loc){handler.error(err,loc);}
	void note(lazy string err, Location loc){handler.note(err,loc);}


	string toString(){return "scope{"~join(map!(to!string)(symtab.values),",")~"}";}

protected:
	bool canDeclareNested(Declaration decl){return true;} // for BlockScope
private:
	Declaration[const(char)*] symtab;
	//FwdRef[] FwdRefs; // TODO: maybe use more efficient datastructure
}

abstract class NestedScope: Scope{
	Scope parent;
	// override Scope pop(){return parent;}
	this(Scope parent) in{assert(!!parent);}body{
		super(parent.handler);
		this.parent=parent;
	}

	override Declaration lookup(Identifier ident, lazy Declaration alt){
		return symtab.get(ident.ptr, parent.lookup(ident, alt));
	}

	override bool insertLabel(LabeledStm stm){
		return parent.insertLabel(stm);
	}
	override LabeledStm lookupLabel(Identifier ident){
		return parent.lookupLabel(ident);
	}
	void registerForLabel(GotoStm stm, Identifier l){
		parent.registerForLabel(stm, l);
	}
	override int unresolvedLabels(scope int delegate(GotoStm) dg){
		return parent.unresolvedLabels(dg);
	}

	override FunctionDef getFunction(){return parent.getFunction();}

}

class FunctionScope: NestedScope{ // Forward references don't get resolved
	this(Scope parent, FunctionDef fun){
		super(parent);
		this.fun=fun;
	}	

	override bool insertLabel(LabeledStm stm){
		if(auto s = lstmsymtab.get(stm.l.ptr,null)){
			error(format("rededefinition of label '%s'",stm.l.toString()),stm.l.loc);
			note("previous definition was here",s.l.loc);
			return false;
		}
		lstmsymtab[stm.l.ptr] = stm;
		return true;
	}
	override LabeledStm lookupLabel(Identifier l){
		if(auto s = lstmsymtab.get(l.ptr,null)) return s;
		return null;
	}
	override int unresolvedLabels(scope int delegate(GotoStm) dg){
		foreach(x;_unresolvedLabels) if(auto r = dg(x)) return r;
		return 0;
	}
	override void registerForLabel(GotoStm stm, Identifier l){
		// rename to lbl to make DMDs hashtable fail
		if(auto lbll = lookupLabel(l)) stm.resolveLabel(lbll);
		else _unresolvedLabels~=stm;
	}
	override FunctionDef getFunction(){return fun;}
	alias Scope.lookup lookup; // overload lookup
protected:
	bool canDeclareNested(Declaration decl){ // for BlockScope
		return !(decl.name.ptr in symtab); // TODO: More complicated stuff.
	}
private:
	FunctionDef fun;
	LabeledStm[const(char)*] lstmsymtab;
	GotoStm[] _unresolvedLabels;
}

class BlockScope: NestedScope{ // No shadowing of declarations in the enclosing function.
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

	void setBreakableStm(BreakableStm brk)in{assert(!brokenOne);}body{
		brokenOne = brk;
	}
	void setLoopingStm(LoopingStm loop)in{assert(!brokenOne&&!theLoop);}body{
		brokenOne = theLoop = loop;
	}
	void setSwitchStm(SwitchStm swstm)in{assert(!brokenOne&&!swstm);}body{
		brokenOne = theSwitch = swstm;
	}

	override BreakableStm getBreakableStm(){
		return brokenOne ? brokenOne : parent.getBreakableStm();
	}
	override LoopingStm getLoopingStm(){
		return theLoop ? theLoop : parent.getLoopingStm();
	}
	override SwitchStm getSwitchStm(){
		return theSwitch ? theSwitch : parent.getSwitchStm();
	}

	override bool isEnclosing(BreakableStm stm){
		return brokenOne is stm || parent.isEnclosing(stm);
	}

protected:
	override bool canDeclareNested(Declaration decl){
		return super.canDeclareNested(decl) && parent.canDeclareNested(decl);
	}
private:
	BreakableStm brokenOne;
	LoopingStm theLoop;
	SwitchStm theSwitch;
}