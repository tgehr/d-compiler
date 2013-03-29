// Written in the D programming language.

import std.algorithm, std.array, std.string, std.conv;

import module_;
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
}

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
}*/

class DoesNotExistDecl: Declaration{
	this(Identifier orig){originalReference = orig; super(STC.init, orig); sstate = SemState.completed;}
	Identifier originalReference;
}

abstract class Scope{ // SCOPE
	abstract @property ErrorHandler handler();

	protected void potentialAmbiguity(Identifier decl, Identifier lookup){
		//error(format("declaration of '%s' results in potential ambiguity", decl), decl.loc);
		// note("offending symbol lookup", lookup.loc);
		error(format("declaration of '%s' smells suspiciously fishy", decl), decl.loc);
		note(format("this lookup should have %s if it was valid", lookup.meaning?"resolved to it":"succeeded"), lookup.loc);
	}

	bool insert(Declaration decl)in{
		assert(decl.name&&decl.name.ptr&&!decl.scope_, decl.toString()~" "~(decl.scope_ is null?" null scope":"non-null scope"));
	}out(result){
		assert(!result||decl.scope_ is this);
	}body{
		auto dd=lookupExactlyHere(decl.name,null), d = dd.value, dep = dd.dependee;
		assert(!dd.dependee||!dd.value);
		if(!dep&&d){
			 if(typeid(d) is typeid(DoesNotExistDecl)){
				potentialAmbiguity(decl.name, d.name);
				mixin(SetErr!q{d.name});
				return false;
		     }else if(auto fd=decl.isOverloadableDecl()){ // some declarations can be overloaded, so no error
				if(auto os=d.isOverloadSet()){
					fd.scope_ = this;
					os.add(fd);
					return true;
				}
				assert(!d.isOverloadableDecl());
			}
			error(format("redefinition of '%s'",decl.name), decl.name.loc);
			note("previous definition was here",d.name.loc);
			mixin(SetErr!q{d});
			return false;
		}

		if(auto ov = decl.isOverloadableDecl()){
			decl.scope_ = this;
			decl = New!OverloadSet(ov);
		}

		symtab[decl.name.ptr]=decl;
		decl.scope_=this;
		Identifier.tryAgain = true; // TODO: is this required?
		return true;
	}

	bool inexistent(Identifier ident){
		auto dd=lookupExactlyHere(ident,null), d = dd.value, dep = dd.dependee;
		assert(!dd.dependee||!dd.value);
		if(!dep&&d){
			if(typeid(d) !is typeid(DoesNotExistDecl)){
				potentialAmbiguity(d.name, ident);
				mixin(SetErr!q{ident});
				return false;
			}
		}else insert(New!DoesNotExistDecl(ident));
		return true;
	}

	// scope where the identifier will be resolved next
	Dependent!Scope getUnresolved(Identifier ident, bool noHope=false){
		mixin(LookupHere!q{auto d; this, ident, null});
		if(d && typeid(d) is typeid(DoesNotExistDecl))
			return null.independent!Scope;
		return this.independent!Scope;
	}

	Dependent!Declaration lookup(Identifier ident, lazy Declaration alt){
		return lookupHere(ident, alt);
	}

	final Dependent!Declaration lookupExactlyHere(Identifier ident, lazy Declaration alt){
		return symtab.get(ident.ptr, alt).independent;
	}

	Dependent!Declaration lookupHere(Identifier ident, lazy Declaration alt){
		return lookupExactlyHere(ident, alt);
	}

	void potentialInsert(Identifier ident, Declaration decl){
		auto ptr = ident.ptr in psymtab;
		if(!ptr) psymtab[ident.ptr]~=decl;
		else if((*ptr).find(decl).empty) (*ptr)~=decl;
	}

	void insertMixin(MixinDecl decl){
		mixins ~= decl;
	}
	void removeMixin(MixinDecl decl){
		foreach(i,x; mixins){
			if(x is decl){
				mixins[i]=move(mixins[$-1]);
				mixins=mixins[0..$-1];
				mixins.assumeSafeAppend();
				break;
			}
		}
	}

	void potentialRemove(Identifier ident, Declaration decl){
		auto ptr = ident.ptr in psymtab;
		if(!ptr) return;
		foreach(i,x;*ptr)
			if(x is decl){
				(*ptr)[i]=move((*ptr)[$-1]);
				(*ptr)=(*ptr)[0..$-1];
				(*ptr).assumeSafeAppend();
				break;
			}
	}

	Declaration/+final+/[] potentialLookup(Identifier ident){
		return psymtab.get(ident.ptr,[])~cast(Declaration[])mixins;
		// TODO: this is probably slow
		// TODO: DMD should allow this without a cast
	}


	bool isNestedIn(Scope rhs){ return rhs is this; }

	VarDecl getDollar(){return null;}
	FunctionDef getFunction(){return null;}
	AggregateDecl getAggregate(){return null;}
	Declaration getDeclaration(){return null;}
	TemplateInstanceDecl getTemplateInstance(){return null;}
	Module getModule(){return null;}
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

	// functionality handy for closures:
	int getFrameNesting(){ return 0; }

	void error(lazy string err, Location loc){handler.error(err,loc);}
	void note(lazy string err, Location loc){handler.note(err,loc);}


	override string toString(){return to!string(typeid(this))~"{"~join(map!(to!string)(symtab.values),",")~"}";}

	final Scope cloneNested(Scope parent){
		auto r = New!NestedScope(parent);
		r.symtab=symtab.dup;
		return r;
	}

protected:
	bool canDeclareNested(Declaration decl){return true;} // for BlockScope
private:
	Declaration[const(char)*] symtab;
	Declaration[][const(char)*] psymtab;
	MixinDecl[] mixins;
}

class ModuleScope: Scope{
	Module module_;
	private ErrorHandler _handler;
	override @property ErrorHandler handler(){return _handler;}
	this(ErrorHandler handler, Module module_){
		this._handler=handler;
		this.module_=module_;
	}
	override Dependent!Declaration lookup(Identifier ident, lazy Declaration alt){
		if(!ident.name.length) return module_.independent!Declaration;
		return super.lookup(ident, alt);
	}
	override Module getModule(){return module_;}
}

class NestedScope: Scope{
	Scope parent;

	override @property ErrorHandler handler(){return parent.handler;}
	this(Scope parent) in{assert(!!parent);}body{
		this.parent=parent;
	}

	override Dependent!Declaration lookup(Identifier ident, lazy Declaration alt){
		mixin(LookupHere!q{auto r; this, ident, null});
		if(!r) return null.independent!Declaration;
		if(typeid(r) is typeid(DoesNotExistDecl)) return parent.lookup(ident, alt);
		return r.independent;
	}

	override Dependent!Scope getUnresolved(Identifier ident, bool noHope=false){
		mixin(LookupHere!q{auto d; this, ident, null});
		if(d && typeid(d) is typeid(DoesNotExistDecl))
			return parent.getUnresolved(ident, noHope);
		return this.independent!Scope;
	}

	override bool isNestedIn(Scope rhs){ return this is rhs || parent.isNestedIn(rhs); }

	override bool insertLabel(LabeledStm stm){
		return parent.insertLabel(stm);
	}
	override LabeledStm lookupLabel(Identifier ident){
		return parent.lookupLabel(ident);
	}
	override void registerForLabel(GotoStm stm, Identifier l){
		parent.registerForLabel(stm, l);
	}
	override int unresolvedLabels(scope int delegate(GotoStm) dg){
		return parent.unresolvedLabels(dg);
	}

	override int getFrameNesting(){ return parent.getFrameNesting(); }

	override VarDecl getDollar(){return parent.getDollar();}
	override FunctionDef getFunction(){return parent.getFunction();}
	override AggregateDecl getAggregate(){return parent.getAggregate();}
	override Declaration getDeclaration(){return parent.getDeclaration();}
	override TemplateInstanceDecl getTemplateInstance(){return parent.getTemplateInstance();}
	override Module getModule(){return parent.getModule();}
}

interface DollarProvider{ VarDecl getDollar(); }

class DollarScope: NestedScope{
	VarDecl dollar;
	DollarProvider provider;

	this(Scope parent, DollarProvider provider){
		super(parent);
		this.provider = provider;
	}

	override VarDecl getDollar(){
		if(!dollar && provider){
			dollar = provider.getDollar();
			provider = null;
		}
		return dollar;
	}
}

class AggregateScope: NestedScope{
	this(AggregateDecl decl) in{assert(!!decl.scope_);}body{
		super(decl.scope_);
		aggr = decl;
	}

	override AggregateDecl getAggregate(){ return aggr; }
	override AggregateDecl getDeclaration(){ return aggr; }

	override int getFrameNesting(){ return parent.getFrameNesting()+1; }
private:
	AggregateDecl aggr;
}

template AggregateParentsInOrderTraversal(string bdy,string raggr="raggr", string parent="parent",bool weak=false){
	enum AggregateParentsInOrderTraversal = mixin(X!q{
		static if(is(typeof(return) A : Dependent!T,T)) alias T R;
		else static assert(0);
		for(size_t i=0; i<@(raggr).parents.length; i++){
			@(raggr).findFirstNParents(i+1,@(weak.to!string));
			if(@(raggr).parents[i].sstate==SemState.error)
				continue;
			static if(@(weak.to!string)){
				mixin(Rewrite!q{@(raggr).parents[i]});
				if(@(raggr).parents[i].sstate != SemState.completed){
					@(raggr).parents[i].needRetry = true;
					return Dependee(@(raggr).parents[i], @(raggr).scope_).dependent!R;
				}
				
			}else{
				if(@(raggr).parents[i].needRetry){
					return Dependee(@(raggr).parents[i], @(raggr).scope_).dependent!R;
				}
			}
			assert(cast(AggregateTy)@(raggr).parents[i]
			       && cast(ReferenceAggregateDecl)(cast(AggregateTy)@(raggr).parents[i]).decl);
			auto @(parent) = cast(ReferenceAggregateDecl)cast(void*)
			(cast(AggregateTy)cast(void*)@(raggr).parents[i]).decl;
			@(bdy)
		}
	});
}

class InheritScope: AggregateScope{
	invariant(){ assert(!!cast(ReferenceAggregateDecl)aggr); }
	@property ref ReferenceAggregateDecl raggr(){ return *cast(ReferenceAggregateDecl*)&aggr; }
	this(ReferenceAggregateDecl decl) in{assert(!!decl.scope_);}body{ super(decl); }

	override Dependent!Declaration lookupHere(Identifier ident, lazy Declaration alt){
		// dw("looking up ",ident," in ", this);
		if(raggr.shortcutScope){
			auto dep = raggr.shortcutScope.lookupHere(ident, null);
			auto val = dep.value;
			if(!dep.dependee && val && typeid(val) is typeid(DoesNotExistDecl))
				return raggr.shortcutScope.lookup(ident, alt);
		}
		mixin(LookupHere!q{auto d; super, ident, alt});
		// TODO: make more efficient than string comparison
		if(ident.name !="this" && ident.name!="~this" && ident.name!="invariant") // do not inherit constructors and destructors and invariants
		// if sstate is 'completed', DoesNotExistDecls do not need to be generated
		if(!d && raggr.sstate == SemState.completed ||
		   d && typeid(d) is typeid(DoesNotExistDecl))
		mixin(AggregateParentsInOrderTraversal!(q{
			auto lkup = parent.asc.lookupHere(ident, null);
			if(lkup.dependee) return lkup.dependee.dependent!Declaration;
			d = lkup.value;
			if(parent.sstate != SemState.completed && !d ||
			   d && typeid(d) !is typeid(DoesNotExistDecl)) break;
		},"raggr","parent",true));
		if(!d) d = alt;
		return d.independent;
	}

	override Dependent!Scope getUnresolved(Identifier ident, bool noHope=false){
		mixin(LookupHere!q{auto d; super, ident, null});
		if(!d || typeid(d) !is typeid(DoesNotExistDecl)) return this.independent!Scope;
		Dependent!Scope traverse(){
			mixin(AggregateParentsInOrderTraversal!(q{
				if(auto lkup = parent.asc.getUnresolved(ident, noHope).prop) return lkup;
			},"raggr","parent",true));
			return null.independent!Scope;
		}
		if(noHope){
			auto tr = traverse();
			if(!tr.dependee && tr.value) return tr;
			if(!raggr.shortcutScope) raggr.initShortcutScope(parent);
			return raggr.shortcutScope.getUnresolved(ident, noHope);
		}
		// TODO: this is a hack
		if(auto tr = traverse().prop) return tr;
		return ident.recursiveLookup?parent.getUnresolved(ident, noHope):null.independent!Scope;
	}
}


class TemplateScope: NestedScope{
	// inherits Scope parent; // parent scope of the template declaration
	Scope iparent; // parent scope of the instance
	TemplateInstanceDecl tmpl;
	this(Scope parent, Scope iparent, TemplateInstanceDecl tmpl) in{assert(!!parent);}body{
		super(parent);
		this.iparent = iparent;
		this.tmpl=tmpl;
	}

	override int getFrameNesting(){ return iparent.getFrameNesting(); }

	override FunctionDef getFunction(){return iparent.getFunction();}
	override AggregateDecl getAggregate(){return iparent.getAggregate();}
	override Declaration getDeclaration(){return iparent.getDeclaration();}
	override TemplateInstanceDecl getTemplateInstance(){ return tmpl; }
}

class OrderedScope: NestedScope{ // Forward references don't get resolved
	invariant(){ foreach(d; symtab) assert(d&&typeid(d) !is typeid(DoesNotExistDecl)); }

	this(Scope parent){super(parent);}
	override Dependent!Declaration lookup(Identifier ident, lazy Declaration alt){
		// this is valid because OrderedScopes never contain any DoesNotExistDecl's
		if(auto t=lookupHere(ident, null).prop) return t;
		return parent.lookup(ident, alt);
	}
	override bool inexistent(Identifier ident){
		return parent.inexistent(ident);
	}
	override Dependent!Scope getUnresolved(Identifier ident, bool noHope=false){
		return parent.getUnresolved(ident, noHope);
	}
}

final class FunctionScope: OrderedScope{
	this(Scope parent, FunctionDef fun){
		super(parent);
		this.fun=fun;
	}

	override bool insertLabel(LabeledStm stm){
		if(auto s = lstmsymtab.get(stm.l.ptr,null)){
			error(format("redefinition of label '%s'",stm.l.toString()),stm.l.loc);
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

	override int getFrameNesting(){ return parent.getFrameNesting()+1; }

	override FunctionDef getFunction(){return fun;}
	override FunctionDef getDeclaration(){return fun;}
protected:
	override bool canDeclareNested(Declaration decl){ // for BlockScope
		return !(decl.name.ptr in symtab); // TODO: More complicated stuff.
	}
private:
	FunctionDef fun;
	LabeledStm[const(char)*] lstmsymtab;
	GotoStm[] _unresolvedLabels;
}

class BlockScope: OrderedScope{ // No shadowing of declarations in the enclosing function.
	this(Scope parent){
		super(parent);
	}

	override bool insert(Declaration decl){
		if(!parent.canDeclareNested(decl)){
			auto confl=parent.lookup(decl.name, null).value;
			assert(!!confl);
			error(format("declaration '%s' shadows a %s%s",decl.name,confl.kind=="parameter"?"":"local ",confl.kind), decl.name.loc);
			note("previous declaration is here",confl.name.loc);
			return false;
		}
		return super.insert(decl); // overload lookup
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
