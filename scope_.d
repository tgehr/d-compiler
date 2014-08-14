// Written in the D programming language.

import std.algorithm, std.array, std.string, std.conv;

import module_;
import lexer, parser, expression, declaration, semantic, util, error;

import std.typecons : q = tuple, Q = Tuple;

mixin CreateBinderForDependent!("LookupImpl");
mixin CreateBinderForDependent!("LookupHereImpl");
mixin CreateBinderForDependent!("GetUnresolvedImpl");
mixin CreateBinderForDependent!("GetUnresolvedHereImpl");


final class DoesNotExistDecl: Declaration{
	this(Identifier orig){originalReference = orig; super(STC.init, orig); sstate = SemState.completed;}
	Identifier originalReference;

	override string toString(){ return "'"~originalReference.name~"' does not exist."; }
}

static interface IncompleteScope{
	bool inexistent(Scope view, Identifier ident);
	Declaration[] potentialLookup(Scope view, Identifier ident);
	// only for use in this module:
	bool inexistentImpl(Scope view, Identifier ident);
	Declaration lookupExactlyHere(Scope view, Identifier ident);
}

enum ImportKind : ubyte{
	private_,
	public_,
	protected_,
	mixin_,
}
auto importKindFromSTC(STC stc){
	if(stc&STCpublic) return ImportKind.public_;
	if(stc&STCprotected) return ImportKind.protected_;
	return ImportKind.private_;
}

enum suspiciousDeclDesc = "smells suspicously fishy"; // "stinks" ? "is suspicous" ?

abstract class Scope: IncompleteScope{ // SCOPE
	abstract @property ErrorHandler handler();

	protected void potentialAmbiguity(Identifier decl, Identifier lookup){
		error(format("declaration of '%s' "~suspiciousDeclDesc, decl), decl.loc);
		note(format("this lookup should have %s if it was valid", lookup.meaning?"resolved to it":"succeeded"), lookup.loc);
	}

	bool insert(Declaration decl)in{
		assert(decl.name&&decl.name.ptr&&!decl.scope_, decl.toString()~" "~(decl.scope_ is null?" null scope":"non-null scope"));
	}out(result){
		assert(!result||decl.scope_ is this);
	}body{
		auto d=symtabLookup(this, decl.name);
		if(d){
			 if(typeid(d) is typeid(DoesNotExistDecl)){
				potentialAmbiguity(decl.name, d.name);
				mixin(SetErr!q{d.name});
				return false;
		     }else if(auto fd=decl.isOverloadableDecl()){ // some declarations can be overloaded, so no error
				if(auto os=d.isOverloadSet()){
					fd.scope_ = this;
					if(os.sealingLookup){
						error("introduction of new overload "~suspiciousDeclDesc, decl.loc);
						note("overload set was sealed here", os.sealingLookup.loc);
						return false;
					}
					os.add(fd);
					return true;
				}else if(auto ad=decl.isAliasDecl()){
					auto add=ad.getAliasedDecl();
					if(!add||add.isOverloadableDecl()){
						fd.scope_ = this;
						auto os=New!OverloadSet(fd);
						os.addAlias(ad);
						decl=os;
						goto Lok;
					}
				}
				assert(!d.isOverloadableDecl());
			}
			redefinitionError(decl, d);
			mixin(SetErr!q{d});
			return false;
		}

		if(auto ov = decl.isOverloadableDecl()){
			decl.scope_ = this;
			decl = New!OverloadSet(ov);
		}
	Lok:
		symtab[decl.name.ptr]=decl;
		decl.scope_=this;
		Identifier.tryAgain = true; // TODO: is this required?
		return true;
	}

	void redefinitionError(Declaration decl, Declaration prev) in{
		assert(decl.name.ptr is prev.name.ptr);
	}body{
		error(format("redefinition of '%s'",decl.name), decl.name.loc);
		note("previous definition was here",prev.name.loc);
	}

	// lookup interface

	private static bool[Object] visited;
	private enum Setup = q{
		assert(visited is null,text(visited));
		scope(exit) visited=null;
	};
	// a dummy DoesNotExistDecl for circular lookups through imports
	private @property DoesNotExistDecl inex(){
		static DoesNotExistDecl inex;
		return inex?inex:(inex=New!DoesNotExistDecl(null));
	}

	final Dependent!Declaration lookup(Scope view, Identifier ident){
		mixin(Setup);
		return lookupImpl(view,ident);
	}
	final Dependent!Declaration lookupHere(Scope view, Identifier ident, bool onlyMixins){
		mixin(Setup);
		return lookupHereImpl(view,ident, onlyMixins);
	}
	final Dependent!IncompleteScope getUnresolved(Scope view, Identifier ident, bool onlyMixins, bool noHope){
		mixin(Setup);
		return getUnresolvedImpl(view,ident, onlyMixins, noHope);
	}

	final bool inexistent(Scope view, Identifier ident){
		mixin(Setup);
		return inexistentImpl(view, ident);
	}

	// lookup implementation

	// TODO: report DMD bug regarding protected
	/+protected+/ Dependent!Declaration lookupImpl(Scope view, Identifier ident){
		return lookupHereImpl(view, ident, false);
	}

	/+protected+/ Dependent!Declaration lookupHereImpl(Scope view, Identifier ident, bool onlyMixins){
		auto t=lookupExactlyHere(view, ident);
		if(!t || typeid(t) !is typeid(DoesNotExistDecl))
			return t.independent;
		return lookupImports(view, ident, onlyMixins, t);
	}

	Declaration lookupExactlyHere(Scope view, Identifier ident){
		auto r = symtabLookup(view, ident);
		if(r) if(auto ov=r.isOverloadSet()) if(!ov.sealingLookup) return null;
		return r;
	}

	protected final Declaration symtabLookup(Scope view, Identifier ident){
		return symtab.get(ident.ptr, null);
	}

	/+protected+/ Dependent!IncompleteScope getUnresolvedImpl(Scope view, Identifier ident, bool onlyMixins, bool noHope){
		return getUnresolvedHereImpl(view, ident, onlyMixins, noHope);
	}

	// scope where the identifier will be resolved next
	/+protected+/ Dependent!IncompleteScope getUnresolvedHereImpl(Scope view, Identifier ident, bool onlyMixins, bool noHope){
		auto t=lookupExactlyHere(view, ident);
		if(!t) return this.independent!IncompleteScope;
		return getUnresolvedImport(view, ident, onlyMixins, noHope);
	}

	final protected Dependent!Declaration lookupImports(Scope view, Identifier ident, bool onlyMixins, Declaration alt){
		if(this in visited) return (alt?alt:inex).independent!Declaration;
		visited[this]=true;

		size_t count = 0;
		Declaration[] decls;
		foreach(im;imports){
			if(onlyMixins && im[1]!=ImportKind.mixin_) continue;
			// TODO: private (imports)
			mixin(LookupHereImpl!q{auto d;im[0],view,ident,onlyMixins});
			if(!d) return d.independent;
			else if(typeid(d) !is typeid(DoesNotExistDecl)) decls~=d;
		}

		if(!decls.length) dontImport(ident);

		return CrossScopeOverloadSet.buildDecl(this, decls, alt).independent;
	}

	final protected Dependent!IncompleteScope getUnresolvedImport(Scope view, Identifier ident, bool onlyMixins, bool noHope){
		if(this in visited) return null.independent!IncompleteScope;
		visited[this]=true;

		IncompleteScope[] unres;
		bool isUnresolved = false;
		foreach(im;imports){
			if(onlyMixins && im[1]!=ImportKind.mixin_) continue;
			// TODO: private (imports)
			// TODO: eliminate duplication?
			mixin(GetUnresolvedHereImpl!q{auto d;im[0], view, ident, onlyMixins, noHope});
			if(d) unres~=d;
		}
		if(!unres.length){
			dontImport(ident);
			return null.independent!IncompleteScope;
		}

		size_t i=noHope<<1|onlyMixins;

		//(this is a memory optimization that slightly complicates the interface to Identifier)
		// TODO: change the design such that IncompleteScope is not required any more.
		if(!unresolvedImports[i])
			unresolvedImports[i]=New!UnresolvedImports(this,onlyMixins,noHope);
		unresolvedImports[i].unres=unres;
		return unresolvedImports[i].independent!IncompleteScope;
	}
	private static class UnresolvedImports: IncompleteScope{
		Scope outer;

		IncompleteScope[] unres;
		bool onlyMixins;
		bool noHope;

		override string toString(){
			return "'UnresolvedImports of "~outer.getModule().name.name~"'";
		}

		this(Scope outer, bool onlyMixins, bool noHope){
			this.outer = outer;
			this.onlyMixins = onlyMixins;
			this.noHope = noHope;
		}

		final bool inexistent(Scope view, Identifier ident){
			mixin(Setup);
			return inexistentImpl(view, ident);
		}

		bool inexistentImpl(Scope view, Identifier ident){
			if(this in visited) return true;
			visited[this]=true;
			bool success = true;
			foreach(d;unres){
				if(auto x=d.lookupExactlyHere(view, ident)) continue;
				success &= d.inexistentImpl(view, ident);
			}
			return success;
		}

		Declaration[] potentialLookup(Scope view, Identifier ident){
			// TODO: this is very wasteful
			Declaration[] r;
			foreach(im;outer.imports) r~=im[0].potentialLookup(view, ident);
			// dw(this," ",r," ",ident," ",outer.imports.map!(a=>a[0].getModule().name));
			return r;
		}

		Declaration lookupExactlyHere(Scope view, Identifier ident){ return null; }
	}
	UnresolvedImports[4] unresolvedImports;

	/+protected+/ bool inexistentImpl(Scope view, Identifier ident){
		auto d=symtabLookup(view, ident);
		if(!d) insert(New!DoesNotExistDecl(ident));
		else if(auto ov=d.isOverloadSet()){
			assert(!ov.sealingLookup);
			ov.sealingLookup = ident;
		}else if(typeid(d) !is typeid(DoesNotExistDecl)){
			potentialAmbiguity(d.name, ident);
			mixin(SetErr!q{ident});
			return false;
		}
		return true;
	}

	void potentialInsert(Identifier ident, Declaration decl){
		auto ptr = ident.ptr in psymtab;
		if(!ptr) psymtab[ident.ptr]~=decl;
		else if((*ptr).find(decl).empty) (*ptr)~=decl;
	}

	void potentialInsertArbitrary(Declaration mxin, Declaration decl){
		arbitrary ~= mxin;
		arbitrarydecls ~= decl;
	}
	void potentialRemoveArbitrary(Declaration mxin, Declaration decl){
		foreach(i,x; arbitrary){
			if(x is mxin && arbitrarydecls[i] is decl){
				arbitrary[i]=move(arbitrary[$-1]);
				arbitrary=arbitrary[0..$-1];
				arbitrary.assumeSafeAppend();
				arbitrarydecls[i]=move(arbitrarydecls[$-1]);
				arbitrarydecls=arbitrarydecls[0..$-1];
				arbitrarydecls.assumeSafeAppend();
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

	Declaration/+final+/[] potentialLookup(Scope view, Identifier ident){
		// TODO: this is very wasteful
		if(auto d=symtabLookup(view, ident)){
			if(d.isOverloadSet()){
				// do not look up overloads in imports/template mixins
				import std.range : chain, zip;
				auto psym=psymtab.get(ident.ptr,[]);
				return zip(chain(psym,arbitrary),chain(psym,arbitrarydecls))
					.filter!(a=>!!a[0].isMixinDecl()).map!(a=>a[1]).array;
			}else return [];
		}
		return psymtab.get(ident.ptr,[])~arbitrarydecls;
	}

	private Identifier[const(char)*] notImported;
	protected void dontImport(Identifier ident){
		notImported[ident.ptr]=ident;
	}

	final bool addImport(Scope sc, ImportKind kind)in{
		assert(!!sc);
	}body{
		foreach(im;imports) if(im[0] is sc) return true; // TODO: make more efficient?
		imports ~= q(sc,kind);
		bool ret = true;
		if(imports.length==1){
			foreach(_,decl;symtab){
				if(typeid(decl) !is typeid(DoesNotExistDecl)) continue;
				auto dne=cast(DoesNotExistDecl)cast(void*)decl;
				dontImport(dne.originalReference);
			}
		}
		foreach(_,ident;notImported){
			// TODO: this will not report ambiguities/contradictions introduced
			// by modules that are not analyzed to sufficient depth
			// (eg, because their import is the last thing that happens.)
			ret&=sc.inexistentImpl(this, ident);
		}
		return ret;
	}


	bool isNestedIn(Scope rhs){ return rhs is this; }

	VarDecl getDollar(){return null;}
	FunctionDef getFunction(){return null;}
	AggregateDecl getAggregate(){return null;}
	Declaration getDeclaration(){return null;}
	TemplateInstanceDecl getTemplateInstance(){return null;}
	Module getModule(){return null;}

	final Declaration getParentDecl(){
		if(auto decl=getDeclaration()) return decl;
		return getModule();
	}

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
	Scope getFrameScope(){ return null; }

	void error(lazy string err, Location loc){handler.error(err,loc);}
	void note(lazy string err, Location loc){handler.note(err,loc);}


	override string toString(){return to!string(typeid(this))~"{"~join(map!(to!string)(symtab.values),",")~"}";}

	final Scope cloneNested(Scope parent){
		auto r = New!NestedScope(parent);
		r.symtab=symtab.dup;
		return r;
	}

	final Scope cloneFunction(Scope parent, FunctionDef fun){
		auto r = New!FunctionScope(parent, fun);
		r.symtab=symtab.dup;
		return r;
	}
protected:
	bool canDeclareNested(Declaration decl){return true;} // for BlockScope
private:

	Declaration[const(char)*] symtab;
	Declaration[][const(char)*] psymtab;
	Declaration[] arbitrary;
	Declaration[] arbitrarydecls;
	/+Q+/std.typecons.Tuple!(Scope,ImportKind)[] imports; // DMD bug
}

class ModuleScope: Scope{
	Module module_;
	private ErrorHandler _handler;
	override @property ErrorHandler handler(){return _handler;}
	this(ErrorHandler handler, Module module_){
		this._handler=handler;
		this.module_=module_;
	}
	protected override Dependent!Declaration lookupImpl(Scope view, Identifier ident){
		if(!ident.name.length) return module_.independent!Declaration;
		return super.lookupImpl(view, ident);
	}
	override Module getModule(){return module_;}
}

class NestedScope: Scope{
	Scope parent;

	override @property ErrorHandler handler(){return parent.handler;}
	this(Scope parent) in{assert(!!parent);}body{
		this.parent=parent;
	}

	protected override Dependent!Declaration lookupImpl(Scope view, Identifier ident){
		mixin(LookupHereImpl!q{auto r; this, view, ident, false});
		if(!r) return null.independent!Declaration;
		if(typeid(r) is typeid(DoesNotExistDecl)) return parent.lookupImpl(view, ident);
		return r.independent;
	}

	protected override Dependent!IncompleteScope getUnresolvedImpl(Scope view, Identifier ident, bool onlyMixins, bool noHope){
		mixin(GetUnresolvedImpl!q{auto d; super, view, ident, onlyMixins, noHope});
		if(d) return d.independent;
		return parent.getUnresolvedImpl(view, ident, onlyMixins, noHope);
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
	override Scope getFrameScope(){ return parent.getFrameScope(); }

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

	override bool isNestedIn(Scope rhs){
		return this is rhs || !(aggr.stc&STCstatic) && parent.isNestedIn(rhs);
	}
	override AggregateDecl getAggregate(){ return aggr; }
	override AggregateDecl getDeclaration(){ return aggr; }

	override int getFrameNesting(){ return parent.getFrameNesting()+1; }
	override Scope getFrameScope(){ return this; }
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
	invariant(){ assert(!aggr||!!cast(ReferenceAggregateDecl)aggr); } // aggr is null during initialization
	@property ref ReferenceAggregateDecl raggr(){ return *cast(ReferenceAggregateDecl*)&aggr; }
	this(ReferenceAggregateDecl decl) in{assert(decl&&decl.scope_);}body{ super(decl); }

	// circular inheritance can lead to circular parent scopes
	// therefore we need to detect circular lookups in InheritScopes
	private bool onstack = false;

	protected override Dependent!Declaration lookupHereImpl(Scope view, Identifier ident, bool onlyMixins){
		if(onstack) return New!DoesNotExistDecl(ident).independent!Declaration;
		onstack = true; scope(exit) onstack = false;

		// dw("looking up ",ident," in ", this);
		if(raggr.shortcutScope){
			// we may want to take a shortcut in order to lookup symbols
			// outside the class declaration before the parent is resolved
			// if the declaration would actually be inherited from the parent
			// an error results.
			auto d = raggr.shortcutScope.lookupExactlyHere(view, ident);
			if(d && typeid(d) is typeid(DoesNotExistDecl))
				if(auto t=raggr.shortcutScope.lookupImpl(view, ident).prop) return t;
		}

		mixin(LookupHereImpl!q{auto d; super, view, ident, onlyMixins});

		// TODO: make more efficient than string comparison
		if(ident.name !="this" && ident.name!="~this" && ident.name!="invariant") // do not inherit constructors and destructors and invariants
		// if sstate is 'completed', DoesNotExistDecls do not need to be generated
		if(raggr.sstate == SemState.completed && !symtabLookup(view, ident) ||
		   d && typeid(d) is typeid(DoesNotExistDecl))
		mixin(AggregateParentsInOrderTraversal!(q{
			auto lkup = parent.asc.lookupHereImpl(view, ident, onlyMixins);
			if(lkup.dependee) return lkup.dependee.dependent!Declaration;
			d = lkup.value;
			if(parent.sstate != SemState.completed && !d ||
			   d && typeid(d) !is typeid(DoesNotExistDecl)) break;
		},"raggr","parent",true));
		return d.independent;
	}

	protected override Dependent!IncompleteScope getUnresolvedImpl(Scope view, Identifier ident, bool onlyMixins, bool noHope){
		mixin(GetUnresolvedImpl!q{auto d; Scope, view, ident, onlyMixins, noHope});
		if(d) return d.independent;
		Dependent!IncompleteScope traverse(){
			if(onstack) return null.independent!IncompleteScope;
			onstack = true; scope(exit) onstack = false;

			mixin(AggregateParentsInOrderTraversal!(q{
				if(auto lkup = parent.asc.getUnresolvedImpl(view, ident, onlyMixins, noHope).prop) return lkup;
			},"raggr","parent",true));
			return null.independent!IncompleteScope;
		}
		if(noHope){
			auto tr = traverse();
			if(!tr.dependee && tr.value) return tr;
			if(!raggr.shortcutScope) raggr.initShortcutScope(parent);
			return raggr.shortcutScope.getUnresolvedImpl(view, ident, onlyMixins, noHope);
		}
		// TODO: this is a hack
		if(auto tr = traverse().prop) return tr;
		return ident.recursiveLookup?parent.getUnresolvedImpl(view, ident, onlyMixins, noHope):null.independent!IncompleteScope;
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
	override Scope getFrameScope(){ return iparent.getFrameScope(); }
	override bool isNestedIn(Scope rhs){ return this is rhs || iparent.isNestedIn(rhs); }

	override FunctionDef getFunction(){return iparent.getFunction();}
	override AggregateDecl getAggregate(){return iparent.getAggregate();}
	override Declaration getDeclaration(){return iparent.getDeclaration();}
	override TemplateInstanceDecl getTemplateInstance(){ return tmpl; }
}

class OrderedScope: NestedScope{ // Forward references don't get resolved
	invariant(){ foreach(d; symtab) assert(d&&typeid(d) !is typeid(DoesNotExistDecl)); }

	this(Scope parent){super(parent);}

	// (there are no DoesNotExistDecls in ordered scopes,
	// so methods relying on them need to be overridden)
	protected override Dependent!Declaration lookupImpl(Scope view, Identifier ident){
		mixin(LookupHereImpl!q{auto decl;this, view, ident, false});
		if(!decl||typeid(decl) !is typeid(DoesNotExistDecl)) return decl.independent;
		return parent.lookupImpl(view, ident);
	}
	protected override Dependent!Declaration lookupHereImpl(Scope view, Identifier ident, bool onlyMixins){
		if(auto t=lookupExactlyHere(view, ident)) return t.independent;
		return lookupImports(view, ident, onlyMixins, inex);
	}
	override Declaration lookupExactlyHere(Scope view, Identifier ident){
		return symtabLookup(view, ident);
	}

	protected override bool inexistentImpl(Scope view, Identifier ident){
		return true;
	}
	protected override Dependent!IncompleteScope getUnresolvedImpl(Scope view, Identifier ident, bool onlyMixins, bool noHope){
		if(auto i=getUnresolvedImport(view, ident, onlyMixins, noHope).prop) return i;
		return parent.getUnresolvedImpl(view, ident, onlyMixins, noHope);
	}

	override protected void dontImport(Identifier ident){ }
}

final class FunctionScope: OrderedScope{
	this(Scope parent, FunctionDef fun){
		super(parent);
		this.fun=fun;
	}

	override bool isNestedIn(Scope rhs){
		return this is rhs || !(fun.stc&STCstatic) && parent.isNestedIn(rhs);
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
	final LabeledStm lookupLabelHere(Identifier l){
		return lstmsymtab.get(l.ptr,null);
	}
	override LabeledStm lookupLabel(Identifier l){
		if(auto s = lookupLabelHere(l)) return s;
		return alternateLabelLookup(l);
	}
	override int unresolvedLabels(scope int delegate(GotoStm) dg){
		foreach(x;_unresolvedLabels) if(auto r = dg(x)) return r;
		return 0;
	}
	override void registerForLabel(GotoStm stm, Identifier l){
		// rename to lbl to make DMDs hashtable fail
		if(auto lbll = lookupLabelHere(l)) stm.resolveLabel(lbll);
		else _unresolvedLabels~=stm;
	}

	override int getFrameNesting(){ return parent.getFrameNesting()+1; }
	override Scope getFrameScope(){ return this; }

	override FunctionDef getFunction(){return fun;}
	override FunctionDef getDeclaration(){return fun;}

	private LoopingStm thisLoopingStm(){
		if(auto oafun=fun.isOpApplyFunctionDef())
			return oafun.lstm;
		return null;
	}

	// functionality supporting opApply:
	override BreakableStm getBreakableStm(){
		if(auto r=thisLoopingStm()) return r;
		return super.getBreakableStm();
	}
	override LoopingStm getLoopingStm(){
		if(auto r=thisLoopingStm()) return r;
		return super.getLoopingStm();
	}
	override bool isEnclosing(BreakableStm stm){
		if(auto oafun=fun.isOpApplyFunctionDef()){
			return stm is oafun.lstm || parent.isEnclosing(stm);
		}
		return super.isEnclosing(stm);
	}
	private LabeledStm alternateLabelLookup(Identifier l){
		if(auto oafun=fun.isOpApplyFunctionDef()) return parent.lookupLabel(l);
		return null;
	}

protected:
	override bool canDeclareNested(Declaration decl){ // for BlockScope
		return typeid(decl) is typeid(DoesNotExistDecl) || !(decl.name.ptr in symtab);
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
		// TODO: get rid of !is DoesNotExistDecl?
		if(!parent.canDeclareNested(decl)){
			auto confl=parent.lookup(this, decl.name).value;
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
	void setSwitchStm(SwitchStm swstm)in{assert(!brokenOne&&!theSwitch);}body{
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
		if(!(typeid(decl) is typeid(DoesNotExistDecl) || !(decl.name.ptr in symtab)))
			return false;
		return parent.canDeclareNested(decl);
	}
private:
	BreakableStm brokenOne;
	LoopingStm theLoop;
	SwitchStm theSwitch;
}
