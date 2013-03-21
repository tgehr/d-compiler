
import std.array, std.conv, std.algorithm;

import parser,expression, statement, declaration, scope_;


// expressions

class Symbol: Expression{ // semantic node
	Declaration meaning;
	override Symbol semantic(Scope sc){
		sstate = meaning.sstate;
		return this;
	}
}


// statements

mixin template Semantic(T) if(is(T==BlockStm)){
	BlockStm semanticNoScope(Scope sc){
		if(sstate == SemState.completed) return this;
		auto newstate = SemState.completed;
		foreach(ref x;s){
			x=x.semantic(sc);
			newstate = min(newstate, x.sstate);
		}
		sstate = newstate;
		return this;
	}
	
	override BlockStm semantic(Scope sc){
		if(!mysc) mysc = New!BlockScope(sc);
		return semanticNoScope(mysc);
	}
private:
	FunctionScope mysc = null;	
}

mixin template Semantic(T) if(is(T==ForStm)){
	override ForStm semantic(Scope sc){
		if(sstate == SemState.completed) return this;
		if(!lsc) lsc = New!BlockScope(sc);
		s1=s1.semantic(lsc); e1=e1.semantic(lsc);
		e2=e2.semantic(lsc); s2=s2.semantic(lsc);
		sstate=min(min(s1.sstate,e1.sstate),min(e2.sstate,s2.sstate));
		return this;
	}
private:
	BlockScope lsc;
}


// declarations

abstract class OverloadableDecl: Declaration{ // semantic node
	this(STC stc,Identifier name){super(stc,name);}
	override OverloadableDecl isOverloadableDecl(){return this;}
}

class OverloadSet: Declaration{ // purely semantic node
	this(OverloadableDecl[] args...)in{assert(args.length);}body{
		super(STC.init,args[0].name);
		foreach(d;args) add(d);
	}
	this(Identifier name){super(STC.init,name);}
	void add(OverloadableDecl decl){decls~=decl;}
	override string toString(){return join(map!(to!string)(decls),"\n");}
	override OverloadSet isOverloadSet(){return this;}
private:
	OverloadableDecl[] decls; // TODO: use more efficient data structure
}

