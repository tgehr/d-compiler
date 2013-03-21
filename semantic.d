
import std.array, std.conv, std.algorithm;

import lexer,parser,expression, statement, declaration, scope_, util;

string uniqueIdent(string base){
	shared static id=0;
	return base~to!string(id++);
}


enum SemState{
	pre,
	begin,
	fwdRefs,
	completed,
	error,
}

enum SemPrlg=q{
	if(sstate >= SemState.completed) return this;	
};

template Semantic(T) if(is(T==Node)){
	Node semantic(Scope s)in{assert(sstate>=SemState.begin);}body{ s.error("unimplemented feature",loc); sstate = SemState.error; return this;}
}

// expressions
mixin template Semantic(T) if(is(T==Expression)){
	Type type;
	Expression semantic(Scope sc){ sc.error("unimplemented feature",loc); sstate = SemState.error; return this; }
}

mixin template Semantic(T) if(is(T==LiteralExp)){
	Expression semantic(Scope sc){
		switch(lit.type){ // TODO: remove some boilerplate
			case Tok!"``": //TODO: this needs to have a polysemous type
				type=Type.get!(immutable(char)[])(); break;
			case Tok!"``c":
				type=Type.get!(immutable(char)[])(); break;
			case Tok!"``w":
				type=Type.get!(immutable(wchar)[])(); break;
			case Tok!"``d":
				type=Type.get!(immutable(dchar)[])(); break;
			case Tok!"''":
				if(lit.int64<128) type=Type.get!char();
				else type=Type.get!dchar(); break;
			case Tok!"0":
				type=Type.get!int(); break;
			case Tok!"0U":
				type=Type.get!uint(); break;
			case Tok!"0L":
				type=Type.get!long(); break;
			case Tok!"0LU":
				type=Type.get!ulong(); break;
			case Tok!".0f":
				type=Type.get!float(); break;
			case Tok!".0":
				type=Type.get!double(); break;
			case Tok!".0L":
				type=Type.get!real(); break;
			case Tok!".0fi":
				type=Type.get!ifloat(); break;
			case Tok!".0i":
				type=Type.get!idouble(); break;
			case Tok!".0Li":
				type=Type.get!ireal(); break;
			case Tok!"null":
				type=Type.get!Null(); break;
			case Tok!"true", Tok!"false":
				type=Type.get!bool(); break;
			default: return super.semantic(sc); // TODO: verify
		}
		sstate = SemState.completed;
		return this;
	}
}

template Semantic(T) if(is(T==IndexExp)){
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		e=e.semantic(sc);
		sstate = e.sstate;
		if(auto ty=e.isType()){
			if(!a.length) return ty.getSlice().semantic(sc);
			return super.semantic(sc); // TODO: implement
		}
		return super.semantic(sc); // TODO: implement
	}
}

template Semantic(T) if(is(T==CallExp)){
	override Expression semantic(Scope sc){ // TODO: type checking
		mixin(SemPrlg);
		e.semantic(sc); // semantically analyze the left part
		auto newstate = e.sstate;
		foreach(ref x;args){
			x = x.semantic(sc);
			newstate = min(newstate, x.sstate);
		}
		sstate = newstate;
		return this;
	}
}

bool isArithmeticOp(TokenType op){
	switch(op){
		// bitwise shift operators
		case Tok!">>": return true;
		case Tok!"<<": return true;
		case Tok!">>>":return true;
			// additive operators
		case Tok!"+",Tok!"-",Tok!"~":
			return true;
			// multiplicative operators
		case Tok!"*",Tok!"/",Tok!"%":
			return true;
		default:
			return false;
	}
}

bool isAssignOp(TokenType op){
	switch(op){
		// assignment operators
		case Tok!"/=",Tok!"&=",Tok!"|=",Tok!"-=":
		case Tok!"+=",Tok!"<<=",Tok!">>=", Tok!">>>=":
		case Tok!"=",Tok!"*=",Tok!"%=",Tok!"^=":
		case Tok!"^^=",Tok!"~=":
			return true;
		default:
			return false;
	}
}

template Semantic(T) if(is(T X==BinaryExp!S,TokenType S)){
	static if(is(T X==BinaryExp!S,TokenType S)):
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		e1=e1.semantic(sc);
		e2=e2.semantic(sc);
		if(e1.sstate == SemState.error || e2.sstate == SemState.error){sstate=SemState.error; return this;}
		auto bt1=cast(BasicType)e1.type, bt2=cast(BasicType)e2.type;
		static if(isArithmeticOp(S)){
			bt1=bt1.intPromote(); bt2=bt2.intPromote();
			// TODO: implicit cast
			if(bt1 && bt2){
				if(auto ty=bt1.combine(bt2)){
					type = ty;
					sstate = min(e1.sstate, e2.sstate);
					return this;
				}
			}
		}
		sc.error(format("incompatible types for binary "~TokChars!S~": '%s' and '%s'",e1.type,e2.type),loc);
		sstate=SemState.error;
		return this;
	}
}


class Symbol: Expression{ // semantic node
	Declaration meaning;
	override Symbol semantic(Scope sc){
		mixin(SemPrlg);
		if(meaning.isErrorDecl()){sstate = SemState.error; return New!ErrorExp;} // TODO: no need for New
		if(!type && meaning.sstate == SemState.completed){
			if(auto vd=meaning.isVarDecl()){type=vd.type.isType(); assert(type&&1);}
			else type=Type.get!void();
		}

		sstate = meaning.sstate; // TODO: type?
		return this;
	}
	override string toString(){return meaning.name;}
	// override Type isType(){...} // TODO.
}

mixin template Semantic(T) if(is(T==Identifier)){
	override Symbol semantic(Scope sc){
		meaning=sc.lookup(this);
		return super.semantic(sc);
	}
}

mixin template Semantic(T) if(is(T==FunctionLiteralExp)){
	override Symbol semantic(Scope sc){
		assert(sstate != SemState.completed);
		if(!type) type=New!FunctionType(STCauto,cast(Expression)null,cast(Parameter[])null,VarArgs.none);
		auto dg=New!FunctionDef(type,New!Identifier(uniqueIdent("__dgliteral")),cast(BlockStm)null,cast(BlockStm)null,cast(Identifier)null,bdy);
		dg.sstate = SemState.begin;
		dg=dg.semantic(sc);
		auto e=New!Symbol;
		e.meaning=dg;
		e.loc=loc;
		return e.semantic(sc);
	}
}

// types
mixin template Semantic(T) if(is(T==Type)){
	override Type semantic(Scope sc){return this;}
}

mixin template Semantic(T) if(is(T==BasicType)){
	override BasicType semantic(Scope sc){
		mixin({
			string r=`switch(type){`;
			foreach(x; basicTypes) r~=`case Tok!"`~x~`": return Type.get!`~x~`();`;
			return r~`default: assert(0);}`;
		}());
	}
}

mixin template Semantic(T) if(is(T==PointerTy)||is(T==SliceTy)||is(T==ArrayTy)||is(T==ConstTy)||is(T==ImmutableTy)||is(T==SharedTy)||is(T==InoutTy)){
	override Type semantic(Scope sc){
		mixin(SemPrlg);
		e=e.semantic(sc);
		if(auto ty=e.isType()){
			static if(is(T==PointerTy)) ty=ty.getPointer();
			else static if(is(T==SliceTy)) ty=ty.getSlice();
			else static if(is(T==ArrayTy)) ty=ty.getArray(size);
			else static if(is(T==ConstTy)) ty=ty.getConst();
			else static if(is(T==ImmutableTy)) ty=ty.getImmutable();
			else static if(is(T==SharedTy)) ty=ty.getShared();
			else static if(is(T==InoutTy)) ty=ty.getInout();
			else static assert(0);
			ty.sstate=SemState.completed;
			return ty;
		}else{
			if(!e.isErrorExp()) sc.error(format("expression '%s' is used as a type",e.loc.rep),e.loc);
			sstate = SemState.error;
			return this; // TOOD: return error type
		}
	}
}

mixin template Semantic(T) if(is(T==TypeofExp)){
	override Type semantic(Scope sc){
		e.semantic(sc);
		sstate = e.sstate;
		if(sstate == SemState.completed){
			if(!e.type) return Type.get!void(); // TODO: make this unecessary
			return e.type.semantic(sc);
		}
		return this;
	}
}

// statements

mixin template Semantic(T) if(is(T==BlockStm)){
	BlockStm semanticNoScope(Scope sc){
		mixin(SemPrlg);
		auto newstate = SemState.max;
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
		mixin(SemPrlg);
		if(!lsc) lsc = New!BlockScope(sc);
		s1=s1.semantic(lsc); e1=e1.semantic(lsc);
		e2=e2.semantic(lsc); s2=s2.semantic(lsc);
		sstate=min(min(s1.sstate,e1.sstate),min(e2.sstate,s2.sstate));
		return this;
	}
private:
	BlockScope lsc;
}

mixin template Semantic(T) if(is(T==ReturnStm)){
	override ReturnStm semantic(Scope sc){
		mixin(SemPrlg);
		e=e.semantic(sc);
		sstate = e.sstate;
		// TODO: match with function return type
		return this;
	}
}

// declarations
mixin template Semantic(T) if(is(T==Declaration)){
	Declaration presemantic(Scope sc){ // insert into symbol table, but don't do the heavy processing yet
		if(sstate != SemState.pre) return this;
		sstate = SemState.begin;
		if(!name){sc.error("unimplemented feature",loc); sstate = SemState.error; return this;} // TODO: obvious
		sc.insert(this);
		return this;
	}
	override Declaration semantic(Scope sc){
		if(sstate==SemState.pre){
			auto ps=presemantic(sc);
			if(ps!is this) return ps.semantic(sc);
		}
		sstate = SemState.completed;
		return this;
	}

}
mixin template Semantic(T) if(is(T==VarDecl)){
	override VarDecl presemantic(Scope sc){return cast(VarDecl)cast(void*)super.presemantic(sc);}

	override VarDecl semantic(Scope sc){
		mixin(SemPrlg);
		if(init) init=init.semantic(sc);
		if(type) type=type.semantic(sc);
		else{
			// assert(init && init.type); // TODO: fix this
			assert(init && 1); // ditto
			if(!init.type) init.type=Type.get!void();// ditto
			type=init.type.semantic(sc); // TODO: take into account STCs
		}
		super.semantic(sc);
		if(type) sstate=min(type.sstate, sstate);
		if(init) sstate=min(init.sstate, sstate);
		return this;
	}
}


mixin template Semantic(T) if(is(T==Declarators)){
	override Declaration presemantic(Scope sc){
		if(sstate>SemState.pre) return this;
		foreach(ref x; decls) x=x.presemantic(sc);
		sstate=SemState.begin;
		return this;
	}
	override Declaration semantic(Scope sc){
		if(sstate==SemState.pre) return presemantic(sc).semantic(sc);
		mixin(SemPrlg);
		super.semantic(sc);
		auto newstate=SemState.max;
		foreach(ref x; decls){
			x=x.semantic(sc);
			newstate = min(newstate, x.sstate);
		}
		sstate = newstate;
		return this;
	}
}

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

mixin template Semantic(T) if(is(T==FunctionDef)){
	FunctionScope fsc;
	override FunctionDef semantic(Scope sc){
		mixin(SemPrlg);
		super.semantic(sc);
		if(!fsc) fsc = New!FunctionScope(sc);
		if(sstate == SemState.pre) presemantic(sc); // add self to parent scope
		foreach(p; type.params) p.presemantic(fsc); // add parameters to function scope
		foreach(p; type.params){
			p.semantic(fsc);
			sstate = min(sstate, p.sstate);
		}
		bdy.semanticNoScope(fsc);
		sstate = min(sstate, bdy.sstate);
		return this;
	}
}

mixin template Semantic(T) if(is(T==PragmaDecl)){
	override Declaration semantic(Scope sc){
		mixin(SemPrlg);
		sstate = SemState.max;
		if(args.length<1){sc.error("missing arguments to pragma",loc); sstate=SemState.error; return this;}
		if(auto id=args[0].isIdentifier()){
			switch(id.name){
				case "msg":
					if(args.length<2){sstate=SemState.completed; return this;}
					foreach(ref x; args[1..$]){
						x = x.semantic(sc);
						sstate = min(sstate, x.sstate);
					}
					if(sstate == SemState.completed){
						// TODO: interpret!
						import std.stdio;
						foreach(x; args[1..$]){
							if(x.type !is Type.get!string()) stderr.write(x);
							else stderr.write(x);
						}
						stderr.writeln();
						return this;
					}
					return this;
				default: break;
			}
		}
		sc.error(format("unrecognized pragma '%s'",args[0].loc.rep),args[0].loc); // TODO: maybe remove this
		return New!Declaration(STC.init,cast(Identifier)null);
	}
}
