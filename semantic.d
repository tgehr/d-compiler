
import std.array, std.conv, std.algorithm, std.string;

import lexer, parser, expression, statement, declaration, scope_, util;

public import operators;

string uniqueIdent(string base){
	shared static id=0;
	return base~to!string(id++);
}
// helper macros

template PropErr(string s){ // propagate the 'error' semantic state TODO: maybe exceptions?
	enum PropErr={
		string r;
		auto ss=s.split(",");
		foreach(t;ss){
			r~="static if(is(typeof("~t~"): Node)){if("~t~".sstate==SemState.error){sstate=SemState.error;return this;};}\n";
			r~="else{foreach(x;"~t~") if(x.sstate==SemState.error){sstate=SemState.error;return this;};}\n";
		}
	return r;
	}();
}

template SemChld(string s){ // perform semantic analysis on child node, propagate all errors
	enum SemChld={
		string r;
		auto ss=s.split(",");
		foreach(t;ss){
			r~="static if(is(typeof("~t~"): Node)) "~t~"="~t~".semantic(sc);\n";
			r~="else foreach(ref x;"~t~"){x=x.semantic(sc);}\n";
		}
		return r~PropErr!s;
	}();
}


enum SemState{
	pre,
	begin,
	started,
	fwdRefs,
	completed,
	error,
}

enum SemPrlg=q{
	if(sstate >= SemState.completed) return this;
	//if(sstate>SemState.begin){sc.error("cyclic dependency",loc);sstate=SemState.error;return this;}
};
enum SemEplg=q{
	sstate = SemState.completed;
	return this;
};
enum ErrEplg=q{
	sstate=SemState.error;
	return this;
};
template Semantic(T) if(is(T==Node)){
	Node semantic(Scope s)in{assert(sstate>=SemState.begin);}body{ s.error("unimplemented feature",loc); sstate = SemState.error; return this;}
}

// error nodes (TODO: file bug against covariance error)

mixin template Semantic(T) if(is(T==ErrorDecl)||is(T==ErrorExp)||is(T==ErrorStm)||is(T==ErrorTy)){
	override T semantic(Scope sc){ return this; } // DMD compiler bug: T is required
}


// expressions
mixin template Semantic(T) if(is(T==Expression)){
	Type type;
	override Expression semantic(Scope sc){ sc.error("unimplemented feature",loc); sstate = SemState.error; return this; }

	Type typeSemantic(Scope sc){
		Expression me;
		if(sstate<SemState.started){ // TODO: is this ok?
			sstate = SemState.started;
			me = semantic(sc);
			if(me.sstate == SemState.error) return New!ErrorTy;
			if(auto ty=me.isType()) return ty;
		}else me=this;
		sc.error(format("%s '%s' is used as a type",me.kind,me.loc.rep),me.loc);
		return New!ErrorTy;
	}

	Expression isLvalue(){return null;}
	Expression implicitlyConvertTo(Type to){ // TODO: assert(to.sstate == SemState.completed);
		if(type is to) return this;
		return New!ImplicitCastExp(to,this);
	}
}

mixin template Semantic(T) if(is(T==LiteralExp)){
	override Expression semantic(Scope sc){
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
		mixin(SemEplg);
	}
}

template Semantic(T) if(is(T==ArrayLiteralExp)){
	override Expression semantic(Scope sc){
		if(!lit.length){type=Type.get!EmptyArray(); sstate=SemState.completed; return this;}
		mixin(SemChld!q{lit});
		auto ty=lit[0].type;
		foreach(x;lit[1..$]){
			// TODO: implicit casts
			if(auto newty=ty.combine(x.type)) ty=newty;
			else{sc.error(format("incompatible type '%s' in array of '%s'",x.type,ty),x.loc); sstate=SemState.error; return this;}
		}
		type=ty.getDynArr();
		mixin(SemEplg);
	}
}

template Semantic(T) if(is(T X==PostfixExp!S,TokenType S)){
	override Expression semantic(Scope sc){ // TODO: rewrite to (auto x=e, op e, e)
		mixin(SemPrlg);
		mixin(SemChld!q{e});
		if(auto bt=cast(BasicType)e.type){
			type=e.type;
			mixin(SemEplg);
		}
		sc.error(format("type '%s' does not support postfix "~TokChars!op,e.type),loc);
		mixin(ErrEplg);
	}
}

template Semantic(T) if(is(T==IndexExp)){
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e});
		if(auto ty=e.isType()){
			if(!a.length) return ty.getDynArr().semantic(sc);
			return super.semantic(sc); // TODO: implement
		}
		return super.semantic(sc); // TODO: implement
	}
}

template Semantic(T) if(is(T==CallExp)){
	override Expression semantic(Scope sc){ // TODO: type checking
		mixin(SemPrlg);
		mixin(SemChld!q{e,args});
		mixin(SemEplg);
	}
}

template Semantic(T) if(is(T==BinaryExp!(Tok!"."))){}

template Semantic(T) if(is(T X==BinaryExp!S,TokenType S) && !is(T==BinaryExp!(Tok!"."))){
	static if(is(T X==BinaryExp!S,TokenType S)):
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e1,e2});
		
		static if(isAssignOp(S)){
			if(auto lv=e1.isLvalue()){
				e2=e2.implicitlyConvertTo(e1.type).semantic(sc);
				if(e2.sstate == SemState.error) sstate=SemState.error;
				return this;
			}else{
				sstate=SemState.error;
				sc.error("expression is not assignable",loc);
				return this;
			}
		}else static if(isArithmeticOp(S) || isBitwiseOp(S)){
			auto bt1=cast(BasicType)e1.type, bt2=cast(BasicType)e2.type;
			if(bt1 && bt2){
				bt1=bt1.intPromote(); bt2=bt2.intPromote();
				if(auto ty=bt1.combine(bt2)){
					// TODO: implicit cast
					type = ty;
					mixin(SemEplg);
				}
			}
		}else static if(isRelationalOp(S)){
			auto bt1=cast(BasicType)e1.type, bt2=cast(BasicType)e2.type;
			if(bt1 && bt2){
				if(auto ty=bt1.combine(bt2)){
					// TODO: implicit cast
					type = Type.get!bool();
					if(ty.op!=Tok!"cfloat"&&ty.op!=Tok!"cdouble"&&ty.op!=Tok!"creal"){mixin(SemEplg);}
					else{sc.error("cannot compare complex operands",loc);mixin(ErrEplg);}
				}
			}
		}
		static if(S==Tok!","){
			type=e2.type;
			mixin(SemEplg);
		}else{
			sc.error(format("incompatible types for binary "~TokChars!S~": '%s' and '%s'",e1.type,e2.type),loc);
			mixin(ErrEplg);
		}
	}
}

template Semantic(T) if(is(T X==TernaryExp)){
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		e1=e1.semantic(sc);
		mixin(SemChld!q{e2,e3});
		auto ty1=cast(Type)e2.type, ty2=cast(Type)e3.type;
		assert(ty1 && ty2);
		auto ty=ty1.combine(ty2);
		if(!ty){
			sc.error(format("incompatible types for ternary operator: '%s' and '%s'",e2.type,e3.type),loc);
			mixin(ErrEplg);
		}
		mixin(PropErr!q{e1});
		type=ty;
		mixin(SemEplg);
	}
}
class Symbol: Expression{ // semantic node
	Declaration meaning;
	override Symbol semantic(Scope sc){
		mixin(SemPrlg);
		if(sstate<SemState.started){
			sstate = SemState.started;
			mixin(SemChld!q{meaning});
		}else{mixin(PropErr!q{meaning});}

		if(auto vd=meaning.isVarDecl()){
			type=vd.type.typeSemantic(sc);
			mixin(PropErr!q{type});
		}
		else type=Type.get!void(); // same as DMD

		sstate = SemState.completed;
		return this;
	}
	override string toString(){return meaning.name;}
	override @property string kind(){return meaning.kind;}

	// override Type isType(){...} // TODO.
}

mixin template Semantic(T) if(is(T==CastExp)){
	override Expression semantic(Scope sc){
		// TODO: sanity checks etc.
		mixin(SemPrlg);
		mixin(SemChld!q{e});
		if(!ty) {
			type=e.type; // TODO: STC casting
			return this;
		}
		type=ty.typeSemantic(sc);
		mixin(PropErr!q{type});
		mixin(SemEplg);
	}
}

class ImplicitCastExp: CastExp{ // semantic node
	this(Expression tt, Expression exp){super(STC.init, tt, exp);}
	override Expression semantic(Scope sc){
		mixin(SemPrlg);
		mixin(SemChld!q{e});
		ty=type=ty.semantic(sc).isType();
		assert(type && 1); // if not a type the program is in error
		if(type.sstate == SemState.error){sstate = SemState.error; return this;}
		if(e.type.implicitlyConvertsTo(type)) return this;
		if(e.type.isIntegral() && type.isIntegral()){ // value range propagation
			
		}
		sstate = SemState.error;
		sc.error(format("cannot implicitly convert expression '%s' of type '%s' to '%s'",e,e.type,type),e.loc); // TODO: replace toString with actual representation
		//error(format("no viable conversion from type '%s' to '%s'",e.type,type),e.loc);
		return this;
	}
	override string toString(){return e.toString();}
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
		e.meaning=dg; // TODO: dg.addressOf();
		e.loc=loc;
		return e.semantic(sc);
	}
}

// types
mixin template Semantic(T) if(is(T==Type)){
	override Type semantic(Scope sc){return this;}
	override Type typeSemantic(Scope sc){return semantic(sc);}
}

mixin template Semantic(T) if(is(T==BasicType)){
	override BasicType semantic(Scope sc){
		mixin({
			string r=`switch(op){`;
			foreach(x; basicTypes) r~=`case Tok!"`~x~`": return Type.get!`~x~`();`;
			return r~`default: assert(0);}`;
		}());
	}
}

mixin template Semantic(T) if(is(T==PointerTy)||is(T==DynArrTy)||is(T==ArrayTy)||is(T==ConstTy)||is(T==ImmutableTy)||is(T==SharedTy)||is(T==InoutTy)){
	override Type semantic(Scope sc){
		mixin(SemPrlg);
		Type ty;
		e=ty=e.typeSemantic(sc);
		mixin(PropErr!q{e});
		static if(is(T==PointerTy)) ty=ty.getPointer();
		else static if(is(T==DynArrTy)) ty=ty.getDynArr();
		else static if(is(T==ArrayTy)) ty=ty.getArray(size);
		else static if(is(T==ConstTy)) ty=ty.getConst();
		else static if(is(T==ImmutableTy)) ty=ty.getImmutable();
		else static if(is(T==SharedTy)) ty=ty.getShared();
		else static if(is(T==InoutTy)) ty=ty.getInout();
		else static assert(0);
		ty.sstate=SemState.completed;
		return ty;
	}
}

mixin template Semantic(T) if(is(T==TypeofExp)){
	override Type semantic(Scope sc){
		mixin(SemPrlg);
		if(sstate == SemState.started){
			sc.error("recursive typeof declaration",loc);
			mixin(ErrEplg);
		}
		sstate = SemState.started;
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
		mixin(SemPrlg);
		if(sstate==SemState.pre){
			auto ps=presemantic(sc);
			if(ps!is this) return ps.semantic(sc);
		}
		mixin(SemEplg);
	}

}
mixin template Semantic(T) if(is(T==VarDecl)){
	override VarDecl presemantic(Scope sc){return cast(VarDecl)cast(void*)super.presemantic(sc);}

	override VarDecl semantic(Scope sc){
		mixin(SemPrlg);
		if(init){init=init.semantic(sc);}
		if(type){
			Type ty;
			type=ty=type.typeSemantic(sc);
			if(init) init=init.implicitlyConvertTo(ty).semantic(sc);
		}else if(init && init.type){ // deduce type
			type=init.type; // TODO: take into account STCs
		}
		if(sstate == SemState.pre) sc.insert(this);
		if(!type||type.sstate==SemState.error) sstate=SemState.error; // deliberately don't propagate init's semantic 'error' state if possible
		else sstate=SemState.completed;
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
		sstate = SemState.begin; // do not insert
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
						if(bdy){mixin(SemChld!q{bdy});}
						return this;
					}
					if(bdy){mixin(SemChld!q{bdy});}
					return this;
				default: break;
			}
		}
		sc.error(format("unrecognized pragma '%s'",args[0].loc.rep),args[0].loc); // TODO: maybe remove this
		return New!Declaration(STC.init,cast(Identifier)null);
	}
}
