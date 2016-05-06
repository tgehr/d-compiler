// Written in the D programming language
// Author: Timon Gehr
// Licence: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

template IsNonASTType(T){
	enum IsNonASTType =
		is(T==Symbol)||
		is(T==TemplateInstanceDecl)||
		is(T==ExpTuple)||
		is(T==TypeTuple)||
		is(T==PtrExp)||
		is(T==LengthExp);
}


mixin template Visitors(){
	// workaround for DMD bug: Interpret goes first
	/*static if(is(typeof({mixin Semantic!(typeof(this));})))*/
	static if(is(typeof(this):Expression)&&!is(typeof(this):Type)) mixin Interpret!(typeof(this));// TODO: minimize and report bug
	static assert(is(TypeTuple==class));
	static if(!IsNonASTType!(typeof(this))) mixin Semantic!(typeof(this));
	// another workaround for DMD bug, other part is in expression.Node
	static if(!is(typeof(this)==Node)){
		static if(!is(typeof(this)==AggregateTy)){
			mixin Analyze; // wtf?
			mixin CTFEInterpret!(typeof(this));
		}
		static if(!is(typeof(this)==AggregateTy)) mixin DeepDup!(typeof(this));
	}

	//static if(is(typeof(this)==Node))
}

import expression,declaration,type;
mixin template DeepDup(T) if(is(T: BasicType)){
	override @trusted inout(T) sdup()inout{ return this; }
	override @trusted inout(T) ddup()inout{ return this; }
}

mixin template DeepDup(T) if(is(T: Node) && !is(T: BasicType)){
	mixin((!is(T==Node)?"override ":"")~q{
	@trusted inout(T) ddup()inout{
		static if(is(T:Type) && !is(T:FunctionTy)){
			if(sstate==SemState.completed) return this;
			assert(sstate == SemState.begin);
		}
		auto res=cast(T)sdup();
		static if(is(T==VarDecl)){
			if(init)
			if(auto tmp=(cast()init).isTemporaryExp()){
				assert(!tmp.tmpVarDecl||tmp.tmpVarDecl is this);
				auto otmp = tmp.tmpVarDecl;
				tmp.tmpVarDecl = null;
				auto n = tmp.ddup();
				n.tmpVarDecl = otmp;
				res.init = n;
			}
		}
		foreach(x;__traits(allMembers, T)){
			static if(x.length && (!is(T:Symbol)||x!="meaning" && x!="circ" && x!="clist") && x!="ctfeCallWrapper" && (!is(T==TemplateInstanceExp)||x!="eponymous"&&x!="inst")&&(!is(T==VarDecl)||x!="tupleContext") && (!is(T==TemplateInstanceDecl)||x!="eponymousDecl"&&x!="constraintEponymousFunctionParameters") && (!is(T:TemporaryExp)||x!="tmpVarDecl") && (!is(T:AliasDecl)||x!="set")){ // hack
				static if(is(typeof(*mixin("&res."~x)) S) &&
					     !is(S:immutable(S))){
					static if(is(S:const(Node))){
						static if(!is(T==FunctionTy)||!is(S==FunctionTy))
							mixin("if(res."~x~" !is null) res."~x~"=res."~x~".ddup();");
					}else static if(is(typeof(*mixin("&res."~x)):const(Node)[])){
						mixin("res."~x~"=res."~x~".dup;");
						static if((!is(T==ReferenceAggregateDecl)||x!="parents"))
						foreach(ref e;mixin("res."~x)) if(e!is null) e=e.ddup();
					}
				}
			}// else{ import std.stdio; writeln("not copying "~T.stringof,".",x);}
		}
		static if(is(T==FunctionTy)){
			res.clearCaches();// TODO: clearCaches is not good enough
		}
		return *cast(inout(T)*)&res;
	}}~(!is(T==Node)?
	q{override @trusted inout(T) sdup()inout{
		enum siz = __traits(classInstanceSize,T);
		auto data = New!(void[])(siz);
		import std.c.string;
		memcpy(data.ptr, cast(void*)this, siz);
		return cast(inout(T))data.ptr;
    }}:""));
}

mixin template DeepDup(T: StaticIfDecl) if(is(T==StaticIfDecl)){
	override @trusted inout(T) ddup()inout{
		assert(sstate==SemState.begin||sstate==SemState.pre);
		enum siz = __traits(classInstanceSize,T);
		auto data = New!(void[])(siz);
		import std.c.string;
		memcpy(data.ptr, cast(void*)this, siz);
		auto res = cast(T)data.ptr;
		res.lazyDup = true;
		res.cond = res.cond.ddup();
		return cast(inout)res;
	}
}

import semantic;
mixin template DeepDup(T: Symbol) {
	override @trusted inout(T) ddup()inout{
		enum siz = __traits(classInstanceSize,T);
		auto data = New!(void[])(siz);
		import std.c.string;
		memcpy(data.ptr, cast(void*)this, siz);
		auto res = cast(T)data.ptr;
		if(isFunctionLiteral) res.meaning = res.meaning.ddup;
		return cast(inout)res;
	}
}
