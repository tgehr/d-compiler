// Written in the D programming language.

mixin template Visitors(){
	// workaround for DMD bug: Interpret goes first
	/*static if(is(typeof({mixin Semantic!(typeof(this));})))*/
	static if(is(typeof(this):Expression)&&!is(typeof(this):Type)) mixin Interpret!(typeof(this));// TODO: minimize and report bug
	static if(!is(typeof(this)==Symbol)&&!is(typeof(this)==TemplateInstanceDecl)) mixin Semantic!(typeof(this));
	// another workaround for DMD bug, other part is in expression.Node
	static if(!is(typeof(this)==Node)){
		static if(!is(typeof(this)==AggregateTy)) mixin Analyze; // wtf?
		mixin CTFEInterpret!(typeof(this));
		mixin DeepDup!(typeof(this));
	}

	//static if(is(typeof(this)==Node))
}

import expression,type;
mixin template DeepDup(T) if(is(T: BasicType)){
	@trusted inout(T) ddup()inout{ return this; }
}

mixin template DeepDup(T) if(is(T: Node) && !is(T: BasicType)){
	@trusted inout(T) ddup()inout in{assert(sstate==SemState.begin||sstate==SemState.pre);}body{
		enum siz = __traits(classInstanceSize,T);
		auto data = New!(void[])(siz);
		import std.c.string;
		memcpy(data.ptr, cast(void*)this, siz);
		auto res=cast(Unqual!(typeof(return)))data.ptr;
		foreach(x;__traits(allMembers, T)){
			static if(is(typeof(*mixin("&res."~x)) S) &&
			         !is(S:immutable(S))){
				static if(is(S:const(Node))){
					mixin("if(res."~x~" !is null) res."~x~"=res."~x~".ddup();");
				}else static if(is(typeof(*mixin("&res."~x)):const(Node)[])){
					mixin("res."~x~"=res."~x~".dup;");
					foreach(ref e;mixin("res."~x)) if(e!is null) e=e.ddup();
				}
			}
		}
		return *cast(inout(T)*)&res;
	}
}

