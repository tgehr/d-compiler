
import expression, type, statement;

import util: ID;

abstract class NodeVisitor{
	
}

mixin template Analyze(){
	alias typeof(this) T;
	static if(is(T==Node)){
		// see expression.d: Node
	}else{
		override void _doAnalyze(scope void delegate(Node) dg){
			// hack: fields of type 'Type' are excluded because
			// they may contain circular references due to caching
			// better solution: use annotations to explicitly annotate
			// what is part of the AST
			if(!is(T==BreakStm) && !is(T==ContinueStm) && !is(T==GotoStm)){ // hack, annotations will solve this
				static assert(!is(typeof(_idfododi)));
				static assert(!is(typeof(_idfododi2)));
				foreach(_idfododi; __traits(allMembers, T)){
					static if(_idfododi.length && _idfododi!="meaning"){ // hack
						mixin(`alias `~_idfododi~` _idfofodi2;`);
						static if(is(typeof(_idfofodi2): Node) && !is(typeof(_idfofodi2): Type)){
						if(_idfofodi2) dg(_idfofodi2);
						}else static if(is(typeof(_idfofodi2[0]): Node) && !is(typeof(_idfofodi2[0]): Type) && _idfododi!="bcErrtbl") // hack, annotations will solve this
							foreach(x; _idfofodi2) dg(x);
					}
				}
			}
		}
	}
}
import std.traits: ParameterTypeTuple;
import std.typetuple;
// TODO: combined analysis as one single call
auto runAnalysis(T)(Node node){
	static if(__traits(hasMember,T,"manualPropagate") && T.manualPropagate)
		enum manualPropagate = true;
	else enum manualPropagate = false;
	T result;
	alias TypeTuple!(__traits(getOverloads,T,"perform")) overloads;
	//static assert(overloads.length<7,"TODO: fix.");
	void runIt(Node node){
		static if(!manualPropagate) node._doAnalyze(&runIt);
		foreach(i, ov; overloads){
			if(auto e = cast(ParameterTypeTuple!(ov)[0])node){
				result.perform(e);
				return;
			}
		}
	}
	runIt(node);
	static if(!manualPropagate) return result;
}

