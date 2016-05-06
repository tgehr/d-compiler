// Written in the D programming language
// Author: Timon Gehr
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import expression, type, statement;

import util: ID;

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
			static if(!is(T==BreakStm) && !is(T==ContinueStm) && !is(T==GotoStm)){ // hack, annotations will solve this
				static assert(!is(typeof(_idfododi)));
				static assert(!is(typeof(_idfofodi2)));
				foreach(_idfododi; __traits(allMembers, T)){
					static if(_idfododi!="rewrite" && _idfododi.length && (!is(T:Symbol)||_idfododi!="meaning" && _idfododi!="circ" && _idfododi!="clist") && _idfododi!="ctfeCallWrapper" && (!is(T:FunctionLiteralExp)||_idfododi!="bdy") && (!is(T:TemplateInstanceExp)||_idfododi!="inst"&&_idfododi!="eponymous")&&(!is(T:TemplateDecl)||_idfododi!="eponymousDecl")&&(!is(T:VarDecl)||_idfododi!="type")&&(!is(T:TemplateInstanceDecl)||_idfododi!="parent"&&_idfododi!="constraintEponymousFunctionParameters"&&_idfododi!="instantiation")&&(!is(T:ReferenceAggregateDecl)||_idfododi!="parents")&&(!is(T:TemporaryExp)||_idfododi!="tmpVarDecl")&&(!is(T==CallExp)||_idfododi!="tmpVarDecl")&&(!is(T:StructConsExp)||_idfododi!="strd")&&_idfododi!="resolved"&&(!is(T==EnumVarDecl)||_idfododi!="enc"&&_idfododi!="prec")&&(!is(T==EnumTy)||_idfododi!="decl")&&(!is(T==OpApplyFunctionDef)||_idfododi!="lstm")&&(!is(T==GotoStm)||_idfododi!="theSwitch")){ // hack
						mixin(`alias `~_idfododi~` _idfofodi2;`);
						static if(is(typeof(_idfofodi2): Node) && !is(typeof(_idfofodi2): Type)){
							//import std.stdio; if(_idfofodi2) writeln(typeof(this).stringof," ",this,".",_idfododi," ",_idfofodi2);
							
							//if(_idfofodi2) writeln(T.stringof,_idfododi," ",(_idfofodi2));

							if(_idfofodi2) dg(_idfofodi2);
						}else static if(is(typeof(_idfofodi2[0]): Node) && !is(typeof(_idfofodi2[0]): Type) && _idfododi!="bcErrtbl" && !is(typeof(_idfofodi2): Type) && (!is(typeof(this)==TemplateInstanceExp)||_idfododi!="args"&&_idfododi!="analyzedArgs"&&_idfododi!="argTypes")){ // hack, annotations will solve this

								//import std.stdio; if(_idfofodi2.length) writeln(typeof(this).stringof," ",this,".",_idfododi," ",_idfofodi2);
								//if(_idfofodi2.length) writeln(_idfododi);
							 foreach(x; _idfofodi2) if(x) dg(x);
						}else static if(is(typeof(_idfofodi2)==TupleContext)){
							if(_idfofodi2){
								foreach(x; _idfofodi2.vds) if(x) dg(x);
								if(_idfofodi2.initLeftover) dg(_idfofodi2.initLeftover);
							}
						}
					}
				}
			}
		}
	}
}
import std.traits: ParameterTypeTuple;
import std.typetuple;
// TODO: combined analysis as one single call
auto runAnalysis(T,S...)(Node node,S args){
	static if(__traits(hasMember,T,"manualPropagate") && T.manualPropagate)
		enum manualPropagate = true;
	else enum manualPropagate = false;
	auto result = T(args);
	alias TypeTuple!(__traits(getOverloads,T,"perform")) overloads;
	//static assert(overloads.length<7,"TODO: fix.");
	void runIt(Node node){
		// import util;dw("h ",node);
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

