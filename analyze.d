
import expression, type, statement;

import util: ID;

/+
template isASTNode(T,string member){
	enum isASTNode=x.length &&
		(!is(T:Symbol)||x!="meaning" && x!="circ")               &&
		(!is(T==FunctionDef)||x!="ctfeCallWrapper")              &&
		(!is(T==FunctionLiteralExp)||x!="bdy")                   &&
		(!is(T==TemplateInstanceExp)||x!="eponymous"&&x!="decl") &&
		true;
}
+/

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
				static assert(!is(typeof(_idfofodi2)));
				foreach(_idfododi; __traits(allMembers, T)){
					static if(_idfododi.length && (!is(T:Symbol)||_idfododi!="meaning" && _idfododi!="circ" && _idfododi!="clist") && _idfododi!="ctfeCallWrapper" && (!is(T==FunctionLiteralExp)||_idfododi!="bdy") && (!is(T==TemplateInstanceExp)||_idfododi!="inst"&&_idfododi!="eponymous")&&(!is(T==TemplateDecl)||_idfododi!="eponymousDecl")&&(!is(T==VarDecl)||_idfododi!="tupleContext")&&(!is(T==TemplateInstanceDecl)||_idfododi!="parent"&&_idfododi!="constraintEponymousFunctionParameters")&&(!is(T==ReferenceAggregateDecl)||_idfododi!="parents")&&_idfododi!="resolved"){ // hack
						mixin(`alias `~_idfododi~` _idfofodi2;`);
						static if(is(typeof(_idfofodi2): Node) && !is(typeof(_idfofodi2): Type)){
							//import std.stdio; if(_idfofodi2) writeln(typeof(this).stringof," ",this,".",_idfododi," ",_idfofodi2);

							//if(_idfofodi2) writeln(T.stringof,_idfododi," ",(_idfofodi2));

							if(_idfofodi2) dg(_idfofodi2);
						}else static if(is(typeof(_idfofodi2[0]): Node) && !is(typeof(_idfofodi2[0]): Type) && _idfododi!="bcErrtbl"){ // hack, annotations will solve this

								//import std.stdio; if(_idfofodi2.length) writeln(typeof(this).stringof," ",this,".",_idfododi," ",_idfofodi2);
								//if(_idfofodi2.length) writeln(_idfododi);
							 foreach(x; _idfofodi2) if(x) dg(x);
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

