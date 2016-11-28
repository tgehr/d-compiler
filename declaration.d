// Written in the D programming language
// Author: Timon Gehr
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import module_;

import std.array, std.algorithm, std.range, std.conv, std.string;

import lexer, parser, expression, statement, type, scope_, semantic, visitors, util;

import analyze;

import variant;
import rope_;
import interpret, error; // byteCompile

abstract class Declaration: Statement{
	STC stc;
	immutable STC astStc; // storage classes as they occur in the code
	Identifier name;
	this(STC stc,Identifier name){
		this.stc=stc;
		astStc = stc;
		this.name=name;
		sstate = SemState.pre;
	}

	override @property string kind(){return "declaration";}
	override Declaration isDeclaration(){return this;}

	mixin DownCastMethods!(
		VarDecl,
		FunctionDecl,
		FunctionDef,
		TemplateDecl,
		TemplateInstanceDecl,
		TemplateMixinDecl,
		NamespaceDecl,
		OverloadableDecl,
		OverloadSet,
		CrossScopeOverloadSet,
		SymbolMatcher,
		GenerativeDecl,
		MixinDecl,
		AliasDecl,
		AggregateDecl,
		ClassDecl,
		InterfaceDecl,
		StructDecl,
		UnionDecl,
		ValueAggregateDecl,
		ReferenceAggregateDecl,
		TmpVarDecl,
		ImportDecl,
		EnumDecl,
		ErrorDecl,
	);

	mixin Visitors;
}

class EmptyDecl: Declaration{
	this(){super(STC.init,null);}
	override string toString(){return ";";}

	mixin Visitors;
}

class ErrorDecl: Declaration{
	this(){super(STC.init, null); sstate=SemState.error;}
	override ErrorDecl isErrorDecl(){return this;}
	override string toString(){return "__error ;";}
	static opCall(){
		static ErrorDecl err;
		return err?err:(err=New!ErrorDecl);
	}
	mixin Visitors;
}

class ModuleDecl: Declaration{
	Expression symbol;
	this(STC stc, Expression sym){symbol=sym; super(stc, null);}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"module "~symbol.toString()~";";}
}

final class ImportBindingsExp: Expression{
	Expression symbol;
	Expression[] bindings;
	this(Expression sym, Expression[] bind){symbol=sym; bindings=bind;}
	override string toString(){return symbol.toString()~": "~join(map!(to!string)(bindings),", ");}
	
	mixin DownCastMethod;
}
class ImportDecl: Declaration{
	Expression[] symbols;
	this(STC stc, Expression[] sym){symbols=sym; super(stc,null);}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"import "~join(map!(to!string)(symbols),", ")~";";}

	mixin DownCastMethod;
	mixin Visitors;
}

class EnumVarDecl: VarDecl{
	this(Expression rtype, Identifier name, Expression initializer){
		super(STCenum, rtype, name, initializer);
	}

	mixin Visitors;
}

class EnumDecl: Declaration{
	Expression rbase;
	EnumVarDecl[] members;
	this(STC stc,Identifier name, Expression rbase, EnumVarDecl[] mem){this.rbase=rbase; members=mem; super(stc,name);}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"enum"~(name?" "~name.toString():"")~(rbase?":"~rbase.toString():"")~
			"{"~join(map!(a=>a.name.toString()~(a.init_?"="~a.init_.toString():""))(members),",")~"}";}

	mixin DownCastMethod;
	mixin Visitors;
}

abstract class GenerativeDecl: Declaration{
	this(STC stc, Identifier name){super(stc, name);}
	
	mixin DownCastMethod;
	mixin Visitors;
}

abstract class ConditionalDecl: GenerativeDecl{
	Statement bdy;
	Statement els;
	this(STC stc,Statement b,Statement e)in{assert(b&&1);}body{bdy=b; els=e; super(stc,null);}

	mixin Visitors;
}
class VersionSpecDecl: Declaration{
	Expression spec;
	this(STC stc,Expression s)in{assert(s!is null);}body{spec=s; super(stc,null);}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"version="~spec.toString()~";";}
}
class VersionDecl: ConditionalDecl{
	Expression cond;
	this(STC stc,Expression c,Statement b, Statement e)in{assert(c!is null);}body{cond=c; super(stc,b,e);}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"version("~cond.toString()~") "~bdy.toString()~
			(els?(cast(CompoundStm)bdy||cast(BlockDecl)bdy?"":"\n")~"else "~els.toString():"");}
}
class DebugSpecDecl: Declaration{
	Expression spec;
	this(STC stc,Expression s)in{assert(s!is null);}body{spec=s; super(stc,null);}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"debug="~spec.toString()~";";}
}
class DebugDecl: ConditionalDecl{
	Expression cond;
	this(STC stc,Expression c,Statement b, Statement e){cond=c; super(stc,b,e);}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"debug"~(cond?"("~cond.toString()~") ":"")~bdy.toString()~
			(els?(cast(CompoundStm)bdy||cast(BlockDecl)bdy?"":"\n")~"else "~els.toString():"");}
}
class StaticIfDecl: ConditionalDecl{
	Expression cond;
	this(STC stc,Expression c,Statement b,Statement e)in{assert(c&&b);}body{cond=c; super(stc,b,e);}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"static if("~cond.toString()~") "~bdy.toString()~
			(els?(cast(CompoundStm)bdy||cast(BlockDecl)bdy?"":"\n")~"else "~els.toString():"");}

	mixin Visitors;
}
class StaticAssertDecl: Declaration{
	Expression[] a;
	this(STC stc,Expression[] args){a = args; super(stc,null);}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"static assert("~join(map!(to!string)(a),",")~");";}

	mixin Visitors;
}

class MixinDecl: GenerativeDecl{
	Expression[] a;
	this(STC stc, Expression[] arg){a=arg; super(stc,null);}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"mixin("~join(map!(to!string)(a),",")~");";}

	override @property string kind(){return "string mixin declaration";}

	mixin DownCastMethod;
	mixin Visitors;
}
final class AliasDecl: Declaration{
	Declaration decl;
	this(STC stc, Declaration declaration){decl=declaration; super(stc, declaration.name);}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"alias "~decl.toString();}
	override @property string kind(){return "alias declaration";}

	mixin DownCastMethod;
	mixin Visitors;
}
class TypedefDecl: Declaration{
	Declaration decl;
	this(STC stc, Declaration declaration){decl=declaration; super(stc, declaration.name);}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"typedef "~decl.toString();}
}
class BlockDecl: Declaration{
	Declaration[] decls;
	this(STC stc,Declaration[] declarations){decls=declarations; super(stc,null);}
	override string toString(){return STCtoString(astStc)~"{\n"~(stc?join(map!(to!string)(decls),"\n")~"\n}":indent(join(map!(to!string)(decls),"\n"))~"\n}");}

	mixin Visitors;
}
class AttributeDecl: BlockDecl{
	this(STC stc,Declaration[] declarations){super(stc,declarations);}
	override string toString(){return STCtoString(astStc)~":\n"~join(map!(to!string)(decls),"\n");}
}

enum WhichTemplateParameter{
	type,
	alias_,
	constant,
	this_,
	tuple,
}

final class TemplateParameter: Node{
	Identifier name;
	Expression rtype, rspec, init_;
	Type type, spec;
	Expression espec;

	WhichTemplateParameter which;
	this(WhichTemplateParameter which, Expression tt, Identifier name, Expression specialization, Expression deflt){
		this.which = which; this.name = name;
		rtype=tt; rspec=specialization; init_=deflt;
	}
	override string toString(){
		bool isAlias = which == WhichTemplateParameter.alias_;
		bool isTuple = which == WhichTemplateParameter.tuple;
		return (isAlias?"alias ":"")~(rtype?rtype.toString()~" ":"")~(name?name.toString():"")~
			(isTuple?"...":"")~(rspec?":"~rspec.toString():"")~(init_?"="~init_.toString():"");
	}
	override string kind(){return "template parameter";}

	mixin Visitors;
}

class TemplateDecl: OverloadableDecl{
	bool isMixin;
	TemplateParameter[] params;
	Expression constraint;
	BlockDecl bdy;
	this(bool m,STC stc,Identifier name, TemplateParameter[] prm, Expression c, BlockDecl b){
		isMixin=m; params=prm; constraint=c; bdy=b; super(stc,name);
	}
	override string toString(){
		return (stc?STCtoString(astStc)~" ":"")~"template "~name.toString()~"("~join(map!(to!string)(params),",")~")"~
			(constraint?" if("~constraint.toString()~")":"")~bdy.toString();
	}
	override string kind(){
		if(eponymousDecl){
			if(iftiDecl()) return "function template";
			if(eponymousDecl.isClassDecl()) return "class template";
			if(eponymousDecl.isStructDecl()) return "struct template";
			if(eponymousDecl.isInterfaceDecl()) return "interface template";
			if(eponymousDecl.isUnionDecl()) return "union template";
		}
		return "template";
	}

	mixin DownCastMethod;
	mixin Visitors;
}

class TemplateMixinDecl: Declaration{
	Expression inst;
	this(STC stc, Expression i, Identifier name)in{assert(i&&1);}body{inst=i; super(stc,name);}
	override string toString(){return "mixin "~inst.toString()~(name?" "~name.toString():"")~";";}

	mixin DownCastMethod;
	mixin Visitors;
}

abstract class AggregateDecl: Declaration, NotifyOnLayoutChanged{
	BlockDecl bdy;
	this(STC stc, Identifier name, BlockDecl b){bdy=b; super(stc,name);}

	override @property string kind(){return "aggregate";}

	mixin DownCastMethod;
	mixin Visitors;
}

abstract class ValueAggregateDecl: AggregateDecl{
	this(STC stc, Identifier name, BlockDecl b){super(stc,name,b);}
	mixin DownCastMethod;
}

abstract class ReferenceAggregateDecl: AggregateDecl{
	Expression[] parents;

	this(STC stc, Identifier name, Expression[] p, BlockDecl b){
		parents=p; super(stc,name,b);
	}

	mixin DownCastMethod;
	mixin Visitors;
}

class StructDecl: ValueAggregateDecl{
	this(STC stc,Identifier name, BlockDecl b){super(stc,name,b);}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"struct"~(name?" "~name.toString():"")~(bdy?bdy.toString():";");}

	override @property string kind(){ return "struct"; }
	mixin DownCastMethod;
	mixin Visitors;
}
class UnionDecl: ValueAggregateDecl{
	this(STC stc,Identifier name, BlockDecl b){super(stc,name,b);}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"union"~(name?" "~name.toString():"")~(bdy?bdy.toString():";");}

	override @property string kind(){ return "union"; }
	mixin DownCastMethod;
	mixin Visitors;
}
class ClassDecl: ReferenceAggregateDecl{
	this(STC stc,Identifier name, Expression[] p, BlockDecl b){
		super(stc,name,p,b);
	}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"class"~(name?" "~name.toString():"")~
			(parents.length?": "~join(map!(to!string)(parents),","):"")~(bdy?bdy.toString():"");}

	override @property string kind(){ return "class"; }

	mixin DownCastMethod;
	mixin Visitors;
}
class InterfaceDecl: ReferenceAggregateDecl{
	this(STC stc,Identifier name, Expression[] p, BlockDecl b){
		super(stc,name,p,b);
	}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"interface"~(name?" "~name.toString():"")~
			(parents?": "~join(map!(to!string)(parents),","):"")~(bdy?bdy.toString():";");}

	override @property string kind(){ return "interface"; }

	mixin DownCastMethod;
	mixin Visitors;
}
/+class TemplateAggregateDecl: Declaration{
	TemplateParameter[] params;
	Expression constraint;
	AggregateDecl decl;
	this(STC stc,TemplateParameter[] p, Expression c, AggregateDecl ad){ params=p; constraint=c; decl=ad; super(stc,decl.name); }
	override string toString(){
		auto s=cast(StructDecl)decl, u=cast(UnionDecl)decl, c=cast(ClassDecl)decl, i=cast(InterfaceDecl)decl;
		string r=(stc?STCtoString(astStc)~" ":"");
		r~=(s?"struct":u?"union":c?"class":"interface")~(decl.name?" "~name.toString():"")~"("~join(map!(to!string)(params),",")~")";
		if(c && c.parents) r~=": "~join(map!(to!string)(c.parents),",");
		if(i && i.parents) r~=": "~join(map!(to!string)(i.parents),",");
		auto bdy=s?s.bdy:u?u.bdy:c?c.bdy:i.bdy;
		return r~(constraint?" if("~constraint.toString()~")":"")~(bdy?bdy.toString():";");
	}
}

class TemplateFunctionDecl: OverloadableDecl{
	TemplateParameter[] params;
	Expression constraint;
	FunctionDecl fdecl;
	this(STC stc, TemplateParameter[] tp, Expression c, FunctionDecl fd){params=tp; constraint=c;fdecl=fd; super(stc, fdecl.name);}
	override string toString(){
		auto fd=cast(FunctionDef)fdecl;
		return (fdecl.type.stc?STCtoString(fdecl.type.stc)~" ":"")~(fdecl.type.rret?fdecl.type.rret.toString()~" ":"")~name.toString()~
			"("~join(map!(to!string)(params),",")~")"~fdecl.type.pListToString()~(constraint?" if("~constraint.toString()~")":"")
			~(fdecl.pre?"in"~fdecl.pre.toString():"")~(fdecl.post?"out"~(fdecl.postres?"("~fdecl.postres.toString()~")":"")~fdecl.post.toString():"")~
			(fd?(fd.pre||fd.post?"body":"")~fd.bdy.toString():!fdecl.pre&&!fdecl.post?";":"");
	}

}+/


class VarDecl: Declaration{
	Expression rtype;
	Expression init_;
	this(STC stc, Expression rtype, Identifier name, Expression initializer){
		this.stc=stc; this.rtype=rtype; init_=initializer; super(stc,name);
	}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~(rtype?rtype.toString()~" ":type?type.toString()~" ":"")~(name?name.toString():"")~(init_?"="~init_.toString():"")~";";}

	override VarDecl isVarDecl(){return this;}

	mixin DownCastMethods!CArrayDecl;
	mixin Visitors;
}

class CArrayDecl: VarDecl{
	Expression postfix; // reverse order until semantic
	this(STC stc, Expression rtype, Identifier name, Expression pfix, Expression initializer)in{assert(rtype&&name&&pfix);}body{
		postfix=pfix; super(stc, rtype, name, initializer);
	}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~rtype.toString()~" "~postfix.toString()~(init_?"="~init_.toString():"")~";";}

	mixin DownCastMethod;
	mixin Visitors;
}

class Declarators: Declaration{
	Declaration[] decls;
	this(Declaration[] declarations){//in{assert(declarations.length>1);foreach(x;declarations) assert(x.type is declarations[0].type);}body{
		decls=declarations;super(STC.init,null);
	}
	override string toString(){
		return decls.map!(a=>a.toString()).join;
		/+string r=(decls[0].stc?STCtoString(decls[0].stc)~" ":"")~(decls[0].type?decls[0].type.toString()~" ":"");
		//return r~join(map!((a){return a.name.toString();})(decls),","); // WTF???
		foreach(x;decls[0..$-1]) r~=x.name.toString()~(x.init_?"="~x.init_.toString():"")~",";
		return r~decls[$-1].name.toString()~(decls[$-1].init_?"="~decls[$-1].init_.toString():"")~";";+/
	}
	mixin Visitors;
}

class Parameter: VarDecl{ // for functions, foreach etc
	this(STC stc, Expression rtype, Identifier name, Expression initializer){super(stc,rtype,name,initializer);}
	override string toString(){return (rtype?STCtoString(astStc)~(astStc?" ":"")~rtype.toString():type?STCtoString(stc)~(stc?" ":"")~type.toString()~" ":"")~
			(name?(stc||rtype?" ":"")~name.toString():"")~(init_?"="~init_.toString():"");}
	override @property string kind(){return "parameter";}

	mixin Visitors;
}

class ForeachVarDecl: Parameter{ // foreach variable
	this(STC stc, Expression rtype, Identifier name, Expression init_){super(stc,rtype,name,init_);}
	mixin Visitors;
}

class CArrayParam: Parameter{
	Expression postfix; // reverse order until semantic
	this(STC stc, Expression rtype, Identifier name, Expression pfix, Expression initializer)in{assert(rtype&&name&&pfix);}body{
		postfix=pfix; super(stc, rtype, name, initializer);
	}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~rtype.toString()~" "~postfix.toString()~(init_?"="~init_.toString():"");}

	mixin Visitors;
}



class PostblitParameter: Parameter{
	this(){super(STC.init,null,null,null);}
	override string toString(){return "this";}
}

class FunctionDecl: OverloadableDecl{
	FunctionTy type;
	CompoundStm pre,post;
	Identifier postres;
	this(STC stc, FunctionTy type,Identifier name,CompoundStm pr,CompoundStm po,Identifier pres)in{assert(type&&1);}body{
		stc &= ~STCauto; // auto does not matter
		this.type=type; pre=pr, post=po; postres=pres; super(stc, name);
	}
	final string signatureString(){
		return (astStc&~type.stc?STCtoString(astStc&~type.stc)~" ":"")~(type.rret?type.rret.toString()~" ":!astStc?"auto ":"")~name.toString()~type.pListToString()~
			(pre?"in"~pre.toString():"")~(post?"out"~(postres?"("~postres.toString()~")":"")~post.toString():"")~(!pre&&!post?";":"");		
	}
	override string toString(){
		return signatureString();
	}
	override @property string kind(){
		return
			isConstructor()?"constructor":
			stc&STCproperty?"property":
			isMember()?"member function":"function";
	}
	override FunctionDecl isFunctionDecl(){return this;}

	mixin Visitors;
}

class FunctionDef: FunctionDecl, NotifyOnLayoutChanged{
	CompoundStm bdy;
	this(STC stc, FunctionTy type,Identifier name, CompoundStm precondition,CompoundStm postcondition,Identifier pres,CompoundStm fbody){
		super(stc, type, name, precondition, postcondition, pres); bdy=fbody;
		possibleSTCs=STCstatic|STCinferrable;
	}
	override string toString(){
		return (astStc&~type.stc?STCtoString(astStc&~type.stc)~" ":"")~(type.rret?type.rret.toString()~" ":"")~name.toString()~type.pListToString()~
			(pre?"in"~pre.toString():"")~(post?"out"~(postres?"("~postres.toString()~")":"")~post.toString():"")~(pre||post?"body":"")~bdy.toString();
	}

	mixin DownCastMethod;
	mixin DownCastMethods!OpApplyFunctionDef;
	mixin Visitors;
}

class UnittestDecl: FunctionDef{
	this(STC stc,CompoundStm b)in{assert(b!is null);}body{
		super(stc|STCstatic,New!FunctionTy(STC.init, Type.get!void(),(Parameter[]).init, VarArgs.none), null, null, null,null,b);
	}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"unittest"~bdy.toString();}

	mixin Visitors;
}

class PragmaDecl: Declaration{
	Expression[] args;
	Statement bdy;
	this(STC stc,Expression[] a, Statement b)in{assert(b&&1);}body{args=a; bdy=b; super(stc,null);}
	override string toString(){return (stc?STCtoString(astStc)~" ":"")~"pragma("~join(map!(to!string)(args),",")~")"~bdy.toString();}

	mixin Visitors;
}

enum LinkageType{
	D,
	C,
	CPP,
	Pascal,
	System,
	Windows,
}

class ExternDecl: Declaration{
	LinkageType linktype;
	Declaration decl;
	this(STC stc,LinkageType l,Declaration d)in{assert(d&&1);}body{
		linktype=l; decl=d;
		super(stc,d.name);
	}
	override string toString(){
		return (stc?STCtoString(astStc)~" ":"")~"extern("~(linktype==LinkageType.CPP?"C++":to!string(linktype))~") "~decl.toString();
	}
}
class AlignDecl: Declaration{
	ulong alignment;
	Declaration decl;
	this(STC stc,ulong a,Declaration d)in{assert(d&&1);}body{
		alignment=a; decl=d;
		super(stc,d.name);
	}
	override string toString(){
		return (stc?STCtoString(astStc)~" ":"")~"align("~to!string(alignment)~") "~decl.toString();
	}
}
