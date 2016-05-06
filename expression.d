// Written in the D programming language
// Author: Timon Gehr
// Licence: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.array, std.algorithm, std.range, std.conv, std.string;

import lexer, parser, declaration, statement, type;
import scope_, semantic, visitors, vrange, util;

import analyze;

import variant;
import rope_;

// Node champ;

abstract class Node{
	// debug auto cccc=0;
	Location loc;
	final @property sourcePriority(){ return q(loc.source.name,loc.line,loc.getColumn(1)); }

	abstract @property string kind();

	mixin DownCastMethods!(
		Declaration,
		//Statement,
		Expression,
	);

	mixin Visitors;
	// Workaround for DMD forward reference bug, other part is in visitors.Visitors
	mixin CTFEInterpret!Node; // TODO: minimize, report
	abstract void _doAnalyze(scope void delegate(Node) dg);
	inout(Node) sdup()inout{ assert(0); }
	inout(Node) ddup()inout{ assert(0); }
}

template Dependent(T){
	// convoluted nesting of declarations to make DMD happy
	struct DependentOrTrue{
		Dependent!T dep;
		alias dep this;
		bool opCast(T: bool)(){ return dep.dependee || dep.value; }
	}
	struct Dependent{
		private alias Dependent D;
		Dependee dependee;
		static if(!is(T==void)) T value;
		DependentOrTrue prop()(){ return DependentOrTrue(this); }

		static if(is(T==bool)){
		// for use in if(auto t = someExpression.prop) return t;
			D not(){ return D(dependee, !value); }
			D and(lazy D lb){
				D b; if(!dependee&&value) b = lb;
				return D(dependee?dependee:b.dependee, value && b.value);
			}
			D or(lazy D lb){
				D b; if(!dependee&&!value) b = lb;
				return D(dependee?dependee:b.dependee, value || b.value);
			}
		}
		bool isIndependent(){ return !dependee; }
		static if(!is(T==void))T force()in{assert(!dependee);}body{ return value; }
	}
}
//auto independent(T:void)() if(is(T==void)){ return Dependent!void(null); } // Y U NO WORK?
auto indepvoid(){ return Dependent!void(Dependee()); }
auto independent(T)(T value) if(!is(T==void)){ return Dependent!T(Dependee(), value); }
auto dependent(T)(Dependee dependee){ return Dependent!T(dependee); }

Dependent!(typeof(a(T.init))) depmap(alias a,T)(Dependent!T dep){
	return dep.isIndependent()?independent(a(dep.value)):dependent!(typeof(a(T.init)))(dep.dependee);
}

struct Dependee{
	Node node = null;
	Scope scope_ = null;
	bool opCast(T: bool)(){return !!node;}
}

class MultiDep: Node{
	Node[] deps;
	Scope sc;
	this(Node/+final+/[] dep, Scope sc = null)in{
		alias util.all all;
		assert(sc||all!(a=>a.isDeclaration().maybe!(a=>a.scope_))(dep));
	}body{
		deps = dep;
		Scheduler().add(this, null);
		if(sc) foreach(ref d; deps){
			mixin(Rewrite!q{d});
			Scheduler().await(this, d, sc);
		}else foreach(ref d; deps){
			mixin(Rewrite!q{d});
			assert(cast(Declaration)d);
			Scheduler().await(this, d, (cast(Declaration)cast(void*)d).scope_);
		}
		needRetry = true;
	}
	override void semantic(Scope sc){ mixin(SemEplg); }
	override void _doAnalyze(scope void delegate(Node) dg){ assert(0); }
	override inout(Node) ddup()inout{ assert(0); }
	override string kind(){ return "multi dependency";}

	override void noHope(Scope sc){
		if(sc)foreach(d;deps) d.noHope(sc);
	}

	override string toString(){
		return text(typeid(this),deps);
	}
}

// TODO: this allocation can probably be avoided in many cases
Dependee multidep(Node[] dep, Scope sc=null)in{assert(dep.length);}body{
	if(dep.length>1) return Dependee(new MultiDep(dep, sc));
	if(!dep[0].sstate==SemState.error) dep[0].needRetry = true; // TODO: ok?
	assert(sc||dep[0].isDeclaration());
	if(!sc) sc = dep[0].isDeclaration().scope_;
	assert(!!sc);
	return Dependee(dep[0],sc);
}



abstract class Expression: Node{
	int brackets=0;
	override string toString(){return _brk("{}()");}
	protected static string leftoverToString(Expression[] es, Expression leftover){
		if(!leftover) return "";
		return (es.length?",":"")~"("~leftover.toString~","~Tuple.toStringEmpty~")";
	}

	protected string _brk(string s){return std.array.replicate("(",brackets)~s~std.array.replicate(")",brackets); return s;}

	override @property string kind(){return isConstant?"constant":"expression";}

	mixin DownCastMethods!(
		Symbol,
		Identifier,
		LookupIdentifier,
		AssignExp,
		FieldExp,
		CommaExp,
		LengthExp,
		CurrentExp,
		ThisExp,
		SuperExp,
		TemplateInstanceExp,
		IndexExp,
		LiteralExp,
		ArrayLiteralExp,
		FunctionLiteralExp,
		VoidInitializerExp,
		StructConsExp,
		CallExp,
		UFCSCallExp,
		TemporaryExp,
		TmpVarExp,
		TernaryExp,
		CastExp,
		Type,
		.semantic.Tuple,
		ExpTuple,
		.semantic.TypeTuple,
		ImportBindingsExp,
	);

	mixin DownCastMethod;

	// UnaryExp!(Tok!"&") isAddressExp(){ return null; } // TODO: reduce bug

	mixin Visitors;
}

// workaround for the bug:
UnaryExp!(Tok!"&") isAddressExp(Expression self){return cast(UnaryExp!(Tok!"&"))self;}

class ErrorExp: Expression{
	this(){sstate = SemState.error;}
	override string toString(){return _brk("__error");}

	mixin Visitors;
}

class StubExp: Expression{
	private bool _isLvalue;
	this(Type type, bool isLvalue=false)in{assert(type && type.sstate==SemState.completed, to!string(type)~(type?" "~to!string(type.sstate):""));}body{
		sstate = SemState.completed;
		this.type = type;
		this._isLvalue = isLvalue;
	}
	override void semantic(Scope sc){mixin(SemPrlg);mixin(SemEplg);}
	override bool isLvalue(){ return _isLvalue; }
}

class LiteralExp: Expression{
	// constructor is in interpret.d, because it contains non-trivial logic
	private Token lit; // TODO: get rid of this field
	//this(Token lit){
	//	this.lit = lit;
	//	if(lit.type==Tok!"true") lit.int64=1;
	//	else if(lit.type==Tok!"false") lit.int64=0;
	//}
	//override string toString(){return _brk(lit.toString());}
	override string toString(){
		//if(loc.rep.length) return loc.rep;
		if(type) if(auto et=type.getHeadUnqual().isEnumTy()) return et.valueToString(value);
		return _brk(value.toString());
	}

	mixin DownCastMethod;

	mixin Visitors;
}

class ArrayAssocExp: Expression{
	Expression key;
	Expression value;
	this(Expression k, Expression v){key=k; value=v;}
	override string toString(){return key.toString()~":"~value.toString();}
}

class ArrayLiteralExp: Expression{
	Expression[] lit;
	this(Expression[] literal){lit=literal;}
	override string toString(){
		return _brk("["~join(map!(to!string)(lit),",")~leftoverToString(lit,litLeftover)~"]");
	}
	mixin DownCastMethod;
	mixin Visitors;
}

class FunctionLiteralExp: Expression{
	FunctionTy fty;
	CompoundStm bdy;
	enum Kind{
		none,
		function_,
		delegate_,
	}
	Kind which;
	this(FunctionTy ft, CompoundStm b, Kind w=Kind.none){ fty=ft; bdy=b; which=w;}
	override string toString(){return _brk((which==Kind.function_?"function"~(fty&&fty.rret?" ":""):which==Kind.delegate_?fty&&fty.rret?"delegate ":"":"")~(fty?fty.toString():"")~bdy.toString());}

	mixin DownCastMethod;
	mixin DownCastMethods!OpApplyFunctionLiteralExp;
	mixin Visitors;
}

class Identifier: Symbol{
	string name;
	// alias name this; // stupid compiler bug prevents this from being useful
	@property auto ptr(){return name.ptr;}
	@property auto length(){return name.length;}
	this(string name){ // TODO: make more efficient, this is a bottleneck!
		static string[string] uniq;
		auto n=uniq.get(name,null);
		if(n !is null) this.name = n;
		else this.name = uniq[name] = name;
	}
	override string toString(){return !meaning?_brk(name):super.toString();}
	override @property string kind(){return meaning?super.kind:"identifier";}

	mixin DownCastMethod;
	mixin Visitors;
}

class ModuleIdentifier: LookupIdentifier{
	this(string name){ super(name, null); }
	override string toString(){return !meaning?_brk("."~name):"."~super.toString();}

	mixin Visitors;
}

class ThisExp: CurrentExp{
	override string toString(){ return "this"; }

	mixin DownCastMethod;
	mixin Visitors;
}
class SuperExp: CurrentExp{
	override string toString(){ return "super"; }

	mixin DownCastMethod;
	mixin Visitors;
}
// special symbols that are used like identifiers in some contexts
class TildeThisExp: Identifier{
	this(){ super(q{~this}); }
}
class InvariantExp: Identifier{
	this(){ super(q{invariant}); }
}
class DollarExp: Identifier{
	this(){ super(q{$}); }

	override @property string kind(){return "array length";}

	mixin Visitors;
}

class CastExp: Expression{
	STC stc;
	Expression e; Expression ty;
	this(STC ss,Expression tt,Expression exp){stc=ss; ty=tt; e=exp;}
	override string toString(){return _brk("cast("~(stc?STCtoString(stc)~(ty?" ":""):"")~(ty?ty.toString():"")~")"~e.toString());}
	override string kind(){ return "cast expression"; }

	mixin DownCastMethod;
	mixin Visitors;
}
class NewExp: Expression{
	Expression[] a1;
	Expression rty;
	Expression[] a2;
	this(Expression[] args1,Expression type,Expression[] args2){a1=args1; rty=type; a2=args2;}
	override string toString(){
		return _brk("new"~(a1?"("~join(map!(to!string)(a1),",")~") ":" ")~rty.toString()~(a2||a2Leftover?"("~join(map!(to!string)(a2),",")~leftoverToString(a2,a2Leftover)~")":""));
	}

	override @property string kind(){ return "new expression"; }
	mixin Visitors;
}
class NewClassExp: Expression{
	Expression[] args;
	ClassDecl class_;
	this(Expression[] a, ClassDecl c)in{assert(c&&c.bdy);}body{args=a; class_=c;}
	override string toString(){
		return "new class("~join(map!(to!string)(args),",")~")"~(class_.parents?" "~join(map!(to!string)(class_.parents),","):"")~class_.bdy.toString();
	}
}
class InstanceNewExp: Expression{
	Expression inst;
	Expression nexp;
	this(Expression instance, Expression newexp)in{assert(instance&&newexp);}body{
		inst=instance, nexp=newexp;
	}
	override string toString(){return inst.toString()~'.'~nexp.toString();}
}

class MixinExp: Expression{
	Expression[] a;
	this(Expression[] arg){a=arg;}
	override string toString(){
		return _brk("mixin("~join(map!(to!string)(a),",")~leftoverToString(a,aLeftover)~")");
	}

	mixin Visitors;
}
class ImportExp: Expression{
	Expression[] a;
	this(Expression[] arg){a=arg;}
	override string toString(){return _brk("import("~join(map!(to!string)(a),",")~")");}
}
class AssertExp: Expression{
	Expression[] a;
	this(Expression[] args){a = args;}
	override string toString(){
		return _brk("assert("~join(map!(to!string)(a),",")~leftoverToString(a,aLeftover)~")");
	}

	mixin Visitors;
}

class UnaryExp(TokenType op): Expression{
	Expression e;
	this(Expression next){e = next;}
	override string toString(){
		//if(auto s=e.isSymbol())if(s.isFunctionLiteral) return s.meaning.loc.rep;
		if(auto s=e.isSymbol())if(s.isFunctionLiteral) return s.meaning.toString();
		return _brk(TokChars!op~e.toString());
	}
	static if(op==Tok!"&"){
		override @property string kind(){
			if(auto s=e.isSymbol())if(s.isFunctionLiteral) return "function literal";
			return "address";
		}
		//override UnaryExp!(Tok!"&") isAddressExp(){return this;}
	}
	mixin Visitors;
}
class PostfixExp(TokenType op): Expression{
	Expression e;
	this(Expression next){e = next;}
	override string toString(){return _brk(e.toString()~TokChars!op);}

	mixin Visitors;
}
class IndexExp: Expression, DollarProvider{ //e[a...]
	Expression e;
	Expression[] a;
	this(Expression exp, Expression[] args){e=exp; a=args;}
	override string toString(){
		return _brk(e.toString()~'['~join(map!(to!string)(a),",")~leftoverToString(a,aLeftover)~']');
	}

	mixin Visitors;
	mixin DownCastMethod;
	// workaround for DMD bug
	mixin CTFEInterpretIE!IndexExp;
}
class SliceExp: Expression, DollarProvider{//e[l..r]
	Expression e;
	Expression l,r;
	this(Expression exp, Expression left, Expression right){e=exp; l=left; r=right;}
	override string toString(){return _brk(e.toString()~'['~l.toString()~".."~r.toString()~']');}

	mixin Visitors;
}
class CallExp: TemporaryExp{
	Expression e;
	Expression[] args;
	this(Expression exp, Expression[] args){e=exp; this.args=args;}
	override string toString(){
		return _brk(e.toString()~'('~join(map!(to!string)(args),",")~leftoverToString(args,argsLeftover)~')');
	}

	mixin DownCastMethod;
	mixin Visitors;
}


import hashtable;
struct TemplArgInfo{
	AssocHash hash;
	bool typeOnly=true; // TODO: use bitfields
	bool isConstant=true;
	bool isConstFoldable=true;
	bool isLvalue=true;
	this(AssocHash hash, bool typeOnly, bool isConstant, bool isConstFoldable, bool isLvalue){
		this.hash=hash;this.typeOnly=typeOnly;
		this.isConstant=isConstant;this.isConstFoldable=isConstFoldable;
		this.isLvalue=isLvalue;
	}
	this(Expression e){
		this(!e?0.assocHash():e.tmplArgToHash().assocHash(),
		     !e||e.isType(),!e||e.isConstant(),!e||e.isConstFoldable(),!e||e.isLvalue());
	}
	TemplArgInfo combine(TemplArgInfo rhs){
		return TemplArgInfo(assocHashCombine(hash,rhs.hash),
		                    typeOnly&&rhs.typeOnly,
		                    isConstant&&rhs.isConstant,
		                    isConstFoldable&&rhs.isConstFoldable,
		                    isLvalue&&rhs.isLvalue);
	}
}

alias Rope!(Expression,TemplArgInfo) TemplArgs;
alias Rope!(Type,TemplArgInfo) TypeTemplArgs;

size_t tmplArgToHash(T)(Rope!(T,TemplArgInfo) arg){ return arg.value.hash.toHash(); }


class TemplateInstanceExp: Expression{
	Expression e;
	Expression[] args;
	this(Expression exp, Expression[] a){e=exp; args=a;}
	override string toString(){return _brk(e.toString()~"!"~(args.length!=1?"(":"")~join(map!(to!string)(args),",")~(args.length!=1?")":""));}

	mixin DownCastMethod;
	mixin Visitors;
}

// super class for all binary expressions
abstract class ABinaryExp: Expression{
	Expression e1, e2;

	mixin Visitors;
}

abstract class AssignExp: ABinaryExp{
	mixin DownCastMethod;
}

abstract class FieldExp: Expression{
	Expression e1;
	Symbol e2;

	override string toString(){
		if(auto id=e2.isIdentifier()) return _brk(e1.toString()~"."~id.name);
		else return _brk(e1.toString()~"."~e2.toString());
	}

	mixin DownCastMethod;
	mixin Visitors;
}
abstract class CommaExp: Expression{
	Expression e1,e2;
	mixin DownCastMethod;
}

template BinaryExpGetParent(TokenType op){
	static if(isAssignOp(op)) alias AssignExp result;
	else static if(op==Tok!".") alias FieldExp result;
	else static if(op==Tok!",") alias CommaExp result;
	else alias ABinaryExp result;
	alias result BinaryExpGetParent;
}

class BinaryExp(TokenType op): BinaryExpGetParent!op{
	this(Expression left, typeof(e2) right){e1=left; e2=right;}


	static if(op!=Tok!".") override string toString(){
		// (the cast is a workaround for a DMD bug)
		static if(op==Tok!"in"||op==Tok!"is"||op==Tok!"!in"||op==Tok!"!is") return _brk(e1.toString() ~ " "~TokChars!op~" "~e2.toString());
		else{
			static if(op==Tok!",")
				if(auto sym=e2.isSymbol())if(sym.meaning&&!sym.meaning.name)
					return _brk(e1.toString());
			return _brk(e1.toString() ~ TokChars!op ~ (cast(Expression)e2).toString());
		}
	}
	//override string toString(){return e1.toString() ~ " "~ e2.toString~TokChars!op;} // RPN

	mixin Visitors;
}

class TernaryExp: TemporaryExp{ // TODO: is this parent too wasteful with memory?
	Expression e1, e2, e3;
	this(Expression cond, Expression left, Expression right){e1=cond; e2=left; e3=right;}
	override string toString(){return _brk(e1.toString() ~ '?' ~ e2.toString() ~ ':' ~ e3.toString());}

	mixin DownCastMethod;
	mixin Visitors;
}

enum WhichIsExp{
	type,
	implicitlyConverts,
	isEqual
}
class IsExp: Expression{
	WhichIsExp which;
	Expression ty;
	Identifier ident;
	Expression tySpec;
	TokenType tySpec2;
	TemplateParameter[] tparams;
	this(WhichIsExp w, Expression t, Identifier i, Expression ts, TokenType ts2, TemplateParameter[] tp)
		in{assert(t&&(which==WhichIsExp.type||tySpec||tySpec2!=Tok!"")); assert(which!=WhichIsExp.type||!tparams);}body{
		which=w; ty=t; ident=i; tySpec=ts;
		tySpec2=ts2; tparams=tp;
	}
	override string toString(){
		return "is("~ty.toString()~(ident?" "~ident.toString():"")~(which!=WhichIsExp.type?(which==WhichIsExp.isEqual?"==":": ")~
			(tySpec?tySpec.toString():TokenTypeToString(tySpec2))~(tparams?","~join(map!(to!string)(tparams),","):""):"")~")";
	}

	mixin Visitors;
}

class TypeidExp: Expression{
	Expression e;
	invariant(){assert(e !is null,text(loc));}
	this(Expression exp)in{assert(!!exp);}body{e=exp;}
	override string toString(){return "typeid("~e.toString()~")";}

	mixin Visitors;
}

class TraitsExp: Expression{
	Expression[] args;
	this(Expression[] a){args=a;}
	override string toString(){return "__traits("~join(map!(to!string)(args),",")~")";}
}
class DeleteExp: Expression{ // why is this an expression and throw a statement? wtf...
	Expression e;
	this(Expression exp)in{assert(exp&&1);}body{e=exp;}
	override string toString(){return "delete "~e.toString();}
}

abstract class InitializerExp: Expression{}
class VoidInitializerExp: InitializerExp{
	override string toString(){return "void";}

	mixin DownCastMethod;
	mixin Visitors;
}

class StructAssocExp: Expression{
	Identifier key;
	Expression value;
	this(Identifier k, Expression v){key=k; value=v;}
	override string toString(){return key.toString()~":"~value.toString();}
}
class ArrayInitAssocExp: Expression{
	Expression key;
	Expression value;
	this(Expression k, Expression v){key=k; value=v;}
	override string toString(){return key.toString()~":"~value.toString();}

	mixin Visitors;
}
class StructLiteralExp: InitializerExp{
	Expression[] args;
	this(Expression[] a){args=a;}
	override string toString(){return "{"~join(map!(to!string)(args),",")~"}";}
}

// for if(auto x=foo()){} etc
class ConditionDeclExp: Expression{
	STC stc;
	Expression ty;
	Identifier name;
	Expression init;
	this(STC s, Expression t, Identifier n, Expression i){stc=s; ty=t; name=n; init=i;}
	override string toString(){return (stc?STCtoString(stc)~" ":"")~(ty?ty.toString()~" ":"")~name.toString()~(init?"="~init.toString():"");}

	mixin Visitors;
}
