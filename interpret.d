import lexer, expression, semantic, scope_, type;
import std.string;


private template NotYetImplemented(T){
	static if(is(T _==BinaryExp!S,TokenType S) && !is(T==BinaryExp!(Tok!".")))
		enum NotYetImplemented = false;
	else enum NotYetImplemented = !is(T==Expression) && !is(T:Type) && !is(T:Symbol) && !is(T:LiteralExp);
}

mixin template Interpret(T) if(is(T:Expression) && NotYetImplemented!T){
	Expression interpret(Scope sc){
		sc.error(format("expression '%s' is not interpretable at compile time yet",loc.rep),loc);
		sstate = SemState.error;
		return this;
	}
}

mixin template Interpret(T) if(is(T==Expression)){
	Expression interpret(Scope sc)in{assert(sstate == SemState.completed);}body{
		sc.error(format("expression '%s' is not interpretable at compile time",loc.rep),loc);
		sstate = SemState.error;
		return this;
	}
}

mixin template Interpret(T) if(is(T==Type)){
	override Expression interpret(Scope sc){return this;}
}mixin template Interpret(T) if(!is(T==Type) && is(T:Type)){}

mixin template Interpret(T) if(is(T==Symbol)){
	override Expression interpret(Scope sc){
		if(auto vd = meaning.isVarDecl()){
			/+ 
			 if(vd.stc&STCenum){
			 auto res = vd.init.dup;
			 res.loc = loc;
			 return res;
			 }+/
		}
		return super.interpret(sc);
	}
}mixin template Interpret(T) if(!is(T==Symbol) && is(T:Symbol)){}
mixin template Interpret(T) if(is(T==LiteralExp)){
	override LiteralExp interpret(Scope sc){
		return this;
	}
}

mixin template Interpret(T) if(is(T _==BinaryExp!S, TokenType S) && !is(T==BinaryExp!(Tok!"."))){
	
}