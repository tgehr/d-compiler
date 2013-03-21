// Written in the D programming language.

mixin template Visitors(){
	// workaround for DMD bug: Interpret goes first
	static if(is(typeof(this):Expression)) mixin Interpret!(typeof(this));// TODO: minimize and report bug
	/*static if(is(typeof({mixin Semantic!(typeof(this));})))*/ mixin Semantic!(typeof(this));
	// another workaround for DMD bug, other part is in expression.Node
	static if(!is(typeof(this)==Node)) mixin CTFEInterpret!(typeof(this));
}
