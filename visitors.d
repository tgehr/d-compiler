
import declaration, type, semantic, interpret;

mixin template Visitors(){
	// workaround for DMD bug: Interpret goes first
	static if(is(typeof(this):Expression)) mixin Interpret!(typeof(this));
	/*static if(is(typeof({mixin Semantic!(typeof(this));})))*/ mixin Semantic!(typeof(this));
}
