
import declaration, type, semantic;

mixin template Visitors(){
	/*static if(is(typeof({mixin Semantic!(typeof(this));})))*/ mixin Semantic!(typeof(this));
}
