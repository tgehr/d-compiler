// fixed bugs exposed during self-compilation

struct NonTerminatingLookup{
	class TemplateInstanceDecl{
		TemplateDecl parent;
		mixin Visitors;
	}
	template Visitors(){ static if(is(inexistent)) mixin("int b=2;"); }

	class TemplateDecl{}
}


struct StaticIfDependenceError{
	mixin template Visitors(){
		static if(true) mixin Interpret!(typeof(this));
	}
	
	mixin template Interpret(T){}
	
	class ExpTuple{
		void foo(){
			enum x = lookupSomething;
		}
		mixin Visitors;
	}
	
	enum lookupSomething = 2;
}


// +/
// +/
// +/
// +/