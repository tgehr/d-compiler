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