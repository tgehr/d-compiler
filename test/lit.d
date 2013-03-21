void main(){
	/+ TODO: static assertions+/
	pragma(msg, typeof(""));
	pragma(msg, typeof(""c));
	pragma(msg, typeof(""w));
	pragma(msg, typeof(""d));
	pragma(msg, typeof(' '));
	pragma(msg, typeof('\u1000'));
	pragma(msg, typeof(0));
	pragma(msg, typeof(0U));
	pragma(msg, typeof(0L));
	pragma(msg, typeof(0LU));
	pragma(msg, typeof(.0f));
	pragma(msg, typeof(.0));
	pragma(msg, typeof(.0L));
	pragma(msg, typeof(.0fi));
	pragma(msg, typeof(.0i));
	pragma(msg, typeof(.0Li));
	pragma(msg, typeof(null));
	pragma(msg, typeof([]));
	pragma(msg, typeof([1]));
	pragma(msg, typeof([1.0]));
	pragma(msg, typeof({return 0;}));
	pragma(msg, typeof(()=>0));
}