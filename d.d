import std.stdio, std.algorithm, std.array;

import std.conv : to;
import core.memory;
import std.c.stdlib;

import std.path;

import module_, semantic;

import file = std.file;

int Ḁ(){return 0;}
int main(string[] args){
	/+import variant,type;

	Variant var = 0L;//"I am a string!";
	//writeln(var.convertTo(Type.get!ifloat()));
	writeln(var<<Variant(1L));
	auto s = cast(ireal)(100000+2i);
	writeln(s);+/

	//import parser, error;writeln(parse(q{void main(){b.tail!int();}}~"\0\0\0\0", null));
	//import lexer;
	//writeln(lex(readln()~"\0\0\0\0"));
	if(args.length<2){
		stderr.writeln("error: no input files");
		return 1;
	}
	args.popFront();

	/+import lexer;
	string f = cast(string)file.read(args[0])~"\0\0\0\0";
	int sum=0;
	foreach(x;lex(f)){
		sum++;
	}
	writeln(sum);return 0;+/
	
	foreach(ref x; args){
		auto ext = extension(x);
		if(ext=="") x = x.setExtension("d");
	}

	bool found = true;
	foreach(x; args){
		// TODO: find the full paths by searching all import directories
		if(!file.exists(x)){
			stderr.writeln("no such file: ", x);
			found = false;
		}
	}
	if(!found) return 1;
	SemState sstate=SemState.completed;
	foreach(x; args){
		// TODO: add to module repository
		auto m=new Module(x);
		m.semantic();
		if(m.sstate == SemState.error) sstate = SemState.error;
	}
	import semantic;
	return sstate == SemState.error;
	//writeln(join(map!(to!string)(parse(code,handler)),"\n"));
	//foreach(i,r;res) handler.error("declaration "~(r.name?r.name.toString():"moo"),r.loc); //*/
	/*import type, scope_, error, lexer;
	auto sc = new Scope(new FormattingErrorHandler("",""));
	Type x = new BasicType(Tok!"int");
	x.semantic(sc);
	x=x.getArray(100);
	x=x.semantic(sc);
	x=x.getShared();
	x=x.getConst();
	x=x.getHeadUnqual();
	x=x.getConst();
	x=x.getShared();
	x=x.getHeadUnqual();
	x=x.getInout();
	writeln(x);*/

	//auto a=lexed.pushAnchor();
	//writeln(lexed);
	//lexed.popAnchor(a);
	/*GC.disable();
	foreach(i;0..2){
		auto a=lexed.pushAnchor();
		while(!lexed.empty) writeln(lexed.front), lexed.popFront();
		lexed.popAnchor(a);
		}*/
	//for(;;) writeln(parse(lex(readln())));
	/*string r="1";
	writeln(parse(lex(q{
		//++a!(b.x)+a+b*x^^y^^z++, 1,2,3
		/+1==2?2==3?1:0?1==2:2==0:1+/
		a=&a?a:a?a:a;
	})));
	GC.disable();
	writeln(parse(lex(import("ttt.d"))));
	GC.enable(); GC.collect();
	//writeln(lex(import("lexer.d")));
	//writeln(lex("0x.ffffffffffffffffp1027L")[0].flt80==0x.ffffffffffffffffp1027L);
	//writeln(0x.fffffffffffffffffp1027L);
	//writeln(lex("12340000000000000000.L"));
	//writefln("%.3f",lex("184467440737095516153.6L")[0].flt80);
	//writefln("%.3f",184467440737095516153.6L);
	//writefln("%.3f",to!real("184467440737095516153.6"));
	//writefln("%.1f", lex("184467440737095516153.6L")[0].flt80);
	//writefln("%.1f", to!real("184467440737095516153.6"));
	//writeln(lex("100000000000000000000000000000000000000000000000f"));
	/*writefln("%.3f",lex("7.8459735791271921e65L")[0].flt80);
	writefln("%.3f",to!real("7.8459735791271921e65"));
	writefln("%.3f",7.8459735791271921e65L);*/
}

/+
extern(C) void sigsegvhandler(int sig) {
	assert(0,"Segmentation fault");
}static this(){import core.stdc.signal;signal(SIGSEGV, &sigsegvhandler);}
+/