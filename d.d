// Written in the D programming language
// Author: Timon Gehr
// Licence: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.stdio, std.algorithm, std.array;

import std.conv : to;
import core.memory;
import std.c.stdlib;

import std.path;

import module_, scheduler;

bool isOption(string x){
	return x.startsWith("--")||x.startsWith("-I");
}

string applyOption(ModuleRepository r,string x)in{assert(isOption(x));}body{
	if(x.startsWith("-I")){
		r.addPath(x[2..$]);
		return null;
	}
	x=x[2..$];
	switch(x){ // TODO: report DMD bug/update compiler
		case "unittest":
			import declaration;
			UnittestDecl.enabled = true;
			break;
		default:
			return "unrecognized option '"~x~"'";
	}
	return null;
}

int main(string[] args){
	import core.memory; GC.disable();

	if(args.length<2){
		stderr.writeln("error: no input files");
		return 1;
	}
	args.popFront();

	bool errors = false;
	auto r = new ModuleRepository();
	Module[] ms;
	foreach(x; args){
		if(!isOption(x)) continue;
		if(auto err=applyOption(r,x)){
			stderr.writeln("error: ",err);
			errors=true;
		}
	}
	foreach(x; args){
		string err;
		if(isOption(x)) continue;
		auto m=r.getModule(x,false,err);
		if(m){
			Scheduler().add(m, null);
			ms~=m;
		}else{
			if(err) stderr.writeln("error: ",err);
			errors=true;
		}
	}
	if(errors) return 1;
	Scheduler().run();
	return r.hasErrors();
}
