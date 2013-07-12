// Written in the D programming language.

import std.stdio, std.algorithm, std.array;

import std.conv : to;
import core.memory;
import std.c.stdlib;

import std.path;

import module_, scheduler;

int Ḁ(){return 0;}
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
		string err;
		auto m=r.getModule(x,err);
		if(!m){
			if(err) stderr.writeln("error: ",err);
			errors=true;
		}
		Scheduler().add(m, null);
		ms~=m;
	}
	if(errors) return 1;
	Scheduler().run();
	return r.hasErrors();
}
