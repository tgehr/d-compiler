import std.stdio, std.file;
import std.process, std.string, std.array;
import std.algorithm, std.conv;

void main(){
	auto sources=shell("ls test/*.d").splitLines;
	Summary total;
	foreach(source;sources){
		writeln("running "~source);
		auto expected=source.getExpected;
		auto actual=source.getActual;
		auto comparison = compare(expected, actual);
		auto summary = comparison.summarize;
		total+=summary;
		if(summary.isInteresting) writeln(summary);
	}
	writeln("TOTAL:");
	writeln(total);
}

struct Summary{
	int unexpectedErrors;
	int expectedErrors;
	int missingErrors;
	int todos;
	int obsoleteTodos;

	auto combine(Summary rhs){
		Summary r;
		foreach(i,t;this.tupleof){
			r.tupleof[i]=t+rhs.tupleof[i];
		}
		return r;
	}
	string toString(){
		return "regressions: "~(unexpectedErrors+missingErrors).to!string~"\n"~
			"TODOs: "~todos.to!string~"\n"~
			"fixed: "~obsoleteTodos.to!string~"\n";
	}
	bool isInteresting(){
		foreach(i,x;this.tupleof) if(i!=1&&x) return true;
		return false;
	}
	void opOpAssign(string op:"+")(Summary rhs){
		foreach(i,ref x;this.tupleof) x+=rhs.tupleof[i];
	}
}

auto summarize(Comparison[] comp){
	Summary result;
	foreach(c;comp){
		final switch(c.status) with(Status){
			case expected:
				if(c.info.error){
					if(c.info.todo){
						result.obsoleteTodos++;
						writeln("FIX AT LINE ",c.info.line);
					}else result.expectedErrors++;
				}else{
					if(c.info.todo) result.todos++;
					else{
						result.missingErrors++;
						writeln("REGRESSION AT LINE ",c.info.line);
					}
				}
				break;
			case unexpected:
				assert(c.info.error);
				result.unexpectedErrors++;
				if(c.info.line!=-1) writeln("REGRESSION AT LINE ",c.info.line);
				else writeln("REGRESSION: AssertError");
				break;
			case missing:
				if(c.info.todo){
					if(c.info.error) result.todos++;
					else{
						result.obsoleteTodos++;
						writeln("FIX AT LINE ",c.info.line);
					}
				}else{
					result.missingErrors++;
					writeln("REGRESSION AT LINE ",c.info.line);
				}
				break;
		}
	}
	return result;
}

enum Status{
	expected,
	unexpected,
	missing,
}
struct Comparison{
	Status status;
	Info info;
}

auto compare(Info[] expected, int[] actual){
	int ai=0;
	Comparison[] result;
	foreach(i,x;expected){
		while(ai<actual.length&&actual[ai]<x.line) ai++;
		if(ai==actual.length){
			foreach(xx;expected[i..$])
				result~=Comparison(Status.missing, xx);
			break;
		}
		result~=Comparison(x.line==actual[ai]?Status.expected:Status.missing,x);
	}
	ai=0;
	foreach(i,a;actual){
		while(ai<expected.length&&expected[ai].line<a) ai++;
		if(ai==expected.length){
			foreach(aa;actual[i..$])
				result~=Comparison(Status.unexpected, Info(aa,true,false));
			break;
		}
		if(expected[ai].line!=a) result~=Comparison(Status.unexpected, Info(a, true, false));
	}
	return result;
}

struct Info{
	int line;
	bool error;
	bool todo;
}

struct Comment{
	int line;
	string text;
}

auto comments(string code){
	Comment[] result;
	int line=1;
	for(;;){
		if(code.startsWith("//")){
			code.popFront(); code.popFront();
			auto start = code.ptr;
			while(!code.empty&&code.front!='\n')
				code.popFront();
			auto text = start[0..code.ptr-start];
			result~=Comment(line,text);
		}
		if(code.startsWith("\n")) line++;
		if(code.startsWith("/*"))
			while(!code.startsWith("*/")){
				if(code.startsWith("\n")) line++;
				code.popFront();
			}
		if(code.startsWith("/+")){
			int nest=1;
			code.popFront();
			while(nest){
				code.popFront();
				if(code.startsWith("\n")) line++;
				else if(code.startsWith("/+")){
					code.popFront();
					nest++;
				}else if(code.startsWith("+/")){
					code.popFront();
					nest--;
				}
			}
		}
		if(code.empty) break;
		code.popFront();
	}
	return result;
}

auto analyze(Comment comment){
	Info result;
	result.line=comment.line;
	result.error=comment.text.canFind("error");
	result.todo=comment.text.canFind("TODO")&&!comment.text.canFind("// TODO");
	return result;
}

auto getExpected(string source){
	Info[] result;
	auto code = source.readText;
	foreach(comment;code.comments){
		auto info = comment.analyze;
		if(info.error||info.todo)
			result~=info;
	}
	return result;
}

int[] getActual(string source){
	auto fin=File(source,"r");
	auto options=fin.readln();
	if(options.startsWith("// options: "))
		options=options["// options: ".length..$].strip()~" ";
	else options="";
	auto output = shell("./d "~options~source~" 2>&1").splitLines;
	int[] result;
	static bool isBad(string x){
		if(x.canFind(": error")) return true;
		if(x.startsWith("core.exception.AssertError"))
			return true;
		return false;
	}
	foreach(err;output.filter!isBad){
		while(err.startsWith("<mixin@")) err=err["<mixin@".length..$];
		if(err.startsWith(source~":")){
			auto line = err[(source~":").length..$].parse!int;
			result~=line;
		}else if(err.startsWith("core.exception.AssertError"))
			result~=-1;
	}
	result=result.sort.uniq.array;
	return result;
}
