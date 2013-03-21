import std.stdio;
import std.string, std.array;

int main(){
	int err;
	for(auto line=readln();line;line=readln()){
		if(!line.startsWith("<ctwriter filename=")){write(line); err=1; continue;}
		auto start=line["<ctwriter filename=".length+1..$];
		auto end=start.indexOf("`");
		auto fname=start[0..end];
		auto mode="a";
		if(start[end..$].startsWith(" mode=")) mode=start[end+"mode=`".sizeof..$].startsWith("clear`")?"w":"a";
		auto f=File(fname,mode);
		for(line=readln();line&&!line.startsWith("</ctwriter>");line=readln()){
			f.write(line);
		}
	}
	return err;
}
