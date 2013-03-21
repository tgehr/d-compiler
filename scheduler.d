import util;
import expression; // : Node

import std.algorithm;

class Component{
	Node[] nodes;
	Component[] deps;
}

void remove(ref Node[] nodes, Node node)in{
	assert(nodes.canFind(node));
}body{
	swap(nodes[nodes.indexOf(node)],nodes[$-1]);
	nodes=nodes[0..$-1];
	nodes.assumeSafeAppend();
}

class Scheduler{
	void addRoot(Node root){}

	Node[][Node] graph;
	Node[][Node] revs;

	bool needComponentUpdate = false;

	final void addDependency(Node from, Node to){
/+		Node[] e = graph.get(from,[]);
		if(!e.canFind(to)){
			//writeln("we have a dependency from ", typeid(from)," ",from," to ",typeid(to)," ",to);
			e~=to;
			graph[from]=e;
			revs[to]~=from;

			needComponentUpdate = true;
		}else redundancy++;+/
	}
	//int redundancy;

	final void removeNode(Node node){
/+		//if(graph.get(node,[])) writeln("done with ",typeid(node)," ",node," ",redundancy);
		graph.remove(node);
		revs.remove(node);+/
	}
	
	void run(){}

	static Scheduler opCall(){
		static Scheduler instance;
		return instance?instance:(instance=new Scheduler);
	}
}