import util;
import expression; // : Node, Identifier
import semantic, scope_;

import std.algorithm, std.conv, std.string:join;

class Scheduler{
	void addRoot(Node root, Scope sc){
		workingset.add(root, sc);
		// workingset.payload~=WorkingSetEntry(root, sc);
	}

	Node[][Node] graph;
	WorkingSetEntry[][Node] revs;

	struct WorkingSetEntry{
		Node node;
		Scope sc;
		void buildInterface(){ 
			// TODO: rather inefficient, do something about it
			auto decl = node.isDeclaration();
			if(!decl) return;
			decl.buildInterface(); mixin(Rewrite!q{node});
		}
		void semantic(){
			if(node.sstate == SemState.completed){
				if(node.needRetry){
					assert(node.needRetry && cast(Expression)node,text(node.needRetry," ",node));
					(cast(Expression)cast(void*)node).interpret(sc);
					mixin(Rewrite!q{node});
					if(!node.needRetry) Scheduler().removeNode(node);
				}else Scheduler().removeNode(node);
				return;
			}else if(node.sstate == SemState.error) Scheduler().removeNode(node);
			node.semantic(sc);
			mixin(Rewrite!q{node});
		}
	}
	
	struct WorkingSet{
		WorkingSetEntry[] payload;
		bool[Node] toRemove;
		bool[WorkingSetEntry] toAdd;

		void add(WorkingSetEntry e) {
			if(toAdd.get(e,false)) return;
			toAdd[e]=true; toRemove.remove(e.node);
		}
		void add(WorkingSetEntry[] es) { foreach(e; es) add(e); }
		void add(Node node, Scope sc) { add(WorkingSetEntry(node, sc)); }

		void remove(Node n) {
			toRemove[n] = true;
			foreach(k,v; toAdd){ // still linear...
				if(k.node==n) { toAdd.remove(k); break; }
			}
			//toAdd = toAdd.partition!(_=>toRemove.get(_.node, false))();
			//toAdd.assumeSafeAppend();
		}
		void update(){
			// dw("toAdd: ", join(map!(_=>text(_.node," ",_.node.sstate))(toAdd),","));
			// dw("toRemove: ", join(map!(to!string)(toRemove.keys),","));
			payload = payload.partition!(_=>toRemove.get(_.node, false))();
			payload.assumeSafeAppend();

			// toAdd = toAdd.partition!(_=>payload.canFind(_))(); // TODO: make fast
			foreach(k; payload) toAdd.remove(k);
			foreach(k,v; toAdd) payload~=k;
			//payload ~= toAdd;

			toAdd.clear();
			toRemove.clear();

			// dw("updated: ",join(map!(_=>text(_.node," ",_.node.sstate))(payload),","));
		}

		void buildInterface(){
			foreach(ref x; payload) x.buildInterface();
			//foreach(ref x; payload) x.semantic();
			update();
		}
		void semantic(){
			foreach(ref x; payload) x.semantic();
			update();
		}
	}
	WorkingSet workingset;

	final void addDependency(Node from, Node to, Scope sc){
		import statement;
		if(cast(ReturnStm)from) assert(!!sc.getFunction());


		Node[] e = graph.get(from,[]);
		if(!e.canFind(to)){
			// dw("we have a dependency from ", typeid(from)," ",from," to ",typeid(to)," ",to,/+" in scope ",sc+/);
			e~=to;
			graph[from]=e;
			auto f = revs.get(to, []);
			if(!f.map!(_=>_.node).canFind(from)){
				f~=WorkingSetEntry(from,sc);
				revs[to] = f;
			}
		}else { redundancy++; }
		
		workingset.remove(from);
		workingset.add(to, sc);
	}
	int redundancy;

	final void removeNode(Node node){
		//if(node in revs) dw("done with ",typeid(node)," ",node," ",redundancy);
		// if(node in revs) dw("completion of ", node, " brings in ", map!(_=>_.node)(revs.get(node,[])));

		workingset.add(revs.get(node,[]));
		workingset.remove(node);

		graph.remove(node);
		revs.remove(node);
		
		// dw(graph.length," ",revs.length);
	}
	
	void run(){
		mixin(Configure!q{Identifier.tryAgain = true});
		mixin(Configure!q{Identifier.allowDelay = true});

		workingset.update();

		int num = 0;
		do{
			Identifier.tryAgain = true;
			do{
				Identifier.tryAgain = false;
				workingset.semantic();
			}while(Identifier.tryAgain);
			
			Identifier.allowDelay=false;
			workingset.semantic();
			Identifier.allowDelay=true;
			// dw("workingset: ",map!(_=>text(_.node," ",_.node.sstate," ",_.node.needRetry))(workingset.payload));
		}while(workingset.payload.length);

		// dw(champ," ",champ.cccc);
	}

	static Scheduler opCall(){
		static Scheduler instance;
		return instance?instance:(instance=new Scheduler);
	}
}