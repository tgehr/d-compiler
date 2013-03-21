import util;
import expression; // : Node, Identifier
import semantic, scope_;

import std.algorithm, std.range, std.conv, std.string:join;
import std.typecons : Tuple, tuple;

import hashtable;

// TODO: make the Scheduler understand all parties that currently make use of
// Identifier.tryAgain. Then get rid of Identifier.tryAgain

class Scheduler{
	void add(Node root, Scope sc){
		workingset.add(root, sc);
	}

	final void remove(Node node){
		workingset.remove(node);
	}


	final void await(Node from, Node to, Scope sc){
		// dw("dep from ", from," to ",to);
		workingset.await(from, to, sc);
	}
	
	struct WorkingSet{
		private enum useBuiltin = true;
		static if(useBuiltin) private template Map(K, V){ alias V[K] Map; }
		else private template Map(K,V){ alias HashMap!(K, V, "a is b","cast(size_t)cast(void*)a/16") Map; }

		Map!(Node,Scope) active;
		Map!(Node,Scope) asleep;
		
		Map!(Node,Node[]) awaited;
		
		Map!(Node,bool) done;
		
		Map!(Node,Scope) payload;

		void add(Node node, Scope sc) {
			if(node in asleep) return;
			active[node]=sc;
		}

		void remove(Node node) {
			done[node] = true;
			// dw("done with: ",node);

			active.remove(node);
			asleep.remove(node);

			foreach(v; awaited.get(node,[])){
				if(v !in asleep) continue; // TODO: why needed?
				Identifier.tryAgain = true;
				auto sc=asleep[v];
				active[v]=sc;
				asleep.remove(v);
			}
			awaited.remove(node);
		}
		
		void await(Node from, Node to, Scope sc){
			if(from in asleep) return; // TODO: turn into preconditions
			if(from !in active) return;

			awaited[to]~=from;
			asleep[from]=active[from]; // ...
			active.remove(from);
			add(to,sc);
		}
		
		void update(){
			// dw("active: ",active.keys);
			// dw("asleep: ",asleep.keys);


			foreach(nd,sc; active){
				if(nd.sstate == SemState.completed && !nd.needRetry
				|| nd.sstate == SemState.error)
					done[nd] = true;
			}
			foreach(nd,b; done) active.remove(nd);

			payload = active.dup();

			assert({foreach(nd,sc;payload) assert(!nd.rewrite,text(nd)); return 1;}());

			done.clear(); assert(!done.length);
		}

		void buildInterface(){
			assert(0); // TODO!
		}
		void semantic(){
			foreach(nd,sc; payload){
				//dw("analyzing ",nd);
				if(nd.sstate == SemState.completed){
					if(nd.needRetry){
						assert(nd.needRetry && cast(Expression)nd,text(nd.needRetry," ",nd));
						(cast(Expression)cast(void*)nd).interpret(sc);
					}else remove(nd);
					continue;
				}else if(nd.sstate == SemState.error) remove(nd);
				nd.semantic(sc);
				//dw("done with ",nd," ",nd.sstate," ",nd.needRetry," ",!!nd.rewrite);
			}
			update();
		}
	}
	WorkingSet workingset;
	
	void run(){
		mixin(Configure!q{Identifier.tryAgain = true});
		mixin(Configure!q{Identifier.allowDelay = true});

		workingset.update();

		do{
			// dw("starting resolution pass");
			Identifier.tryAgain = true;
			do{
				Identifier.tryAgain = false;
				workingset.semantic();
			}while(Identifier.tryAgain);

			// dw("starting kill pass");
			
			Identifier.allowDelay=false;
			workingset.semantic();
			Identifier.allowDelay=true;
			//dw("workingset: ",map!(_=>text(_," ",_.sstate," ",typeid(_)))(workingset.payload.keys));
			// dw(workingset.payload.length);
		}while(workingset.payload.length);

		// dw(champ," ",champ.cccc);
	}

	static Scheduler opCall(){
		static Scheduler instance;
		return instance?instance:(instance=new Scheduler);
	}
}