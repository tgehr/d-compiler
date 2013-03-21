/+
auto gizmo(int id) {
	return struct{
		string toString(){ return "gizmo " ~ .toString(id); }
	}
}

auto hoozit(int id){
	auto that = gizmo(id);
	return struct{
		alias that this;
		auto test(int testid){
			return testid == id;
		}
	};
}
+/