
bool isSortedNoBloat(alias less = "a < b", Range)(Range r){
	pragma(msg, "no bloat ",Range);
	assert(0);
}

bool isSortedBloat(alias less = (a, b) => a < b, Range)(Range r){
	pragma(msg, "bloat ",Range); // // TODO: this should only be printed once!
	assert(0);
}

void main(){
	auto x = [1,2,3];
	assert(x.isSortedNoBloat);
	assert(x.isSortedBloat);
	assert(x.isSortedBloat);
}
