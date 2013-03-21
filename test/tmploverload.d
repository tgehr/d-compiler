template ambiguous(T...){}
template ambiguous(T...){}

pragma(msg, ambiguous!(int, double));
