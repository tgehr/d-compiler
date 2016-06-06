
enum cent a=1L<<63;
static assert(a*a != 0L); // TODO
pragma(msg, a*a);
