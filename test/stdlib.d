// options: -I/home/tgehr/.dvm/compilers/dmd-2.070.0/src/phobos/
// TODO: currently dependent on my own specific setup. fix this.

//import std.algorithm; // TODO

(int)delegate(int) k;

pragma(msg, typeof(k));
