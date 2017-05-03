// options: -I/home/tgehr/.dvm/compilers/dmd-2.070.0/src/phobos/

// // TODO: currently dependent on my own setup. fix this.

import std.algorithm;

(int)delegate(int) k;

pragma(msg, typeof(k));
