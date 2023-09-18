if [[ "$OSTYPE" == "linux-gnu" ]]; then
    BIN="linux/bin64"
elif [[ "$OSTYPE" == "darwin"* ]]; then
    BIN="osx/bin"
fi

if [[ -d "dmd2" ]]; then
    DMD="./dmd2/$BIN/dmd"
else
    DMD="dmd"
fi

SRCFILES="d.d lexer.d operators.d parser.d expression.d statement.d declaration.d type.d scope_.d module_.d semantic.d scheduler.d analyze.d variant.d interpret.d vrange.d visitors.d error.d terminal.d cent_.d util.d hashtable.d rope_.d bst.d"
OBJFILES="d.o lexer.o operators.o parser.o expression.o statement.o declaration.o type.o scope_.o module_.o semantic.o scheduler.o analyze.o variant.o interpret.o vrange.o visitors.o error.o terminal.o cent_.o util.o hashtable.o rope_.o bst.o"

DMD_OPT="$DMD -d -debug -g -m32 -L-no-pie"

$DMD_OPT -J. $SRCFILES -ofd
