SRCFILES = d.d lexer.d operators.d parser.d expression.d statement.d declaration.d type.d scope_.d module_.d semantic.d variant.d interpret.d vrange.d visitors.d error.d terminal.d util.d
OBJFILES = d.o lexer.o operators.o parser.o expression.o statement.o declaration.o type.o scope_.o module_.o semantic.o variant.d interpret.o vrange.o visitors.o error.o terminal.o util.o

DMD = dmd -m32 -O -release -noboundscheck
#DMD = dmd -m32 -O -release -inline -noboundscheck
#DMD = dmd -property -gc -m32
#DMD = ../dmd/src/dmd -gc -m32
#DMD = ../dmd/src/dmd -property -gc -m32
#DMD = gdmd -m32 -L-lgphobos2 -O -release -inline -noboundscheck
#DMD = gdmd -gc -m32 -L-lgphobos2


all: d

__ttt: $(OBJFILES)
	$(DMD) $(OBJFILES) -ofd

%.o: %.d
	$(DMD) -J. -c $<

d: $(SRCFILES) makefile
	$(DMD) -J. $(SRCFILES) -ofd
#$(DMD) $(OBJFILES) -ofttt
clean:
	rm *.o d tt
