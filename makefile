SRCFILES = d.d lexer.d operators.d parser.d expression.d statement.d declaration.d type.d scope_.d module_.d semantic.d scheduler.d analyze.d variant.d interpret.d vrange.d visitors.d error.d terminal.d util.d hashtable.d rope_.d
OBJFILES = d.o lexer.o operators.o parser.o expression.o statement.o declaration.o type.o scope_.o module_.o semantic.o scheduler.o analyze.o variant.o interpret.o vrange.o visitors.o error.o terminal.o util.o hashtable.o rope_.o

#DMD = dmd -m64 -O -release -noboundscheck
#DMD = dmd -m32 -O -release -noboundscheck
DMD = dmd -debug -gc -m32
#DMD = ../dmd/src/dmd -m32 -O -release -noboundscheck
#DMD = ../dmd/src/dmd -debug -gc -m32
#DMD = ../dmd/src/dmd -m32 -O -release -inline -noboundscheck
#DMD = gdmd -gc -m32 -L-lgphobos2 -O -release -inline -noboundscheck
#DMD = gdmd -gc -m32 -L-lgphobos2 -O -inline
#DMD = gdmd -gc -m32 -L-lgphobos2


all: d


__ttt: $(OBJFILES)
	$(DMD) $(OBJFILES) -ofd

%.o: %.d
	$(DMD) -J. -c $<

d: $(SRCFILES) makefile
	$(DMD) -J. $(SRCFILES) -ofd

dgdc:
	gdmd -m32 -L-lgphobos2 -O -release -inline -noboundscheck -J. $(SRCFILES) -ofdgdc

dldc:
	ldmd2 -m32 -O -release -inline -noboundscheck -J. $(SRCFILES) -ofdldc

#$(DMD) $(OBJFILES) -ofttt
clean:
	rm *.o d tt
