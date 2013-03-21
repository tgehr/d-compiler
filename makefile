SRCFILES = ttt.d lexer.d operators.d parser.d expression.d statement.d declaration.d type.d scope_.d module_.d semantic.d vrange.d visitors.d error.d terminal.d util.d
OBJFILES = ttt.o lexer.o operators.o parser.o expression.o statement.o declaration.o type.o scope_.o module_.o semantic.o vrange.o visitors.o error.o terminal.o util.o

#DMD = dmd -m32 -O -release -inline -noboundscheck
DMD = dmd -property -gc -m32
#DMD = ../dmd/src/dmd -property -gc -m32
#DMD = gdmd -m32 -L-lgphobos2 -O -release -inline -noboundscheck
#DMD = gdmd -gc -m32 -L-lgphobos2


all: ttt

__ttt: $(OBJFILES)
	$(DMD) $(OBJFILES) -ofttt

%.o: %.d
	$(DMD) -J. -c $<

ttt: $(SRCFILES) makefile
	$(DMD) -J. $(SRCFILES) -ofttt
#$(DMD) $(OBJFILES) -ofttt
clean:
	rm *.o ttt tt
