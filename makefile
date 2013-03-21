SRCFILES = ttt.d lexer.d operators.d parser.d expression.d statement.d declaration.d type.d scope_.d module_.d semantic.d vrange.d visitors.d error.d terminal.d util.d
OBJFILES = ttt.o lexer.o operators.o parser.o expression.o statement.o declaration.o type.o scope_.o module_.o semantic.o vrange.o visitors.o error.o terminal.o util.o
#DMD = dmd -m32 -O -release -inline -noboundscheck
DMD = dmd -gc -m32
#DMD = gdmd -m32 -O -release -inline -noboundscheck


all: ttt

__ttt: $(OBJFILES)
	$(DMD) $(OBJFILES) -ofttt

%.o: %.d
	$(DMD) -J. -c $<

ttt: $(SRCFILES)
	$(DMD) -J. $(SRCFILES)
#$(DMD) $(OBJFILES) -ofttt
clean:
	rm *.o ttt tt
