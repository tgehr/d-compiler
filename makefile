SRCFILES = ttt.d lexer.d parser.d expression.d statement.d declaration.d type.d scope_.d module_.d semantic.d visitors.d error.d terminal.d util.d
OBJFILES = ttt.o lexer.o parser.o expression.o statement.o declaration.o type.o scope_.o module_.o semantic.o visitors.o error.o terminal.o util.o
#DMD = dmd -m32 -O -release -inline
DMD = dmd -gc -m32
#DMD = gdmd -m32 -O -release -inline


all: ttt

__ttt: $(OBJFILES)
	$(DMD) $(OBJFILES) -ofttt

%.o: %.d
	$(DMD) -J. -c $<

ttt: $(SRCFILES)
	$(DMD) -J. ttt.d lexer.d parser.d expression.d statement.d declaration.d type.d scope_.d module_.d semantic.d visitors.d error.d terminal.d util.d
#$(DMD) $(OBJFILES) -ofttt
clean:
	rm *.o ttt
