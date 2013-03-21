OBJFILES = ttt.o lexer.o parser.o expression.o statement.o declaration.o type.o scope_.o module_.o semantic.o error.o terminal.o util.o
#DMD = dmd -m32 -O -release -inline
#DMD = gdmd -g -m32
DMD = gdmd -m32 -O -release -inline


all: ttt

ttt: $(OBJFILES)
	$(DMD) $(OBJFILES) -ofttt

%.o: %.d
	$(DMD) -J. -c $<

clean:
	rm *.o ttt
