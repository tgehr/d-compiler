OBJFILES = ttt.o lexer.o parser.o expression.o statement.o declaration.o type.o scope_.o module_.o error.o terminal.o util.o
#DMD = dmd -m32 -O -release -inline
DMD = dmd -g -m32
# -O -release -inline


all: ttt

ttt: $(OBJFILES)
	$(DMD) $(OBJFILES)

%.o: %.d
	$(DMD) -J. -c $<

clean:
	rm *.o ttt
