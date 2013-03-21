OBJFILES = ttt.o lexer.o parser.o module_.o error.o terminal.o util.o
DMD = dmd -m32 -cov -O -release -inline
#DMD = dmd -m64 -O -release -inline


all: ttt

ttt: $(OBJFILES)
	$(DMD) $(OBJFILES)

%.o: %.d
	$(DMD) -J. -c $<

clean:
	rm *.o ttt
