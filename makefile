OBJFILES = ttt.o lexer.o parser.o module_.o util.o
DMD = dmd -m32 -O -release -inline

all: ttt

ttt: $(OBJFILES)
	$(DMD) $(OBJFILES)

%.o: %.d
	$(DMD) -J. -c $<

clean:
	rm *.o ttt
