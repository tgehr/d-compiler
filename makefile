OBJFILES = ttt.o lexer.o parser.o module_.o util.o
DMD = dmd -m32 -O -release -inline

all: ttt

ttt: $(OBJFILES)
	$(DMD) $(OBJFILES)

%.o: %.d
	$(DMD) -J. -c $<

parser.o: parser.d
	$(DMD) -J. -c $< 2>&1 | ./ctwriter


clean:
	rm *.o ttt
