STDLIB=/usr/share/agda-stdlib/

all: obj

main.agda.o: *.agda
	agda --compile --ghc-dont-call-ghc -i $(STDLIB) Main.agda
	ghc                                                           \
            -package text -package ghc                                \
            MAlonzo/Code/Main.hs                                      \
            -main-is MAlonzo.Code.Main                                \
            -fwarn-incomplete-patterns -fno-warn-overlapping-patterns \
            -XGADTs                                                   \
            -o main.agda.o

main.c: main.agda.o
	./main.agda.o > main.c

main.o: main.c
	clang main.c -o main.o

agda: main.agda.o
c: main.c
obj: main.o

clean:
	rm -r MAlonzo
	rm *.agdai
	rm *.c
	rm *.o
