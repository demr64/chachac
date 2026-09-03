FRAMAC=frama-c 
SRC=src/chachac.c  

check:  
	$(FRAMAC) -wp $(SRC) 

run: test/test.o src/chachac.o
	gcc src/chachac.o test/test.o -o test.exe
	./test.exe

test.o:
	gcc -o test/test.c

chachac.o:
	gcc -o src/chachac.c

