FRAMAC=frama-c 
SRC=src/chachac.c  

pre:  
	$(FRAMAC) -eva $(SRC) 
check:  
	$(FRAMAC) -wp $(SRC) 
run:  
	gcc -O2 -Wall -Wextra -o chachac.exe src/chachac.c  
	./chachac.exe
