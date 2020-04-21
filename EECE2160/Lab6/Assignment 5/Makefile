#make lab6

GCC = g++
CFLAGS = -g -Wall
OBJS = Arithmetic.o main.o
EXE = lab6

$(EXE): $(OBJS)
	$(GCC) $(FLAGS) $(OBJS) -o $(EXE)
        
Arithmetic.o: Arithmetic.h Arithmetic.cpp
	$(GCC) $(CFLAGS) -c Arithmetic.cpp

main.o: Arithmetic.h main.cpp
	$(GCC) $(CFLAGS) -c main.cpp
              
clean:
	rm $(OBJS) $(EXE)
