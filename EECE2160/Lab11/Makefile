#make final

GCC = g++
CFLAGS = -g -Wall
OBJS = RoboticArm.o main.o
EXE = final

$(EXE): $(OBJS)
    $(GCC) $(FLAGS) $(OBJS) -o $(EXE)
        
RoboticArm.o: RoboticArm.h RoboticArm.cpp
    $(GCC) $(CFLAGS) -c RoboticArm.cpp

main.o: RoboticArm.h main.cpp
    $(GCC) $(CFLAGS) -c main.cpp
              
clean:
    rm $(OBJS) $(EXE)
