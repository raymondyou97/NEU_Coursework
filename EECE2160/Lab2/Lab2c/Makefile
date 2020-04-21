# WiimoteAccel program Makefile 

WiimoteAccel: main.o WiimoteAccel.o
	g++ -g -Wall main.o WiimoteAccel.o -o WiimoteAccel 	

main.o: main.cpp WiimoteAccel.h
	g++ -g -Wall -c main.cpp

WiimoteAccel.o: WiimoteAccel.cpp WiimoteAccel.h
	g++ -g -Wall -c WiimoteAccel.cpp

clean:
	rm main.o WiimoteAccel.o WiimoteAccel
