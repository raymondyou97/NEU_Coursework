# Calculator program Makefile 

Calculator:  Calculator.o CalcMain.o
	g++ -o Calculator Calculator.o CalcMain.o

Calculator.o: Calculator.h Calculator.cpp
	g++ -c Calculator.cpp

CalcMain.o: Calculator.h CalcMain.cpp
	g++ -c CalcMain.cpp
	
clean:
	rm Calculator.o CalcMain.o Calculator