# Furniture program Makefile 

Furniture:  Furniture.o Table.o Bed.o main.o
	g++ -o Furniture Furniture.o Table.o Bed.o main.o

Furniture.o: Furniture.h Furniture.cpp
	g++ -c Furniture.cpp

Bed.o: Bed.h Bed.cpp Furniture.h
	g++ -c Bed.cpp

Table.o: Table.h Table.cpp Furniture.h
	g++ -c Table.cpp
	
main.o: Bed.h Furniture.h main.cpp
	g++ -c main.cpp
	
clean:
	rm Furniture.o Bed.o Table.o main.o Furniture