MainApplication: Vector.o Stack.o Queue.o main.o
	g++ -o MainApplication Vector.o Stack.o Queue.o main.o

Vector.o: Vector.hpp Vector.cpp IContainer.hpp
	g++ -c Vector.cpp

Stack.o: Stack.hpp Stack.cpp IContainer.hpp Node.hpp
	g++ -c Stack.cpp

Queue.o: Queue.hpp Queue.cpp IContainer.hpp
	g++ -c Queue.cpp
	
main.o: Vector.hpp IContainer.hpp main.cpp
	g++ -c main.cpp
	
clean:
	rm MainApplication Vector.o Stack.o Queue.o main.o
