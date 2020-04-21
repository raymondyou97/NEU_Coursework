LIBS=-lsfml-graphics -lsfml-window -lsfml-system -lsfml-audio
VERSION=-std=c++11

FINAL: bird.o pipe.o main.o
	g++ $(VERSION) -o FINAL Bird.o Pipe.o main.o $(LIBS)

bird.o: Bird.hpp Bird.cpp
	g++ $(VERSION) -c Bird.cpp

pipe.o: Pipe.hpp Pipe.cpp
	g++ $(VERSION) -c Pipe.cpp

main.o: main.cpp Game.hpp Bird.hpp Pipe.hpp
	g++ $(VERSION) -c main.cpp

clean:
	rm FINAL Bird.o Pipe.o main.o
