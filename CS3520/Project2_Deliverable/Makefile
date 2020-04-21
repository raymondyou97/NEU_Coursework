LIBS=-lsfml-graphics -lsfml-window -lsfml-system -lsfml-audio
VERSION=-std=c++11

FINAL: game.o bird.o main.o
	g++ $(VERSION) -o FINAL Game.o Bird.o main.o $(LIBS)

bird.o: Bird.hpp Bird.cpp
	g++ $(VERSION) -c Bird.cpp

game.o: Game.hpp Game.cpp
	g++ $(VERSION) -c Game.cpp

main.o: main.cpp Game.hpp Bird.hpp
	g++ $(VERSION) -c main.cpp

clean:
	rm FINAL Bird.o Game.o main.o
