#include <SFML/Graphics.hpp>
#include <string>

class Pipe {
    private:
        sf::RectangleShape * model;
        int x;
        int y;
        sf::Vector2f * size;
        bool from_top;
        bool long_pipe;
        bool middle_pipe;
    public:
        Pipe();
        ~Pipe();
        sf::RectangleShape get_model();
        void move();
};
