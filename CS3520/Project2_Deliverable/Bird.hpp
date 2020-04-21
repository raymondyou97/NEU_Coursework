#include <SFML/Graphics.hpp>
#include <string>

class Bird {
    private:
        sf::CircleShape * model;
        int x;
        int y;
    public:
        Bird(int initial_x, int initial_y);
        ~Bird();
        sf::CircleShape get_model();
        void move_up();
        void move_down();
        bool can_move(std::string direction);
        bool collision();
};