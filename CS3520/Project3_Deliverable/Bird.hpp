#include <SFML/Graphics.hpp>
#include <string>

class Bird {
    private:
        sf::Sprite * model;
        sf::Texture * texture;
        int x;
        int y;
        int velocity;
    public:
        Bird();
        ~Bird();
        sf::Sprite get_model();
        void up();
        void fall_from_gravityyy();
        void reset();
        bool can_move(std::string direction);
};
