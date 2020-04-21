#ifndef BIRD_H
#define BIRD_H

#include <SFML/Graphics.hpp>
#include <string>
#include "Constants.hpp"

class Bird {
    private:
        sf::Sprite * model;
        sf::Texture * texture;
        int x;
        int y;
        int velocity;
        bool special;
    public:
        Bird(int selected_bird = 1, bool special = false);
        ~Bird();
        sf::Sprite get_model() const;
        void up();
        void fall_from_gravityyy();
        void reset();
        bool can_move(std::string direction) const;
        bool is_special() const;
        virtual void flip_ability();
        virtual bool ability() const;
};

#endif
