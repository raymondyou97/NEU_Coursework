#ifndef SUPERBIRD_HPP
#define SUPERBIRD_HPP

#include "Bird.hpp"

// SuperBird can go invincible for 5 seconds
class SuperBird : public Bird {
    private:
        bool ability_flag;
    public:
        SuperBird(int selected_bird = 1);
        void flip_ability();
        bool ability() const;
};

#endif
