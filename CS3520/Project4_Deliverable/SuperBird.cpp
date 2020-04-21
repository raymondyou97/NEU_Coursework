#include "SuperBird.hpp"

#include <iostream>

SuperBird::SuperBird(int selected_bird) : Bird(selected_bird, true) {
    this->ability_flag = false;
}

void SuperBird::flip_ability() {
    this->ability_flag = !this->ability_flag;
}

bool SuperBird::ability() const {
    return this->ability_flag;
}
