#include "Bird.hpp"
#include "Constants.hpp"

#include <SFML/Graphics.hpp>

#include <string>
#include <iostream>

Bird::Bird(int selected_bird, bool special) {
    sf::Texture * bird_tex = new sf::Texture();
    // switches based on bird passed in
    switch(selected_bird) {
        case 1:
            bird_tex->loadFromFile(original_bird_img);
            break;
        case 2:
            bird_tex->loadFromFile(superman_bird_img);
            break;
    }
    sf::Sprite * bird_model = new sf::Sprite(*bird_tex);
    // inital bird position
    bird_model->setPosition(bird_initial_x, bird_initial_y);
    // set all values
    this->texture = bird_tex;
    this->model = bird_model;
    this->x = bird_initial_x;
    this->y = bird_initial_y;
    this->velocity = bird_velocity;
    this->special = special;
}

Bird::~Bird() {
    delete this->model;
    delete this->texture;
}

sf::Sprite Bird::get_model() const {
    return *(this->model);
}

void Bird::up() {
    // bird can only move up
    if (this->can_move(std::string("up"))) {
        this->model->move(0, -bird_step);
        this->y -= bird_step;
        this->velocity = bird_velocity;
    }
}

// accounts for gravity for bord
void Bird::fall_from_gravityyy() {
    this->model->move(0, this->velocity);
    this->velocity++;
}

void Bird::reset() {
    this->model->setPosition(bird_initial_x, bird_initial_y);
    this->x = bird_initial_x;
    this->y = bird_initial_y;
    this->velocity = bird_velocity;
}

// checks if the bird can move aka not moving off the screen
bool Bird::can_move(std::string direction) const {
    int current_y = this->model->getPosition().y;
    if (direction == std::string("up")) {
        return current_y - bird_step >= 0 ? true : false;
    } else if (direction == std::string ("down")) {
        return current_y + bird_step <= window_height - bird_step ? true : false;
    } else {
        return false;
    }
}

bool Bird::is_special() const {
    return this->special;
}

void Bird::flip_ability() {}

bool Bird::ability() const {
    return false;
}
