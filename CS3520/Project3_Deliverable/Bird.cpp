#include "Bird.hpp"
#include "Constants.hpp"

#include <SFML/Graphics.hpp>

#include <string>
#include <iostream>

Bird::Bird() {
    sf::Texture * bird_tex = new sf::Texture();
    bird_tex->loadFromFile(bird_img);
    sf::Sprite * bird_model = new sf::Sprite(*bird_tex);
    bird_model->setPosition(bird_initial_x, bird_initial_y);
    this->texture = bird_tex;
    this->model = bird_model;
    this->x = bird_initial_x;
    this->y = bird_initial_y;
    this->velocity = bird_velocity;
}

Bird::~Bird() {
    delete this->model;
    delete this->texture;
}

sf::Sprite Bird::get_model() {
    return *(this->model);
}

void Bird::up() {
    if (this->can_move(std::string("up"))) {
        this->model->move(0, -bird_step);
        this->y -= bird_step;
        this->velocity = bird_velocity;
    }
}

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

bool Bird::can_move(std::string direction) {
    int current_y = this->model->getPosition().y;
    if (direction == std::string("up")) {
        return current_y - bird_step >= 0 ? true : false;
    } else if (direction == std::string ("down")) {
        return current_y + bird_step <= window_height - bird_step ? true : false;
    } else {
        return false;
    }
}
