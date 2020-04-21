#include "Bird.hpp"
#include "Constants.hpp"

#include <SFML/Graphics.hpp>

#include <string>
#include <iostream>

Bird::Bird(int initial_x, int initial_y) {
    sf::CircleShape * model = new sf::CircleShape(20.f);
    model->setFillColor(sf::Color::Blue);
    model->setPosition(initial_x, initial_y);
    this->model = model;
    this->x = initial_x;
    this->y = initial_y;
}

Bird::~Bird() {
    delete this->model;
}

sf::CircleShape Bird::get_model() {
    return *(this->model);
}

void Bird::move_up() {
    if (this->can_move(std::string("up"))) {
        this->model->move(0, -bird_step);
        this->y -= bird_step;
    }
}

void Bird::move_down() {
    if (this->can_move(std::string("down"))) {
        this->model->move(0, bird_step);
        this->y += bird_step;
    }
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

bool Bird::collision() {
    return false;
}