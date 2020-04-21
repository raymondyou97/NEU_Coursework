#include "Pipe.hpp"
#include "Constants.hpp"

#include <SFML/Graphics.hpp>

#include <time.h>
#include <iostream>
#include <string>
#include <tuple>

bool completed_set = true;
Pipe * last_pipe = nullptr;

/* 
Pipes comes in pairs. One pipe coming from the top, and another pipe coming from the bottom.
The first pipe is nondeterministic, it can be any combination of (top, bot) and (short, medium, long)
The second pipe is deterministic as it has to always be the counter of the first pipe; meaning
if the first pipe is a long pipe from top, the second pipe has to be a short pipe from bottom
*/
Pipe::Pipe() {
    srand(time(NULL));
    this->x = window_length + pipe_default_width;
    sf::Vector2f * size = nullptr;
    // pipes come in pairs. completed_set = next pipe is 1/2
    if (completed_set) {
        this->middle_pipe = std::rand() % 2;
        this->from_top = std::rand() % 2;
        this->long_pipe = std::rand() % 2;
        if (this->from_top) {
            this->y = 0;
            if (this->middle_pipe) // middle pipe from top
                size = new sf::Vector2f(pipe_default_width, middle_pipe_size);
            else if (this->long_pipe) // long pipe from top
                size = new sf::Vector2f(pipe_default_width, long_pipe_size);
            else // short pipe from top
                size = new sf::Vector2f(pipe_default_width, short_pipe_size);
        } else {
            if (this->middle_pipe) { // middle pipe from bot
                this->y = window_height - middle_pipe_size;
                size = new sf::Vector2f(pipe_default_width, middle_pipe_size);
            } else if (this->long_pipe) { // long pipe from bot
                this->y = window_height - long_pipe_size;
                size = new sf::Vector2f(pipe_default_width, long_pipe_size);
            } else { // short pipe from bot
                this->y = window_height - short_pipe_size;
                size = new sf::Vector2f(pipe_default_width, short_pipe_size);
            }
        }
        last_pipe = this;
    } else { // next pipe is 2/2
        if (last_pipe->from_top) {
            this->from_top = false;
            if (last_pipe->middle_pipe) { // middle pipe from bot
                this->y = window_height - middle_pipe_size;
                size = new sf::Vector2f(pipe_default_width, middle_pipe_size);
            } else if (last_pipe->long_pipe) { // short pipe from bot
                this->y = window_height - short_pipe_size;
                size = new sf::Vector2f(pipe_default_width, short_pipe_size);
            } else { // long pipe from bot
                this->y = window_height - long_pipe_size;
                size = new sf::Vector2f(pipe_default_width, long_pipe_size);
            }
        } else {
            this->from_top = true;
            this->y = 0;
            if (last_pipe->middle_pipe) // middle pipe from top
                size = new sf::Vector2f(pipe_default_width, middle_pipe_size);
            else if (last_pipe->long_pipe) // short pipe from top
                size = new sf::Vector2f(pipe_default_width, short_pipe_size);
            else // long pipe from top
                size = new sf::Vector2f(pipe_default_width, long_pipe_size);
        }
        if (last_pipe->middle_pipe) {
            this->long_pipe = false;
            this->middle_pipe = true;
        } else if (last_pipe->long_pipe) {
            this->long_pipe = false;
            this->middle_pipe = false;
        } else {
            this->long_pipe = true;
            this->middle_pipe = false;
        }
        last_pipe = nullptr;
    }
    sf::RectangleShape * model = new sf::RectangleShape(*size);
    model->setFillColor(sf::Color(0, 128, 0));
    model->setPosition(this->x, this->y);
    this->model = model;
    this->size = size;
    completed_set = !completed_set;
}

Pipe::~Pipe() {
    delete this->size;
    delete this->model;
}

sf::RectangleShape Pipe::get_model() const {
    return *model;
}

void Pipe::move() {
    this->model->move(-1, 0);
}
