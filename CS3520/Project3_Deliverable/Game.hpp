#include "Bird.hpp"
#include "Pipe.hpp"
#include "Constants.hpp"

#include <SFML/Audio.hpp>
#include <SFML/Graphics.hpp>
#include <SFML/Window/Keyboard.hpp>

#include <iostream>
#include <string>
#include <math.h>
#include <vector>
#include <stdexcept>

sf::RenderWindow window(sf::VideoMode(window_length, window_height), game_title);
std::vector<Pipe *> pipes = {new Pipe(), new Pipe()};
int gravity_counter, pipe_counter = 0;
bool game_over = false;
bool flag_text = false;
int high_score = 0;
int current_score = 0;

void pipe_status() {
    for (auto p : pipes) {
        int x = p->get_model().getPosition().x;
        // delete pipes that are past the left border of screen
        if (x < -pipe_default_width) {
            pipes.erase(std::remove(pipes.begin(), pipes.end(), p), pipes.end());
            if (pipes.size() % 2 == 1) {
                current_score++;
                if (current_score > high_score) {
                    high_score = current_score;
                }
            }
        }

        // spawn new set of pipes once previous passes halfway
        if ((pipes.size() == 2) && (x < window_length / 2)) {
                Pipe * p1 = new Pipe();
                Pipe * p2 = new Pipe();
                pipes.push_back(p1);
                pipes.push_back(p2);
        }
    }
}

bool collision(Bird * bird, std::vector<Pipe *> pipes) {
    for (auto p : pipes) {
        sf::Sprite bird_model = bird->get_model();
        sf::RectangleShape pipe_model = p->get_model();
        if (bird_model.getGlobalBounds().intersects(pipe_model.getGlobalBounds())) {
            return true;
        }
    }
    return false;
}

void falling_bird(Bird * bird) {
    gravity_counter++;
    if (gravity_counter == 150) {
        bird->fall_from_gravityyy();
        gravity_counter = 0;
    }
    // check if bird is dead
    int current_y = bird->get_model().getPosition().y;
    if (current_y > window_height + bird_step) {
        game_over = true;
    }
}

void moving_pipes() {
    pipe_counter++;
    if (pipe_counter == 20) {
        for (auto p : pipes) {
            p->move();
        }
        pipe_counter = 0;
    }
}

void reset(Bird * bird) {
    pipes = {new Pipe(), new Pipe()};
    gravity_counter, pipe_counter = 0;
    game_over = false;
    flag_text = false;
    current_score = 0;
    bird->reset();
}

int start_game() {
    // Load the background image
    sf::Texture texture;
    texture.loadFromFile(background_file);
    sf::Sprite background(texture);
    // Load the font
    sf::Font font;
    font.loadFromFile(font_file);
    // Load the music
    sf::Music music;
    music.openFromFile(music_file);
    music.play();

    // Bunch of texts
    sf::Text g_score(std::to_string(current_score), font, 50);
    g_score.setFillColor(sf::Color::Yellow);
    g_score.setStyle(sf::Text::Bold);
    g_score.setPosition(185, 45);
    sf::Text h_score("High score: " + std::to_string(high_score), font, 25);
    h_score.setFillColor(sf::Color::Blue);
    h_score.setStyle(sf::Text::Bold);
    h_score.setStyle(sf::Text::Underlined);
    h_score.setPosition(125, 15);
    sf::Text gg_text("Game \n Over", font, 100);
    gg_text.setFillColor(sf::Color::Red);
    gg_text.setStyle(sf::Text::Bold);
    gg_text.setPosition(75, 250);

    // initial, sole bird
    Bird * bird = new Bird();

    // starts the game clock
    sf::Clock clock;
    int initial_time_elapsed = floor(clock.getElapsedTime().asSeconds());

    // Process events
    sf::Event event;
    // Start the game loop
    while (window.isOpen()) {
        // keyboard event listener
        while (window.pollEvent(event)) {
            // key events that can always happen
            if (event.type == sf::Event::Closed ||
            (event.type == sf::Event::KeyPressed && event.key.code == sf::Keyboard::Q)) {
                window.close();
            } else if (event.type == sf::Event::KeyPressed) {
                if (event.key.code == sf::Keyboard::R) {
                    reset(bird);
                }
            }
            // key events that can only happen when game is over
            if (!game_over) {
                if (event.type == sf::Event::KeyPressed) {
                    if (event.key.code == sf::Keyboard::U) {
                        bird->up();
                    }
                }
            }
        }
        // actual game ticks
        if (game_over) {
            if (!flag_text) {
                window.draw(gg_text);
                window.display();
                flag_text = true;
            }
        } else {
            // clear old game state first
            window.clear();
            falling_bird(bird);
            moving_pipes();
            // 1 second ticks
            int current_seconds_elapsed = floor(clock.getElapsedTime().asSeconds());
            if (initial_time_elapsed != current_seconds_elapsed) {
                initial_time_elapsed = current_seconds_elapsed;
            }
            pipe_status();
            g_score.setString(std::to_string(current_score));
            h_score.setString("High score: " + std::to_string(high_score));
            window.draw(background);
            window.draw(bird->get_model());
            for (auto p : pipes) {
                window.draw(p->get_model());
            }
            window.draw(g_score);
            window.draw(h_score);
            // build new game state
            window.display();
            // check if game over
            if (collision(bird, pipes)) {
                game_over = true;
            }
        }
    }
    return EXIT_SUCCESS;
}
