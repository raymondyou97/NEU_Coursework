#ifndef GAME_H
#define GAME_H

#include "Bird.hpp"
#include "SuperBird.hpp"
#include "Pipe.hpp"
#include "Constants.hpp"

#include <SFML/Audio.hpp>
#include <SFML/Graphics.hpp>
#include <SFML/Window/Keyboard.hpp>

#include <iostream>
#include <string>
#include <math.h>
#include <vector>

sf::RenderWindow window(sf::VideoMode(window_length, window_height), game_title);
std::vector<Pipe *> pipes = {new Pipe(), new Pipe()};
int gravity_counter, pipe_counter, gen_counter = 0;
bool game_over = false;
bool flag_text = false;
int high_score = 0;
int current_score = 0;

// checks if the pipes are working properly
void pipe_status() {
    gen_counter++;
    if (gen_counter == 2000) {
        for (auto p : pipes) {
            int x = p->get_model().getPosition().x;
            // delete pipes that are past the left border of screen
            if (x < -pipe_default_width) {
                pipes.erase(std::remove(pipes.begin(), pipes.end(), p), pipes.end());
                delete(p);
                if (pipes.size() % 2 == 1) {
                    current_score++;
                    if (current_score > high_score) {
                        high_score = current_score;
                    }
                }
            }
        }

        // create new pipes if a set passes the set mark
        if (pipes.size() == 2 && pipes.front()->get_model().getPosition().x < window_length / 3) {
            Pipe * p1 = new Pipe();
            Pipe * p2 = new Pipe();
            pipes.push_back(p1);
            pipes.push_back(p2);
        }
        gen_counter = 0;
    }
}

// checks if the bird collides with any pipes
bool collision(Bird * bird) {
    if (bird->ability()) {
        return false;
    } else {
        for (auto p : pipes) {
            sf::Sprite bird_model = bird->get_model();
            sf::RectangleShape pipe_model = p->get_model();
            if (bird_model.getGlobalBounds().intersects(pipe_model.getGlobalBounds())) {
                return true;
            }
        }
        return false;
    }
}

// drops the bird due to gravity
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

// shifts the pipes each tick
void moving_pipes() {
    pipe_counter++;
    if (pipe_counter == 20) {
        for (auto p : pipes) {
            p->move();
        }
        pipe_counter = 0;
    }
}

// resets game to start a new game
void reset(Bird * bird) {
    pipes = {new Pipe(), new Pipe()};
    gravity_counter, pipe_counter, gen_counter = 0;
    game_over = false;
    flag_text = false;
    current_score = 0;
    bird->reset();
}

// first screen where the player chooses a bird
int select_bird() {
    // Load the background image
    sf::Texture texture;
    texture.loadFromFile(background_file);
    sf::Sprite background(texture);

    // Load the font
    sf::Font font;
    font.loadFromFile(font_file);

    // Buttons
    sf::Vector2f button_size(100, 100);
    sf::RectangleShape bird_1(button_size);
    bird_1.setFillColor(sf::Color::White);
    bird_1.setPosition(155, 300);
    sf::RectangleShape bird_2(button_size);
    bird_2.setFillColor(sf::Color::White);
    bird_2.setPosition(155, 500);

    // Birds
    sf::Texture bird_tex1;
    bird_tex1.loadFromFile(original_bird_img);
    sf::Sprite bird_model1(bird_tex1);
    bird_model1.setPosition(180, 325);
    sf::Texture bird_tex2;
    bird_tex2.loadFromFile(superman_bird_img);
    sf::Sprite bird_model2(bird_tex2);
    bird_model2.setPosition(180, 525);

    // Bunch of texts
    sf::Text g_score(std::to_string(current_score), font, 50);
    g_score.setFillColor(sf::Color::Yellow);
    g_score.setStyle(sf::Text::Bold);
    g_score.setPosition(185, 45);
    sf::Text welcome("Welcome to \nFlappy Bird!", font, 50);
    welcome.setFillColor(sf::Color::Blue);
    welcome.setStyle(sf::Text::Bold);;
    welcome.setPosition(75, 15);
    sf::Text select_bird("Select a bird", font, 25);
    select_bird.setFillColor(sf::Color::Red);
    select_bird.setStyle(sf::Text::Bold);;
    select_bird.setPosition(125, 135);
    sf::Text currently_selected("", font, 18);
    currently_selected.setFillColor(sf::Color::Black);
    currently_selected.setStyle(sf::Text::Bold);;
    sf::Text controls("      Controls\nU, D: select bird\nEnter: start game", font, 25);
    controls.setFillColor(sf::Color::Black);
    controls.setStyle(sf::Text::Bold);;
    controls.setPosition(100, 650);

    int selected_bird = 1; // initial is first
    // Process events
    sf::Event event;
    while (window.isOpen()) {
        while (window.pollEvent(event)) {
            // keyboard events
            if (event.type == sf::Event::Closed ||
            (event.type == sf::Event::KeyPressed && event.key.code == sf::Keyboard::Q)) {
                window.clear();
                window.close();
            } else if (event.type == sf::Event::KeyPressed) {
                if (event.key.code == sf::Keyboard::Return) {
                    // function termination exists only here
                    window.clear();
                    return selected_bird;
                } else if (event.key.code == sf::Keyboard::U) {
                    selected_bird = 1;
                } else if (event.key.code == sf::Keyboard::D) {
                    selected_bird = 2;
                }  
            }
        }
        // Highlight the currently selected bird
        switch(selected_bird) {
            case 1:
                currently_selected.setString("Selected: Default\nSpecial Ability: None");
                currently_selected.setPosition(120, 235);
                bird_1.setOutlineColor(sf::Color::Yellow);
                bird_1.setOutlineThickness(10);
                bird_2.setOutlineThickness(0);
                break;
            case 2:
                currently_selected.setString("Selected: Super\nSpecial Ability:\nPress SPACE to go \ninvincible for 5 seconds");
                currently_selected.setPosition(120, 400);
                bird_2.setOutlineColor(sf::Color::Yellow);
                bird_2.setOutlineThickness(10);
                bird_1.setOutlineThickness(0);
                break;
        }
        window.clear();
        window.draw(background);
        window.draw(welcome);
        window.draw(select_bird);
        window.draw(controls);
        window.draw(currently_selected);
        window.draw(bird_1);
        window.draw(bird_model1);
        window.draw(bird_2);
        window.draw(bird_model2);
        window.display();
    }
}

// second screen (main game) where game happens
int start_game(int selected_bird) {
    // Load the background image
    sf::Texture texture;
    texture.loadFromFile(background_file);
    sf::Sprite background(texture);

    // Load the font
    sf::Font font;
    font.loadFromFile(font_file);

    // Load sounds
    sf::SoundBuffer flap_buffer;
    flap_buffer.loadFromFile(flap_sound);
    sf::Sound flap(flap_buffer);
    flap.setVolume(volume);
    sf::SoundBuffer crash_buffer;
    crash_buffer.loadFromFile(crash_sound);
    sf::Sound crash(crash_buffer);
    crash.setVolume(volume);

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
    sf::Text controls("Q: Quit\nR: Restart", font, 35);
    controls.setFillColor(sf::Color::Black);
    controls.setStyle(sf::Text::Bold);;
    controls.setPosition(125, 650);
    sf::Text special_text("Invincible for", font, 50);
    special_text.setFillColor(sf::Color::Red);
    special_text.setStyle(sf::Text::Bold);;
    special_text.setPosition(125, 150);

    // switches based on bird selected on previous screen
    Bird * bird;
    if (selected_bird == 1)
        bird = new Bird(selected_bird);
    else if (selected_bird == 2)
        bird = new SuperBird(selected_bird);

    // starts the game clock
    sf::Clock clock;

    // Process events
    sf::Event event;
    // Start the game loop
    while (window.isOpen()) {
        // keyboard event listener
        while (window.pollEvent(event)) {
            // events that can always happen aka close the window/game
            if (event.type == sf::Event::Closed ||
            (event.type == sf::Event::KeyPressed && event.key.code == sf::Keyboard::Q)) {
                window.close();
            }
            // events that can happen only when game is over
            if (game_over) {
                if (event.type == sf::Event::KeyPressed) {
                    if (event.key.code == sf::Keyboard::R) {
                        reset(bird);
                    }
                }
            } 
            // events that can happen only when game is in progress
            else {
                if (event.type == sf::Event::KeyPressed) {
                    if (event.key.code == sf::Keyboard::U) {
                        bird->up();
                        flap.play();
                    } else if (event.key.code == sf::Keyboard::Space) {
                        // special ability only works for super bird
                        if (bird->is_special() && !bird->ability()) {
                            bird->flip_ability();
                            clock.restart();
                        }
                    }
                }
            }
        }
        // actual game ticks
        if (game_over) {
            if (!flag_text) {
                crash.play();
                window.draw(controls);
                window.draw(gg_text);
                window.display();
                flag_text = true;
            }
        } else {
            // clear old game state first
            window.clear();
            //ability lasts for only 5 seconds
            if (bird->is_special() && bird->ability()) {
                int current_seconds_elapsed = floor(clock.getElapsedTime().asSeconds());
                if (current_seconds_elapsed == 5) {
                    bird->flip_ability();
                }
            }
            falling_bird(bird);
            moving_pipes();
            pipe_status();
            g_score.setString(std::to_string(current_score));
            h_score.setString("High score: " + std::to_string(high_score));
            window.draw(background);
            for (auto p : pipes) {
                window.draw(p->get_model());
            }
            window.draw(bird->get_model());
            window.draw(g_score);
            window.draw(h_score);
            // build new game state
            window.display();
            // check if game over
            if (collision(bird)) {
                game_over = true;
            }
        }
    }

    // teardown
    delete(bird);
    for (auto p : pipes)
        delete(p);

    return EXIT_SUCCESS;
}

#endif
