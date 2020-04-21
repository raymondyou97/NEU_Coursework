#include "Game.hpp"
#include "Bird.hpp"
#include "Constants.hpp"

#include <SFML/Audio.hpp>
#include <SFML/Graphics.hpp>
#include <SFML/Window/Keyboard.hpp>

#include <iostream>
#include <string>
#include <math.h>


// TODO cleanup this big function
int start_game() {
    // Create the main window
    sf::RenderWindow window(sf::VideoMode(window_length, window_height), game_title);
    // Load a sprite to display
    sf::Texture texture;
    if (!texture.loadFromFile(background_file))
        return EXIT_FAILURE;
    sf::Sprite sprite(texture);
    // Create a graphical text to display
    sf::Font font;
    if (!font.loadFromFile(font_file))
        return EXIT_FAILURE;
    // Load a music to play
    sf::Music music;
    if (!music.openFromFile(music_file))
        return EXIT_FAILURE;
    // Play the music
    music.play();

    Bird * bird = new Bird(5, 400);
    
    // TODO abstract this into a class and randomize pipes
    // Y_index
    // window_height - PIPE_HEIGHT = BOTTOM PIPE
    // 0 = TOP PIPE
    sf::RectangleShape pipe_1(sf::Vector2f(50, 250));
    pipe_1.setFillColor(sf::Color::Red);
    pipe_1.setPosition(window_length - 100, 0);

    sf::RectangleShape pipe_2(sf::Vector2f(50, 250));
    pipe_2.setFillColor(sf::Color::Red);
    pipe_2.setPosition(window_length - 200, window_height - 250);

    sf::RectangleShape pipe_3(sf::Vector2f(50, 400));
    pipe_3.setFillColor(sf::Color::Red);
    pipe_3.setPosition(window_length, window_height - 400);

    sf::Clock clock; // starts the clock
    int initial_time_elapsed = floor(clock.getElapsedTime().asSeconds());
    // Start the game loop
    while (window.isOpen())
    {
        // Process events
        sf::Event event;
        while (window.pollEvent(event))
        {
            // Close window: exit
            if (event.type == sf::Event::Closed)
                window.close();
		
            if (event.type == sf::Event::KeyPressed) {
                if (event.key.code == sf::Keyboard::Up) {
                    bird->move_up();
                } else if (event.key.code == sf::Keyboard::Down) {
                    bird->move_down();
                }
            }
        }
        // clear old game state first
        window.clear();

        // game ticks
        int current_time_elapsed = floor(clock.getElapsedTime().asSeconds());
        if (initial_time_elapsed != current_time_elapsed) {
            std::cout << "GAME TICK" << std::endl;
            initial_time_elapsed = current_time_elapsed;
            pipe_1.move(pipe_step, 0);
            pipe_2.move(pipe_step, 0);
            pipe_3.move(pipe_step, 0);
        }

        // TODO make this cleaner by throwing into a list or something
        window.draw(sprite);
        window.draw(bird->get_model());
        window.draw(pipe_1);
        window.draw(pipe_2);
        window.draw(pipe_3);

        // build new game state
        window.display();
    }
    return EXIT_SUCCESS;
}