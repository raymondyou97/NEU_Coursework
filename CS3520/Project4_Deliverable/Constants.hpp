#ifndef CONSTANTS_H
#define CONSTANTS_H

#include <string>

static const std::string game_title = "Flappy Bird";
static const std::string background_file = "assets/background.jpg";
static const std::string font_file = "assets/arial.ttf";
static const std::string flap_sound = "assets/flap.wav";
static const std::string crash_sound = "assets/crash.wav";

static const std::string original_bird_img = "assets/birds/original_45x45.png";
static const std::string superman_bird_img = "assets/birds/superman_45x45.png";

static const int volume = 20;

static const int window_length = 400;
static const int window_height = 800;

static const int bird_initial_x = 5;
static const int bird_initial_y = 400;
static const int bird_step = 70;
static const int bird_velocity = 0;

static const int short_pipe_size = 75;
static const int middle_pipe_size = 300;
static const int long_pipe_size = 525;
static const int pipe_default_width = 50;

#endif
