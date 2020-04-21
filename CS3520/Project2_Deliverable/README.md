# Deliverable Overview

As mentioned last class, you need to develop a working example demonstratring the library/s you picked in action. 
If you have few choices in mind then build a working example for each one of them to get familiar with how they work,
and to know how to build and link them.

# Deliverable Requirements:

* Must show the library in action by building a running executable. You must implement few library features that you 
are planning on using.
* The code must be commented, explaining what you are trying to achive with each feature you are demostrating.
(Think of this as writing a mini tutorial that demonstrates how to use the features you are going to use).
* Provide build instructions.
* Provide the library code if appropriate.
* Record a short video and either post it on youtube or push it in this folder demonstrarting the library in action.

# Answer the following questions:

Provide answers to each of the following:

* What library features is your demo showing.

    - display of working game elements such as game background, game music, game window, and more
    - handling of keyboard events such as when the bird moves up and down
    - game tick events aka each second the pipes shift to the left
    - usage of existing library classes (the shapes)

 * How will these features be used as part of your final project.
    - I will be using all of these features in my final project such as the libaries shape elements to represent my in-game models
    - the libraries handling of keyboard events, eventually gonna add mouse events too
    - the library's timer class to handle each game tick

* How are you building and linking the library.

    - I am building and linking the library by first building every object file for every `.cpp/.hpp` combination.
    - Then, linking these dependencies to the main.cpp class
    - Finally, adding all the library SFML dependencies with the final output
    - All of this can be easily seen in the Makefile

* Did you have any difficulties in builidng and linking the library that were hard to resolve

    - No, everything was pretty simple due to the excellent documentation found online.

* Were you able to find enough documentation for your library about how to use it? How about how to built it.

    - Yes, the documentation was great which was why I didn't run into much difficulty. It shows you how to build, install, and create a basic, working example with the library.
    - Documentation can be found here `https://www.sfml-dev.org/documentation/2.5.1/`
 
* What was the hardest part of the whole process?

    - Building and linking all the object dependency files through the Makefile and not have everything be in one giant file of mess.
    - Figuring out the numbers for the X and Y coordinates for the game objects and not having it 'fall off the screen'.

* What are you next steps going to be in developing your project.

    - Make the pipes randomly generated
    - The bird should fall down due to the gravity
    - Make the game more fluid and not hard jumps through pixels
    - Figure out how to implement collisions aka game over specifically with the SFML library
    - Think of some cool extra things to make Flappy Birds more interesting

* What difficulties do you foresee in your design/library use? 

    - Collisions will be difficult due to the library not having any built-in shape collision function, so I will have to figure out how to implement `bool hasCollision()` with the coordinates provided.
    - I also need to implement the object-oriented C++ concepts as I am currently using mainly the library utility classes and functions.

* Provide the URL to your demo or indicate where it is pushed in the repo
 
    - `https://drive.google.com/file/d/1uhgoISZB1phFYilut6jd5zwTYX_EtGLy/view?usp=sharing`
 
* What are the build instructions.
  
    - I am running a Linux distribution specifically Ubuntu 18.0.4 so all I had to do is run the command `sudo apt-get install libsfml-dev`
    - But, here are the download instructions for other systems `https://www.sfml-dev.org/download/sfml/2.5.1/` . I don't think it should be too hard setting it up on windows or mac. Something along the lines of downloading the library, unzipping it into your C++ library location.
    - Once the library is successfully downloaded and installed, it's just a simple two commands to build and run the game.
        ```
        make
        ./FINAL
        ```
 
* Did you upload all of your code? 

    - Yes, all the most up-to-date code is in this folder.

# Rubric
* 15% of final project.
* Will be graded how detailed and thoughtfull your responses are. Unthoughtfull answers will not recieve many points. 
