### TODO Please edit the following information in your assignment

- Name(s): Raymond You
- How many hours did it take you to complete this Assignment? 3 hours
- Did you collaborate with any other students/TAs/Professors? No
- Did you use any external resources? (Cite them below)
  - https://stackoverflow.com/questions/17846212/generate-a-random-number-between-1-and-10-in-c
  - https://beginnersbook.com/2014/01/c-for-loop/
  - http://www.cplusplus.com/reference/cstdio/scanf/
- (Optional) What was your favorite part of the assignment?
- (Optional) How would you improve the assignment?

# Prompt

<img align="right" width="250px" src="./media/cardtrick.jpg">

I was always impressed by those folks at the amusement parks and country fairs who could perform magic tricks. I even remember once getting a booklet where if you asked someone enough questions in a row, you could guess their date of birth. It was a sort of neat magic trick, but back then (when I was about five years old) I did not realize I was being tricked by not a circus act, but instead by a programmer! 

Let’s figure out how to write a similar program to guess a randomly generated number by the computer.

# Logistics

For this assignment (and every assignment/lab), you must login into the servers through `your_khoury_usernamename@login.khoury.neu.edu` to complete and test your work. The reason is the examples I will provide below are compiled strictly for our machines architecture, and this is a consistent architecture where your submission will be graded.

# Part 1 - Establishing your work environment

## VIM and TMUX

<img align="right" width="300px" src="https://joshldavis.com/img/vim/tabs.gif">

(Note this part is ungraded--but you are required to do it!)

Figuring out a good workflow on Unix, Mac, and windows is an important part of becoming a good programmer. My work environment (and the suggested one so I can help you during class), is to use the combination of the [VIM text editor](https://www.vim.org/docs.php) and [tmux window manager](https://en.wikipedia.org/wiki/Tmux) to program your assignments in. I also might use XCode in class.

### Student and Teacher Dialouge

*"But I love visual studio, sublime, XCode, Atom, etc."*

*That's great, but you cannot use those in a remote environment easily--so I suggest learning another skill. By all means, use both or multiple tools to write the highest quality code.*

*"Hehe, the professor will never know if I just use notepad. I'll just take a shortcut on this assignment"*

*While that's true you can take a shortcut now, it will eventually catch up to you. I promise this is a good skill to learn! This first assignment is much more lightweight, take the time now to do things properly.*

Here are some suggested resources to get started.
* (VIM+TMUX Example) https://www.youtube.com/watch?v=YD9aFIvlQYs (16:31)
* Type *man tmux* in a terminal.
* Tmux tutorial - https://www.youtube.com/watch?v=BHhA_ZKjyxo (11:23)

> A hint I got a long time ago from a colleague when working, is to ask a colleague if you can shadow them working for 30 minutes.
> It was interesting to see what different tools other computer scientists would use. Whether it was different text editors, short-cuts, plugin-ins, etc.
> Establishing a good workflow can even be part of the fun!

## Compiling and running this assignment

As mentioned in the lab, learning some C can help us better understand and appreciate C++. For this assignemnt, you may use the [clang](https://clang.llvm.org/) or [gcc](https://www.gnu.org/software/gcc/) compiler. Both are industry standard compilers for compiling C programs (in addition to many other programming languages). Sometimes trying different compilers will given you more informative or helpful error messages--either one is perfectly fine for this course!

Here is how you will compile your code on the terminal.

`clang main.c -o main`

or

`gcc main.c -o main`

Both achieve the same thing. 

* First the compiler is specified.
* Then a 'space' follows, and then the '.c' file we want to compile.
* `-o` is a flag abbreviated for output. Items that begin with *dash marks* in general are compiler flags.
  * In this case the 'output' file we will generate(if there are no errors) will be called 'main'
  * Note: This 'main' file is a binary file that we can execute. This is different than 'main.c' which has the .c extension, and is a text file.
  
Finally, to execute your program, you will type in: `./main`

## Overall workflow

So the overall workflow for completing this assignment will likely be something like:

1. Open up the VIM text editor (and perhaps use multiple panes with tmux)
2. Write or change a very small number of lines of code (sometimes just one change!)
3. Save and then close the text file (in Vim lingo this is writing to the current text file)
4. Recompile your program
5. Run your program, and see if it meets your assumptions.

This is the full "Edit, Save, compile, and run" cycle.

# Part 2 - Guessing Game in C

<img align="right" width="300px" src="./media/guess.jpg">

It is now time to implement the guessing game in **main.c**. The requirements of the program are as follows:

- You will play the guessing game a total of 5 times in a row.
- Each round a new number must be randomly generated generate a number from 1 to 10.
- The user will guess the number.
  - If the number is correct, then the game ends.
  - If the number is wrong, then a hint should be provided whether the correct number is higher or lower.
  - If they guess more than 10 times, the game ends. Display a message saying they run out of guesses and display the random number.
- Each time a user guesses, you should increment how many guesses the user has made for the round.
- When the user guesses the correct answer, output that they have finished.
  - Then either start a new game, or if 5 rounds have been played then output the summary of how many guesses the user made over 5 games.
- You should use an 'array' data structure to store the number of guesses made each round.


### Helpful hints

1. If you would like, while you are 'debugging' your program, you can print out the correct answer to shorten iteration time. Be sure not to do this for your final version however!
2. There is a handy function called `rand` found in the stdlib.h for generating random numbers. You will want to think about how to use it.
3. Additionally, you will want to think about how to get user input. For this assignment, you should only need to read in a single numerical value.


### Sample of Correct output 

Below is a sample of a correct iteration of the game. You can make your display 'prettier' if you like, but at a minimum it should look similar to the output below. 

```
-bash-4.2$ clang main.c -o main
-bash-4.2$ ./main
==========================
CPU Says: Pick a number 1-10
==========================
Make a guess:1
No guess higher!
Make a guess:2
No guess higher!
Make a guess:3
No guess higher!
Make a guess:4
No guess higher!
Make a guess:5
No guess higher!
Make a guess:6
No guess higher!
Make a guess:7
No guess higher!
Make a guess:8
You got it!
==========================
CPU Says: Pick a number 1-10
==========================
Make a guess:5
No guess higher!
Make a guess:7
No guess lower!
Make a guess:6
You got it!
==========================
CPU Says: Pick a number 1-10
==========================
Make a guess:5
No guess higher!
Make a guess:8
You got it!
==========================
CPU Says: Pick a number 1-10
==========================
Make a guess:5
No guess higher!
Make a guess:8
No guess higher!
Make a guess:9
You got it!
==========================
CPU Says: Pick a number 1-10
==========================
Make a guess:5
No guess lower!
Make a guess:3
No guess lower!
Make a guess:1
No guess higher!
Make a guess:2
You got it!
=================================================
|Here are the results of your guessing abilities|
=================================================
Game 0 took you 8 guesses
Game 1 took you 3 guesses
Game 2 took you 2 guesses
Game 3 took you 3 guesses
Game 4 took you 4 guesses
```

(Game 0? Yes...I do often count from 0--remember the C langauge is 0-indexed!)


# Resources to help

* [Learn C Interactive Tutorial](http://www.learn-c.org/)

# Rubric

* 90% Guessing Game
    * 20% Program Style
      * Was your program nicely indented?
      * Did you have variable names that are properly named?
      * Are your variables in the appropriate scope (i.e. not all globally accessible)
    * 70% Program Correctnesss
      * Was a new random number generated each game?
      * Was a number 1-10 generated?
      * Did you 'reset' the number of guesses after each round?
      * Were there any 'off by 1 errors' in your game?
      * Did you output the final number of guesses?
      * Did your game run exactly 5 times?
      * Did your program give an appropriate hint of higher or lower?
      * Did you use an array to store the number of guesses?
* 10% for Correct Answers
    * 5% each for answers in the 'exercises.txt'

**Since this is a simple assignment, if the code doesn't compile, we cannot give credit.**

### Important notes

* Note: Your code **must** compile and run on the Khoury machines. Make sure you test your programs on these machines, as this is where we grade your assignments.
* Note: You must commit any additional files(if any) into your repository so we can test your code.
  * Points will be lost if you forget!
* And do not forget, if we do not see your most recent changes 'pushed into this repository' (i.e. what you see on github.com), then we cannot grade them. Updates to the repository must be before the assignment deadline!
* Make sure you add me and the TAs as collaborators to your private repository on the khory github servers so we can grade your code.

# Feedback Loop

(An optional task that will reinforce your learning throughout the semester)

Keep trying 'C' programming exercises from 'The C Programming Language' book or learn-c.org

