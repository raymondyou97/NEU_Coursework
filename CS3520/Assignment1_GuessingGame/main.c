// Add your program here!
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <stdbool.h>


bool checkGuess(int target, int guess) {
    if (target == guess) {
        return true;
    }
    return false;
}

bool checkGuessHigher(int target, int guess) {
    if (guess > target) {
        return true;
    }
    return false;
}

void printGameResults(int numberOfGames, int gameResults[]) {
    printf("=================================================\n");
    printf("|Here are the results of your guessing abilities|\n");
    printf("=================================================\n");

    int i;
    for (i = 0; i < numberOfGames; i++) {
        printf("Game %d took you %d guesses\n", i + 1, gameResults[i]);
    }
}

void startGames(int numberOfGames) {
    int maxGuesses = 10;
    int gameResults[numberOfGames];

    int i;
    for(i = 0; i < numberOfGames; i++) {
        srand(time(NULL));
        int target = rand() % 11;
        // rand() goes from 0 to num so 0 is an edge case

        printf("==========================\n");
        printf("CPU Says: Pick a number 1-10\n");
        printf("==========================\n");

        int guess = -1;
        int guessCount = 0;

        while (guess != target) {
            if (guessCount == maxGuesses) {
                printf("You only get 10 guesses unfortunately. Maybe next time! \n");
                break;
            }
     
            printf("Make a guess:");
            if (target == 0) {
                target = 1;
            }
            
            scanf("%d", &guess);
            guessCount++;
            bool check = checkGuess(target, guess);
            if (check) {
                printf("You got it!\n");
            }
            else {
                bool checkHigher = checkGuessHigher(target, guess);
                if(checkHigher) {
                    printf("No guess lower!\n");
                }
                else {
                    printf("No guess higher!\n");
                }
            }
        }
        gameResults[i] = guessCount;
    }
    printGameResults(numberOfGames, gameResults);
}
 
int main() {
    startGames(5);
    return 0;
}

