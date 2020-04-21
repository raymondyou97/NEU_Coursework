/* See Chapter 5 of Advanced UNIX Programming:  http://www.basepath.com/aup/
 *   for further related examples of systems programming.  (That home page
 *   has pointers to download this chapter free.
 *
 * Copyright (c) Gene Cooperman, 2006; May be freely copied as long as this
 *   copyright notice remains.  There is no warranty.
 */

/* To know which "includes" to ask for, do 'man' on each system call used.
 * For example, "man fork" (or "man 2 fork" or man -s 2 fork") requires:
 *   <sys/types.h> and <unistd.h>
 */

#include <sys/types.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <stdio.h>    /* 'man fprintf' says we need this. */
#include <sys/wait.h> /* 'man waitpid' says we need this. */

#define MAXLINE 200  /* This is how we declare constants in C */
#define MAXARGS 20
#define PIPE_READ 0
#define PIPE_WRITE 1
/*
#define STDIN_FILENO    0       Standard input.  
#define STDOUT_FILENO   1       Standard output.  
#define STDERR_FILENO   2       Standard error output.  
*/

//Global variables used (their uses are explanatory)
char *fileInput = "";
char *fileOutput = "";
int hasPipe = 0;
int hasBackground = 0;


//Part 1: bugs fixed with each bug number labeled above the fix, below
//Part 2: added >, <, |, &, stdin/stdout redirection, background jobs support
//Much of execution function is based off of the file pipe-example.c which was given



/* In C, "static" means not visible outside of file.  This is different
 * from the usage of "static" in Java.
 * Note that end_ptr is an output parameter.
 */
static char * getword(char * begin, char **end_ptr) {
    char * end = begin;

    while ( *begin == ' ' )
        begin++;  /* Get rid of leading spaces. */
    end = begin;
    while ( *end != '\0' && *end != '\n' && *end != ' ' )
        end++;  /* Keep going. */
    if ( end == begin )
        return NULL;  /* if no more words, return NULL */
    *end = '\0';  /* else put string terminator at end of this word. */
    *end_ptr = end;
    if (begin[0] == '$') { /* if this is a variable to be expanded */
        begin = getenv(begin+1); /* begin+1, to skip past '$' */
	if (begin == NULL) {
	    perror("getenv");
	    begin = "UNDEFINED";
        }
    }
    return begin; /* This word is now a null-terminated string.  return it. */
}

/* In C, "int" is used instead of "bool", and "0" means false, any
 * non-zero number (traditionally "1") means true.
 */
/* argc is _count_ of args (*argcp == argc); argv is array of arg _values_*/
//Part 2 here
static void getargs(char cmd[], int *argcp, char *argv[])
{
    char *cmdp = cmd;
    char *end;
    int i = 0;
	int lengthOut = strlen(fileOutput);
	int lengthIn = strlen(fileInput);

    /* fgets creates null-terminated string. stdin is pre-defined C constant
     *   for standard intput.  feof(stdin) tests for file:end-of-file.
     */
    if (fgets(cmd, MAXLINE, stdin) == NULL && feof(stdin)) {
        printf("Couldn't read from standard input. End of file? Exiting ...\n");
        exit(1);  /* any non-zero value for exit means failure. */
    }
	//Bug #1
    while ( (cmdp = getword(cmdp, &end)) != NULL && *cmdp != '#') { /* end is output param */
		if (*cmdp == '|'){
			if(hasPipe == 0) {
				hasPipe = 1;
			}
			else {
				break;
			}
        }
        else if (*cmdp == '<'){
			if(lengthIn == 0) {
				cmdp = end + 1;
				fileInput = getword(cmdp, &end);
			}
			else {
				break;
			}
        }
        else if (*cmdp == '>'){
            if(lengthOut == 0) {
				cmdp = end + 1;
				fileOutput = getword(cmdp, &end);
			}
			else {
				break;
			}
        }
        else if (*cmdp == '&'){
			if(hasBackground == 0) {
				hasBackground = 1;
			}
			else {
				break;
			}
        }
        else {
            /* getword converts word into null-terminated string */
            argv[i++] = cmdp;
        }
        /* "end" brings us only to the '\0' at end of string */
        cmdp = end + 1;
    }
    argv[i] = NULL; /* Create additional null word at end for safety. */
    *argcp = i;
}

//Bug #3
void myhandler(int signum) {
	printf(" Process has been killed by the user\n");
}

//Part 2 cont.
static void execute(int argc, char *argv[])
{
	//pipefd[0] refers to the read end of the pipe.  pipefd[1] refers to the write end of the pipe.
    int pipe_fd[2];       /* 'man pipe' says its arg is this type */
    int fd;               /* 'man dup' says its arg is this type */
	//processor IDs
    pid_t child1, child2; /* 'man fork' says it returns type 'pid_t' */
	int lengthOut = strlen(fileOutput);
	int lengthIn = strlen(fileInput);
	
	//On success, zero is returned.  On error, -1 is returned
    if (hasPipe == 1 && pipe(pipe_fd) == -1) {
		perror("pipe"); 
    }
	
//-------------------------------------------------------------------------------
    child1 = fork();
	/* child1 > 0 implies that we're still the parent. */
    if (hasPipe == 1 && child1 > 0)
		//fork for pipe here
        child2 = fork();
	
	//childpid = 0 in child here
    if (child1 == 0) { /* if we are child1, do:  "ls | ..." */
		// for > 
        if (lengthOut > 0){
            close(STDOUT_FILENO);
            //open std output
			//write only, create if not exist, user has read/write permission
            fd = open(fileOutput, O_WRONLY | O_CREAT, S_IRWXU);
            if (fd == -1) 
				perror("error");
        }
		// for <
        else if (lengthIn > 0){
            close(STDIN_FILENO);
            //open std input
			//read only permission
            fd = open(fileInput, O_RDONLY);
            if (fd == -1) 
				perror("error");
        }
		// for |
        else if (hasPipe == 1) { /* if we are child1, do:  "ls | ..." */
			/* close  */
            if (close(STDOUT_FILENO) == -1) {
              perror("close");
            }
            fd = dup(pipe_fd[PIPE_WRITE]); /* set up empty STDOUT to be pipe_fd[1] */
            if (fd == -1) {
                perror("dup");
            }
            if (fd != STDOUT_FILENO) {
                fprintf(stderr, "Pipe output not at STDOUT.\n");
            }

            close(pipe_fd[PIPE_READ]); /* never used by child1 */
            close(pipe_fd[PIPE_WRITE]); /* not needed any more */

            argv[1] = NULL;
        }

        if (execvp(argv[0], argv) == -1) {
            perror("execvp");
        }
        
		
//-------------------------------------------------------------------------------
    } else if (child2 == 0 && hasPipe == 1) {
        /* close */
        if (close(STDIN_FILENO) -1) {
            perror("close");
        }

        /* set up empty STDIN to be pipe_fd[0] */
        fd = dup(pipe_fd[PIPE_READ]);
        if (fd == -1) {
            perror("dup");
        }

        if (fd != STDIN_FILENO) {
            fprintf(stderr, "Pipe input not at STDIN.\n");
        }

        close(pipe_fd[PIPE_READ]); /* not needed any more */
        close(pipe_fd[PIPE_WRITE]); /* never used by child2 */

        argv[0] = argv[1];
        argv[1] = NULL;
		
        if (execvp(argv[0], argv) == -1) {
            perror("execvp");
            printf("  Invalid command\n");
        }
//-------------------------------------------------------------------------------
    } else { /* else we're parent */
        int status;

        if (hasPipe == 1) {
			/* Close parent copy of pipes;
			* In particular, if pipe_fd[1] not closed, child2 will hang
			*   forever waiting since parent could also write to pipe_fd[1]
			*/
            close(pipe_fd[PIPE_READ]);
            close(pipe_fd[PIPE_WRITE]);
			
			if (waitpid(child1, &status, 0) == -1) {
				perror("waitpid");
			}

            /* Optionally, check return status.  This is what main() returns. */
            if (WIFEXITED(status) == 0) {
                printf("child1 returned w/ error code %d\n", WEXITSTATUS(status));
            }

            if (waitpid(child2, &status, 0) == -1) {
                perror("waitpid");
            }

            /* Optionally, check return status.  This is what main() returns. */
            if (WIFEXITED(status) == 0) {
                printf("child2 returned w/ error code %d\n", WEXITSTATUS(status));
            }
        }
    }
}

int main(int argc, char *argv[])
{
    char cmd[MAXLINE];
    char *childargv[MAXARGS];
    int childargc;
	pid_t backgroundPID;

	//Bug #2
    if (argc > 1) {
		freopen(argv[1], "r", stdin);
    }

    //Bug #3
    signal(SIGINT, myhandler);
	
    while (1) {
        printf("%% "); /* printf uses %d, %s, %x, etc.  See 'man 3 printf' */
        fflush(stdout); /* flush from output buffer to terminal itself */
        getargs(cmd, &childargc, childargv); /* childargc and childargv are
                output args; on input they have garbage, but getargs sets them. */

		//check for basic exit commands
        if ( childargc > 0 && strcmp(childargv[0], "exit") == 0 )
            exit(0);
        if ( childargc > 0 && strcmp(childargv[0], "logout") == 0 )
            exit(0);
		
		
		
		// check for background process first
        if (hasBackground == 1) {
			backgroundPID = fork();
			if (backgroundPID == 0) {
				// execute command on child
				execute(childargc, childargv);
				break;
			}
		}
		else {
			execute(childargc, childargv);
		}
		//reset global variables for next command
		fileOutput = "";
		fileInput = "";
		hasPipe = 0;
		hasBackground = 0;
    }
    /* NOT REACHED */
}