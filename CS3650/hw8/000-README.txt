			    Homework 8
			DUE:  Tuesday, Mar. 27

The goal of this homework is to write your own implementation
of condition variables.  You must test your implementation
on the producer-consumer problem, below.  Then, you must also
write your own solution of the reader-writer problem (writers preferred)
using your implementation of condition variables.  Please read on
for the details.

Note that I also include here a file, reader-writer.txt, to help
provide further background on the reader-writer problem.
Similarly, I have provided a file, condition-variables.txt, to help
provide further background on the implementation of condition variables.

Chapter 30 of the online text, ostep.org, has a solution
in Figure 30.12 for the producer-consumer problem using pthread_cond_wait,
pthread_cond_signal, and pthread_mutex_lock/unlock.  That solution
is reproduced at the end of this file, so that you can use it.

So, Figure 30.12 from ostep.org solves the producer-consumer problem using
condition variables.
Note also that Figure 31.16 (Chapter 31) implements semaphores
using condition variables.

Your job is to write an implementation of pthread_cond_wait(),
pthread_cond_signal(), and pthread_cond_init() in terms of
sem_init(), sem_wait(), sem_post(), and possibly pthread_mutex_lock/unlock.

Chapter 31 of ostep.org also notes at the end that "building locks and
condition variables out of semaphores is a much trickier proposition."
That's your job!

Specifically, you may use pthread_mutex_lock/unlock, sem_init(), sem_wait(),
and sem_post().  You must write your own implementation of functions:

Pthread_cond_t, Pthread_cond_signal(), and Pthread_cond_wait().
The signatures for Pthread_cond_signal() and Pthread_cond_wait()
should be the same as for pthread_cond_signal() and pthread_cond_wait().
We use the capitalized version so that your implementation of these
functions doesn't see any interference from the built-in version in
libpthread.so.

Your implementation of pthread_cond_wait/signal should also be
efficient.  In particular, your implementation should avoid
busy waiting, and it should avoid unnecessary spurious wakeups.
In the file "condition-variables.txt", there is a discussion
of "busy waiting" and "spurious wakeups" and techniques
to avoid them.

**************************************************************************
**** If your implementation does use busy waiting or spurious wakeups,
**** you will still receive generous partial credit.  If efficiency is
**** the only problem in your implementation, then your grade will still
**** be in the 90s.  But you must solve these issues in order to get 100.
**************************************************************************

When you are ready, you can test your implementation by combining
it with the solution for producer-consumer at the end of this
section.  Don't forget to add a main() routine with pthread_create()
and pthread() join.  You must have at least four producers and
four consumers in your test.  So, you will need to call pthread_create()
eight times from main().

Finally, once you are convinced that your implementation of
condition variables works, you must then implement a solution
for the reader-writer problem, using your implementation of condition
variables.  Note that Wikipedia has a solution for reader-writer
with readers preferred:
  https://en.wikipedia.org/wiki/Readers%E2%80%93writers_problem
But that implementation uses semaphores instead of condition variables.
You should implement the _second_ reader-writer problem:
  https://en.wikipedia.org/wiki/Readers%E2%80%93writers_problem#Second_readers-writers_problem

This variation is known as a reader-writer problem with writers preferred.
As before, you must implement it using condition variables.

Note that you are _not_ allowed to copy reader-writer solutions
from the Internet.  You must write your own reader-writer solution.
Please don't make me google for subexpressions in your solution.  :-)

Good luck.

=============================================================================
Figure 30.11 from ostep.org:
  Solving the producer-consumer problem using condition variables,
    an implementation of the "monitor" abstraction for thread concurrency.

// NOTE:  You must still write a main routine for this.  The constants
//        MAX and loops were chosen arbitrarily, and can be changed.
//        Your code must work for large values for these constants.
// NOTE:  Don't forget that you will compile this using:
//          gcc THIS_FILE -lpthread  # -lpthread means
//           "libpthread.a" (if -static is used), or "libpthread.so" (default)
//          OR THE SHORTER VERSION:  gcc THIS_FILE -pthread

#include <stdio.h>
#include <pthread.h>

#define MAX 20  /* Change this constant to suit your testing. */

int buffer[MAX];
int fill_ptr = 0;
int use_ptr  = 0;
int count    = 0;

void put(int value) {
  buffer[fill_ptr] = value;
  fill_ptr = (fill_ptr + 1) % MAX;
  count++;
}

int get() {
  int tmp = buffer[use_ptr];
  use_ptr = (use_ptr + 1) % MAX;
  count--;
  return tmp;
}

// =======================================
// NOTE: You can uncomment the three defines below and write a main()
//       routine, and this program should work for you.  You will
//       also want to call pthread_init from inside your main().  Your job
//       is to implement your own Pthread_cond_t, Pthread_cond_signal,
//       and Pthread_cond_wait, instead of defining them to be the
//       system version.

/*
#define Pthread_cond_t pthread_cond_t
#define Pthread_cond_signal pthread_cond_signal
#define Pthread_cond_wait pthread_cond_wait
*/

Pthread_cond_t empty, fill;  /* Modified from original */
pthread_mutex_t mutex;       /* Modified from original */
const int loops = 100;       /* Added; not in ostep.org original */

void *producer(void * arg) {
  int i;
  for (i = 0; i < loops; i++) {
    pthread_mutex_lock(&mutex);            // p1
    while (count == MAX)                   // p2
      Pthread_cond_wait(&empty, &mutex);   // p3
    put(i);                                // p4
    Pthread_cond_signal(&fill);            // p5
    pthread_mutex_unlock(&mutex);          // p6
  }
}

void * consumer(void * arg) {
  int i;
  for (i = 0; i < loops; i++) {
    pthread_mutex_lock(&mutex);            // c1
    while (count == 0)                     // c2
      Pthread_cond_wait(&fill, &mutex);    // c3
    int tmp = get();                       // c4
    Pthread_cond_signal(&empty);           // c5
    pthread_mutex_unlock(&mutex);          // c6
    printf("%d\n", tmp);
  }
}
