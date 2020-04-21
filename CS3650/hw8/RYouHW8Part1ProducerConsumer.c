// Raymond You
// CS 3650 - Computer Systems
// HW8 Part 1

//Separated the two parts of HW8 into two programs for easier visibility and management: RYouHW8ProducerConsumer.c and RYouHW8ReaderWriter.c
//Run separately with 
//	gcc RYouHW8Part1ProducerConsumer.c -pthread 
//	./a.out
//and
//	gcc RYouHW8Part2ReaderWriter.c -pthread
//	./a.out


//GOAL:
//1. write an implementation of pthread_cond_wait(), pthread_cond_signal(), and pthread_cond_init() in terms of
//   sem_init(), sem_wait(), sem_post(), and possibly pthread_mutex_lock/unlock. 
//2. test your implementation by combining it with the solution for producer-consumer at the end of this section.  
//   Don't forget to add a main() routine with pthread_create() and pthread() join.  You must have at least four 
//   producers and four consumers in your test.  So, you will need to call pthread_create() eight times from main().


#include <semaphore.h>
#include <stdio.h>
#include <pthread.h>
#define MAX 20  /* Change this constant to suit your testing. */

typedef struct Pthread_cond_t {
	sem_t semaphore;
} Pthread_cond_t;

//implementation of pthread_cond_init
void Pthread_cond_init(Pthread_cond_t *condition) {
	//initialize semaphore with value 0
	sem_init(&(condition->semaphore), 0, 0);
}

//implementation of pthread_cond_wait
void Pthread_cond_wait(Pthread_cond_t *condition, pthread_mutex_t *mutex) {
	pthread_mutex_unlock(mutex);
	
	/*sem_wait() decrements (locks) the semaphore pointed to by sem.  If
    the semaphore's value is greater than zero, then the decrement
    proceeds, and the function returns, immediately.  If the semaphore
    currently has the value zero, then the call blocks until either it
    becomes possible to perform the decrement (i.e., the semaphore value
    rises above zero), or a signal handler interrupts the call.*/
	sem_wait(&(condition->semaphore));
	pthread_mutex_lock(mutex);
}

//implementation of pthread_cond_signal
void Pthread_cond_signal(Pthread_cond_t *condition) {
	//unlock semaphore
	sem_post(&(condition->semaphore));
}

//given--------------------------------------------------------------------------------------------------


int done = 0;

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
//--------------------------------------------------------------------------------------------------

int main() {
	//initialize two condition variables
	//producer threads wait on condition empty, and signals fill
	//consumer threads wait on condition fill and signal empty
	Pthread_cond_init(&empty);
	Pthread_cond_init(&fill);

	//threads for 4 producers and 4 consumers
	pthread_t producer1;
	pthread_t producer2;
	pthread_t producer3;
	pthread_t producer4;
	pthread_t consumer1;
	pthread_t consumer2;
	pthread_t consumer3;
	pthread_t consumer4;

	//create producers
	pthread_create(&producer1, NULL, producer, NULL);
	pthread_create(&producer2, NULL, producer, NULL);
	pthread_create(&producer3, NULL, producer, NULL);
	pthread_create(&producer4, NULL, producer, NULL);

	//create consumers
	pthread_create(&consumer1, NULL, consumer, NULL);
	pthread_create(&consumer2, NULL, consumer, NULL);
	pthread_create(&consumer3, NULL, consumer, NULL);
	pthread_create(&consumer4, NULL, consumer, NULL);

	//finish
	pthread_join(producer1, NULL);
	pthread_join(consumer1, NULL);
	pthread_join(producer2, NULL);
	pthread_join(consumer2, NULL);
	pthread_join(producer3, NULL);
	pthread_join(consumer3, NULL);
	pthread_join(producer4, NULL);
	pthread_join(consumer4, NULL);

	//exit
	return 0;
}