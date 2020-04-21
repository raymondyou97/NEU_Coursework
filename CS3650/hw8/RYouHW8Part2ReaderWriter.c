// Raymond You
// CS 3650 - Computer Systems
// HW8 Part 2

//GOAL:
//1. implement a solution for the reader-writer problem, using your implementation of condition variables. known as a reader-writer 
//	 problem with writers preferred. As before, you must implement it using condition variables
/*  Phase A:  ACQUIRE THE RIGHTS TO A RESOURCE
	    For example, acquire read permission on the master
		copy of a video on the Web.
            For example, acquire write permission on the master
		copy of a video on the Web.
	    OUTCOME:  Either we acquire permission immediately,
		or we have to wait for that permission.
		(This is similar to sem_wait() in the discussion
		 of producer-consumer using semaphores.)

  Phase B:  USE THE PERMISSION FOR AS LONG AS YOU NEED TO GET THE JOB DONE.
	    For example, stream the master copy of the video to
		your desktop.  It's also fine if two readers want
		to independently stream this video.
	    For example,.if you are a writer with _exclusive_ access,
		then over-write (edit) the master copy of the video at the
		server site with a new version, since you know that no
		one else is currently streaming the video.

  Phase C:  RELEASE THE RIGHTS TO A RESOURCE
	    For example, release read permission on the master
		copy of the video.
            For example, release write permission on the master
		copy of the video.
	    OUTCOME:  Release the permission immediately.
		In addition, signal to anybody who is waiting
		that the e-book might now be available.
		(This is similar to sem_post() in the discussion
		 of producer-consumer using semaphores.) 
*/

#include <semaphore.h>
#include <stdio.h>
#include <pthread.h>

//represent number of readers
int NumReaders = 0;
//represent number of writers
int NumWriters = 0;
//condition variables
pthread_cond_t empty, fill;
//monitor for phase A and C
pthread_mutex_t monitor_lock;

void *writer() {
	int count;
	for (count = 0; count < 100; count++) {
		//Phase A
		pthread_mutex_lock(&monitor_lock);
		while (NumWriters > 0 || NumReaders > 0) {
			//printf("test1");
			pthread_cond_wait(&fill, &monitor_lock);
			//printf("test2");
		}
		NumWriters++;
		pthread_mutex_unlock(&monitor_lock);

		//Phase B
		//Professor says doesn't matter if you actually write to something so print writing to indicate instead
		printf("WRITING!!!\n");

		//Phase C
		pthread_mutex_lock(&monitor_lock);
		NumWriters--;
		if (NumReaders == 0 && NumWriters > 0) {
			pthread_cond_signal(&empty);  // wake up a writer
		}
		pthread_mutex_unlock(&monitor_lock);
		
	}
}

void *reader() {
	int count;
	for (count = 0; count < 100; count++) {
		//Phase A
		pthread_mutex_lock(&monitor_lock);
		while (NumWriters > 0) {
			//printf("test1");
			pthread_cond_wait(&fill, &monitor_lock);
			//printf("test2");
		}
		NumReaders++;
		pthread_mutex_unlock(&monitor_lock);

		//Phase B
		//Professor says doesn't matter if you actually read something so print reading to indicate instead
		printf("READING!!!\n");

		//Phase C
		pthread_mutex_lock(&monitor_lock);
		NumReaders--;
		if (NumReaders == 0 && NumWriters > 0) {
			pthread_cond_signal(&empty);  // wake up a writer
		}
		pthread_mutex_unlock(&monitor_lock);
	}
}

int main() {
	//initialize two condition variables
	//producer threads wait on condition empty, and signals fill
	//consumer threads wait on condition fill and signal empty
	pthread_cond_init(&empty, NULL);
	pthread_cond_init(&fill, NULL);

	//threads for 4 readers and 4 writers
	pthread_t reader1;
	pthread_t reader2;
	pthread_t reader3;
	pthread_t reader4;
	pthread_t writer1;
	pthread_t writer2;
	pthread_t writer3;
	pthread_t writer4;
	
	//create the readers
	pthread_create(&reader1, NULL, reader, NULL);
	pthread_create(&reader2, NULL, reader, NULL);
	pthread_create(&reader3, NULL, reader, NULL);
	pthread_create(&reader4, NULL, reader, NULL);

	//create the writers
	pthread_create(&writer1, NULL, writer, NULL);
	pthread_create(&writer2, NULL, writer, NULL);
	pthread_create(&writer3, NULL, writer, NULL);
	pthread_create(&writer4, NULL, writer, NULL);

	//finish
	pthread_join(reader1, NULL);
	pthread_join(writer1, NULL);
	pthread_join(reader2, NULL);
	pthread_join(writer2, NULL);
	pthread_join(reader3, NULL);
	pthread_join(writer3, NULL);
	pthread_join(reader4, NULL);
	pthread_join(writer4, NULL);

	//exit
	return 0;
}
