// Compile this assignment with: gcc main.c -o main
//
// Include parts of the C Standard Library
// These have been written by some other really
// smart engineers.
#include <stdio.h>  // For IO operations
#include <stdlib.h> // for malloc/free
#include <assert.h> // For unit tests

// Our library that we have written.
// Also, by a really smart engineer!
#include "myqueue.h"
// Note that we are locating this file
// within the same directory, so we use quotations 
// and provide the path to this file which is within
// our current directory.


// Tests the null cases
void unitTest1(){
    // check all null cases
    queue_t* q = NULL;
    assert(q == NULL);
    assert(queue_enqueue(q, 1) == -1);
    assert(queue_dequeue(q) == -1);
    assert(queue_full(q) == -1 );
    assert(queue_empty(q) == -1);
    assert(queue_size(q) == -1);
}

// Tests creating queue,enqueuing until full, correct size, empty?, full?,
// and dequeuing too. Full code coverage of functions included.
void unitTest2() {
    // create queue with size 3
    queue_t* q = create_queue(3);
    assert(q != NULL);

    // ensure full empty and size are correct
    int full = queue_full(q);
    assert(full == 0);
    int empty = queue_empty(q);
    assert(empty == 1);
    int size = queue_size(q);
    assert(size == 0);

    // fill to max
    int val = queue_enqueue(q, 1);
    assert(val == 1);
    val = queue_enqueue(q, 2);
    assert(val == 1);
    val = queue_enqueue(q, 3);
    assert(val == 1);

    // cant add cuz full
    val = queue_enqueue(q, 123123);
    assert(val == 0);

    // check full empty and size again
    full = queue_full(q);
    assert(full == 1);
    empty = queue_empty(q);
    assert(empty == 0);
    size = queue_size(q);
    assert(size == 3);

    // remove till empty
    val = queue_dequeue(q);
    assert(val == 1);
    val = queue_dequeue(q);
    assert(val == 2);
    val = queue_dequeue(q);
    assert(val == 3);

    // cant add cuz empty
    val = queue_dequeue(q);
    assert(val == 0);

    // check full empty and size again
    full = queue_full(q);
    assert(full == 0);
    empty = queue_empty(q);
    assert(empty == 1);
    size = queue_size(q);
    assert(size == 0);

    // cleanup
    free_queue(q);
}

// test for too high capacity
void unitTest3() {
    queue_t* q = create_queue(0);
    assert(q == NULL);
}

// ====================================================
// ================== Program Entry ===================
// ====================================================
int main(){
    // List of Unit Tests to test your data structure	
    unitTest1();
    printf("Unit Test 1 Passed.\n");
    unitTest2();
    printf("Unit Test 2 Passed.\n");
    unitTest3();
    printf("Unit Test 3 Passed.\n");

    printf("All unit tests passed!\n");

    return 0;
}
