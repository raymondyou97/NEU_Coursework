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
#include "mystack.h"
// Note that we are locating this file
// within the same directory, so we use quotations 
// and provide the path to this file which is within
// our current directory.


// Tests for adding and removing, empty, full
void unitTest1() {
    stack_t* test1 = create_stack(3);
    
    // ensure empty and full correct
    int empty = stack_empty(test1);
    assert(empty == 1);
    int full = stack_full(test1);
    assert(full == 0);

    // add until full
    int success = stack_enqueue(test1, 1);
    assert(success == 1);
    success = stack_enqueue(test1, 2);
    assert(success == 1);
    success = stack_enqueue(test1, 3);
    assert(success == 1);

    // cant add anymore as full
    success = stack_enqueue(test1, 100);
    assert(success == 0);

    // ensure full correct
    full = stack_full(test1);
    assert(full == 1);

    // remove until empty
    int val = stack_dequeue(test1);
    assert(val == 3);
    val = stack_dequeue(test1);
    assert(val == 2);
    val = stack_dequeue(test1);
    assert(val == 1);

    // cant remove anymore as empty
    val = stack_dequeue(test1);
    assert(val == 0);
    // ensure empty still correct
    empty = stack_empty(test1);
    assert(empty == 1);

    // cleanup
    free_stack(test1);
}

// Tests for null cases
void unitTest2() {
    stack_t* s = NULL;
    int n = stack_empty(s);
    n = stack_full(s);
    assert(n == -1);
    n = stack_enqueue(s, 123);
    assert(n == -1);
    n = stack_dequeue(s);
    assert(n == -1);
    n = stack_size(s);
    assert(n == -1);
}

// Test for too large size stack
void unitTest3() {
    stack_t* s = create_stack(10000000);
    assert(s == NULL);
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
