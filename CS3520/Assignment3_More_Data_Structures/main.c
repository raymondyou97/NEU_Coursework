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
#include "my_dll.h"
// Note that we are locating this file
// within the same directory, so we use quotations
// and provide the path to this file which is within
// our current directory.



// ====================================================
// ================== Program Entry ===================
// ====================================================

// Test all functions work as expected
void unitTest1() {
    printf("\nSTART TEST 1\n");
    dll_t* dll = create_dll();

    assert(dll != NULL);
    assert(dll_empty(dll) == 1);
    assert(dll_size(dll) == 0);

    dll_push_front(dll, 1);
    dll_push_front(dll, 2);
    dll_push_front(dll, 3);
    forward_print(dll); // should print 3 2 1
    backward_print(dll); // should print 1 2 3

    dll_push_back(dll, 100);
    dll_push_back(dll, 200);
    dll_push_back(dll, 300);
    forward_print(dll); // should print 3 2 1 100 200 300
    backward_print(dll); // should print 300 200 100 1 2 3 

    int temp = dll_pop_front(dll);
    assert(temp == 3);
    assert(dll_empty(dll) == 0);
    assert(dll_size(dll) == 5);
    temp = dll_pop_back(dll);
    assert(temp == 300);
    assert(dll_size(dll) == 4);
    forward_print(dll); // should print 2 1 100 200
    backward_print(dll); // should print 200 100 1 2

    int size = dll_size(dll);
    dll_insert(dll, size-1, 9999);
    dll_insert(dll, 0, 99);
    dll_insert(dll, 2, 999);
    forward_print(dll); // should print 99 2 1 999 100 200 9999
    backward_print(dll); // should print 9999 200 100 999 1 2 99
    
    temp = dll_get(dll, 0);
    assert(temp == 99);
    temp = dll_get(dll, dll_size(dll)-1);
    assert(temp == 9999);

    temp = dll_remove(dll, 0);
    assert(temp == 99);
    temp = dll_remove(dll, dll_size(dll)-1);
    assert(temp == 9999);
    forward_print(dll); // should print 2 1 99 100 200
    backward_print(dll); // should print 200 100 999 1 2

    // empty the list
    dll_remove(dll, 0);
    dll_remove(dll, 0);
    dll_remove(dll, 0);
    dll_remove(dll, 0);
    dll_remove(dll, 0);

    assert(dll_size(dll) == 0);
    forward_print(dll);
    backward_print(dll);

    free_dll(dll);
}

// Test all functions fail properly when null
void unitTest2() {
    printf("\nSTART TEST 2\n");
    dll_t* dll = NULL;
    assert(dll_empty(dll) == -1);
    assert(dll_push_front(dll, 1) == -1);
    assert(dll_push_back(dll, 1) == -1);
    assert(dll_pop_front(dll) == -1);
    assert(dll_pop_back(dll) == -1);
    assert(dll_insert(dll, 0, 0) == -1);
    assert(dll_get(dll, 0) == -1);
    assert(dll_remove(dll, 0) == -1);
    assert(dll_size(dll) == -1);
    forward_print(dll);
    backward_print(dll);
    free_dll(dll);
}

// Test all other edge cases
void unitTest3() {
    printf("\nSTART TEST 3\n");
    dll_t* dll = create_dll();
    assert(dll_empty(dll) == 1);
    dll_push_front(dll, 1);
    assert(dll->head == dll->tail);
    dll_push_back(dll, 2);
    assert(dll->head != dll->tail);
    forward_print(dll);
    backward_print(dll);
    free_dll(dll);
}

int main() {
    unitTest1();
    unitTest2();
    unitTest3();
}

