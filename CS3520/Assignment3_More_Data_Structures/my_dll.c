#include "my_dll.h"
#include <stdio.h>
#include <stdlib.h>

// Creates a DLL
// Returns a pointer to a newly created DLL.
// The DLL should be initialized with data on the heap.
// (Think about what the means in terms of memory allocation)
// The DLLs fields should also be initialized to default values.
dll_t* create_dll() {
    dll_t* myDLinkedList = malloc(sizeof(dll_t));
    myDLinkedList->count = 0;
    myDLinkedList->head = NULL;
    myDLinkedList->tail = NULL;

    return myDLinkedList;
}

// DLL Empty
// Check if the DLL is empty
// Returns 1 if true (The DLL is completely empty)
// Returns 0 if false (the DLL has at least one element enqueued)
int dll_empty(dll_t* l) {
    // null list
    if (l == NULL) {
        return -1;
    // at least one element
    } else if (l->count > 0) {
        return 0;
    // empty list
    } else {
        return 1;
    }
}

// push a new item to the front of the DLL ( before the first node in the list).
// Returns a -1 if the operation fails ( and if the DLL is NULL), otherwise returns 1 on success.
// (i.e. the memory allocation for a new node failed).
int dll_push_front(dll_t* l, int item) {
    // null list
    if (l == NULL) {
        return -1;
    } else {
        node_t* node = malloc(sizeof(node_t));
        node->data = item;
        node->next = NULL;
        node->previous = NULL;
        
        //check if memory allocation failed
        if (node == NULL) {
            return -1;
        }

        // first node?
        if (dll_empty(l)) {
            l->head = node;
            l->tail = node;
        } else {
            // update current head's prev to new node
            node_t* currentHead = l->head;
            currentHead->previous = node;
            node->next = currentHead;
            
            // update new head to new node
            l->head = node;
        }
        l->count++;
        return 0;
    }
}

// push a new item to the end of the DLL (after the last node in the list).
// Returns a -1 if the operation failsm (and if the DLL is NULL), otherwise returns 1 on success.
// (i.e. the memory allocation for a new node failed).
int dll_push_back(dll_t* l, int item) {
    // null list
    if (l == NULL) {
        return -1;
    } else {
        node_t* node = malloc(sizeof(node_t));
        node->data = item;
        node->next = NULL;
        node->previous = NULL;
        
        //check if memory allocation failed
        if (node == NULL) {
            return -1;
        }

        // first node?
        if (dll_empty(l)) {
            l->head = node;
            l->tail = node;
        } else {
            // update current tails's next to new node
            node_t* currentTail = l->tail;
            currentTail->next = node;
            node->previous = currentTail;
            
            // update new tail to new node
            l->tail = node;
        }
        l->count++;
        return 0;
    }
}

// Returns the first item in the DLL and also removes it from the list.
// Returns a -1 if the operation fails (and if the DLL is NULL). Assume no negative numbers in the list.
int dll_pop_front(dll_t* t) {
    // null list
    if (t == NULL || dll_empty(t)) {
        return -1;
    } else {
        node_t* currentHead = t->head;
        int data = currentHead->data;

        // this is only node in list
        if (t->count == 1) {
            t->head = NULL;
            t->tail = NULL;
        }
        else {
            // get the new head
            node_t* newHead = currentHead->next;

            // update prev of new head
            newHead->previous = NULL;

            // set head to new head
            t->head = newHead;
        }
        t->count--;
        free(currentHead);
        return data;
    }
}

// Returns the last item in the DLL, and also removes it from the list.
// Returns a -1 if the operation fails (and if the DLL is NULL). Assume no negative numbers in the list.
int dll_pop_back(dll_t* t) {
    // null list
    if (t == NULL || dll_empty(t)) {
        return -1;
    } else {
        node_t* currentTail = t->tail;
        int data = currentTail->data;

        // this is only node in list
        if (t->count == 1) {
            t->head = NULL;
            t->tail = NULL;
        }
        else {
            // get the new tail
            node_t* newTail = currentTail->previous;

            // update next of new tail
            newTail->next = NULL;

            // set tail to new tail
            t->tail = newTail;
        }
        t->count--;
        free(currentTail);
        return data;
    }
}

// Inserts a new node before the node at the specified position.
// Returns a -1 if the operation fails (and if the DLL is NULL), otherwise returns 1 on success.
// (i.e. the memory allocation for a new node failed or trying to insert at a negative position or at 
//  a position past the size of the DLL ). Think testcases here.
int dll_insert(dll_t* l, int pos, int item) {
    // null test and edge cases
    if (l == NULL || (pos < 0 || pos >= l->count)) {
        return -1;
    } else if (pos == 0) {
        // front
        dll_push_front(l, item);
    } else if (pos == l->count - 1) {
        // back
        dll_push_back(l, item);
    } else {
        node_t* head = l->head;

        int i = 0;
        // get target
        while (i != pos) {
            head = head->next;
            i++;
       }

        // create new node
        node_t* node = malloc(sizeof(node_t));
        node->data = item;

        // update pointers for back nodes
        node_t* next = head->next;
        node->next = next;
        next->previous = node;
        // update pointers for front nodes
        head->next = node;
        node->previous = head;

        l->count++;
        return 0;
    }
}

// Returns the item at position pos starting at 0 ( 0 being the first item )
// Returns a -1 if the operation fails (and if the DLL is NULL). Assume no negative numbers are in the list.
// (i.e. trying to get at a negative position or at a position past the size of the DLL ). 
// Think testcases here.
int dll_get(dll_t* l, int pos) {
    // null test and edge cases
    if (l == NULL || dll_empty(l) || (pos < 0 || pos >= l->count)) {
        return -1;
    } else {
        node_t* head = l->head;

        int i = 0;
        // get target
        while (i != pos) {
            head = head->next;
            i++;
        }
        
        int data = head->data;
        return data;
    }
}

// Removes the item at position pos starting at 0 ( 0 being the first item )
// Returns a -1 if the operation fails (and if the DLL is NULL). 
// (i.e. trying to remove at a negative position or at a position past the size of the DLL ). 
// Think testcases here.
int dll_remove(dll_t* l, int pos) {
    // null test and edge cases
    if (l == NULL || (pos < 0 || pos >= l->count)) {
        return -1;
    } else if (pos == 0) {
        return dll_pop_front(l);
    } else if (pos == l->count-1) {
        return dll_pop_back(l);
    } else {
        node_t* head = l->head;

        int i = 0;
        // get target
        while (i != pos) {
            head = head->next;
            i++;
        }
        
        int data = head->data;
        node_t* next = head->next;
        node_t* prev = head->previous;

        if (next == NULL) {
            prev->next = NULL;
        } else {
            next->previous = prev;
            prev->next = next;
        }

        l->count--;
        free(head);
        return data;
    }
}

// DLL Size
// Queries the current size of a DLL
// A DLL that has not been previously created will crash the program.
// Returns -1 if the DLL is NULL.
int dll_size(dll_t* t) {
    // null check
    if (t == NULL) {
        return -1;
    } else {
        return t->count;
    }
}

// Free DLL
// Removes a DLL and ALL of its elements from memory.
// This should be called before the proram terminates.
void free_dll(dll_t* t) {
    // null check
    if (t == NULL) {
        return;
    } else {
        node_t* tempNode = NULL;

        // cleanup all nodes first
        while (t->head != NULL) {
            tempNode = t->head;
            t->head = t->head->next;
            free(tempNode);
        }
        // finally clean up data structure
        free(t);
    }
}

// Print out all the elements in the list in forwards direction
void forward_print(dll_t* t) {
    if (t == NULL) {
        printf("LIST IS NULL\n");
        return;
    }

    node_t* head = t->head;
    printf("Printing from head to tail.\n");
    while (head != NULL) {
        printf("%d ", head->data);
        head = head->next;
    }
    printf("\n");
    printf("DONE\n");
}

// Print out all the elements in the list in backwards direction
void backward_print(dll_t* t) {
    if (t == NULL) {
        printf("LIST IS NULL\n");
        return;
    }

    node_t* tail = t->tail;
    printf("Printing from tail to head.\n");
    while (tail != NULL) {
        printf("%d ", tail->data);
        tail = tail->previous;
    }
    printf("\n");
    printf("DONE\n");
}

