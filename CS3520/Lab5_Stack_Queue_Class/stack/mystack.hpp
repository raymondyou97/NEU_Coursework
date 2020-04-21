#ifndef MYSTACK_H
#define MYSTACK_H

#include <iostream>

typedef struct node {
    int data;
    struct node* next;
}node_t;

class Stack {
    private:
        int count;
        int capacity;
        node_t * head;

    public:
        Stack(int capacity);
        ~Stack();
        bool stack_empty();
        bool stack_full();
        void stack_enqueue(int item);
        int stack_dequeue();
        int stack_size();
};

#endif
