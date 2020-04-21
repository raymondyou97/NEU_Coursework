#include "mystack.hpp"

#include <iostream>
#include <cstddef>
#include <stdexcept>

Stack::Stack(int capacity) {
    this->count = 0;
    this->capacity = capacity;

    node_t* head = new node_t;
    head->next = NULL;
    this->head = head;
}

Stack::~Stack() {
    node_t* temp_node = NULL;
    while (this->head != NULL) {
        temp_node = this->head;
        this->head = this->head->next;
        delete(temp_node);
    }
}

bool Stack::stack_empty() {
    return this->count == 0;
}

bool Stack::stack_full() {
    return this->count == this->capacity;
}

void Stack::stack_enqueue(int item) {
    if (stack_full()) {
        throw std::out_of_range("Stack full");
    } else {
        node_t* newNode = new node_t;
        newNode->data = item;

        node_t * prevTop = this->head->next;
        newNode->next = prevTop;

        this->head->next = newNode;

        this->count++;
    }
}

int Stack::stack_dequeue() {
    if (stack_empty()) {
        throw std::out_of_range("Stack empty");
    } else {
        node_t * n = this->head->next;
        int data = n->data;

        this->head->next = n->next;

        this->count--;
        delete n;

        return data;
    }
}

int Stack::stack_size() {
    return this->count;
}

