#include "Stack.hpp"
#include "Node.hpp"
#include <stdexcept>
#include <iostream>

Stack::Stack(int capacity) {
    this->count = 0;
    this->capacity = capacity;

    Node* head = new Node;
    head->next = NULL;
    this->head = head;
}

Stack::~Stack() {
    Node* temp_node = NULL;
    while (this->head != NULL) {
        temp_node = this->head;
        this->head = this->head->next;
        delete(temp_node);
    }
}

void Stack::resize(int newCapacity) {
    throw "Not Supported";
}

void Stack::push_back(const int & element) {
    if (this->count == this->capacity) {
        throw std::out_of_range("Stack full");
    } else {
        Node * newNode = new Node;
        newNode->data = element;

        Node * prevTop = this->head->next;
        newNode->next = prevTop;

        this->head->next = newNode;

        this->count++;
    }
}

void Stack::push_front(const int & element) {
    throw "Not Supported";
}

void Stack::pop_back() {
    if (this->count == 0) {
        throw std::out_of_range("Stack empty");
    } else {
        Node * n = this->head->next;
        int data = n->data;

        this->head->next = n->next;

        this->count--;
        delete n;
    }
}

void Stack::pop_front() {
    throw "Not Supported";
}

int Stack::front() const {
    throw "Not Supported";
}

int Stack::back() const {
    Node * n = this->head->next;
    int data = n->data;

    return data;
}

void Stack::insert(int pos, int elem) {
    throw "Not Supported";
}

void Stack::erase(int pos) {
    throw "Not Supported";
}

int Stack::size() const {
    return this->count;
}

int Stack::get(int pos) const {
    throw "Not Supported";
}