#include "myqueue.hpp"

#include <iostream>
#include <cstddef>
#include <stdexcept>

Queue::Queue(int capacity) {
    this->size = 0;
    this->data = new int[capacity];
    this->capacity = capacity;
 }

Queue::~Queue() {
    delete[] this->data;
}

bool Queue::queue_empty() {
    return this->size == 0;
}

bool Queue::queue_full() {
    return this->size == this->capacity;
}

void Queue::queue_enqueue(int item) {
    if (queue_full()) {
        throw std::out_of_range("Queue currently full");
    }
    this->data[this->size] = item;
    this->size++;
}

int Queue::queue_dequeue() {
    if (queue_empty()) {
        throw std::out_of_range("Queue currently empty");
    }
    int data = this->data[0];

    for (int i = 1; i < this->size; i++) {
        this->data[i - 1] = this->data[i];
    }
    this->size--;
    return data;
}

int Queue::queue_size() {
    return this->size;
}

int Queue::get(int i) {
    return this->data[i];
}

std::ostream& operator<<(std::ostream & out, Queue & other) {
    for (int i = 0; i < other.queue_size(); i++) {
        out << other.get(i) << ' ';
    }
    return out;
}

