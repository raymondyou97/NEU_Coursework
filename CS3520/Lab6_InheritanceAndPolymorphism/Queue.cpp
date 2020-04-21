#include "Queue.hpp"

#include <iostream>
#include <cstddef>
#include <stdexcept>

Queue::Queue(int capacity) {
    this->m_size = 0;
    this->data = new int[capacity];
    this->capacity = capacity;
}

Queue::~Queue() {
    delete[] this->data;
}

void Queue::resize(int newCapacity) {
    throw "Not Supported";
}

void Queue::push_back(const int & element) {
    if (this->m_size == this->capacity) {
        throw std::out_of_range("Queue currently full");
    }
    this->data[this->m_size] = element;
    this->m_size++;
}

void Queue::push_front(const int & element) {
    throw "Not Supported";
}

void Queue::pop_back() {
    throw "Not Supported";
}

void Queue::pop_front() {
    if (this->m_size == 0) {
        throw std::out_of_range("Queue currently empty");
    }
    int data = this->data[0];

    for (int i = 1; i < this->m_size; i++) {
        this->data[i - 1] = this->data[i];
    }
    this->m_size--;
}

int Queue::front() const {
    if (this->m_size == 0) {
        throw std::out_of_range("Queue currently empty");
    }
    int data = this->data[0];
    
    return data;
}

int Queue::back() const {
    throw "Not Supported";
}

void Queue::insert(int pos, int elem) {
    throw "Not Supported";
}

void Queue::erase(int pos) {
    throw "Not Supported";
}

int Queue::size() const {
    return this->m_size;
}

int Queue::get(int pos) const {
    throw "Not Supported";
}
