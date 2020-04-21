#include "Vector.hpp"
#include <stdexcept>
#include <iostream>

Vector::Vector(int capacity) {
    if (capacity <= 0) {
        throw "Invalid capacity";
    }
    this->data = new int[capacity];
    this->capacity = capacity;
    this->m_size = 0;
}

Vector::~Vector() {
    delete[] this->data;
}

void Vector::resize(int newCapacity) {
    // create new array and copy everything over
    int * new_arr = new int[newCapacity];
    for (int i = 0; i < this->capacity; i++) {
        new_arr[i] = this->data[i];
    }

    delete[] this->data;
    this->data = new_arr;
    
    // update capacity
    this->capacity = newCapacity;
    std::cout << "RESIZING TO " << newCapacity << " COMPLETE" << std::endl;
}

void Vector::push_back(const int & element) {
    // if full, resize the vector
    if (this->m_size == this->capacity) {
        resize(2 * this->m_size);
    }
    this->data[this->m_size] = element;
    this->m_size++;
}

void Vector::push_front(const int & element) {
    // if full, resize the vector
    if (this->m_size == this->capacity) {
        resize(2 * this->m_size);
    }

    for (int i = this->capacity - 1; i != 0; i--) {
        this->data[i+1] = this->data[i];
    }
    this->data[0] = element;
    this->m_size++;
}

void Vector::pop_back() {
    if (this->m_size == 0) {
        throw std::out_of_range("Empty array");
    }
    this->data[this->m_size - 1] = 0;
    this->m_size--;
}

void Vector::pop_front() {
    if (this->m_size == 0) {
        throw std::out_of_range("Empty array");
    }

    for (int i = 0; i < this->m_size; i++) {
        this->data[i] = this->data[i+1];
    }
    this->m_size--;
}

int Vector::front() const {
    if (this->m_size == 0) {
        throw std::out_of_range("Empty array");
    }
    return this->data[0];
}

int Vector::back() const {
    if (this->m_size == 0) {
        throw std::out_of_range("Empty array");
    }
    return this->data[this->m_size-1];
}

void Vector::insert(int pos, int elem) {
    if (pos < 0 || pos >= this->capacity) {
        throw std::out_of_range("Position out of range");
    }

    if (this->m_size == this->capacity) {
        resize(2 * this->m_size);
    }

    // shift everything down 1 at position and after
    for (int i = this->m_size - 1; i >= pos; i--) {
        this->data[i + 1] = this->data[i];
    }
    this->data[pos] = elem;
    this->m_size++;
}

void Vector::erase(int pos) {
    if (pos >= this->m_size) {
        throw std::out_of_range("No element at specified position");
    }

    // shift everything down 1 at position and after
    for (int i = pos; i < this->m_size; i++) {
        this->data[i] = this->data[i + 1];
    }
    this->m_size--;   
}

int Vector::size() const {
    return this->m_size;
}

int Vector::get(int pos) const {
    return this->data[pos];
}
