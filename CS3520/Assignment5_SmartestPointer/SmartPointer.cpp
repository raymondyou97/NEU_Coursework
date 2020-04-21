#include "SmartPointer.hpp"
#include <exception>
#include <stdexcept>
#include <iostream>
#include <map>
#include <iterator> 

std::map<Rectangle *, int> SmartRectanglePointer::table;

SmartRectanglePointer::SmartRectanglePointer(Rectangle * ptr) {
    if ( ptr == NULL ){
        throw std::invalid_argument("Cannot point to NULL pointer");
    }
    this->data = ptr;
    this->counter = new int(1);

    // find if pointer already exists. Increment if exists, else set to 1
    std::map<Rectangle *, int>::iterator itr = this->table.find(ptr);
    if (itr != this->table.end()) {
        // delete counter and create new counter with new count
        delete this->counter;
        itr->second++;
        this->counter = new int(itr->second);
        std::cout << "Key for " << this->data->getId() << " found. Updating count to " << itr->second << "." << std::endl;
    } 
    else {
        this->table.insert({ptr, 1});
        std::cout << "Key for " << this->data->getId() << " not found. Setting count to 1." << std::endl;
    }
}

SmartRectanglePointer::SmartRectanglePointer(const SmartRectanglePointer & other) {
    this->data = other.data;
    this->table = other.table;
}

//implement operator* to mimic an actual pointer.
Rectangle & SmartRectanglePointer::operator*() {
    return *this->data;
}

//implement operator& to mimic an actual pointer.
Rectangle * SmartRectanglePointer::operator->() {
    return this->data;
}

SmartRectanglePointer::~SmartRectanglePointer() {
    std::map<Rectangle *, int>::iterator itr = this->table.find(this->data);
    if (itr != this->table.end()) {
        itr->second--;
        std::cout << "Destroying smart pointer with key for " << this->data->getId() << ". Decrementing count to " << itr->second << "." << std::endl;
        if (itr->second == 0) {
            std::cout << "Smart pointer with key for " << this->data->getId() << " has count 0. Destroying rectangle." << std::endl;
            this->table.erase(this->data);
            delete this->data;
        }
    }
    delete this->counter;
    std::cout << "Destroying smart pointer complete." << std::endl;
}

void SmartRectanglePointer::reset(Rectangle * ptr) {
    // can't reset to the same existing ptr
    if (ptr == this->data) {
        throw std::logic_error("Can't reset to the same existing rectangle ptr.");
    }

    // cleanup old pointer count first
    std::map<Rectangle *, int>::iterator itr = this->table.find(this->data);
    if (itr != this->table.end()) {
        itr->second--;
        std::cout << "Resetting smart pointer. First, decrement old key for " << this->data->getId() << " to " << itr->second << "." << std::endl;
        if (itr->second == 0) {
            std::cout << "Smart pointer with key for " << this->data->getId() << " has count 0. Destroying rectangle." << std::endl;
            this->table.erase(this->data);
            delete this->data;
        }
        delete this->counter;
    }
    this->counter = new int(1);
    // set to new rectangle and update count accordingly
    this->data = ptr;
    itr = this->table.find(ptr);
    if (itr != this->table.end()) {
        itr->second++;
        // delete counter and create new counter with new count
        delete this->counter;
        this->counter = new int(itr->second);
        std::cout << "Key for " << this->data->getId() << " found. Updating count to " << itr->second << "." << std::endl;
    } 
    else {
        this->table.insert({ptr, 1});
        std::cout << "Key for " << this->data->getId() << " not found. Setting count to 1." << std::endl;
    }
}
