#include "Vector.hpp"
#include <stdexcept>

Vector::Vector(int initialCapacity) {
    this->data = new int[initialCapacity];
    this->capacity = initialCapacity;
    this->m_size = 0;
    //Continue implementation.
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

//= operator, do not make a shallow copy.
Vector & Vector::operator=(const Vector & other) {
    if (this == &other) {
        return *this;
    }

    // clean up in case
    delete[] data;
    m_size = other.m_size;
    capacity = other.capacity;
    // copy data over if exists
    if (other.data) {
        data = new int[other.capacity];
        for (int i = 0; i < m_size; i++) {
            data[i] = other.data[i];
        }
    }
    else {
        data = NULL;
    }

    return *this;
}

//== operator, does an elementwise comparison
bool Vector::operator==(const Vector & other) const {
    if (m_size != other.m_size || capacity != other.capacity) {
        return false;
    }

    for (int i = 0; i < m_size; i++) {
        if (data[i] != other.data[i]) {
            return false;
        }
    }
    return true;
}

//Adds element to the end of the vector.
void Vector::push_back(const int & element) {
    // if full, resize the vector
    if (this->m_size == this->capacity) {
        resize(2 * this->m_size);
    }
    this->data[this->m_size] = element;
    this->m_size++;
}

//Adds element to the front of the vector.
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

//Removes the last element, throws std::std::out_of_range on error
void Vector::pop_back() {
    if (this->m_size == 0) {
        throw std::out_of_range("Empty array");
    }
    this->data[this->m_size - 1] = 0;
    this->m_size--;
}

//Removes the first element, throws std::std::out_of_range on error
void Vector::pop_front() {
    if (this->m_size == 0) {
        throw std::out_of_range("Empty array");
    }

    for (int i = 0; i < this->m_size; i++) {
        this->data[i] = this->data[i+1];
    }
    this->m_size--;
}

//Returns ( does not remove ) the first element, throws std::std::out_of_range on error
int Vector::front() const {
    if (this->m_size == 0) {
        throw std::out_of_range("Empty array");
    }
    return this->data[0];
}

 //Returns ( does not remove ) the last element, throws std::std::out_of_range on error
int Vector::back() const {
    if (this->m_size == 0) {
        throw std::out_of_range("Empty array");
    }
    return this->data[this->m_size-1];
}

//Inserts an int at the specified position, throws std::std::out_of_range on error
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

//Removes the element at the specified position, throws std::std::out_of_range on error
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

//Returns the size
int Vector::size() const {
    return this->m_size;
}

//Returns the ith element
int Vector::get(int pos) const {
    return this->data[pos];
}

std::ostream& operator<<(std::ostream & out, const Vector & other) {
    for (int i = 0; i < other.size(); i++) {
        out << other.get(i) << ' ';
    }
    return out;
}

