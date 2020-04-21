//
//  Vector.hpp
//  Vector
//
//  Created by Vidoje Mihajlovikj on 1/27/20.
//  Copyright © 2020 Vidoje Mihajlovikj. All rights reserved.
//

#ifndef Vector_hpp
#define Vector_hpp

#include <iostream>

class Vector{
private:
    int * data;
    int capacity;
    int m_size;
    void resize(int newCapacity);
public:
    //NOTE: do not make shallow copies of the data.
    
    //Constructor
    Vector(int initialCapacity);
    //Destructor
    ~Vector();
    //Copy Consturctor, do not make a shallow copy.
    Vector(const Vector & other);
    //= operator, do not make a shallow copy.
    Vector & operator=(const Vector & other);
    //== operator, does an elementwise comparison
    bool operator==(const Vector & other) const;
    //Adds element to the end of the vector.
    void push_back(const int & element);
    //Adds element to the front of the vector.
    void push_front(const int & element);
    //Removes the last element, throws std::std::out_of_range on error
    void pop_back();
    //Removes the first element, throws std::std::out_of_range on error
    void pop_front();
    //Returns ( does not remove ) the first element, throws std::std::out_of_range on error
    int front() const;
     //Returns ( does not remove ) the last element, throws std::std::out_of_range on error
    int back() const;
    //Inserts an int at the specified position, throws std::std::out_of_range on error
    void insert(int pos, int elem);
    //Removes the element at the specified position, throws std::std::out_of_range on error
    void erase(int pos);
    //Returns the size
    int size() const;
    //Returns the ith element
    int get(int pos) const;
    
};
//Prints all the elements of the vector to the stream.
std::ostream & operator<<(std::ostream & out, const Vector & other);
#endif /* Vector_hpp */
