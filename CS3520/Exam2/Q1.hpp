//
//  Q1.hpp
//  CS3520_Exam2_Q1
//
//  Created by Vidoje Mihajlovikj on 4/9/20.
//  Copyright © 2020 Vidoje Mihajlovikj. All rights reserved.
//

#ifndef Q1_hpp
#define Q1_hpp

#include <iostream>
#include <stdio.h>

/*
 Design a BackAndForthIterator that iterates through the elements of a vector in a back-and-forth fashion, starting from the first element, then going to the last, then moving to the second, then going to the one before the last one. Here are some examples:

 Vector:{"Paul","Ringo","John","George","Freddie"}

 The BackAndForthIterator should go over the elemtns in the following order:

 "Paul", "Freddie", "Ringo", George", "John"

 A Sample test is included for your reference.

 A partially completed class called BackAndForthFilter has been provided for your reference.
 */

class BackAndForthIterator {
private:
    std::vector<std::string> & container;
    int count;
    int size;
    bool nextFront;
    void advance() {
        if (this->nextFront) {
            this->container.erase(this->container.begin());
        } else {
            this->container.pop_back();
        }
        this->count++;
        this->nextFront = !this->nextFront;
    }
public:
    BackAndForthIterator(std::vector<std::string> & container, bool isEnd = false) : container(container) {
        this->size = container.size();
        this->nextFront = true;
        if (isEnd)
            this->count = container.size();
        else
            this->count = 0;
    }

    bool operator==(const BackAndForthIterator & other) {
        if (&container != &other.container || size != other.size) {
            return false;
        }

        return count == other.count;
    }

    bool operator!=(const BackAndForthIterator & other) {
        return !(*this == other);
    }

    std::string operator*() const {
        if (this->container.size() == 0) {
            throw std::out_of_range("Invalid range for iterator");
        }

        std::string next;
        if (nextFront) {
            next = container.front();
        } else {
            next = container.back();
        }
        return next;
    }

    BackAndForthIterator operator++(int) {
        BackAndForthIterator temp = *this;
        advance();
        return temp;
    }

    BackAndForthIterator & operator++() {
        advance();
        return *this;
    }
};

class BackAndForthFilter {
private:
    std::vector<std::string> & container;
public:
    BackAndForthFilter(std::vector<std::string> & vec) : container(vec) {}

    BackAndForthIterator begin() {
        BackAndForthIterator iter(container);
        return iter;
    }

    BackAndForthIterator end() {
        BackAndForthIterator iter(container, true);
        return iter;
    }
};

#endif /* Q1_hpp */
