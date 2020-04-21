//
//  Q2.hpp
//  CS3520_Exam2_Q1
//
//  Created by Vidoje Mihajlovikj on 4/9/20.
//  Copyright © 2020 Vidoje Mihajlovikj. All rights reserved.
//

#ifndef Q2_hpp
#define Q2_hpp

#include <stdio.h>
#include <iostream>
#include <algorithm>

/*
 Design a SortedIterator that iterates through the elements of a vector in a sorted fashion, Here are some examples:

 Vector:{"Paul","Ringo","John","George","Freddie"}

 The SortedIterator should go over the elemtns in the following order:

 "Freddie", "George", "John", Paul", "Ringo"

 A Sample test is included for your reference.

 A partially completed class called SortedFilter has been provided for your reference.
 */

class SortedIterator {
private:
    std::vector<std::string> & container;
    int currentIndex;
public:
    SortedIterator(std::vector<std::string> & container, bool isEnd = false) : container(container) {
        this->currentIndex = 0;
        if (isEnd) {
            this->currentIndex = container.size();
        }
    }

    bool operator==(const SortedIterator & other) {
        if (&container != &other.container) {
            return false;
        }

        if (currentIndex >= container.size() && other.currentIndex >= other.container.size()) {
            return true;
        }

        return currentIndex == other.currentIndex;
    }

    bool operator!=(const SortedIterator & other) {
        return !(*this == other);
    }

    std::string operator*() const {
        if (currentIndex >= container.size()) {
            throw std::out_of_range("Invalid Index");
        }
        return container[currentIndex];
    }

    SortedIterator operator++(int) {
        SortedIterator temp = *this;
        this->currentIndex++;
        return temp;
    }

    SortedIterator & operator++() {
        this->currentIndex++;
        return *this;
    }
};

class SortedFilter {
private:
    std::vector<std::string> & container;
public:
    SortedFilter(std::vector<std::string> & vec) : container(vec) {
        std::sort(container.begin(), container.end());
    }

    SortedIterator begin() {
        SortedIterator iter(container);
        return iter;
    }

    SortedIterator end() {
        SortedIterator iter(container, true);
        return iter;
    }
};

#endif /* Q2_hpp */
