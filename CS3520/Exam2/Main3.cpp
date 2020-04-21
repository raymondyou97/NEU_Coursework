//
//  main.cpp
//  CS3520_Exam2_Q1
//
//  Created by Vidoje Mihajlovikj on 4/9/20.
//  Copyright © 2020 Vidoje Mihajlovikj. All rights reserved.

#include <iostream>
#include <vector>
#include <list>
#include <sstream>
#include "Q3.hpp"


void assertEquals(int expected, int actual, std::string testName) {
    if (expected == actual) {
        std::cout << "Pass: " << testName << std::endl;
    }else {
        std::cout << "Failed: " << testName << std::endl;
        std::cout << "Expected: " << expected << std::endl;
        std::cout << "Actual: " << actual << std::endl;
    }
    std::cout << "-----------------------------------" << std::endl;
}

void testQ3(std::vector<int> vec1, std::list<int> list, int diff) {
    int numSame = intersection(vec1.begin(), vec1.end(), list.begin(), list.end());
    assertEquals(diff, numSame, __FUNCTION__ );
}

void testMoreQ3(std::set<int> list1, std::vector<int> list2, int diff) {
    int numSame = intersection(list1.begin(), list1.end(), list2.begin(), list2.end());
    assertEquals(diff, numSame, __FUNCTION__ );
}

int main(int argc, const char * argv[]) {
    testQ3({1,2,3,4,5,6,7,8,9,10}, {0,2,4,6,13,15}, 3);
    testQ3({1,2,3,4,5,6,7,8,9,10}, {}, 0);
    testQ3({}, {0,2,4,6,13,15}, 0);
    testQ3({1, 2}, {1, 2}, 2);
    testQ3({}, {}, 0);
    testMoreQ3({1,2,3,4,5,6,7,8,9,10}, {0,2,4,6,13,15}, 3);
    testMoreQ3({1,2,3,4,5,6,7,8,9,10}, {}, 0);
    testMoreQ3({}, {0,2,4,6,13,15}, 0);
    testMoreQ3({1, 2}, {1, 2}, 2);
    testMoreQ3({}, {}, 0);
    return 0;
}
