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
#include <algorithm>
#include "Q2.hpp"

void assertEquals(std::string expected, std::string actual, std::string testName){
    if (expected.compare(actual) == 0 ){
        std::cout << "Pass: " << testName << std::endl;
    }else{
        std::cout << "Failed: " << testName << std::endl;
        std::cout << "Expected: " << expected << std::endl;
        std::cout << "Actual: " << actual << std::endl;
    }
    std::cout << "-----------------------------------" << std::endl;
}

void testQ2(std::vector<std::string> vec1, std::string expectedOutput){
    std::stringstream ss;

    SortedFilter container(vec1);
    std::for_each ( container.begin(), container.end(), [&ss] (std::string n){ ss << n << ","; });

    assertEquals(expectedOutput, ss.str(), __FUNCTION__ );
}


int main(int argc, const char * argv[]) {
    testQ2({"Paul","Ringo","John","George","Freddie"},  "Freddie,George,John,Paul,Ringo,");
    //Add other test cases here.
    testQ2({}, "");
    testQ2({"aa"}, "aa,");
    testQ2({"aa","aa"}, "aa,aa,");
    testQ2({"aa","bb"}, "aa,bb,");
    testQ2({"aa","bb","aa"}, "aa,aa,bb,");
    testQ2({"d","c","b","a"}, "a,b,c,d,");
    return 0;
}
