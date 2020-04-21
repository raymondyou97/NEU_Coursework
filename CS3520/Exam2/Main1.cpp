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
#include "Q1.hpp"

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

void testQ1(std::vector<std::string> vec1, std::string expectedOutput){
    std::stringstream ss;

    BackAndForthFilter container(vec1);
    std::for_each(container.begin(), container.end(), [&ss] (std::string n){ ss << n << ","; });

    assertEquals(expectedOutput, ss.str(), __FUNCTION__ );
}


int main(int argc, const char * argv[]) {
    testQ1({"Paul","Ringo","John","George","Freddie"}, "Paul,Freddie,Ringo,George,John,");
    //Add other test cases here.
    testQ1({}, "");
    testQ1({"Paul"}, "Paul,");
    testQ1({"Paul","Paul"}, "Paul,Paul,");
    testQ1({"Paul","Ringo"}, "Paul,Ringo,");
    testQ1({"Paul","Ringo","John"}, "Paul,John,Ringo,");
    return 0;
}
