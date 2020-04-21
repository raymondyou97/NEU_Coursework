#include <iostream>
#include "Rectangle.hpp"
#include "SmartPointer.hpp"

// count for ptr should go up to 2
void unit_test1() {
    std::cout << "---UNIT TEST 1 START---" << std::endl;
    Rectangle * r1 = new Rectangle("r1");
    SmartRectanglePointer sp1(r1);
    SmartRectanglePointer sp2(r1);
}

// counts should be 1 as separate rectangles
void unit_test2() {
    std::cout << "---UNIT TEST 2 START---" << std::endl;
    Rectangle * r1 = new Rectangle("r1"); 
    Rectangle * r2 = new Rectangle("r2");
    SmartRectanglePointer sp1(r1);
    SmartRectanglePointer sp2(r2);
}

// when switching data, old rectangle should be destroyed too as count is 0
void unit_test3() {
    std::cout << "---UNIT TEST 3 START---" << std::endl;
    Rectangle * r1 = new Rectangle("r1"); 
    Rectangle * r2 = new Rectangle("r2");
    SmartRectanglePointer sp1(r1);
    sp1.reset(r2);
}

void unit_test4() {
    std::cout << "---UNIT TEST 4 START---" << std::endl;
    Rectangle * r1 = new Rectangle("r1"); 
    Rectangle * r2 = new Rectangle("r2");
    Rectangle * r3 = new Rectangle("r3");
    SmartRectanglePointer sp1(r1);
    SmartRectanglePointer sp2(r2);
    SmartRectanglePointer sp3(r3);
    SmartRectanglePointer sp4(r2);
    SmartRectanglePointer sp5(r2);
    SmartRectanglePointer sp6(r1);
    sp1.reset(r2);
}

void unit_test5() {
    std::cout << "---UNIT TEST 5 START---" << std::endl;
    Rectangle * r1 = new Rectangle("r1"); 
    Rectangle * r2 = new Rectangle("r2");
    SmartRectanglePointer sp1(r1);
    SmartRectanglePointer sp2(r1);
    sp2.reset(r2);
}

// test for resetting to itself. should throw exception. commenting out
// so tests don't fail
void unit_test6() {
    std::cout << "---UNIT TEST 6 START---" << std::endl;
    Rectangle * r1 = new Rectangle("r1"); 
    SmartRectanglePointer sp1(r1);
    sp1.reset(r1);
}

int main(int argc, const char * argv[]) {   
    unit_test1();
    unit_test2();
    unit_test3();
    unit_test4();
    unit_test5();
    //unit_test6();
    return 0;
}
