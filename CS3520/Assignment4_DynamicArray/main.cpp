#include "Vector.hpp"

#include <iostream>

void unit_test1() {
    std::cout << "START UNIT TEST 1" << std::endl;

    Vector v(2);
    v.push_back(1);
    v.push_back(2);
    v.push_back(3);
    v.push_back(4);
    v.push_back(5); 
    std::cout << v << std::endl;
    std::cout << "END UNIT TEST 1" << std::endl;
}

void unit_test2() {
    std::cout << "START UNIT TEST 2" << std::endl;
    Vector v(2);
    v.push_front(1);
    std::cout << v << std::endl;
    std::cout << "END UNIT TEST 2" << std::endl;
}

void unit_test3() {
    std::cout << "START UNIT TEST 3" << std::endl;
    Vector v2(4);
    v2.push_back(1);
    v2.push_back(2);
    v2.push_back(3);
    v2.push_back(4);
    std::cout << v2 << std::endl;
    v2.pop_back();
    v2.pop_back();
    std::cout << v2 << std::endl;
    v2.pop_back();
    v2.pop_back();
    std::cout << v2 << std::endl;
    std::cout << "END UNIT TEST 3" << std::endl;
}

void unit_test4() {
    std::cout << "START UNIT TEST 4" << std::endl;
    Vector v2(4);
    v2.push_back(1);
    v2.push_back(2);
    v2.push_back(3);
    v2.push_back(4);
    std::cout << v2 << std::endl;
    v2.pop_front();
    v2.pop_front();
    v2.pop_front();
    v2.pop_front();
    std::cout << v2 << std::endl;
    std::cout << "END UNIT TEST 4" << std::endl;
}

void unit_test5() {
    std::cout << "START UNIT TEST 5" << std::endl;
    Vector v(4);
    v.push_back(1);
    v.push_back(2);
    std::cout << v.front() << std::endl;
    std::cout << v.back() << std::endl;
    v.insert(0, 100);
    v.insert(3, 100000);
    std::cout << v << std::endl;
    v.erase(0);
    v.erase(1);
    std::cout << v << std::endl;
    std::cout << "END UNIT TEST 5" << std::endl;
}

void unit_test6() {
    std::cout << "START UNIT TEST 6" << std::endl;

    // test == operator
    Vector v1(2);
    Vector v2(2);
    v1.push_back(1);
    v1.push_back(2);
    v2.push_back(1);
    v2.push_back(2);
    bool test = v1 == v2;
    std::cout << test << std::endl;

    // test = operator
    Vector v3(12);
    v3 = v1;
    std::cout << v3 << std::endl;

    std::cout << "END UNIT TEST 6" << std::endl;
}

int main(int argc, const char * argv[]) {
    unit_test1();
    unit_test2();
    unit_test3();
    unit_test4();
    unit_test5();
    unit_test6();

    return 0;
}
