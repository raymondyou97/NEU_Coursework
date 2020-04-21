#include "my_dll.hpp"

#include <iostream>


void unitTest1() {
    std::cout << "Start Unit Test 1" << std::endl;
    DLL l;
    l.dll_push_back(1);
    l.dll_push_back(2);
    l.dll_push_back(3);
    l.dll_insert(0, 100);
    l.dll_insert(3, 10000);
    l.dll_insert(1, 1000);
    l.forward_print();
    l.backward_print();
}

void unitTest2() {
    std::cout << "Start Unit Test 2" << std::endl;
    DLL l;
    l.dll_push_back(1);
    l.dll_push_back(2);
    l.dll_push_back(3);
    l.dll_push_back(4);
    l.dll_push_back(5);
    l.dll_push_back(6);
    l.dll_push_back(7);
    l.dll_pop_back();
    l.dll_pop_front();
    l.dll_remove(0);
    l.dll_remove(3);
    l.forward_print();
    l.backward_print();
}

void unitTest3() {
    std::cout << "Start Unit Test 3" << std::endl;
    DLL l;
    l.dll_push_back(1);
    l.dll_push_back(2);
    l.dll_push_back(3);
    l.dll_push_back(4);
    l.dll_push_back(5);
    l.dll_push_back(6);
    l.dll_push_back(7);
    int v = l.dll_pop_back();
    std::cout << v << std::endl;
    v = l.dll_pop_front();
    std::cout << v << std::endl;
    v = l.dll_get(0);
    std::cout << v << std::endl;
    v = l.dll_get(3);
    std::cout << v << std::endl;
}

int main(int argc, const char * argv[]) {
    unitTest1();
    unitTest2();
    unitTest3();

    return 0;
}

