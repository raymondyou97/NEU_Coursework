#include <iostream>
#include <stdexcept>
#include "Vector.hpp"
#include "my_dll.hpp"
#include "Iterable.hpp"
#include "ConstIterable.hpp"

typedef void (*ModifierFunc)(int &);

void print(int start, int end, ConstIterable & itr) {
    for (int i = start; i < end; i++){
        std::cout << itr[i] << std::endl;
        
    }
}

void foreach(int start, int end, Iterable & itr, ModifierFunc f ) {
    for (int i = start; i < end; i++) {
        (*f)( itr[i]);
    }
}

// tests for vector
void unit_test1() { 
    std::cout << "START TESTS FOR VECTORS" << std::endl;
    Vector vec = {1,2,3};
    print(0, vec.size(), vec); // should print 1 2 3
    foreach(0, vec.size(), vec, [](int & n) { n = n*5; });
    print(0, vec.size(), vec); // should print 1 5 15
    foreach(0, vec.size(), vec, [](int & n) { n = -n; });
    print(0, vec.size(), vec); // should print -1 -10 -15
}

// test for dll
void unit_test2() {
    std::cout << "START TESTS FOR DLL" << std::endl;
    DLL dll;
    dll.dll_push_back(1);
    dll.dll_push_back(2);
    dll.dll_push_back(3);
    print(0, dll.size(), dll); // should print 1 2 3
    foreach(0, dll.size(), dll, [](int & n) { n = -n; });
    print(0, dll.size(), dll); // should print -1 -2 -3
}

int main(int argc, const char *argv[]) {
    unit_test1();
    unit_test2();

    return 0;
}
