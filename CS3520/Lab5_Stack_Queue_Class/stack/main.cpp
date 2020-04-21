#include "mystack.hpp"

#include <iostream>

void unit_test1() {
    Stack s(2);
    s.stack_enqueue(1);
    s.stack_enqueue(2);
    s.stack_dequeue();
    s.stack_dequeue();
    s.stack_enqueue(1);
    s.stack_enqueue(2);
    s.stack_dequeue();
    s.stack_dequeue();
    s.stack_enqueue(1);
    s.stack_enqueue(2);
    s.stack_dequeue();
    s.stack_dequeue();
}

void unit_test2() {
    Stack s(1);
    // this should throw an error
    //s.stack_dequeue();
    s.stack_enqueue(1);
}

void unit_test3() {
    Stack s(3);
    s.stack_enqueue(1);
    s.stack_enqueue(2);
    s.stack_enqueue(3);
    std::cout << s.stack_size() << std::endl;
    std::cout << s.stack_dequeue() << std::endl;
    std::cout << s.stack_dequeue() << std::endl;
    std::cout << s.stack_dequeue() << std::endl;
}   

void unit_test4() {
    Stack s(1);
    // this should throw an error
    //s.stack_enqueue(1);
}

int main(int argc, const char * argv[]) {
    unit_test1();
    unit_test2();
    unit_test3();
    unit_test4();
}
