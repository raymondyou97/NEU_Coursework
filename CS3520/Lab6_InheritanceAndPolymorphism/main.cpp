#include "IContainer.hpp"
#include "Vector.hpp"
#include "Stack.hpp"
#include "Queue.hpp"

#include <stdexcept>
#include <iostream>

// void testPushBack(IContainer * container) {
//     container->push_back(10);
// }

void unit_test1() {
    std::cout << "START TEST 1" << std::endl;
    IContainer * v = new Vector(2);
    v->push_back(3);
    v->push_back(4);
    v->push_back(5);
    v->push_front(2);
    v->push_front(1);
    std::cout << v->front() << std::endl;
    std::cout << v->back() << std::endl;
    delete v;
}

void unit_test2() {
    std::cout << "START TEST 2" << std::endl;
    IContainer * s = new Stack(2);
    s->push_back(1);
    s->push_back(2);
    std::cout << s->back() << std::endl;
    s->pop_back();
    std::cout << s->back() << std::endl;
    s->pop_back();
    s->push_back(100);
    s->push_back(200);
    std::cout << s->back() << std::endl;
    s->pop_back();
    std::cout << s->back() << std::endl;
    s->pop_back();
    delete s;
}

void unit_test3() {
    std::cout << "START TEST 3" << std::endl;
    IContainer * q = new Queue(4);
    q->push_back(1);
    q->push_back(2);
    q->push_back(3);
    q->push_back(4);
    std::cout << q->front() << std::endl;
    q->pop_front();
    std::cout << q->front() << std::endl;
    q->pop_front();
    std::cout << q->front() << std::endl;
    q->pop_front();
    std::cout << q->front() << std::endl;
    q->pop_front();
    delete q;
}

int main(int argc, const char * argv[]) {
    unit_test1();
    unit_test2();
    unit_test3();
}
