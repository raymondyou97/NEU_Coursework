#include "myqueue.hpp"

#include <iostream>

void unit_test1() {
    Queue q(2);
    std::cout << q.queue_empty() << std::endl;
    std::cout << q.queue_full() << std::endl;
    q.queue_enqueue(1);
    q.queue_enqueue(2);
    std::cout << q.queue_size() << std::endl;
    std::cout << q << std::endl;
    std::cout << q.queue_dequeue() << std::endl;
    std::cout << q.queue_dequeue() << std::endl;
    std::cout << q.queue_size() << std::endl;
}

void unit_test2() {
    Queue q(10);
    q.queue_enqueue(1);
    q.queue_enqueue(2);
    q.queue_enqueue(3);
    q.queue_enqueue(4);
    q.queue_enqueue(5);
    q.queue_enqueue(6);
    std::cout << q << std::endl;
}

void unit_test3() {
    Queue q(1);
    // should throw error
    //q.queue_dequeue();
}

void unit_test4() {
    Queue q(1);
    q.queue_enqueue(1);
    // should throw error
    //q.queue_enqueue(2);
}

void unit_test5() {
    Queue q(2);
    q.queue_enqueue(1);
    q.queue_enqueue(2);
    q.queue_dequeue();
    q.queue_dequeue();
    q.queue_enqueue(1);
    q.queue_enqueue(2);
    q.queue_dequeue();
    q.queue_dequeue();
}

int main(int argc, const char * argv[]) {
    unit_test1();
    unit_test2();
    unit_test3();
    unit_test4();
    unit_test5();
}
