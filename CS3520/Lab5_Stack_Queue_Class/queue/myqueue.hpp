#ifndef MYQUEUE_H
#define MYQUEUE_H

#include <iostream>

class Queue {
    private:
        int back;
        int front;
        int size;
        int capacity;
        int * data;
    public:
        Queue(int capacity);
        ~Queue();
        bool queue_empty();
        bool queue_full();
        void queue_enqueue(int item);
        int queue_dequeue();
        int queue_size();
        int get(int i);
};
std::ostream & operator<<(std::ostream & out, Queue & other);
#endif
