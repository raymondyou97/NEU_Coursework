#ifndef Queue_hpp
#define Queue_hpp

#include "IContainer.hpp"

class Queue : public IContainer {
    private:
        int m_size;
        int capacity;
        int * data;
    public:
        Queue(int capacity);
        ~Queue();
        void resize(int newCapacity);
        void push_back(const int & element);
        void push_front(const int & element);
        void pop_back();
        void pop_front();
        int front() const;
        int back() const;
        void insert(int pos, int elem);
        void erase(int pos);
        int size() const;
        int get(int pos) const;
};

#endif
