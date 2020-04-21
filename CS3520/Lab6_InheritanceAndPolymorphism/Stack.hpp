#ifndef Stack_hpp
#define Stack_hpp

#include "Node.hpp"
#include "IContainer.hpp"

class Stack : public IContainer {
    private:
        int count;
        int capacity;
        Node * head;
    public:
        Stack(int capacity);
        ~Stack();
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