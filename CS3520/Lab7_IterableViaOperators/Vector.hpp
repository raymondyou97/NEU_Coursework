#ifndef Vector_hpp
#define Vector_hpp

#include <initializer_list>
#include "Iterable.hpp"
#include "ConstIterable.hpp"

class Vector : public Iterable, public ConstIterable {
    private:
        int * data;
        int capacity;
        int m_size;
        void resize(int newCapacity);
    public:
        // old stuff
        Vector(int capacity);     
        ~Vector();
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
        // new stuff
        Vector(const std::initializer_list<int> & initList);
        int & operator[] ( int index );
        const int & operator[] ( int index ) const;
};

#endif
