#ifndef MYDLL_H
#define MYDLL_H

#include "Node.hpp"
#include "ConstIterable.hpp"
#include "Iterable.hpp"

class DLL : public Iterable, public ConstIterable {
    private:
        int count;
        Node * head;
        Node * tail;
        DLL(const DLL & other);
        DLL & operator=(const DLL & other);
    public:
        // old
        DLL();
        ~DLL();
        bool dll_empty();
        void dll_push_front(int item);
        void dll_push_back(int item);
        int dll_pop_front();
        int dll_pop_back();
        void dll_insert(int pos, int item);
        int dll_get(int pos);
        void dll_remove(int pos);
        int size();
        void forward_print();
        void backward_print();
        // new
        int & operator[] (int index);
        const int & operator[] (int index) const;
};

#endif
