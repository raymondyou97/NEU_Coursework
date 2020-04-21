#ifndef MYDLL_H
#define MYDLL_H


typedef struct node{
	int data;
	struct node* next;
  	struct node* previous;
}node_t;

class DLL {
    private:
        int count;
        node_t * head;
        node_t * tail;
        DLL(const DLL & other);
        DLL & operator=(const DLL & other);
    public:
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
        int dll_size();
        void forward_print();
        void backward_print();
};

#endif
