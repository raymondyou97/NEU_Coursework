#include "my_dll.hpp"
#include "Node.hpp"

#include <iostream>
#include <cstddef>
#include <stdexcept>

// old

DLL::DLL() {
    this->count = 0;
    this->head = NULL;
    this->tail = NULL;
}   

DLL::~DLL() {
    Node * temp_node = NULL;
    while (this->head != NULL) {
        temp_node = this->head;
        this->head = this->head->next;
        delete(temp_node);
    }
}

bool DLL::dll_empty() {
    if (this->count  == 0) {
        return true;
    } else {
        return false;
    }
}
 
void DLL::dll_push_front(int item) {
    Node * node = new Node;
    node->data = item;
    node->next = NULL;
    node->previous = NULL;

    if (dll_empty()) {
        this->head = node;
        this->tail = node;
    } else {
        Node * current_head = this->head;
        current_head->previous = node;
        node->next = current_head;
        this->head = node;
    }
    this->count++;
}

void DLL::dll_push_back(int item) {
    Node * node = new Node;
    node->data = item;
    node->next = NULL;
    node->previous = NULL;

    if (dll_empty()) {
        this->head = node;
        this->tail = node;
    } else {
        Node * current_tail = this->tail;
        current_tail->next = node;
        node->previous = current_tail;
        this->tail = node;
    }
    this->count++;
}

int DLL::dll_pop_front() {
    if (dll_empty()) {
        throw std::out_of_range("Empty list");
    } else {
        Node* current_head = this->head;
        int data = current_head->data;

        if (this->count == 1) {
            this->head = NULL;
            this->tail = NULL;
        } else {
            Node* new_head = current_head->next;
            new_head->previous = NULL;
            this->head = new_head;
        }
        this->count--;
        delete(current_head);
        return data;
    }
}
int DLL::dll_pop_back() {
    if (dll_empty()) {
        throw std::out_of_range("Empty list");
    } else {
        Node* current_tail = this->tail;
        int data = current_tail->data;

        if (this->count == 1) {
            this->head = NULL;
            this->tail = NULL;
        } else {
            Node* new_tail = current_tail->previous;
            new_tail->next = NULL;
            this->tail = new_tail;
        }
        this->count--;
        delete(current_tail);
        return data;
    }
}

void DLL::dll_insert(int pos, int item) {
    if (dll_empty() || pos < 0 || pos >= this->count) {
        throw std::out_of_range("Empty list");
    } else if (pos == 0) {
        dll_push_front(item);
    } else if (pos == this->count - 1) {
        dll_push_back(item);
    } else {
        Node * head = this->head;
        int i = 0;

        while (i != pos) {
            head = head->next;
            i++;
        }

        Node* node = new Node;
        node->data = item;

        Node* prevprev = head->previous;
        prevprev->next = node;
        node->next = head;
        node->previous = prevprev;
        head->previous = node;

        this->count++;
    }
}
 
int DLL::dll_get(int pos) {
    if (dll_empty() || pos < 0 || pos >= this->count) {
        throw std::out_of_range("Empty list");
    } else {
        Node* head = this->head;

        int i = 0;
        while (i != pos) {
            head = head->next;
            i++;
        }

        int data = head->data;
        return data;
    }
}
 
void DLL::dll_remove(int pos) {
    if (dll_empty() || pos < 0 || pos >= this->count) {
        throw std::out_of_range("Empty list");
    } else if (pos == 0) {
        dll_pop_front();
    } else if (pos == this->count - 1) {
        dll_pop_back();
    } else {
        Node * head = this->head;
        int i = 0;

        while (i != pos) {
            head = head->next;
            i++;
        }

        Node* next = head->next;
        Node* prev = head->previous;

        if (next == NULL) {
            prev->next = NULL;
        } else {
            next->previous = prev;
            prev->next = next;
        }

        this->count--;
        delete(head);
    }
}

int DLL::size() {
    return this->count;
}

void DLL::forward_print() {
    if (dll_empty()) {
        std::cout << "List is empty" << std::endl;
        return;
    }
    Node* head = this->head;
    std::cout << "Printing from head to tail" << std::endl;
    while (head != NULL) {
        std::cout << head->data << ' ';
        head = head->next;
    }
    std::cout << std::endl;
}

void DLL::backward_print() {
    if (dll_empty()) {
        std::cout << "List is empty" << std::endl;
        return;
    }
    Node* tail = this->tail;
    std::cout << "Printing from tail to head" << std::endl;
    while (tail != NULL) {
        std::cout << tail->data << ' ';
        tail = tail->previous;
    }
    std::cout << std::endl;
}

// new

int & DLL::operator[](int index){
    if (this->count == 0 || index < 0 || index >= this->count) {
        throw std::out_of_range("Empty list");
    } else {
        Node* head = this->head;

        int i = 0;
        while (i != index) {
            head = head->next;
            i++;
        }

        return head->data;
    }
}

const int & DLL::operator[](int index) const{
    if (this->count == 0 || index < 0 || index >= this->count) {
        throw std::out_of_range("Empty list");
    } else {
        Node* head = this->head;

        int i = 0;
        while (i != index) {
            head = head->next;
            i++;
        }

        return head->data;
    }
}
