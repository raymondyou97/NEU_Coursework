// Modify this file
// compile with: gcc linkedlist.c -o linkedlist

#include <stdio.h>
#include <stdlib.h> // contains the functions free/malloc

// Create your node_t type here
typedef struct node {
    int year;
    int wins;
    struct node* next;
}node_t;

// Write your functions here
// There should be 1.) create_list 2.) print_list 3.) free_list
// You may create as many helper functions as you like.

node_t* create_node(int year, int wins) {
    node_t* node = (node_t*)malloc(sizeof(node_t));
    node->year = year;
    node->wins = wins;
    node->next = NULL;

    return node;
}

void connect_node(node_t* current, node_t* next) {
    current->next = next;
}

node_t* create_list() {
    node_t* head = create_node(2018, 108);

    node_t* n1 = create_node(2017, 93);
    connect_node(head, n1);

    node_t* n2 = create_node(2016, 93);
    connect_node(n1, n2);

    node_t* n3 = create_node(2015, 78);
    connect_node(n2, n3);

    node_t* n4 = create_node(2014, 71);
    connect_node(n3, n4);

    return head;
}

void print_list(node_t* list) {
    node_t* iterator = list;
    while (iterator != NULL) {
        printf("%d, %d wins \n", iterator->year, iterator->wins);
        iterator = iterator->next;
    }
}

void free_list(node_t* list) {
    node_t* head = list;
    node_t* temp;
    while (head != NULL) {
        temp = head;
        head = head->next;
        free(temp);
    }
}

int main() {
    node_t* list = create_list(); 
    print_list(list);
    free_list(list);

    return 0;
}
