//
//  Tree.hpp
//  TreeHomeworkCode
//
//  Created by Vidoje Mihajlovikj on 3/15/20.
//  Copyright © 2020 Vidoje Mihajlovikj. All rights reserved.
//

#ifndef Tree_hpp
#define Tree_hpp

#include <stdio.h>
#include <iostream>
#include <queue>
#include <initializer_list>
#include <iterator>

//Represents the node of the tree.
class Node{
private:
    int _data;
    Node * _right;
    Node * _left;
public:
    Node(int data) : _data(data), _right(NULL), _left(NULL){};

    void setRight(Node * right){
        this->_right = right;
    }

    void setLeft(Node * left){
        this->_left = left;
    }

    void setData(const int data){
        this->_data = data;
    }
    int getData() const{
        return _data;
    }

    Node * getRight() const{
        return this->_right;
    }

    Node * getLeft() const {
        return this->_left;
    }
};

class Tree;
//Iterates through the nodes of the tree using BFS.
class BSTForwardIterator{
private:
    Tree * _t;
    std::queue<Node *> iterQueue;
    void buildQueue();
    void buildQueueHelper(Node * node, int treeLevel);
public:
    BSTForwardIterator(Tree * t, bool endIter);
    bool operator==(const BSTForwardIterator & other) const;
    bool operator!=(const BSTForwardIterator & other) const;
    int operator*() const;
    BSTForwardIterator operator++(int);
    BSTForwardIterator& operator++();
    typedef int difference_type;
    typedef int value_type;
    typedef BSTForwardIterator* pointer;
    typedef BSTForwardIterator& reference;
    typedef std::forward_iterator_tag iterator_category;
};

//Adds to the tree via an iterator, very similar to the back inster from class.
class TreeInserterIterator{
private:
    Tree & _t;
public:
    TreeInserterIterator(Tree & t);
    TreeInserterIterator & operator=(int value);
    TreeInserterIterator operator*() const;
    TreeInserterIterator operator++(int);
    TreeInserterIterator& operator++();
    typedef int difference_type;
    typedef int value_type;
    typedef TreeInserterIterator* pointer;
    typedef TreeInserterIterator& reference;
    typedef std::output_iterator_tag iterator_category;
};

//The tree structure as represented in the video.
class Tree{
private:
    Node * _root;
    int _count;
    //The recuresive helper that adds the newNode.
    bool addHelper(Node * node, Node * newNode){
        if ( node == NULL || newNode == NULL ){
            return false;
        }
        //Should we go to the left
        if ( newNode->getData() < node->getData() ){
            //Are we done recursing
            if ( node->getLeft() == NULL ){
                node->setLeft(newNode);
                this->_count++;
                return true;
            }
            else{
                //Not done, call addHelper on the left node.
                return addHelper(node->getLeft(), newNode);
            }
        //Should we go to the right.
        }else if ( newNode->getData() > node->getData() ){
            if ( node->getRight() == NULL ){
                node->setRight( newNode );
                this->_count++;
                return true;
            }else{
                return addHelper(node->getRight(), newNode);
            }
        }
        //Do no add if the newNode is equal to the current node.
        return false;
    }

    //Recursive printAscending// Code from lecture notes.
    //Uses an ostream as opposed to printing to starndard out so we can test it.
    void printAscendingHelper(Node * node, std::ostream & out){
        if ( node == NULL ){
            return;
        }
        printAscendingHelper(node->getLeft(), out);
        out << node->getData();
        printAscendingHelper(node->getRight(), out);

    }


    // Helper that computes the height of the entire tree
    int height(Node * node) {
        if (node == NULL)
            return 0;
        else {
            int leftHeight = height(node->getLeft());
            int rightHeight = height(node->getRight());
            if (leftHeight > rightHeight)
                return leftHeight + 1;
            else
                return rightHeight + 1;
        }
    }

    //Problem 1. Implement the function but with using an ostream iterator.
    void appendAscendingHelperOstreamIter(Node * node, std::ostream_iterator<int> outItr){
        if (node == NULL) {
            return;
        }
        appendAscendingHelperOstreamIter(node->getLeft(), outItr);
        *outItr = node->getData();
        appendAscendingHelperOstreamIter(node->getRight(), outItr);
    }

    //Problem 2. Implement the function using a generic iterator.
    template <class Iter>
    void appendAscendingHelperGenericIter(Node * node, Iter & outItr){
        if (node == NULL) {
            return;
        }
        appendAscendingHelperGenericIter(node->getLeft(), outItr);
        *outItr = node->getData();
        outItr++;
        appendAscendingHelperGenericIter(node->getRight(), outItr);
    }

public:
    friend class BSTForwardIterator;

    BSTForwardIterator begin(){
        return BSTForwardIterator(this, false);
    }

    BSTForwardIterator end(){
        return BSTForwardIterator(this, true);
    }


    //Default constructor.
    Tree() : _root(NULL), _count(0) {};

    //Initalizer_list constructor.
    Tree(std::initializer_list<int> list) : Tree(){
        for ( std::initializer_list<int>::iterator itr = list.begin(); itr != list.end(); itr++){
            add(*itr);
        }
    }
    //The public add method that calls the recursive helper.
    //Only sets the root if the tree is empty otherwise calls the recursive helper method.
    void add(int data){
        Node * newNode = new Node(data);
        if ( this->_root == NULL ){
            this->_root = newNode;
            this->_count++;
            return;
        }
        else{
            addHelper(this->_root, newNode);
            return;
        }
    }

    //Prints the tree in ascneding order using a stream.
    void printAscending(std::ostream & out){
        if ( this->_root == NULL ){
            return;
        }else{
            printAscendingHelper(this->_root, out);
        }
    }

    //Problem 1. Implement the function but with using an ostream iterator.
    //      Should call the helper defined above.
    void appendAscnedingOstreamIter(std::ostream_iterator<int> outItr){
        appendAscendingHelperOstreamIter(this->_root, outItr);
    }

     //Problem 3. Implement the function using a generic iterator.
     //      Should call the helper defined above.
    template <class Iterator>
    void appendAscnedingGenericIter(Iterator itr){
        appendAscendingHelperGenericIter(this->_root, itr);
    }

    template <class Iterator>
    void appendViaBSTHelper(Iterator & itr, Node * root) {
        if (root == NULL) {
            return;
        }

        int treeHeight = height(root);
        for (int i = 1; i <= treeHeight; i++)
            printBSTTreeLevel(itr, root, i);
    }

    template <class Iterator>
    void printBSTTreeLevel(Iterator & itr, Node* root, int treeLevel) {
        if (root == NULL) {
            return;
        }

        if (treeLevel == 1) {
            *itr = root->getData();
            itr++;
        } else if (treeLevel > 1) {
            int nextLevel = treeLevel - 1;
            printBSTTreeLevel(itr, root->getLeft(), nextLevel);
            printBSTTreeLevel(itr, root->getRight(), nextLevel);
        }
    }

    //Problem 4
    //Appends to a container via an iterator in a BST fashion.
    //Hint: Implement BST where you print each node.
    //Then, as opposed to printing, update and increment the iterator.
    template <class Iterator>
    void appendViaBST(Iterator itr){
        appendViaBSTHelper(itr, this->_root);
    }
};

//Implement a BST forward iterator.
//Populate iterQueue to have all of the nodes in the tree in a BST fashion.
void BSTForwardIterator::buildQueue(){
    Node * root = _t->_root;
    if (root == NULL) {
        return;
    }

    int treeHeight = this->_t->height(root);
    for (int i = 1; i <= treeHeight; i++)
        buildQueueHelper(root, i);
}

void BSTForwardIterator::buildQueueHelper(Node * node, int treeLevel) {
    if (node == NULL) {
        return;
    }

    if (treeLevel == 1) {
        this->iterQueue.push(node);
    } else if (treeLevel > 1) {
        int nextLevel = treeLevel - 1;
        buildQueueHelper(node->getLeft(), nextLevel);
        buildQueueHelper(node->getRight(), nextLevel);
    }
}

//Creates an iterator, makeEnd indicates whether an start or an end iterator should be built.
//Think how you can use this boolean to implement this information.
BSTForwardIterator::BSTForwardIterator(Tree * t, bool makeEnd){
    this->_t = t;
    if (!makeEnd) {
        buildQueue();
    }
}

//Check if two iterators are the same. Not that if the trees the iterators
//point to are not the same, then then there is no way the ietrators are the same.
//Think how you are going to check when a start iterator reaches and end iterator
//the have to be the same. To simplify things instead of comparing the queues of the
//iterators just make the assumption that if the queues are the same size then
//the queues are the same.
bool BSTForwardIterator::operator==(const BSTForwardIterator & other) const{
    if (this->_t != other._t) {
        return false;
    }

    return this->iterQueue.size() == other.iterQueue.size();
}

bool BSTForwardIterator::operator!=(const BSTForwardIterator & other) const{
    return !(*this == other);

}
//The dereference operator. Note the return type. This is readonly
//version. No assignment will be done. Think why and if this was assignable,
//why it would not work. Provide the answer in the README.md.
//Throw an exception if we are trying to dereferene an invalid iterator.
//Think what an invalid iterator might mean.
int BSTForwardIterator::operator*() const{
    if (this->iterQueue.size() == 0) {
        throw std::out_of_range("Invalid range for iterator");
    }
    return this->iterQueue.front()->getData();
}
//HINT: think what happens with the stack here.
//HINT: note how this signature is different than the one bellow,
//and how we have the extra argument.
BSTForwardIterator BSTForwardIterator::operator++(int){
    BSTForwardIterator temp = *this;
    temp.iterQueue.pop();
    return temp;
}

//Hint: think what happens with the stack and how is this different than above.
BSTForwardIterator & BSTForwardIterator::operator++(){
    this->iterQueue.pop();
    return *this;
}

TreeInserterIterator::TreeInserterIterator(Tree & t) : _t(t) {}
//Hint: think what we did with the backinster in class, very simple to implement

TreeInserterIterator & TreeInserterIterator::operator=(int value){
    this->_t.add(value);
    return *this;
}

TreeInserterIterator TreeInserterIterator::operator*() const{
    return *this;
}

TreeInserterIterator TreeInserterIterator::operator++(int){
    return *this;
}

TreeInserterIterator & TreeInserterIterator::operator++(){
    return *this;
}

#endif /* Tree_hpp */
