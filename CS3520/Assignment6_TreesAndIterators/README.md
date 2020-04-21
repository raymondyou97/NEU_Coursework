# Binary Search Tree (BST) Iterators, BFS, DFS.

We covered the basics of the binary search tree in the [video lectures](https://www.youtube.com/playlist?list=PL_N7YxtCMPycSSFFdG5paOIMbc3FROhxT).

In this assignment we have provided you nearly complete code that you need to finish. All testing and complete node and tree
implementation has been provided to you in the Teee.h file. All code has been written in a single header file, this way it
is easier for you to compile and run the code. 

# The node class

The node class follows a similar approach as our other node classes that we have done so far. 

```cpp
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
```
# The Tree.

For a detail explanation of how a tree works, please refer to the lecture video and notes. We have provided you with a binary 
search tree implementation that has the add function implemented for you. 

```cpp
//The tree structure as represented in the video.
class Tree{
private:
    Node * _root;
    int _count;
    ////////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////
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
public:
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
            bool added = addHelper(this->_root, newNode);
            if ( added ){
                this->_count++;
            }
            return;
        }
    }
    ////////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////
    //Prints the tree in ascneding order using a stream.
    void printAscending(std::ostream & out){
        if ( this->_root == NULL ){
            return;
        }else{
            printAscendingHelper(this->_root, out);
        }
    }
```

We have also provided you with class defenitions for all of the iterator classes that you are asked to implemented as 
part of the code (not shown above). Please take a look at the provided code to familiarize yourself with the iterator classes that you need to implement. 

# TODO

The header file provided asks you to implement a number of methods and iterator classes. Most of these shouldn't take
too long to implement. We have provided you with a sample function from which to start and use as an example. 

We recommend doing the problems in the order provided as we think this will be easier for you.

We have also provided recommendations of how to implement the iterator classes and have provided some of the functions
that you need to implement along with private data members. Note that you don't have to follow this approach. This is 
just one way that could be done. In light of all the events we have provided this so it is easier for you to implement the
assignment. 

# Grading

We have provided you with a test file so you don't have to write one. Each section of test cases has been assgined 
a number of points. Each test you pass you get the assigned points. We will still look at your code and change the expected
output but you can use these tests as a guideline for your grade on this assignment.

Please let us know if you have any questions.

# Answer to dereference operator being readonly

The code below has to be readonly aka const because if we were able to dereference the iterator and mutate the class, we would lose the nature of the iterator aka what the iterator's purpose is, looping through an iterable and performing some operation. We don't want to be modifying the iterator nor its data when dereferencing.

```cpp
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
```