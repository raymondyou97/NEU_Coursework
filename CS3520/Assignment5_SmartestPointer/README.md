# REDO

# Please edit the following information in your assignment

- Name: Raymond You
- How many hours did it take you to complete this assignment? 2 hour
- Did you collaborate with any other students/TAs/Professors? No
- Did you use any external resources? (Cite them below)
  - https://www.geeksforgeeks.org/smart-pointers-cpp/
  - https://en.wikipedia.org/wiki/Smart_pointer
  - https://stackoverflow.com/questions/4527686/how-to-update-stdmap-after-using-the-find-method
- (Optional) What was your favorite part of the assignment?
- (Optional) How would you improve the assignment?

# Logistics

For this assignment (and every assignment/lab), you must login into the servers through `your_khoury_name@login.khoury.neu.edu` to complete and test your work. The reason is the examples I will provide below are compiled strictly for our machines architecture, and this is a consistent architecture where your submission will be graded.


# Smarter smart pointer.

In class we have discussed how to implement a smart pointer so we can avoid memory leaks. In this assignment we are going to 
built on this idea by making an even smarter pointer, one that will keep track of what all smart pointers are pointing to.

# The regular smart pointer.

Pointer misuse can be a major source of bugs. Smart pointers prevent most situations of memory leaks by making the 
memory deallocation automatic. More generally, they make object destruction automatic: an object controlled by a 
smart pointer is automatically destroyed, when the last owner of an object is destroyed.

Smart pointers also eliminate dangling pointers by postponing destruction until an object is no longer in use. 
<sup>[excerpt taken from wikipedia](#myfootnote1)</sup> 

In class we developed the following code:

```cpp
class SmartRectanglePointer{
private:
    Rectangle * data;
    int * counter;
public:
    SmartRectanglePointer( Rectangle * ptr ){
        if ( ptr == NULL ){
          throw std::invalid_argument("Cannot point to NULL pointer");
        }
        
        this->data = ptr;
        this->counter = new int(1); // Initalize the counter to 1 as we have only one smart pointer pointing to the data.
    }
    
    SmartRectanglePointer( const SmartRectanglePointer & other){
        this->data = other.data;
        this->counter = other.counter;
        *(this->counter) = *(this->counter) + 1; //Make sure we increment the count as this is the copy constructor.
        //You would also have to do this for the operator=.
    }
    //immplement operator* to mimic an actual pointer.
    Rectangle & operator*(){
        return *this->ptr;
    }
     //immplement operator& to mimic an actual pointer.
    Rectangle * operator->(){
        return this->ptr;
    }
    
    ~SmartRectanglePointer(){
        if ( this->data != NULL && this->counter != NULL ){
            
            //Some smart pointer went ouf of scope therefore cannot be used anymore.
            //Decreement the count.
             *(this->counter) = *(this->counter) - 1;
            
            //Check to see if this was the last smrt pointer pointing to the data.
            //If so delete the data and the counter. 
            if ( *(this->counter)  == 0 )
            {
                delete this->counter;
                delete this->data;
            }
        }
    }
};

```

This was a smart pointer for our Rectangle class (later we will see how we can template this so we don't have to write
a smart pointer class for every type).

```cpp
class Rectangle{
private:
    std::string m_id;
public:
    Rectangle(): m_id("Unknown"){};
    
    Rectangle(std::string id) : m_id(id){}
    
    Rectangle(const Rectangle & other ){
        this->m_id = other.m_id + " copy";
    }
    
    ~Rectangle(){}
    
    std::string getId(){
        return this->m_id;
    }
    
    void setId(std::string id){
        this->m_id = id;
    }
};
```

# Making the smart pointer a little smarter. 

Take a look at the following example:

```cpp
int main(int argc, const char * argv[]) {
    
    SmartPointer sp1(new Rectangle("r1"));
    SmartPointer sp2( &(*sp1) );
}
```

I get the following segmentation fault error:

```cppp
malloc: *** error for object 0x1023119a0: pointer being freed was not allocated
```

Take a minute and try to understand what is going on. ```(*sp)``` returns ``` *(this->data) ``` which is the actual rectangle
that we are pointing to. Also note, in the following statement ```& (*(this->data))``` the & will negate the * which means we are getting the actual raw pointer. 

Now we have two smart pointers having the same this->data. This is another example of the same idea:

```cpp
int main(int argc, const char * argv[]) {
    Rectangle * r1 = new Rectangle("r1");
    SmartPointer sp1( r1 );
    SmartPointer sp2( r1 );
}
```

When ```sp1``` goes out of scope will will delete ```sp1's data``` ( which is ```r1``` ). Then when ```sp2``` goes out of scope, we will delete ```sp2's data``` ( which is also ```r1```), but this is the same pointer! Lets fix this. 

# To Do

* Implement a smarter smart pointer that will prevent this scenario by building a table of all the ```Rectangle *``` that 
our ```SmartPointers``` are keeping track off. If we try to constrcut a SmartPointer with ```Rectangle *``` that another ```SmartPointer``` already keeps track off, we will sync the new ```SmartPointer``` counter to the counter of the ```SmartPointer``` that is already keeping track of the the pointer in question. 

* Implement ```void reset(Rectangle * ptr)``` that resets the ownership to ptr. Make sure you make the corresponding updates depending if anyone else is pointing to the old pointer or the current smart pointer is the only one that kept track of the old pointer.

# Unit Tests

A unit test is a standalone test that checks for the correctness of a specific use case in your code. 
In our case, we are testing if we have a working vector implementation. 

Please write unit tests to test your implementation.

# Rubric

- 100% Correct SmartPointer implementation
  - All functions should be implemented in a separte .cpp file. A Makefile also needs to be implemented. Do not rename the functions, but you may add any 'helper' functions if you deem necessary.
  - There should be no memory leaks
  - There should be no bugs in your functions 
  - Your implementation will be graded by our set of unit tests, and we will check your code 'style' as well.

# Resources to help
  - https://www.geeksforgeeks.org/smart-pointers-cpp/
  - https://en.wikipedia.org/wiki/Smart_pointer
  

