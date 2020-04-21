# Please edit the following information in your assignment

- Name: Raymond You
- How many hours did it take you to complete this assignment? 2 hours
- Did you collaborate with any other students/TAs/Professors? No
- Did you use any external resources? (Cite them below)
  - N/A
- (Optional) What was your favorite part of the assignment?
- (Optional) How would you improve the assignment?

# Logistics

For this assignment (and every assignment/lab), you must login into the servers through `your_khoury_name@login.khoury.neu.edu` to complete and test your work. The reason is the examples I will provide below are compiled strictly for our machines architecture, and this is a consistent architecture where your submission will be graded.


# Creating an inheritance hierarchy for your containers. 

In previous labs you implemented a generic interface IContainer, which contained all the functionality from the various
containers that you imlemented. The idea behind this approach was to be able to write algorithms that would work on a generic
IContainer, thus avoiding the need to write multiple versions of the same algorithm.

The issue with this approach was that classes were foreced to implement unsuported functionallity. Because of this
our methods were required to throw exceptions. The SOLID principles says that
classes shouldn't be forced to implemented functionallity that they don't need. So this seems like a bad approach.

In class we introduced a new appraoch by writing the ConstIterable and Iterable pure virtual classes.

```cpp
class Iterable{
public:
    virtual int & operator[] ( int index ) = 0;
};

class ConstIterable{
public:
    virtual const int & operator[] ( int index ) const = 0;
};

```

Then we made our vector container implement these pure virtual classes:

```cpp
//In the .hpp file
class Vector : public Iterable, public ConstIterable{
  ...
  int & operator[] ( int index ) = 0;
  const int & operator[] ( int index ) const;
  ...
}
int & Vector::operator[](int index){
    if ( index < 0 || index >=this->m_size){
        throw std::invalid_argument("Index out of bounds");
    }
    
    return this->data[index];
}

const int & Vector::operator[](int index) const{
    if ( index < 0 || index >=this->m_size){
        throw std::invalid_argument("Index out of bounds");
    }

    return this->data[index];
}
```
As you can see we are implmeneting the ```operator[](int) ``` so we can iterate over the vector container. 

Then we can write algorithms that take the Iterable interface and we don't have to worry about specific method signatures or
names of the container. 

```cpp
typedef void (*ModifierFunc)(int &);

void print(int start, int end, ConstIterable & itr){
    for (int i = start; i < end; i++){
        std::cout << itr[i] << std::endl;
        
    }
}

void foreach(int start, int end, Iterable & itr, ModifierFunc f ){
    (*f)( itr[start]);
}

int main(int argc, const char *argv[]) {
    DLL dll;
    Vector vec = {1,2,3};
    
    print(0, vec.size(), vec);
    foreach(0, vec.size(), vec, [](int & n) { n = -n; });
    print(0, vec.size(), vec);
    
    return 0;
}
```
We also implemented a constructor that takes in an initializer list. 

```cpp
Vector::Vector(const std::initializer_list<int> & initList) :Vector((int)initList.size()){
    for ( std::initializer_list<int>::iterator itr = initList.begin(); itr != initList.end(); itr++){
        push_back(*itr);
    }
}
```
In a following lecture we are going to see how we can build upon improve on this interface. 

## TODO

In this lab you need to implement the Iterable, ConstIterable, and Initializer list constructor for your DLL. 
Make sure the list can work with the same example that we have written above for vector. 

### Unit Tests

No need to write unit tests. 

# Rubric

- 100% Correct Implementations.
  - All functions should be implemented. Do not rename the functions, but you may add any 'helper' functions if you deem necessary.
  - There should be no memory leaks
  - There should be no bugs in your functions 
  - Your implementation will be graded by our set of unit tests, and we will check your code 'style' as well.
  
