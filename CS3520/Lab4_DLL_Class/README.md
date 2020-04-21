# Please edit the following information in your assignment

- Name: Raymond You
- How many hours did it take you to complete this assignment? 2
- Did you collaborate with any other students/TAs/Professors? No
- Did you use any external resources? (Cite them below)
  - N/A
- (Optional) What was your favorite part of the assignment?
- (Optional) How would you improve the assignment?

# Logistics

For this assignment (and every assignment/lab), you must login into the servers through `your_khoury_name@login.khoury.neu.edu` to complete and test your work. The reason is the examples I will provide below are compiled strictly for our machines architecture, and this is a consistent architecture where your submission will be graded.


# Doubly Linked List *(DLL) as a class*

In Assignment 3 you implemented a DLL using structs. 

The code for our node struct looked like this:

```cpp
typedef struct node{
	int myData;
	struct node* next;
	struct node* previous;
}node_t;
```

And our linked list struct looked like: 

```cpp
typedef struct DLL{
	int count;		
	node_t* head;		// head points to the first node in our DLL.
	node_t* tail;		// head points to the last node in our DLL.
}dll_t;
```

In this lab we are going to convert our implementation to use classes and not structs. Therefore all of our functions will become methods. 

# Reflection on the previous implementation. 

What did you think were some shortcomings of using structs and how will these be overcomed with classes? 

Structs didn't have private fields (all fields are public by default) whereas classes do have private fields. We don't want all our class attributes and functions to be exposed so easily.

# Implementing a Doubly Linked List (Your TO DO )

Conver the implemntatino from Assignment 3 to use clases. Note that the create_dll function will become our constructor, and the free function will be our destructor. Make your copy constructor and assignment operators private for this lab. This will make the lab easier to implement.

### Unit Tests

Adapt your unit tests to work with your new implementation. 

# Rubric

- 100% Correct Doubly-Linked List(DLL) implementation
  - All functions should be implemented. Do not rename the functions, but you may add any 'helper' functions if you deem necessary.
    - (e.g. You might have a 'double_linked_list_print' to help you debug)
  - There should be no memory leaks
  - There should be no bugs in your functions 
  - Your implementation will be graded by our set of unit tests, and we will check your code 'style' as well.

# Resources to help

-http://www.cplusplus.com/doc/tutorial/classes/
  



