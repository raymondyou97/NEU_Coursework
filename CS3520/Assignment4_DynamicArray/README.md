# Please edit the following information in your assignment

- Name: Raymond You
- How many hours did it take you to complete this assignment? 4
- Did you collaborate with any other students/TAs/Professors? No
- Did you use any external resources? (Cite them below)
  - N/A
- (Optional) What was your favorite part of the assignment?
- (Optional) How would you improve the assignment? It would be nice if the assignment was fully fleshed out with no typos/errors when it is assigned. I have been finding myself waiting till the last day for all the problems to be fixed before starting...

# Logistics

For this assignment (and every assignment/lab), you must login into the servers through `your_khoury_name@login.khoury.neu.edu` to complete and test your work. The reason is the examples I will provide below are compiled strictly for our machines architecture, and this is a consistent architecture where your submission will be graded.


# Vector/DynamicArray *(Vector)*

So far you've implemented a singly linked list, a doubly linked list a stack, and a queue. In this assignment we are going to
implement a vector (or a dynamic array. You might be familiar with ArrayList from java). 

## What is a Vector <sup>[excerpt taken from cpplusplus.com](#myfootnote1)</sup> 

Vectors are sequence containers representing arrays that can change in size.

Just like arrays, vectors use contiguous storage locations for their elements, which means that their elements can also 
be accessed using offsets on regular pointers to its elements, and just as efficiently as in arrays. But unlike arrays, 
their size can change dynamically, with their storage being handled automatically by the container.

Internally, vectors use a dynamically allocated array to store their elements. This array may need to be reallocated in 
order to grow in size when new elements are inserted, which implies allocating a new array and moving all elements to it. 
This is a relatively expensive task in terms of processing time, and thus, vectors do not reallocate each time an element 
is added to the container.

Instead, vector containers may allocate some extra storage to accommodate for possible growth, and thus the container may 
have an actual capacity greater than the storage strictly needed to contain its elements (i.e., its size). Libraries can 
implement different strategies for growth to balance between memory usage and reallocations, but in any case, reallocations 
should only happen at logarithmically growing intervals of size so that the insertion of individual elements at the 
end of the vector can be provided with amortized constant time complexity (see push_back).

Therefore, compared to arrays, vectors consume more memory in exchange for the ability to manage storage and grow dynamically
in an efficient way.

Compared to the other dynamic sequence containers (deques, lists and forward_lists), vectors are very efficient accessing its
elements (just like arrays) and relatively efficient adding or removing elements from its end. For operations that involve 
inserting or removing elements at positions other than the end, they perform worse than the others, and have less consistent 
iterators and references than lists and forward_lists.

<a name="myfootnote1">1</a>: http://www.cplusplus.com/reference/vector/vector/


# To Do

Usa a dymically allocated integer array (i.e allocated on the heap ) to help you implement a vector of integers. Note that
later we can see how to generallize this to any sort of data. 

Implement the class provded to you in the .hpp file. 

### Unit Tests

A unit test is a standalone test that checks for the correctness of a specific use case in your code. 
In our case, we are testing if we have a working vector implementation. 

Please write unit tests to test your implementation.

# Rubric

- 100% Correct Vector implementation
  - All functions should be implemented. Do not rename the functions, but you may add any 'helper' functions if you deem necessary.
    - (e.g. You might have a 'double_linked_list_print' to help you debug)
  - There should be no memory leaks
  - There should be no bugs in your functions 
  - Your implementation will be graded by our set of unit tests, and we will check your code 'style' as well.

# Resources to help
  - https://www.geeksforgeeks.org/how-do-dynamic-arrays-work/
  _ https://en.wikipedia.org/wiki/Dynamic_array
  - http://www.cplusplus.com/reference/vector/vector/
  
# Feedback Loop

(An optional task that will reinforce your learning throughout the semester)

- Investigate/Review more data strutures on this webpage: https://visualgo.net/en/list
  - There are visuals for the doubly-linked list here!
  - Use them as a *rough* outline for the general concept. Do make sure to follow the specifications above.

