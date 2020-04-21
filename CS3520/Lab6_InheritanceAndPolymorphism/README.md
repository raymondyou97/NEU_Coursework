# TODO Please edit the following information in your assignment

- Name: Raymond You
- How many hours did it take you to complete this assignment? 5
- Did you collaborate with any other students/TAs/Professors? No
- Did you use any external resources? (Cite them below)
  - N/A
- (Optional) What was your favorite part of the assignment?
- (Optional) How would you improve the assignment?

# Logistics

For this assignment (and every assignment/lab), you must login into the servers through `your_khoury_name@login.khoury.neu.edu` to complete and test your work. The reason is the examples I will provide below are compiled strictly for our machines architecture, and this is a consistent architecture where your submission will be graded.


# Creating an inheritance hierarchy for your containers. 

By this point you should have converted our DLL, Stack, Queue and Vector C implementations to C++ classes.
As you can see all of our containers share commoon functions, such as ```push_back```, ```pop_back```, ```size``` etc.
In this lab we are going to introduce a inheritance to mimic the Java Collections hierarchy.

## TODO: Creating the Container interface

* Firstly define all of our container functions in an pure virtual class ( think Interface ), this should be an ```hpp``` file.
* Then think about the abstract class/es you would like to define (there could be multiple abstract classes). Note that
Queue and Vector could share an abstract classes since they both use an array as their underlying structure. 
* Provide concrete implementations for all of our containers that either extend our pure virtual base class, or the abstract
class that you wrote. If a container doesn't support an operation defined in the interface you can trhow an unsuported operation
exception. Later we can fine tune our hierarchy to avoid this issue. 




### Unit Tests

At this point we will not modify our unit tests. In a later lab we will abstract our unit tests to work on our bases types as 
opposed to concrete implementations.

# Rubric

- 100% Correct Implementations.
  - All functions should be implemented. Do not rename the functions, but you may add any 'helper' functions if you deem necessary.
    - (e.g. You might have a 'double_linked_list_print' to help you debug)
  - There should be no memory leaks
  - There should be no bugs in your functions 
  - Your implementation will be graded by our set of unit tests, and we will check your code 'style' as well.

# Resources to help

-http://www.cplusplus.com/doc/tutorial/classes/
  



