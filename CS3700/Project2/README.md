# Project 2

- BGP Router
- Team Name: PythonCats
- Team Members: Raymond You, Oliver Zheng

## High-level Approach
First, we made sure we were able to connect to our neighbors and successfully send messages and receive messages back. We then checked that we were able to serialize and deserialize the JSON properly. Finally, we started working on the actual project aka the router functionalities by following it step by step and testing after each step to make sure we didn't break any past correct functionality. We started off with basic support for update and data messages and then dump messages to get the base level-1 tests passing. We then started implementing each rule of the forwarding table implementation one at a time, following the instructions and specifications in the assignment. After getting all the level-2 tests passing, we started on the revoke messages which allows you to remove paths from the forwarding table and finally the level-3 tests were passing. Next, we enforced the peering and provider/customer relationships to make sure that the correct steps were followed based off of the routers type (customer, peer, provider) and level-4 tests were now passing. Next, we implemented longest prefix matching so that the best route would be chosen and tests 5 passing. Finally, we implemented coalesceing which allowed for route aggregation and disaggregation.

## Challenges Faced
It was difficult to keep track of all the data that was going on, especially all the IP addresses, where they should be sent. Especially as the tests got more complex, the route table got bigger and bigger and more data was being passed around, so even though we were printing everything for testing and debugging purposes, as it went on it got harder to read the long messages printed out. Prefix matching was tricky as we checked if the bits were equal (first == second) and some of them weren't equal lengths aka missing 0s at the end, and the equality was returning false when it should've been true. Finally, route aggregation and disaggregation was difficult as we weren't sure where to start and what to do originally. After reading the section and looking at the example, it became more clear. 

Another challenged we faced was getting disaggregation to work. Initially we didn't take into account the fact that 2 aggregation could potentially need to be aggregated. Afterwards, we realized that the way we stored routes, updates, and revokes were wrong as the same object was in all 3, so when one was edited, the contents of all 3 was also edited. 

## Overview of Testing
Testing was primarily done through printing DEBUG statements to STDOUT. With each step along the way, we would print out some form of test message to ensure our code was doing what we wanted it to do. We would also print out the routing table before an operation and the routing table after the operation to ensure our router was doing what we wanted it to do. We would also output the routes, revokes, and updates to make sure the state of all was correct.
