//
//  Q3.hpp
//  CS3520_Exam2_Q1
//
//  Created by Vidoje Mihajlovikj on 4/9/20.
//  Copyright © 2020 Vidoje Mihajlovikj. All rights reserved.
//

#ifndef Q3_hpp
#define Q3_hpp

#include <stdio.h>
#include <set>

/*
 Q3. Write a template function working on iterators, that will find the number of elements common to both ranges.
 You can assume that both ranges are going to contain the same type of element and that the type has operator== defined.
 i.e. ints, std::string etc.
 You may assume that each range will have unique elements. For example:
 {1,2,3,4,5} and {0,2,4,6} should return a count of 2, since 2 and 4 are common to both lists.
 You can assume that the input containers are not going to have duplicate elements. For example you are not going
 to see input such us this {1,2,2,2,2,3,4}, all elements will be unique.
 
 Please note your intersection function should not work on containers but rather on iterators.
 You can take a look at the test to get an idea of what the function signature should be like.
 
 Your function must be templatized.
 
 */



template<class Iterator1, class Iterator2>
int intersection(Iterator1 start, Iterator1 end, Iterator2 start1, Iterator2 end1) {
    std::set<int> my_set;
    int count = 0;

    while (start != end) {
        my_set.insert(*start);
        start++;
    }

    while (start1 != end1) {
        if (my_set.find(*start1) != my_set.end())
            count++;

        start1++;
    }
    return count;
}


#endif /* Q3_h */
