//
//  main.cpp
//  TreeHomeworkCode
//
//  Created by Vidoje Mihajlovikj on 3/15/20.
//  Copyright © 2020 Vidoje Mihajlovikj. All rights reserved.
//

#include <iostream>
#include "Tree.hpp"
#include <vector>
#include <sstream>
#include <assert.h>
#include<algorithm>

void assertEquals(std::string expected, std::string actual, std::string testName){
    if (expected.compare(actual) == 0 ){
        std::cout << "Pass: " << testName << std::endl;
    }else{
        std::cout << "Failed: " << testName << std::endl;
        std::cout << "Expected: " << expected << std::endl;
        std::cout << "Actual: " << actual << std::endl;
    }
    std::cout << "-----------------------------------" << std::endl;
}

void testAscendingPrintWithOstreamIterator(Tree t, std::string expectedOutput){
    std::stringstream ss;
    
    std::ostream_iterator<int> out_it (ss,", ");
    t.appendAscnedingOstreamIter(out_it);
    assertEquals(expectedOutput, ss.str(), "testAscendingPrintWithOstreamIterator" );
}

void testAscendingPrintWithGenericIter(Tree t, std::string expectedOutput){
    std::stringstream ss;
    
    std::ostream_iterator<int> out_it (ss,", ");
    t.appendAscnedingGenericIter(out_it);
    
    assertEquals(expectedOutput, ss.str(), "testAscendingPrintWithGenericIter" );
}

void testBSTPrintWithGenericIter(Tree t, std::string expectedOutput){
    std::stringstream ss;
    std::ostream_iterator<int> out_it (ss,", ");
    t.appendViaBST(out_it);
    assertEquals(expectedOutput, ss.str(), "testBSTPrintWithGenericIter" );
}

void testCopyToVectorBSTPrintWithGenericIter(Tree t, std::string expectedOutput){
    std::stringstream ss;
    std::ostream_iterator<int> out_it (ss,", ");
    std::vector<int> vector(7);
    
    t.appendViaBST(vector.begin());
    std::for_each(vector.begin(), vector.end(), [&ss](int & n){ ss << n << ", ";});
    assertEquals(expectedOutput, ss.str(), "testCopyToVectorBSTPrintWithGenericIter" );
}

void testCopyToVectorAscendingUsingGenericIterator(Tree t, std::string expectedOutput){
    std::stringstream ss;
    std::vector<int> vector(7);
    t.appendAscnedingGenericIter(vector.begin());
    std::for_each(vector.begin(), vector.end(), [&ss](int & n){ ss << n << ", ";});
    
    assertEquals(expectedOutput, ss.str(), "copyToVectorAscendingUsingGenericIterator" );
}

void testBSTForwardIterator(Tree t, std::string expectedOutput){
    std::stringstream ss;
    
    std::for_each(t.begin(), t.end(), [&ss](int n){ ss << n << ", ";});
    assertEquals(expectedOutput, ss.str(), "testBSTForwardIterator" );
}

void testBSTForwardIteratorVectorCopy(Tree t, std::string expectedOutput){
    std::stringstream ss;
    std::vector<int> vector(7);
    std::copy(t.begin(), t.end(), vector.begin());
    std::for_each(vector.begin(), vector.end(), [&ss](int n){ ss << n << ", ";});
    assertEquals(expectedOutput, ss.str(), "testBSTForwardIteratorVectorCopy" );
}

void testTreeInserterIterator(Tree t, std::string expectedOutput){
    std::stringstream ss;
    std::vector<int> vector = { 50, 30, 60, 25, 45, 65, 70};
    TreeInserterIterator treeInserter(t);
    std::copy(vector.begin(), vector.end(), treeInserter);
    
    std::for_each(t.begin(), t.end(), [&ss](int n){ ss << n << ", ";});
    assertEquals(expectedOutput, ss.str(), "testTreeInserterIterator" );
}

int main(int argc, const char * argv[]) {
    Tree t = { 50, 30, 60, 25, 45, 65, 70};
    //10pts
    testAscendingPrintWithOstreamIterator(t, "25, 30, 45, 50, 60, 65, 70, ");
    //10pts
    testAscendingPrintWithGenericIter(t, "25, 30, 45, 50, 60, 65, 70, ");
    //10pts
    testCopyToVectorAscendingUsingGenericIterator(t, "25, 30, 45, 50, 60, 65, 70, ");
    //30pts
    testBSTPrintWithGenericIter(t, "50, 30, 60, 25, 45, 65, 70, ");
    testCopyToVectorBSTPrintWithGenericIter(t, "50, 30, 60, 25, 45, 65, 70, ");
    //20pts
    testTreeInserterIterator({}, "50, 30, 60, 25, 45, 65, 70, ");
    //20Pts;
    testBSTForwardIterator(t, "50, 30, 60, 25, 45, 65, 70, ");
    testBSTForwardIteratorVectorCopy(t, "50, 30, 60, 25, 45, 65, 70, ");
    return 0;
}
