//
//  main.cpp
//  GraphHWCode
//
//  Created by Vidoje Mihajlovikj on 3/30/20.
//  Copyright © 2020 Vidoje Mihajlovikj. All rights reserved.
//

#include <iostream>
#include "MyGraph.hpp"

void assertEquals(bool value, const char * test){
    if ( value ){
        std::cout << "Passed: " << test << std::endl;
    }
    else{
        std::cout << "--FAILED--" << test << std::endl;
    }
}

void testEmptyGraph(MyGraph g){
    assertEquals(g.numNodes() == 0, __FUNCTION__ );
}

void testNonEmptyGraph(MyGraph g, int expectedSize){
    assertEquals(g.numNodes() == expectedSize, __FUNCTION__ );
}

void testAddingSameNode(MyGraph g, int expectedSize){
    assertEquals(g.numNodes() == expectedSize, __FUNCTION__ );
}

void testContainsPositive(MyGraph g, int node){
    assertEquals(g.containsNode(node), __FUNCTION__ );
}

void testContainsNegative(MyGraph g, int node){
    assertEquals(!g.containsNode(node), __FUNCTION__ );
}

void testRemovePositive(MyGraph g, int node){
    bool before = g.containsNode(node);
    g.removeNode(node);
    
    assertEquals(before && !g.containsNode(node), __FUNCTION__ );
}

void testRemoveNegative(MyGraph g, int node){
    bool before = g.containsNode(node);
    g.removeNode(node);
    
    assertEquals(!before && !g.containsNode(node), __FUNCTION__ );
}

void testAddEdge(MyGraph g, int numEdges){
    assertEquals(g.numEdges() == numEdges, __FUNCTION__ );
}

void testRemoveEdge(MyGraph g, std::pair<int,int> edge,  int numEdges){
    bool before = g.numEdges() == numEdges + 1;
    g.removeEdge( edge.first, edge.second );
    bool after = g.numEdges() == numEdges;
    assertEquals( before && after, __FUNCTION__ );
}

void testRemoveNodeWithEdges(MyGraph g, int node){
    bool before = g.numEdges() == 3;
    g.removeNode(node);
    bool after = g.numEdges() == 0;
    assertEquals(before && after, __FUNCTION__);
    
}

void testNeighbors(MyGraph g, int node){
    bool condition = g.getNeighbors(node).size()== 0;
    std::vector<int> neighbors = g.getNeighbors(node);
    
    for_each(neighbors.begin(), neighbors.end(), [](const int & n){std::cout << n << ", "; });
    std::cout << std::endl;
    assertEquals(condition, __FUNCTION__);
}



void testHasCycle(MyGraph g, bool containsCycle){
    assertEquals( g.hasCycle() == containsCycle, __FUNCTION__);
}

void testIsReachable(MyGraph g, int src, int dst, bool reachable){
    assertEquals( g.isReachalbe(src, dst) == reachable, __FUNCTION__);
}

void testShortestPath(MyGraph g, int src, int dst, const std::vector<int> & sPath){
    std::vector<int> path = g.shortestPath(src,dst);
    //bool same = std::equal(sPath.cbegin(), sPath.cend(), path.cbegin() ); This seems to fail on empty vectors.
    bool same = path == sPath; //since we are dealing with ints we can use ==.
    assertEquals(same, __FUNCTION__);
}

int main(int argc, const char * argv[]) {
    
    testEmptyGraph( { {}, {} } );
    testNonEmptyGraph( { {1,2,3}, {} }, 3);
    testAddingSameNode( { {1,1,1}, {} }, 1);
    testContainsPositive( { {1,1,1}, {} }, 1);
    testContainsNegative( { {1,1,1}, {} }, 2);
    testRemovePositive( { {1,1,1}, {} }, 1);
    testRemoveNegative( { {1,1,1}, {} }, 2);
    testAddEdge( { {1,2}, { {1,2} } }, 1);
    testAddEdge( { {1,2,3}, { {1,2}, {2,3}, {1,3} } }, 3);
    testRemoveEdge( { {1,2,3}, { {1,2}, {2,3}, {1,3} } }, {1,3}, 2);
    testRemoveNodeWithEdges( { {1,2,3,4}, { {1,2}, {2,3}, {4,2} } }, 2); // 1->2->3; 1->    3
    testNeighbors( { {1,2,3,4}, { {1,2}, {2,3}, {2,4} } }, 4);
    //20pts
    testIsReachable( { {1,2,3,4,5,6,7,8,9,10}, { {1,2}, {2,3}, {2,5}, {5,6}, {6,3}, {3,4}, {4,7}, {3,8}, {7,9}, {7,10} } }, 5, 1, false);
    testIsReachable( { {1,2,3,4,5,6,7,8,9,10}, { {1,2}, {2,3}, {2,5}, {5,6}, {6,3}, {3,4}, {4,7}, {3,8}, {7,9}, {7,10} } }, 5, 10, true);
    //30pts
    testHasCycle( { {1,2,3,4,5,6,7}, { {1,2}, {2,3}, {2,5}, {5,6}, {6,3}, {3,4}, {4,7} } }, false);
    testHasCycle( { {1,2,3,4,5,6,7}, { {1,2}, {3,2}, {2,5}, {5,6}, {6,3}, {3,4}, {4,7} } }, true);
    
    //50ths
    testShortestPath( { {1,2,3,4,5,6,7,8,9,10}, { {1,2}, {2,3}, {2,5}, {5,6}, {6,3}, {3,4}, {4,7}, {3,8}, {7,9}, {7,10},{2,8}, {8,7} } }, 1,7, {1,2,8,7});
    testShortestPath( { {1,2,3,4,5,6,7,8,9,10}, { {1,2}, {2,3}, {2,5}, {5,6}, {6,3}, {3,4}, {4,7}, {3,8}, {7,9}, {7,10},{2,8} } }, 1,7, {1,2,3,4,7});
    
    testShortestPath( { {1,2,3,4,5,6,7,8,9,10}, { {1,2}, {2,3}, {2,5}, {5,6}, {6,3}, {3,4}, {4,7}, {3,8}, {7,9}, {7,10},{2,8} } }, 4,2, {});
    
    // insert code here...
    std::cout << "Hello, World!\n";
    return 0;
}
