//
//  MyGraph.hpp
//  GraphHWCode
//
//  Created by Vidoje Mihajlovikj on 3/30/20.
//  Copyright © 2020 Vidoje Mihajlovikj. All rights reserved.
//

#ifndef MyGraph_hpp
#define MyGraph_hpp

#include <stdio.h>
#include <unordered_map>
#include <vector>
#include <set>
#include <queue>
#include <algorithm>

class Node {
private:
    int data;
public:
    Node(int data) {
        this->data = data;
    }

    int & getData() {
        return this->data;
    }
};

class MyGraph{
private:
    std::unordered_map<int, Node *> nodes;
    std::unordered_multimap<Node *, Node *> outEdges;
    std::unordered_multimap<Node *, Node* > inEdges;

    Node * getNode(int value) {
        if ( containsNode(value) ) {
            //the return is an iterator to pair.
            return nodes.find(value)->second;
        } else {
            return NULL;
        }
    }

    void removeInEdge(Node * srcNode, Node * dstNode) {
        rangePair rPair = inEdges.equal_range(srcNode);
        for (multimapIter start = rPair.first; start != rPair.second; start++) {
            if (start->second == dstNode) {
                inEdges.erase (start);
                break;
            }
        }
    }

    void BFS(int src, int parentOfNode[], bool nodesVisited[]) {
        std::queue<int> queue;
        std::vector<int> neighbors;
        // set data to default state before running BFS
        for (int i = 1; i <= this->numNodes(); i++) {
            nodesVisited[i] = false;
            parentOfNode[i] = -1;
        }

        // set values for source node
        nodesVisited[src] = true;
        queue.push(src);

        // iterate until queue of nodes is empty
        while (queue.size() > 0) {
            int currentNode = queue.front();
            queue.pop();
            neighbors = this->getNeighbors(currentNode);
            // go through all neighbors of current node
            for (int node: neighbors) {
                // new node found
                if (!nodesVisited[node]) {
                    queue.push(node);
                    parentOfNode[node] = currentNode;
                    nodesVisited[node] = true;
                }
            }
        }
    }

    bool cycleHelper(int node) {
        std::queue<int> queue;
        int size = this->numNodes();
        int nodesVisited[size];
        for (int i = 1; i <= size; i++) {
            nodesVisited[i] = 0;
        }

        queue.push(node);
        while (queue.size() > 0) {
            int currentNode = queue.front();
            queue.pop();
            nodesVisited[currentNode]++;

            // if we reach the intial source node more than once, we have a loop
            if (nodesVisited[node] > 1)
                return true;

            std::vector<int> neighbors = this->getNeighbors(currentNode);
            for (int node: neighbors) {
                queue.push(node);
            }
        }
        return false;
    }

public:
    typedef std::initializer_list<int> nodeList;
    typedef std::initializer_list< std::pair<int, int> > edgeList;
    typedef std::unordered_multimap<Node *, Node*>::iterator multimapIter;
    typedef std::pair<multimapIter, multimapIter> rangePair;

    MyGraph( nodeList nList, edgeList eList) {
        for (auto itr = nList.begin(); itr != nList.end(); itr++) {
            addNode(*itr);
        }

        for (auto itr = eList.begin(); itr != eList.end(); itr++) {
            addEdge(itr->first, itr->second);
        }
    }

    ~MyGraph() {
        for (std::pair<int, Node *> p: nodes) {
            delete(p.second);
        }
    }

    void addNode(int value) {
        if (!containsNode(value)) {
            Node * node = new Node(value);
            nodes.insert({value, node});
        }
    }

    void removeNode(const int & value){
        Node * node = getNode(value);
        if (node == NULL) return;
        rangePair rangePairItr = inEdges.equal_range( node );
        for (multimapIter start = rangePairItr.first; start != rangePairItr.second; start++) {
            removeEdge(start->second->getData(), start->first->getData());
        }
        rangePairItr= outEdges.equal_range(node);
        for (multimapIter start = rangePairItr.first; start != rangePairItr.second; start++ ) {
            removeInEdge(start->second, start->first);
        }
        outEdges.erase(node);
        inEdges.erase(node);
        nodes.erase(value);
    }

    bool containsNode(const int & value) {
        return nodes.find(value) != nodes.end();
    }

    size_t numNodes() const {
        return nodes.size();
    }

    void removeEdge(const int & src, const int & dst) {
        if (!containsNode(src) || !containsNode(dst)) {
            return;
        }
        Node * srcNode = getNode(src);
        Node * dstNode = getNode(dst);

        if (srcNode == NULL || dstNode == NULL) {
            return;
        }
        rangePair rPair = outEdges.equal_range(srcNode);
        for ( multimapIter start = rPair.first; start != rPair.second; start++) {
            if (start->second == dstNode) {
                outEdges.erase (start);
                break;
            }
        }
    }

    void addEdge(const int & src, const int & dst) {
        if (!containsNode(src) || !containsNode(dst)) {
            return;
        }
        Node * srcNode = getNode(src);
        Node * dstNode = getNode(dst);

        if (srcNode == NULL || dstNode == NULL) {
            return;
        }

        outEdges.insert({ srcNode, dstNode});
        inEdges.insert({ dstNode, srcNode });
    }

    std::vector<int> getNeighbors(const int & value) {
        std::vector<int> neighbors;

        Node * node = getNode(value);
        if (node == NULL)
            return neighbors;

        rangePair rangePairNeighbors = outEdges.equal_range(node);
        for (multimapIter itr = rangePairNeighbors.first; itr != rangePairNeighbors.second; itr++) {
            neighbors.push_back(itr->second->getData());
        }
        return neighbors;
    }

    size_t numEdges(){
        return outEdges.size();
    }

    bool isReachalbe(int src, int dst) {
        int size = this->numNodes();
        int parentOfNode[size];
        bool nodesVisited[size];

        BFS(src, parentOfNode, nodesVisited);

        // if dst is not visited, it's unreachable from src
        return nodesVisited[dst];
    }

    // Returns true if the graph has a cycle, false otherwise.
    bool hasCycle() {
        std::unordered_map<int, Node *> allNodes = this->nodes;
        for (std::pair<int, Node *> node_pair: allNodes) {
            bool hasCycle = cycleHelper(node_pair.first);
            if (hasCycle) return true;
        }
        return false;
    }

    // Returns the shortest path between src and dst as a vector of nodes that need to be g.visited.
    std::vector<int> shortestPath(int src, int dst) {
        std::vector<int> path;
        int size = this->numNodes();
        int parentOfNode[size];
        bool nodesVisited[size];

        BFS(src, parentOfNode, nodesVisited);

        // if dst is not visited, it's unreachable from src
        if (!nodesVisited[dst]) return path;

        // trace back the path from dst to source by following the parents upwards
        int startNode = dst;
        path.insert(path.begin(), startNode);
        while (parentOfNode[startNode] != -1) {
            path.insert(path.begin(), parentOfNode[startNode]);
            startNode = parentOfNode[startNode];
        }
        return path;
    }
};

#endif
