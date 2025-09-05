//===- SVF-Teaching Assignment 2-------------------------------------//
//
//     SVF: Static Value-Flow Analysis Framework for Source Code
//
// Copyright (C) <2013->
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===-----------------------------------------------------------------------===//
/*
 // SVF-Teaching Assignment 2 : Source Sink ICFG DFS Traversal
 //
 // 
 */

#include <set>
#include "Assignment-2.h"
#include <iostream>
#include <sstream>
using namespace SVF;
using namespace std;

/// TODO: print each path once this method is called, and
/// add each path as a string into std::set<std::string> paths
/// Print the path in the format "START->1->2->4->5->END", where -> indicate an ICFGEdge connects two ICFGNode IDs

void ICFGTraversal::collectICFGPath(std::vector<unsigned> &path){

     std::ostringstream oss;
    oss << "START";
    for (unsigned id : path) {
        oss << "->" << id;
    }
    oss << "->END";
    const std::string s = oss.str();

    // print and record
    std::cout << s << std::endl;
    paths.insert(s);
    
}


/// TODO: Implement your context-sensitive ICFG traversal here to traverse each program path (once for any loop) from src to dst
void ICFGTraversal::reachability(const ICFGNode *src, const ICFGNode *dst)
{

     // 2) pair = <curNode, callstack>
    auto key = std::make_pair(src, callstack);

    // 3) if pair is visited then return
    if (visited.find(key) != visited.end())
        return;

    // 5) visited.insert(pair)
    visited.insert(key);

    // 6) path.push_back(curNode)
    path.push_back(src->getId());

    // 7–8) if src == snk -> collectICFGPath(path)
    if (src == dst) {
        collectICFGPath(path);
        // backtrack (23, 24)
        visited.erase(key);
        path.pop_back();
        return;
    }

    // 9) foreach edge in curNode.getOutEdges()
    for (const ICFGEdge *edge : src->getOutEdges()) {

        // 10–11) intra edge
        if (SVFUtil::dyn_cast<IntraCFGEdge>(edge)) {
            reachability(edge->getDstNode(), dst);
        }

        // 12–15) call edge
        else if (const CallCFGEdge *callEdge = SVFUtil::dyn_cast<CallCFGEdge>(edge)) {
            callstack.push_back(callEdge->getSrcNode());     // 13) push back(edge.src)
            reachability(callEdge->getDstNode(), dst);       // 14)
            callstack.pop_back();                            // 15)
        }

        // 16–22) return edge (
        else if (const RetCFGEdge *retEdge = SVFUtil::dyn_cast<RetCFGEdge>(edge)) {
            const CallICFGNode *callsite = retEdge->getCallSite();

            // 17–20) only follow if it matches top of stack
            if (!callstack.empty() && callstack.back() == callsite) {
                callstack.pop_back();                        // 18)
                reachability(retEdge->getDstNode(), dst);    // 19)
                callstack.push_back(callsite);               // 20) restore same callsite 
            }
            // 21–22) allow if callstack is empty 
            else if (callstack.empty()) {
                reachability(retEdge->getDstNode(), dst);
            }
            // else: not infeasible in this context; 
        }
    }

    // 23–24) backtrack
    visited.erase(key);
    path.pop_back();
}

