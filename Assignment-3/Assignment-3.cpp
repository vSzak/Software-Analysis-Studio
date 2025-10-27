//===- Assignment-3.cpp -- Taint analysis ------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013-2022>  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.

// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===----------------------------------------------------------------------===//
/*
 * Graph reachability, Andersen's pointer analysis and taint analysis
 *
 * Created on: Feb 18, 2024
 */

#include "Assignment-3.h"
#include "WPA/Andersen.h"
#include <sys/stat.h>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <iostream>
#include <string>

using namespace SVF;
using namespace llvm;
using namespace std;

/// TODO: Implement your context-sensitive ICFG traversal here to traverse each program path
/// by matching calls and returns while maintaining a `callstack`.
/// Sources and sinks are identified by implementing and calling `readSrcSnkFromFile`
/// Each path including loops, qualified by a `callstack`, should only be traversed once using a `visited` set.
/// You will need to collect each path from src to snk and then add the path to the `paths` set.
/// Add each path (a sequence of node IDs) as a string into std::set<std::string> paths
/// in the format "START->1->2->4->5->END", where -> indicate an ICFGEdge connects two ICFGNode IDs
void ICFGTraversal::reachability(const ICFGNode* src, const ICFGNode* dst)
{  
    //Stop if source or destination node is null
    if (!src || !dst) return;


    //Current state key = <node, callstack>
    auto key = std::make_pair(src, callstack);


    //If state has already been visited this, skip
    if (visited.find(key) != visited.end())
        return;


    //Mark state as visited and add the current node to the path
    visited.insert(key);
    path.push_back(src->getId());


    //Check if sink node has been reached
    if (src == dst) {


        //Print ICFGPath
        std::ostringstream oss;
        oss << "START";
        for (unsigned id : path) oss << "->" << id;
        oss << "->END";
        paths.insert(oss.str());


        //Backtrack
        //visited.erase(key);
        path.pop_back();
        return;
    }


    //Explore outgoing ICFG edges from the current node
    for (const ICFGEdge* edge : src->getOutEdges()) {


        // Intra-procedural edge
        if (SVFUtil::dyn_cast<IntraCFGEdge>(edge)) {
            reachability(edge->getDstNode(), dst);
        }


        //Call edge: push the callsite on the callstack, recurse, then pop
        else if (const CallCFGEdge* callEdge = SVFUtil::dyn_cast<CallCFGEdge>(edge)) {


            //Ensure the source of this edge is a CallICFGNode
            const CallICFGNode* callsitenode = SVFUtil::dyn_cast<CallICFGNode>(callEdge->getSrcNode());
            if (callsitenode) {


                //Add callsite to the callstack so returns can be matched later
                callstack.push_back(callsitenode);
                reachability(callEdge->getDstNode(), dst);


                //Restore the callstack after returning
                callstack.pop_back();
            } else {
                //Fallback if the src isn’t a CallICFGNode (defensive)
                reachability(callEdge->getDstNode(), dst);
            }
        }


        // Return edge: only follow if it matches the top of the callstack
        else if (const RetCFGEdge* retEdge = SVFUtil::dyn_cast<RetCFGEdge>(edge)) {
            const CallICFGNode* callsite = retEdge->getCallSite();


            if (!callstack.empty() && callstack.back() == callsite) {
               
                //Return matches the top of the callstack, so it is a valid return
                callstack.pop_back();
                reachability(retEdge->getDstNode(), dst);


                //Restore for other paths
                callstack.push_back(callsite);
            }
            else if (callstack.empty()) {
                // Allow “top-level” returns (e.g., no callsite context)
                reachability(retEdge->getDstNode(), dst);
            }
            // else: not infeasible in this context;
        }
    }


    // Backtrack
    path.pop_back();
    //visited.erase(key);
}
   




	


/// TODO: Implement your code to parse the two lines to identify sources and sinks from `SrcSnk.txt` for your
/// reachability analysis The format in SrcSnk.txt is in the form of
/// line 1 for sources  "{ api1 api2 api3 }"
/// line 2 for sinks    "{ api1 api2 api3 }"
void ICFGTraversal::readSrcSnkFromFile(const string& filename) 
{
    //Clear any old API names for sources and sinks
    checker_source_api.clear();
    checker_sink_api.clear();

    //Open the configuration file 
    std::ifstream inputFile(filename);
    if (!inputFile.is_open()) {
        std::cerr << "Cannot open SrcSnk config file: " << filename << "\n";
        abort();
    }
    //Skip comments and blank space
    auto nextMeaningfulLine = [&](std::string& outputLine) -> bool {
        std::string line;
        while (std::getline(inputFile, line)) {
            //Trim leading whitespaces
            size_t firstNonWhitespace = line.find_first_not_of(" \t\r\n");
            
            //Skip Whitespace-only lines
            if (firstNonWhitespace == std::string::npos) continue; 
           
            //Skip Commented Lines 
            if (line.compare(firstNonWhitespace, 2, "//") == 0 || line[firstNonWhitespace] == '#')
                continue;
            
                //Return the first non-empty, non-commented line
            outputLine = line;
            return true;
        }
        return false;
    };
    
    //Parse a Line Containing APIs inside braces
    auto parseBraceTokens = [&](const std::string& line, std::set<std::string>& outSet, const char* typeName) {

        //Expect line to contain {...} (e.g,  api1 api2 api3)
        size_t leftBrace = line.find('{');
        size_t rightBrace = line.rfind('}');
        if (leftBrace == std::string::npos || rightBrace == std::string::npos || rightBrace <= leftBrace) {
            std::cerr << "Bad format in " << typeName << " line: " << line << "\n";
            abort();
        }

        //Extract the substring inside the braces
        std::string insideBraces = line.substr(leftBrace + 1, rightBrace - leftBrace - 1);

        // Split the contents inside the braces by whitespace and add each API name to the set
        std::istringstream tokenStream(insideBraces);
        std::string apiName;
        while (tokenStream >> apiName) outSet.insert(apiName);

        if (outSet.empty()) {
            std::cerr << "No APIs found in " << typeName << " list.\n";
            abort();
        }
    };

    //The first non-empty line is the source list, the second is the sink list
    std::string srcLine, snkLine;
    if (!nextMeaningfulLine(srcLine) || !nextMeaningfulLine(snkLine)) {
        std::cerr << "SrcSnk file must contain two lines: sources then sinks.\n";
        abort();
    }
    
    //Parse both lines into sets
    parseBraceTokens(srcLine, checker_source_api, "sources");
    parseBraceTokens(snkLine, checker_sink_api,  "sinks");
}





// TODO: Implement your Andersen's Algorithm here
/// The solving rules are as follows:
/// p <--Addr-- o        =>  pts(p) = pts(p) ∪ {o}
/// q <--COPY-- p        =>  pts(q) = pts(q) ∪ pts(p)
/// q <--LOAD-- p        =>  for each o ∈ pts(p) : q <--COPY-- o
/// q <--STORE-- p       =>  for each o ∈ pts(q) : o <--COPY-- p
/// q <--GEP, fld-- p    =>  for each o ∈ pts(p) : pts(q) = pts(q) ∪ {o.fld}
/// pts(q) denotes the points-to set of q
void AndersenPTA::solveWorklist() {

    //p <--Addr-- o  =>  pts(p) ∪= {o}
    for (ConstraintGraph::const_iterator it = consCG->begin(), ie = consCG->end();
         it != ie; ++it) {
        ConstraintNode* n = it->second;
        for (ConstraintEdge* e : n->getAddrInEdges()) {
            const AddrCGEdge* addr = SVFUtil::cast<AddrCGEdge>(e);
            NodeID dst = addr->getDstID();  // pointer
            NodeID src = addr->getSrcID();  // object
            if (addPts(dst, src)) {
                pushIntoWorklist(dst);
            }
        }
    }

    //Propagate through COPY, GEP, LOAD, Store Edges until a fixed point is reached
    while (!isWorklistEmpty()) {
        NodeID nid = popFromWorklist();
        ConstraintNode* node = consCG->getConstraintNode(nid);

        // Direct edges: COPY and GEP
        for (ConstraintEdge* e : node->getDirectOutEdges()) {
            NodeID src = e->getSrcID();
            NodeID dst = e->getDstID();

            // COPY:  q <--COPY-- p   =>  pts(q) ∪= pts(p)
            if (const CopyCGEdge* copyEdge = SVFUtil::dyn_cast<CopyCGEdge>(e)) {
                if (unionPts(dst, src)) {
                    pushIntoWorklist(dst);
                }
                (void)copyEdge; //Used to prevent "unused-variable when compiling"
            }
            // GEP:  q <--GEP,fld-- p => pts(q) ∪ {o.fld}
            else if (const GepCGEdge* gep = SVFUtil::dyn_cast<GepCGEdge>(e)) {
                bool changed = false;

                // Constant GEP: known index/field offset -> precise propagation
                if (const NormalGepCGEdge* ngep = SVFUtil::dyn_cast<NormalGepCGEdge>(gep)) {
                    APOffset ap = ngep->getConstantFieldIdx();
                    const PointsTo& srcPts = getPts(src);
                    for (NodeID o : srcPts) {
                        NodeID fldObj = getGepObjVar(o, ap);
                        changed |= addPts(dst, fldObj);
                    }
                }
                // Variant GEP: unknown/variable field index —> conservative fallback
                else if (SVFUtil::isa<VariantGepCGEdge>(gep)) {
                    changed = unionPts(dst, src);
                }

                if (changed) {
                    pushIntoWorklist(dst);
                }
            }
        }

        // Indirect edges: LOAD AND STORE
        // LOAD:  q <--LOAD-- p  =>  q <--COPY-- o
        for (ConstraintEdge* e : node->getLoadOutEdges()) {
            const LoadCGEdge* ld = SVFUtil::cast<LoadCGEdge>(e);
            NodeID p = ld->getSrcID();
            NodeID q = ld->getDstID();
            const PointsTo& ptsP = getPts(p);
            for (NodeID o : ptsP) {
                // Add a constraint o -> q
                if (addCopyEdge(o, q)) {
                    pushIntoWorklist(q);
                }
                // Also propagate points-to set
                if (unionPts(q, o)) {
                    pushIntoWorklist(q);
                }
            }
        }

        //Store: q <--STORE-- p => o <--COPY-- p
        for (ConstraintEdge* e : node->getStoreOutEdges()) {
            const StoreCGEdge* st = SVFUtil::cast<StoreCGEdge>(e);
            NodeID p = st->getSrcID();
            NodeID q = st->getDstID();
            const PointsTo& ptsQ = getPts(q);
            for (NodeID o : ptsQ) {
                // Add a constraint p -> o
                if (addCopyEdge(p, o)) {
                    pushIntoWorklist(o);
                }
                // Also propagate points-to set
                if (unionPts(o, p)) {
                    pushIntoWorklist(o);
                }
            }
        }
    }
}

	


/// TODO: Checking aliases of the two variables at source and sink. For example:
/// src instruction:  actualRet = source();
/// snk instruction:  sink(actualParm,...);
/// return true if actualRet is aliased with any parameter at the snk node (e.g., via ander->alias(..,..))
bool ICFGTraversal::aliasCheck(const CallICFGNode* src, const CallICFGNode* snk) {
	      if (!src || !snk) return false;

    //Get its paired return node from the source callsite
    const RetICFGNode* retNode = src->getRetICFGNode();
    if (!retNode) return false; 

    //Get the actual return variable produced by the source
    const SVFVar* srcRet = retNode->getActualRet();
    if (!srcRet) return false;
    const NodeID srcId = srcRet->getId();

    //Iterate over all of the actual parameters of the sink callsite
    const CallICFGNode::ActualParmNodeVec& params = snk->getActualParms(); 
    for (const ValVar* p : params) {
        if (!p) continue;
        const NodeID pid = p->getId();

        //Use Andersen's pointer analysis to check aliasing between source return value and the sink parameter
        const AliasResult ar = ander->alias(srcId, pid);

        //If aliasing is possible, treat it as a potential taint flow 
        if (ar == AliasResult::MayAlias ||
            ar == AliasResult::MustAlias ||
            ar == AliasResult::PartialAlias) {
            return true;
        }
    }
    return false;
}

// Start taint checking.
// There is a tainted flow from p@source to q@sink
// if (1) alias(p,q)==true and (2) source reaches sink on ICFG.
void ICFGTraversal::taintChecking() {
	const fs::path& config = CUR_DIR() / "Tests/SrcSnk.txt";
	// configure sources and sinks for taint analysis
	readSrcSnkFromFile(config);
    
    //I had issues with parsing SrcSnk.text, used to help verify that the config file was read and parsed as expected -> checking config parsing
    SVFUtil::outs() << "[SrcSnk] sources=" << checker_source_api.size()
                << " sinks=" << checker_sink_api.size() << "\n";
    
    //Used to confirm the program actually contained source and sink calls ->checking ICFG matching
    auto srcs = identifySources(), snks = identifySinks();
    SVFUtil::outs() << "[ICFG] #source calls=" << srcs.size()
                << " #sink calls=" << snks.size() << "\n";

	// Set file permissions to read-only for user, group and others
	if (chmod(config.string().c_str(), S_IRUSR | S_IRGRP | S_IROTH) == -1) {
		std::cerr << "Error setting file permissions for " << config << ": " << std::strerror(errno) << std::endl;
		abort();
	}
	ander = new AndersenPTA(pag);
	ander->analyze();
	for (const CallICFGNode* src : identifySources()) {
		for (const CallICFGNode* snk : identifySinks()) {
			if (aliasCheck(src, snk))
				reachability(src, snk);
		}
	}
}

/*!
 * Andersen analysis
 */
void AndersenPTA::analyze() {
	initialize();
	initWorklist();
	do {
		reanalyze = false;
		solveWorklist();
		if (updateCallGraph(getIndirectCallsites()))
			reanalyze = true;
	} while (reanalyze);
	finalize();
}