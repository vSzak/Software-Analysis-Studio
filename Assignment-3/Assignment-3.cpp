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
    if (!src || !dst) return;

    // State key = <node, callstack>
    auto key = std::make_pair(src, callstack);

    // If we've already visited this (node,callstack) state, stop.
    if (visited.find(key) != visited.end())
        return;

    // Mark visited and extend current path
    visited.insert(key);
    path.push_back(src->getId());

    // If we've reached the sink, build "START->...->END", record, and backtrack
    if (src == dst) {
        std::ostringstream oss;
        oss << "START";
        for (unsigned id : path) oss << "->" << id;
        oss << "->END";
        const std::string s = oss.str();
        std::cout << s << std::endl;
        paths.insert(s);

        // backtrack
		visited.erase(key);
        path.pop_back();
        return;
    }

    // Explore outgoing ICFG edges
    for (const ICFGEdge* edge : src->getOutEdges()) {

        // Intra-procedural edge
        if (SVFUtil::dyn_cast<IntraCFGEdge>(edge)) {
            reachability(edge->getDstNode(), dst);
        }

        // Call edge: push the callsite on the callstack, recurse, then pop
        else if (const CallCFGEdge* callEdge = SVFUtil::dyn_cast<CallCFGEdge>(edge)) {
            // IMPORTANT: ensure callstack stores CallICFGNode*
            const CallICFGNode* callsitenode = SVFUtil::dyn_cast<CallICFGNode>(callEdge->getSrcNode());
            if (callsitenode) {
                callstack.push_back(callsitenode);
                reachability(callEdge->getDstNode(), dst);
                callstack.pop_back();
            } else {
                // Fallback if the src isn’t a CallICFGNode (defensive)
                reachability(callEdge->getDstNode(), dst);
            }
        }

        // Return edge: only follow if it matches the top of the callstack
        else if (const RetCFGEdge* retEdge = SVFUtil::dyn_cast<RetCFGEdge>(edge)) {
            const CallICFGNode* callsite = retEdge->getCallSite();

            if (!callstack.empty() && callstack.back() == callsite) {
                // Matched return: pop, recurse, then restore
                callstack.pop_back();
                reachability(retEdge->getDstNode(), dst);
                callstack.push_back(callsite);
            }
            else if (callstack.empty()) {
                // Allow “top-level” returns (e.g., external/library exits)
                reachability(retEdge->getDstNode(), dst);
            }
            // else: mismatched return in this context — skip
        }
    }

    // Backtrack
    path.pop_back();
    visited.erase(key);
}
	


/// TODO: Implement your code to parse the two lines to identify sources and sinks from `SrcSnk.txt` for your
/// reachability analysis The format in SrcSnk.txt is in the form of
/// line 1 for sources  "{ api1 api2 api3 }"
/// line 2 for sinks    "{ api1 api2 api3 }"
void ICFGTraversal::readSrcSnkFromFile(const string& filename) 
{
    // Reset any old entries
    checker_source_api.clear();
    checker_sink_api.clear();

    std::ifstream in(filename);
    if (!in.is_open()) {
        std::cerr << "Cannot open SrcSnk config file: " << filename << "\n";
        abort();
    }

    auto nextMeaningfulLine = [&](std::string& out) -> bool {
        std::string s;
        while (std::getline(in, s)) {
            // trim leading spaces
            size_t b = s.find_first_not_of(" \t\r\n");
            if (b == std::string::npos) continue;          // empty line
            if (s.compare(b, 2, "//") == 0 || s[b] == '#') // comment
                continue;
            out = s;
            return true;
        }
        return false;
    };

    auto parseBraceTokens = [&](const std::string& line,
                                std::set<std::string>& outSet,
                                const char* which) {
        // find {...} no matter what prefix (e.g., "source -> " or "sink -> ")
        size_t l = line.find('{');
        size_t r = line.rfind('}');
        if (l == std::string::npos || r == std::string::npos || r <= l) {
            std::cerr << "Bad format in " << which << " line: " << line << "\n";
            abort();
        }
        std::string inside = line.substr(l + 1, r - l - 1);
        std::istringstream iss(inside);
        std::string tok;
        while (iss >> tok) outSet.insert(tok);

        if (outSet.empty()) {
            std::cerr << "No APIs found in " << which << " list.\n";
            abort();
        }
    };

    // By spec: first meaningful line = sources, second = sinks
    std::string srcLine, snkLine;
    if (!nextMeaningfulLine(srcLine) || !nextMeaningfulLine(snkLine)) {
        std::cerr << "SrcSnk file must contain two lines: sources then sinks.\n";
        abort();
    }

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
    // ------------------------------------------------------------
    // 1) Seed with Address edges:  p <--Addr-- o  =>  pts(p) ∪= {o}
    // ------------------------------------------------------------
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

    // ------------------------------------------------------------
    // 2) Propagate until fixed-point
    // ------------------------------------------------------------
    while (!isWorklistEmpty()) {
        NodeID nid = popFromWorklist();
        ConstraintNode* node = consCG->getConstraintNode(nid);

        // ---------- (a) Direct edges: COPY and GEP ----------
        for (ConstraintEdge* e : node->getDirectOutEdges()) {
            NodeID src = e->getSrcID();
            NodeID dst = e->getDstID();

            // COPY:  q <--COPY-- p   =>  pts(q) ∪= pts(p)
            if (const CopyCGEdge* cpy = SVFUtil::dyn_cast<CopyCGEdge>(e)) {
                if (unionPts(dst, src)) {
                    pushIntoWorklist(dst);
                }
                (void)cpy;
            }
            // GEP:  q <--GEP,fld-- p
            else if (const GepCGEdge* gep = SVFUtil::dyn_cast<GepCGEdge>(e)) {
                bool changed = false;

                // Constant (normal) GEP: use concrete field offset
                if (const NormalGepCGEdge* ngep = SVFUtil::dyn_cast<NormalGepCGEdge>(gep)) {
                    APOffset ap = ngep->getConstantFieldIdx();
                    const PointsTo& srcPts = getPts(src);
                    for (NodeID o : srcPts) {
                        NodeID fldObj = getGepObjVar(o, ap);
                        changed |= addPts(dst, fldObj);
                    }
                }
                // Variant GEP: unknown field index — conservative field-insensitive fallback
                else if (SVFUtil::isa<VariantGepCGEdge>(gep)) {
                    changed = unionPts(dst, src);
                }

                if (changed) {
                    pushIntoWorklist(dst);
                }
            }
        }

        // ---------- (b) LOAD ----------
        // Rule:  q <--LOAD-- p  =>  for o ∈ pts(p):  (i) add edge o -> q, (ii) pts(q) ∪= pts(o)
        for (ConstraintEdge* e : node->getLoadOutEdges()) {
            const LoadCGEdge* ld = SVFUtil::cast<LoadCGEdge>(e);
            NodeID p = ld->getSrcID();
            NodeID q = ld->getDstID();
            const PointsTo& ptsP = getPts(p);
            for (NodeID o : ptsP) {
                // add constraint o -> q
                if (addCopyEdge(o, q)) {
                    pushIntoWorklist(q);
                }
                // IMPORTANT: propagate now, since 'o' (an object) won't change later
                if (unionPts(q, o)) {
                    pushIntoWorklist(q);
                }
            }
        }

        // ---------- (c) STORE ----------
        // Rule:  q <--STORE-- p  =>  for o ∈ pts(q):  (i) add edge p -> o, (ii) pts(o) ∪= pts(p)
        for (ConstraintEdge* e : node->getStoreOutEdges()) {
            const StoreCGEdge* st = SVFUtil::cast<StoreCGEdge>(e);
            NodeID p = st->getSrcID();
            NodeID q = st->getDstID();
            const PointsTo& ptsQ = getPts(q);
            for (NodeID o : ptsQ) {
                // add constraint p -> o
                if (addCopyEdge(p, o)) {
                    pushIntoWorklist(o);
                }
                // IMPORTANT: propagate now
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

    // 1) find the value produced by source
    const RetICFGNode* retNode = src->getRetICFGNode();
    if (!retNode) return false;  // handle “no return value” sources if needed

    const SVFVar* srcRet = retNode->getActualRet();
    if (!srcRet) return false;
    const NodeID srcId = srcRet->getId();

    // 2) check each sink parameter
    const CallICFGNode::ActualParmNodeVec& params = snk->getActualParms(); // vector<const ValVar*>
    for (const ValVar* p : params) {
        if (!p) continue;
        const NodeID pid = p->getId();

        const AliasResult ar = ander->alias(srcId, pid);
        // treat any non-NoAlias as taint-capable
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
	const fs::path& config = CUR_DIR() / "../Tests/SrcSnk.txt";
	// configure sources and sinks for taint analysis
	readSrcSnkFromFile(config);

	// after readSrcSnkFromFile(config);
SVFUtil::outs() << "[SrcSnk] sources=" << checker_source_api.size()
                << " sinks=" << checker_sink_api.size() << "\n";

// after building the sets:
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
