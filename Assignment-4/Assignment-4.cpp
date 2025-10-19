//===- Assignment-4.cpp -- Automated assertion-based verification (Static symbolic execution) --//
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
 * Automated assertion-based verification (Static symbolic execution)
 *
 * Created on: Feb 19, 2024
 */

#include "Assignment-4.h"
#include "Util/Options.h"

using namespace SVF;
using namespace SVFUtil;
using namespace llvm;
using namespace z3;

/// TODO: Implement your context-sensitive ICFG traversal here to traverse each program path (once for any loop) from
/// You will need to collect each path from src node to snk node and then add the path to the `paths` set by
/// calling the `collectAndTranslatePath` method which is then trigger the path translation.
/// This implementation, slightly different from Assignment-1, requires ICFGNode* as the first argument.
void SSE::reachability(const ICFGEdge* curEdge, const ICFGNode* sink) {
	 // Determine current node: for the very first call we pass a dummy edge
    const ICFGNode* curNode = curEdge->getDstNode();
    if (curNode == nullptr) {
        // fall back to program entry (GlobalICFGNode) if needed
        curNode = const_cast<ICFGNode*>(*identifySources().begin());
    }

    // If we’ve reached the sink (assert site), collect and translate this path
    if (curNode == sink) {
        collectAndTranslatePath();
        return;
    }

    // Explore all outgoing ICFG edges from the current node
    for (const ICFGEdge* e : curNode->getOutEdges()) {

        bool pushedCall  = false;
        bool poppedOnRet = false;
        const ICFGNode* savedCallsite = nullptr; // for restoring after recursion

        // Maintain a context-sensitive call stack
        if (const CallCFGEdge* call = SVFUtil::dyn_cast<CallCFGEdge>(e)) {
            callstack.push_back(call->getSrcNode());
            pushedCall = true;
        } else if (const RetCFGEdge* ret = SVFUtil::dyn_cast<RetCFGEdge>(e)) {
            const ICFGNode* callsite = ret->getCallSite();   // match return to last call
            if (callstack.empty() || callstack.back() != callsite) {
                // mismatched return under current context; skip this edge
                continue;
            }
            callstack.pop_back();
            poppedOnRet   = true;
            savedCallsite = callsite;
        }

        // De-duplicate by (edge, callstack) to avoid infinite exploration
        ICFGEdgeStackPair key(e, callstack);
        if (visited.find(key) != visited.end()) {
            // restore before trying next edge
            if (pushedCall)  callstack.pop_back();
            if (poppedOnRet) callstack.push_back(savedCallsite);
            continue;
        }
        visited.insert(key);

        // DFS: descend with this edge appended to the current path
        path.push_back(e);
        reachability(e, sink);
        path.pop_back();

        // Restore call stack for sibling edges
        if (pushedCall)  callstack.pop_back();
        if (poppedOnRet) callstack.push_back(savedCallsite);
    }
}


/// TODO: collect each path once this method is called during reachability analysis, and
/// Collect each program path from the entry to each assertion of the program. In this function,
/// you will need (1) add each path into the paths set, (2) call translatePath to convert each path into Z3 expressions.
/// Note that translatePath returns true if the path is feasible, false if the path is infeasible. (3) If a path is feasible,
/// you will need to call assertchecking to verify the assertion (which is the last ICFGNode of this path).
void SSE::collectAndTranslatePath() {
 // 1) Record the path textually (helps debugging)
    std::stringstream ss;
    ss << "START";
    for (const ICFGEdge* e : path) ss << "->" << e->getDstNode()->getId();
    ss << "->END";
    paths.insert(ss.str());

    // 2) Translate + check feasibility in an isolated solver scope
    getSolver().push();
    bool feasible = translatePath(path);

    // 3) If feasible, run the assert check on the last node
    if (feasible && !path.empty()) {
        const ICFGNode* last = path.back()->getDstNode();
        assertchecking(last);
    }
    getSolver().pop();
}

/// TODO: Implement handling of function calls
void SSE::handleCall(const CallCFGEdge* calledge) {
	//1. Identify the source (caller) and destination (callee entry)
	const ICFGNode* srcNode = calledge->getSrcNode();
	DBOP(std::cout << "\n## Analyzing "<< srcNode->toString() << "\n");

	CallICFGNode* callNode = SVFUtil::cast<CallICFGNode>(calledge->getSrcNode());
	FunEntryICFGNode* FunEntryNode = SVFUtil::cast<FunEntryICFGNode>(calledge->getDstNode());

	assert(callNode->getSVFStmts().size()==callNode->getActualParms().size() && "Numbers of CallPEs and ActualParms not the same?");

	// === Algorithm 4 (slides) ===
    // enter callee context
    getSolver().push();
    // if your framework uses a calling context, push it
    pushCallingCtx(callNode);  // (leave the pop to handleRet)

    // bind actuals to formals
    for (const CallPE* pe : calledge->getCallPEs()) {
        expr lhs = getZ3Expr(pe->getLHSVarID()); // formal (callee)
        expr rhs = getZ3Expr(pe->getRHSVarID()); // actual (caller)
        addToSolver(lhs == rhs);
    }

	// --- detect external callee by inspecting ICFG edges from entry ---
bool hasBody = false;
for (const ICFGEdge* oe : FunEntryNode->getOutEdges()) {
    // If the callee has any real control-flow (intra or nested calls), consider it a body
    if (SVFUtil::isa<IntraCFGEdge>(oe) || SVFUtil::isa<CallCFGEdge>(oe)) {
        hasBody = true;
        break;
    }
}

// External calls (no body) won't produce a RetCFGEdge to trigger popping.
// Close the solver scope and calling context here to avoid leaks.
if (!hasBody) {
    getSolver().pop();
    popCallingCtx();
}

    (void)FunEntryNode; // silence unused if needed
    // NOTE: do NOT pop here; handleRet will pop solver + calling ctx
}

/// TODO: Implement handling of function returns
void SSE::handleRet(const RetCFGEdge* retEdge) {
    DBOP(std::cout << "\n## Analyzing "<< retEdge->getDstNode()->toString() << "\n");

    FunExitICFGNode* FunExitNode = SVFUtil::cast<FunExitICFGNode>(retEdge->getSrcNode());
    RetICFGNode* retNode = SVFUtil::cast<RetICFGNode>(retEdge->getDstNode());

    assert(retNode->getSVFStmts().size()<=1 && "We can only has one RetPE per function!");

	// === Algorithm 6 (slides) ===
    expr rhs(getCtx());                              // 1) default rhs (unused if no ret)
    if (const RetPE* retPE = retEdge->getRetPE()) {      // 2) capture callee's return expr
        rhs = getZ3Expr(retPE->getRHSVarID());
    }

    // Leave callee context (matching the push in handleCall)
    getSolver().pop();                                   // 3) pop solver scope
    popCallingCtx();                                     //    pop calling context (if tracked)

    // Assign return value into caller (if any)
    if (const RetPE* retPE = retEdge->getRetPE()) {      // 4) bind caller LHS := rhs
        expr lhs = getZ3Expr(retPE->getLHSVarID());
        addToSolver(lhs == rhs);
    }

    (void)FunExitNode; (void)retNode;                    // silence unused warnings

	//return true not needed since the function signature is void
}


/// TODO: Implement handling of branch statements inside a function
/// Return true if the path is feasible, false otherwise.
/// A given branch on the ICFG looks like the following:
///       	     ICFGNode1 (condition %cmp)
///       	     1	/    \  0
///       	  ICFGNode2   ICFGNode3
/// edge->getCondition() returns the branch condition variable (%cmp) of type SVFValue* (for if/else) or a numeric condition variable (for switch).
/// Given the condition variable, you could obtain the SVFVar ID via "edge->getCondition())->getId()"
/// edge->getCondition() returns nullptr if this IntraCFGEdge is not a branch.
/// edge->getSuccessorCondValue() returns the actual condition value (1/0 for if/else) when this branch/IntraCFGEdge is executed. For example, the successorCondValue is 1 on the edge from ICFGNode1 to ICFGNode2, and 0 on the edge from ICFGNode1 to ICFGNode3
bool SSE::handleBranch(const IntraCFGEdge* edge) {
	assert(edge->getCondition() && "not a conditional control-flow transfer?");
	expr cond = getZ3Expr(edge->getCondition()->getId());
	expr successorVal = getCtx().int_val((int) edge->getSuccessorCondValue());

	DBOP(std::cout << "@@ Analyzing Branch " << edge->toString() << "\n");

expr q = (cond == successorVal);
expr v = getEvalExpr(q);

if (v.is_false()) {
    addToSolver(cond != successorVal);
    return false;
} else if (v.is_true()) {
    addToSolver(cond == successorVal);
    return true;
}
// unknown: allow traversal

    return true;
}

/// TODO: Translate AddrStmt, CopyStmt, LoadStmt, StoreStmt, GepStmt and CmpStmt
/// Translate AddrStmt, CopyStmt, LoadStmt, StoreStmt, GepStmt, BinaryOPStmt, CmpStmt, SelectStmt, and PhiStmt
bool SSE::handleNonBranch(const IntraCFGEdge* edge) {
	const ICFGNode* dstNode = edge->getDstNode();
	const ICFGNode* srcNode = edge->getSrcNode();
	DBOP(if(!SVFUtil::isa<CallICFGNode>(dstNode) && !SVFUtil::isa<RetICFGNode>(dstNode)) std::cout << "\n## Analyzing "<< dstNode->toString() << "\n");

	for (const SVFStmt *stmt : dstNode->getSVFStmts())
	{
		if (const AddrStmt *addr = SVFUtil::dyn_cast<AddrStmt>(stmt))
		// x := &obj
{
	expr lhs = getZ3Expr(addr->getLHSVarID());
	expr obj = getMemObjAddress(addr->getRHSVarID());
    addToSolver(lhs == obj);
}
		else if (const CopyStmt *copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
		// x := y
{
    expr lhs = getZ3Expr(copy->getLHSVarID());
    expr rhs = getZ3Expr(copy->getRHSVarID());
    addToSolver(rhs == lhs);
}
		else if (const LoadStmt *load = SVFUtil::dyn_cast<LoadStmt>(stmt))
		// x := *p
{
expr lhs = getZ3Expr(load->getLHSVarID());
expr rhs   = getZ3Expr(load->getRHSVarID());
addToSolver(lhs == z3Mgr->loadValue(rhs));
}
		else if (const StoreStmt *store = SVFUtil::dyn_cast<StoreStmt>(stmt))
		// *p := v
{
expr lhs = getZ3Expr(store->getLHSVarID());
expr rhs = getZ3Expr(store->getRHSVarID());
(void)z3Mgr->storeValue(lhs, rhs);
}
		else if (const GepStmt *gep = SVFUtil::dyn_cast<GepStmt>(stmt))
		// x := gep(base, offset)
{
expr lhs   = getZ3Expr(gep->getLHSVarID());
expr base  = getZ3Expr(gep->getRHSVarID()); 
u32_t offset = z3Mgr->getGepOffset(gep, callingCtx);
expr gepAddress = z3Mgr->getGepObjAddress(base, offset);
addToSolver(lhs == gepAddress);
}
		/// Given a CmpStmt "r = a > b"
		/// cmp->getOpVarID(0)/cmp->getOpVarID(1) returns the first/second operand, i.e., "a" and "b"
		/// cmp->getResID() returns the result operand "r" and cmp->getPredicate() gives you the predicate ">"
		/// Find the comparison predicates in "class CmpStmt:Predicate" under SVF/svf/include/SVFIR/SVFStatements.h
		/// You are only required to handle integer predicates, including ICMP_EQ, ICMP_NE, ICMP_UGT, ICMP_UGE, ICMP_ULT, ICMP_ULE, ICMP_SGT, ICMP_SGE, ICMP_SLE, ICMP_SLT
		/// We assume integer-overflow-free in this assignment
		else if (const CmpStmt *cmp = SVFUtil::dyn_cast<CmpStmt>(stmt))
		// r := (op0 ? op1)    // r modeled as 0/1 int
{
expr op0 = getZ3Expr(cmp->getOpVarID(0));
expr op1 = getZ3Expr(cmp->getOpVarID(1));
expr res = getZ3Expr(cmp->getResID());
expr one  = getCtx().int_val(1);
expr zero = getCtx().int_val(0);

switch (cmp->getPredicate()) {
case CmpStmt::ICMP_EQ:  addToSolver(res == ite(op0 == op1, one, zero)); break;
case CmpStmt::ICMP_NE:  addToSolver(res == ite(op0 != op1, one, zero)); break;
case CmpStmt::ICMP_SGT: addToSolver(res == ite(op0 >  op1, one, zero)); break;
case CmpStmt::ICMP_SGE: addToSolver(res == ite(op0 >= op1, one, zero)); break;
case CmpStmt::ICMP_SLT: addToSolver(res == ite(op0 <  op1, one, zero)); break;
case CmpStmt::ICMP_SLE: addToSolver(res == ite(op0 <= op1, one, zero)); break;
// Unsigned: compare as 32-bit bitvectors, then back to 0/1 int
case CmpStmt::ICMP_UGT: addToSolver(res == ite(ugt(int2bv(32,op0), int2bv(32,op1)), one, zero)); break;
case CmpStmt::ICMP_UGE: addToSolver(res == ite(uge(int2bv(32,op0), int2bv(32,op1)), one, zero)); break;
case CmpStmt::ICMP_ULT: addToSolver(res == ite(ult(int2bv(32,op0), int2bv(32,op1)), one, zero)); break;
case CmpStmt::ICMP_ULE: addToSolver(res == ite(ule(int2bv(32,op0), int2bv(32,op1)), one, zero)); break;
default: assert(false && "unhandled integer comparison predicate");
}
}
		else if (const BinaryOPStmt *binary = SVFUtil::dyn_cast<BinaryOPStmt>(stmt))
		{
			expr op0 = getZ3Expr(binary->getOpVarID(0));
			expr op1 = getZ3Expr(binary->getOpVarID(1));
			expr res = getZ3Expr(binary->getResID());
			switch (binary->getOpcode())
			{
			case BinaryOperator::Add:
				addToSolver(res == op0 + op1);
				break;
			case BinaryOperator::Sub:
				addToSolver(res == op0 - op1);
				break;
			case BinaryOperator::Mul:
				addToSolver(res == op0 * op1);
				break;
			case BinaryOperator::SDiv:
				addToSolver(res == op0 / op1);
				break;
			case BinaryOperator::SRem:
				addToSolver(res == op0 % op1);
				break;
			case BinaryOperator::Xor:
				addToSolver(res == bv2int(int2bv(32, op0) ^ int2bv(32, op1), 1));
				break;
			case BinaryOperator::And:
				addToSolver(res == bv2int(int2bv(32, op0) & int2bv(32, op1), 1));
				break;
			case BinaryOperator::Or:
				addToSolver(res == bv2int(int2bv(32, op0) | int2bv(32, op1), 1));
				break;
			case BinaryOperator::AShr:
				addToSolver(res == bv2int(ashr(int2bv(32, op0), int2bv(32, op1)), 1));
				break;
			case BinaryOperator::Shl:
				addToSolver(res == bv2int(shl(int2bv(32, op0), int2bv(32, op1)), 1));
				break;
			default:
				assert(false && "implement this part");
			}
		}
		else if (const BranchStmt *br = SVFUtil::dyn_cast<BranchStmt>(stmt))
		{
			DBOP(std::cout << "\t skip handled when traversal Conditional IntraCFGEdge \n");
		}
		else if (const SelectStmt *select = SVFUtil::dyn_cast<SelectStmt>(stmt)) {
			expr res = getZ3Expr(select->getResID());
			expr tval = getZ3Expr(select->getTrueValue()->getId());
			expr fval = getZ3Expr(select->getFalseValue()->getId());
			expr cond = getZ3Expr(select->getCondition()->getId());
			addToSolver(res == ite(cond == getCtx().int_val(1), tval, fval));
		}
		else if (const PhiStmt *phi = SVFUtil::dyn_cast<PhiStmt>(stmt)) {
			expr res = getZ3Expr(phi->getResID());
			bool opINodeFound = false;
			for(u32_t i = 0; i < phi->getOpVarNum(); i++){
				assert(srcNode && "we don't have a predecessor ICFGNode?");
				if (srcNode->getFun()->postDominate(srcNode->getBB(),phi->getOpICFGNode(i)->getBB()))
				{
					expr ope = getZ3Expr(phi->getOpVar(i)->getId());
					addToSolver(res == ope);
					opINodeFound = true;
				}
			}
			assert(opINodeFound && "predecessor ICFGNode of this PhiStmt not found?");
		}
	}

	return true;
}

/// Traverse each program path
bool SSE::translatePath(std::vector<const ICFGEdge*>& path) {
	for (const ICFGEdge* edge : path) {
		if (const IntraCFGEdge* intraEdge = SVFUtil::dyn_cast<IntraCFGEdge>(edge)) {
			if (handleIntra(intraEdge) == false)
				return false;
		}
		else if (const CallCFGEdge* call = SVFUtil::dyn_cast<CallCFGEdge>(edge)) {
			handleCall(call);
		}
		else if (const RetCFGEdge* ret = SVFUtil::dyn_cast<RetCFGEdge>(edge)) {
			handleRet(ret);
		}
		else
			assert(false && "what other edges we have?");
	}

	return true;
}

/// Program entry
void SSE::analyse() {
	for (const ICFGNode* src : identifySources()) {
		assert(SVFUtil::isa<GlobalICFGNode>(src) && "reachability should start with GlobalICFGNode!");
		for (const ICFGNode* sink : identifySinks()) {
			const IntraCFGEdge startEdge(nullptr, const_cast<ICFGNode*>(src));
			/// start traversing from the entry to each assertion and translate each path
			reachability(&startEdge, sink);
			resetSolver();
		}
	}
}
