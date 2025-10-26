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

    // Current node is the destination of the edge we just traversed.
    const ICFGNode* curNode = curEdge->getDstNode();

    // Build state pair for visited
    ICFGEdgeStackPair state(curEdge, callstack);
    if (visited.find(state) != visited.end()) {
        return;
    }

     visited.insert(state);

    // Add this edge to the current path (except for the synthetic "start edge"
    // at the very beginning which has null src; we still include it so that
    // collectAndTranslatePath can reconstruct from START though).
    path.push_back(curEdge);

    // Did we just arrive at the sink (assert call)?
    if (curNode == sink) {
        // Turn this path into constraints + assertion check
        collectAndTranslatePath();
    }

    // Otherwise, continue DFS along outgoing edges of curNode.
    for (ICFGNode::const_iterator it = curNode->OutEdgeBegin();
         it != curNode->OutEdgeEnd(); ++it) {

        const ICFGEdge* outEdge = *it;

        // Case 1: Intra edge
        if (const IntraCFGEdge* intraE = SVFUtil::dyn_cast<IntraCFGEdge>(outEdge)) {
            reachability(intraE, sink);
        }

        // Case 2: Call edge
        else if (const CallCFGEdge* callE = SVFUtil::dyn_cast<CallCFGEdge>(outEdge)) {

            const CallICFGNode* callNode =
                SVFUtil::cast<CallICFGNode>(callE->getSrcNode());

            // push callsite for context-sensitive path
            callstack.push_back(callNode);

            reachability(callE, sink);

            callstack.pop_back();
        }

        // Case 3: Ret edge
        else if (const RetCFGEdge* retE = SVFUtil::dyn_cast<RetCFGEdge>(outEdge)) {
if (!callstack.empty()) {
        // temporarily pop the most recent callsite context
        const ICFGNode* savedTop = callstack.back();
        callstack.pop_back();

        reachability(retE, sink);

        // restore callstack context
        callstack.push_back(savedTop);
    } else {
        // top-level return (e.g. returning from main)
        reachability(retE, sink);
    }
        }

        else {
            // shouldn't happen
            assert(false && "Unknown edge type in reachability");
        }
    }

    // backtrack
    path.pop_back();
    visited.erase(state);
	
}

/// TODO: collect each path once this method is called during reachability analysis, and
/// Collect each program path from the entry to each assertion of the program. In this function,
/// you will need (1) add each path into the paths set, (2) call translatePath to convert each path into Z3 expressions.
/// Note that translatePath returns true if the path is feasible, false if the path is infeasible. (3) If a path is feasible,
/// you will need to call assertchecking to verify the assertion (which is the last ICFGNode of this path).
void SSE::collectAndTranslatePath() {

    // 1. Build path string
    std::stringstream ss;
    ss << "START";

    for (size_t i = 0; i < path.size(); ++i) {
        const ICFGEdge* e = path[i];
        const ICFGNode* dst = e->getDstNode();
        ss << "->" << dst->getId();
    }

    ss << "->END";
    std::string pathStr = ss.str();
    paths.insert(pathStr);

    DBOP(std::cout << "[Path] " << pathStr << "\n");

     // 2. Translate the path into constraints
    bool feasible = translatePath(path);
    if (!feasible)
        return; // infeasible path: nothing to assert-check

    // 3. Get the last node on this path
    const ICFGNode* lastNode = path.back()->getDstNode();

    // We only assert-check if the last node is actually a call to an assert-like function.
    if (!SVFUtil::isa<CallICFGNode>(lastNode)) {
        // Not an assertion -> just end this path.
        return;
    }

    const CallICFGNode* callnode = SVFUtil::cast<CallICFGNode>(lastNode);
    if (!isAssertFun(callnode->getCalledFunction())) {
        // It's a call, but not svf_assert/assert/sink -> ignore.
        return;
    }

    // 4. Build the "bad condition" (arg0 == 0) and test it under a sandboxed push
    expr arg0 = getZ3Expr(callnode->getActualParms().at(0)->getId());

    getSolver().push();
    addToSolver(arg0 == getCtx().int_val(0));
    check_result res = getSolver().check();
    getSolver().pop();

    if (res == z3::unsat) {
        // Safe: same message as assertchecking()'s UNSAT branch,
        // but we skip its model-printing (which crashes under UNSAT).
        std::stringstream okmsg;
        okmsg << "The assertion is successfully verified!! ("
              << lastNode->toString() << ")" << "\n";
        SVFUtil::outs() << okmsg.str() << std::endl;
    }
    else {
        // Counterexample exists (sat or unknown): delegate to assertchecking()
        // which will print CE and assert(false)
        getSolver().push();
        assertchecking(lastNode);
        getSolver().pop();
    }
}
	


/// TODO: Implement handling of function calls
void SSE::handleCall(const CallCFGEdge* calledge) {
	const ICFGNode* srcNode = calledge->getSrcNode();
	DBOP(std::cout << "\n## Analyzing "<< srcNode->toString() << "\n");

	CallICFGNode* callNode = SVFUtil::cast<CallICFGNode>(calledge->getSrcNode());
	FunEntryICFGNode* FunEntryNode = SVFUtil::cast<FunEntryICFGNode>(calledge->getDstNode());

	assert(callNode->getSVFStmts().size()==callNode->getActualParms().size() && "Numbers of CallPEs and ActualParms not the same?");

    //
    // If this is an assert/sink call (svf_assert, assert, sink), we don't create a new frame.
    // We'll verify later in assertchecking() instead.
    if (isAssertFun(callNode->getCalledFunction())) {
        DBOP(std::cout << "\t[handleCall] assert-like call, no frame push\n";)
        return;
    }

    // 1. Snapshot actual arg values under *current* callingCtx
std::vector<z3::expr> actualVals;
{
    const auto& actualParms = callNode->getActualParms(); // vector<const ValVar*>
    for (auto* actualVar : actualParms) {
        actualVals.push_back(getZ3Expr(actualVar->getId()));
    }
}

    // 2. Enter callee context
    getSolver().push();
    pushCallingCtx(callNode);
  //  callstack.push_back(callNode);

    // We DO NOT modify reachability's callstack here; that's handled in DFS.
    // But we conceptually just entered a new symbolic frame for Z3 naming.

    // 3. Constrain formals == captured actuals
   {
    const auto& formalParms = FunEntryNode->getFormalParms(); // vector<const ValVar*>
    assert(formalParms.size() == actualVals.size() &&
           "Mismatched number of formals/actuals?");
    for (size_t i = 0; i < formalParms.size(); ++i) {
        z3::expr formalExpr = getZ3Expr(formalParms[i]->getId());
        addToSolver(formalExpr == actualVals[i]);
    }
    }
    //

}

/// TODO: Implement handling of function returns
void SSE::handleRet(const RetCFGEdge* retEdge) {
    DBOP(std::cout << "\n## Analyzing "<< retEdge->getDstNode()->toString() << "\n");

    FunExitICFGNode* FunExitNode = SVFUtil::cast<FunExitICFGNode>(retEdge->getSrcNode());
    RetICFGNode* retNode = SVFUtil::cast<RetICFGNode>(retEdge->getDstNode());

    assert(retNode->getSVFStmts().size()<=1 && "We can only has one RetPE per function!");
    //
    // Step 1: grab RHS (callee return value) under callee context
    z3::expr rhsVal = getCtx().int_val(0); // dummy init
    const RetPE* retPE = retEdge->getRetPE(); // or whatever the actual type is in your headers
    if (retPE) {
        rhsVal = getZ3Expr(retPE->getRHSVarID()); // still in callee context
    }

    z3::expr rhsConst = rhsVal;
    if (retPE) {
        getSolver().push();
        // (no extra constraint here, just check current path is consistent)
        if (getSolver().check() == z3::sat) {
            z3::model m = getSolver().get_model();
            // evaluate rhsVal under model to get a ground value
            rhsConst = m.eval(rhsVal, /*model_completion*/ true);
        }
        getSolver().pop();
    }

    // pop callee frame
    getSolver().pop();
    popCallingCtx();

    // link caller LHS to that ground value
    if (retPE) {
        z3::expr lhsCaller = getZ3Expr(retPE->getLHSVarID());
        addToSolver(lhsCaller == rhsConst);
    }
    //
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
     //
     // Check feasibility with a temporary push
    getSolver().push();
    addToSolver(cond == successorVal);
    z3::check_result res = getSolver().check();
    getSolver().pop();

    if (res == z3::unsat) {
        // This successor edge is infeasible
        return false;
    }

    // Feasible: permanently record that we took this branch
    addToSolver(cond == successorVal);
    //
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
		{
			// TODO: Implement handling of AddrStmt
            expr lhs = getZ3Expr(addr->getLHSVarID());
            expr objAddr = getMemObjAddress(addr->getRHSVarID());
            addToSolver(lhs == objAddr);
		}
		else if (const CopyStmt *copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
		{
			// TODO: Implement handling of CopyStmt
            expr lhs = getZ3Expr(copy->getLHSVarID());
            expr rhs = getZ3Expr(copy->getRHSVarID());
            addToSolver(lhs == rhs);
		}
		else if (const LoadStmt *load = SVFUtil::dyn_cast<LoadStmt>(stmt))
		{
			// TODO: Implement handling of LoadStmt
            expr lhs    = getZ3Expr(load->getLHSVarID());
            expr rhsPtr = getZ3Expr(load->getRHSVarID());
            expr memVal = z3Mgr->loadValue(rhsPtr);
            addToSolver(lhs == memVal);
		}
		else if (const StoreStmt *store = SVFUtil::dyn_cast<StoreStmt>(stmt))
		{
			// TODO: Implement handling of StoreStmt
            expr lhsPtr = getZ3Expr(store->getLHSVarID());
            expr rhsVal = getZ3Expr(store->getRHSVarID());
            z3Mgr->storeValue(lhsPtr, rhsVal);
		}
		else if (const GepStmt *gep = SVFUtil::dyn_cast<GepStmt>(stmt))
		{
			// TODO: Implement handling of GepStmt
            expr lhsPtr  = getZ3Expr(gep->getLHSVarID());
            expr basePtr = getZ3Expr(gep->getRHSVarID());

            // Compute the field/element offset in bytes/slots using callingCtx
            s32_t offset = z3Mgr->getGepOffset(gep, callingCtx);

            // Compute the derived address as a stable virtual address using Z3SSEMgr
            expr gepAddr = z3Mgr->getGepObjAddress(basePtr, offset);

            addToSolver(lhsPtr == gepAddr);
		}
		/// Given a CmpStmt "r = a > b"
		/// cmp->getOpVarID(0)/cmp->getOpVarID(1) returns the first/second operand, i.e., "a" and "b"
		/// cmp->getResID() returns the result operand "r" and cmp->getPredicate() gives you the predicate ">"
		/// Find the comparison predicates in "class CmpStmt:Predicate" under SVF/svf/include/SVFIR/SVFStatements.h
		/// You are only required to handle integer predicates, including ICMP_EQ, ICMP_NE, ICMP_UGT, ICMP_UGE, ICMP_ULT, ICMP_ULE, ICMP_SGT, ICMP_SGE, ICMP_SLE, ICMP_SLT
		/// We assume integer-overflow-free in this assignment
		else if (const CmpStmt *cmp = SVFUtil::dyn_cast<CmpStmt>(stmt))
		{
			// TODO: Implement handling of CmpStmt
            expr op0 = getZ3Expr(cmp->getOpVarID(0));
            expr op1 = getZ3Expr(cmp->getOpVarID(1));
            expr res = getZ3Expr(cmp->getResID());

            // We'll encode all integer predicates as Int comparisons + ite -> {1,0}
            SVF::u32_t pred = cmp->getPredicate();

            using P = CmpStmt;
            expr one  = getCtx().int_val(1);
            expr zero = getCtx().int_val(0);

            switch (pred) {
            case P::ICMP_EQ:
                addToSolver(res == ite(op0 == op1, getCtx().int_val(1), getCtx().int_val(0)));
                break;
            case P::ICMP_NE:
                addToSolver(res == ite(op0 != op1, getCtx().int_val(1), getCtx().int_val(0)));
                break;
            case P::ICMP_UGT:
            case P::ICMP_SGT:
                addToSolver(res == ite(op0 > op1, getCtx().int_val(1), getCtx().int_val(0)));
                break;
            case P::ICMP_UGE:
            case P::ICMP_SGE:
                addToSolver(res == ite(op0 >= op1, getCtx().int_val(1), getCtx().int_val(0)));
                break;
            case P::ICMP_ULT:
            case P::ICMP_SLT:
                addToSolver(res == ite(op0 < op1, getCtx().int_val(1), getCtx().int_val(0)));
                break;
            case P::ICMP_ULE:
            case P::ICMP_SLE:
                addToSolver(res == ite(op0 <= op1, getCtx().int_val(1), getCtx().int_val(0)));
                break;
            default:
                assert(false && "Unhandled Cmp predicate");
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