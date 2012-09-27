#include <sys/fcntl.h>
#include <err.h>
#include <stdio.h>
#include <unistd.h>

#include "sli.h"
#include "inferred_information.hpp"
#include "oracle.hpp"
#include "offline_analysis.hpp"
#include "intern.hpp"
#include "genfix.hpp"
#include "dnf.hpp"
#include "simplify_ordering.hpp"
#include "enforce_crash.hpp"
#include "allowable_optimisations.hpp"
#include "alloc_mai.hpp"

#ifndef NDEBUG
static bool debug_declobber_instructions = false;
#else
#define debug_declobber_instructuions false
#endif

unsigned long
__trivial_hash_function(const VexRip &vr)
{
	return vr.hash();
}

void
instrToInstrSetMap::print(FILE *f) const
{
	for (auto it = begin(); it != end(); it++) {
		fprintf(f, "%s -> {", it->first->label.name());
		for (auto it2 = it->second.begin();
		     it2 != it->second.end();
		     it2++) {
			if (it2 != it->second.begin())
				fprintf(f, ", ");
			fprintf(f, "%s", (*it2)->label.name());
		}
		fprintf(f, "}\n");
	}
}

abstractThreadExitPointsT::abstractThreadExitPointsT(
	CrashCfg &cfg,
	happensBeforeMapT &happensBeforePoints)
{
	/* We need to exit thread X if we reach instruction Y and
	   there is some message which is needed by thread X such that
	   Y cannot have already received that message and cannot
	   subsequently send it.  We also exit if Y can neither send
	   nor receive any further messages. */

	typedef Instruction<ThreadCfgLabel> instrT;

	/* Step one: build control-flow reachability maps */

	/* forwardReachable[x] -> the set of instructions y such that
	   there's some control flow path from x to y */
	instrToInstrSetMap forwardReachable;
	/* backwardReachable[x] -> the set of instructions y such that
	   there's some control flow path from y to x */
	instrToInstrSetMap backwardReachable;

	for (auto it = cfg.begin(); !it.finished(); it.advance())
		if (it.instr())
			forwardReachable[it.instr()].insert(it.instr());

	bool progress;
	do {
		progress = false;
		for (auto it = cfg.begin(); !it.finished(); it.advance()) {
			instrT *i = it.instr();
			if (!i)
				continue;

			/* Forward reachability: look at our
			   successors, and make sure that anything
			   which they can reach is reachable from us
			   as well. */
			std::set<instrT *> &f(forwardReachable[i]);
			for (auto it2 = i->successors.begin(); it2 != i->successors.end(); it2++) {
				instrT *successor = it2->instr;
				if (!successor)
					continue;
				std::set<instrT *> &f2(forwardReachable[successor]);
				for (auto it3 = f2.begin(); it3 != f2.end(); it3++) {
					if (!f.count(*it3)) {
						progress = true;
						f.insert(*it3);
					}
				}
			}
		}
	} while (progress);
	/* Invert it to build the backwardReachable map */
	for (auto it = forwardReachable.begin(); it != forwardReachable.end(); it++)
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
			backwardReachable[*it2].insert(it->first);

	/* Figure out which instructions should be present. */
	std::set<instrT *> instructionPresence;
	for (auto it = cfg.begin(); !it.finished(); it.advance()) {
		instrT *i = it.instr();
		if (!i)
			continue;

		AbstractThread thread(it.instr()->rip.thread);

		/* Should @i be present in thread @thread? */
		bool should_be_present = false;
		/* Must be able to send or receive some message */
		for (auto it3 = happensBeforePoints.begin();
		     !should_be_present && it3 != happensBeforePoints.end();
		     it3++) {
			for (auto it4 = it3->second.begin();
			     it4 != it3->second.end();
			     it4++) {
				happensBeforeEdge *hbe = *it4;
				if (hbe->before->rip.thread == thread) {
					/* Can we send this message? */
					if (forwardReachable[i].count(hbe->before))
						should_be_present = true;
				} else if (hbe->after->rip.thread == thread) {
					/* Can we receive this message? */
					if (forwardReachable[i].count(hbe->after))
						should_be_present = true;
				}
			}
		}

		/* Not only must some send or receive be
		   forward-reachable, every receive must be
		   either forward or backwards reachable. */
		for (auto it3 = happensBeforePoints.begin();
		     should_be_present && it3 != happensBeforePoints.end();
		     it3++) {
			for (auto it4 = it3->second.begin();
			     it4 != it3->second.end();
			     it4++) {
				happensBeforeEdge *hbe = *it4;
				if (hbe->after->rip.thread == thread) {
					instrT *receiver = hbe->after;
					if (!forwardReachable[i].count(receiver) &&
					    !backwardReachable[i].count(receiver)) {
						/* No path between this instruction and this
						   receive point -> not in patch */
						should_be_present = false;
					}
				}
			}
		}

		if (should_be_present)
			instructionPresence.insert(i);
	}

#if 0
	printf("Desired instructions:\n");
	for (auto it = instructionPresence.begin(); it != instructionPresence.end(); it++)
		printf("\t%s\n", (*it)->rip.name());
#endif
		       
	/* Now figure out the transitions.  We're looking for any
	   instructions which are present but which have a successor
	   which is not present.  That successor will then be marked
	   as an exit instruction for the relevant thread. */
	for (auto it = instructionPresence.begin(); it != instructionPresence.end(); it++) {
		instrT *i = *it;

		for (auto it2 = i->successors.begin(); it2 != i->successors.end(); it2++) {
			if (it2->type == succ_call)
				continue;
			if (it2->instr && !instructionPresence.count(it2->instr))
				insert(it2->instr->rip);
		}
	}

}

static bool
exprUsesRegister(IRExpr *e, const threadAndRegister &reg)
{
	struct : public IRExprTransformer {
		const threadAndRegister *reg;
		bool res;
		IRExpr *transformIex(IRExprGet *ieg) {
			if (*reg ==  ieg->reg)
				res = true;
			return ieg;
		}
	} doit;
	doit.reg = &reg;
	doit.res = false;
	doit.doit(e);
	return doit.res;
}

static bool
instrUsesExpr(Instruction<ThreadCfgLabel> *instr, IRExprGet *expr, crashEnforcementData &ced)
{
	{
		auto it = ced.happensBeforePoints.find(instr->rip);
		if (it != ced.happensBeforePoints.end()) {
			for (auto it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++) {
				happensBeforeEdge *hbe = *it2;
				if (hbe->before->rip == instr->rip) {
					for (auto it3 = hbe->content.begin();
					     it3 != hbe->content.end();
					     it3++) {
						if ((*it3)->reg == expr->reg)
							return true;
					}
				}
			}
		}
	}

	{
		auto it = ced.expressionEvalPoints.find(instr->rip);
		if (it != ced.expressionEvalPoints.end()) {
			for (auto it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++) {
				if (exprUsesRegister(it2->e, expr->reg))
					return true;
			}
		}
	}
	return false;
}

static void
optimiseHBContent(crashEnforcementData &ced)
{
	std::set<happensBeforeEdge *> hbEdges;
	for (auto it = ced.happensBeforePoints.begin();
	     it != ced.happensBeforePoints.end();
	     it++)
		hbEdges.insert(it->second.begin(), it->second.end());
	bool progress = true;
	while (progress) {
		progress = false;
		for (auto it = hbEdges.begin(); it != hbEdges.end(); it++) {
			happensBeforeEdge *hbe = *it;
			for (unsigned x = 0; x < hbe->content.size(); ) {
				bool must_keep = false;
				std::queue<Instruction<ThreadCfgLabel> *> pending;
				pending.push(hbe->after);
				while (!must_keep && !pending.empty()) {
					Instruction<ThreadCfgLabel> *l = pending.front();
					pending.pop();
					if (instrUsesExpr(l, hbe->content[x], ced))
						must_keep = true;
					for (unsigned y = 0; y < l->successors.size(); y++)
						pending.push(l->successors[y].instr);
				}
				if (must_keep) {
					x++;
				} else {
					hbe->content.erase(hbe->content.begin() + x);
					progress = true;
				}
			}
		}
	}
}

static bool
buildCED(DNF_Conjunction &c,
	 std::map<unsigned, std::set<CfgLabel> > &rootsCfg,
	 CrashSummary *summary,
	 crashEnforcementData *out,
	 ThreadAbstracter &abs,
	 int &next_hb_id,
	 AddressSpace *as,
	 simulationSlotT &next_slot)
{
	/* Figure out what we actually need to keep track of */
	std::set<IRExpr *> neededExpressions;
	for (unsigned x = 0; x < c.size(); x++)
		enumerateNeededExpressions(c[x].second, neededExpressions);

	*out = crashEnforcementData(*summary->mai, neededExpressions, abs, rootsCfg, c, next_hb_id, next_slot, summary, as);
	optimiseHBContent(*out);
	return true;
}

static bool
analyseHbGraph(DNF_Conjunction &c, CrashSummary *summary)
{
	std::set<IRExprHappensBefore *, HBOrdering> hb;
	std::set<IRExprHappensBefore *, HBOrdering> assumption;

	extractImplicitOrder(summary->loadMachine, assumption);
	extractImplicitOrder(summary->storeMachine, assumption);
	for (unsigned x = 0; x < c.size(); x++) {
		if (c[x].second->tag == Iex_HappensBefore) {
			IRExprHappensBefore *g = (IRExprHappensBefore *)c[x].second;
			IRExprHappensBefore *h;
			if (c[x].first) {
				h = (IRExprHappensBefore *)IRExpr_HappensBefore(g->after, g->before);
			} else {
				h = g;
			}
			hb.insert(h);
		}
	}

	if (!simplifyOrdering(hb, assumption)) {
		/* Contradiction, get out */
		return false;
	}

	/* Build the results */
	DNF_Conjunction out;
	for (unsigned x = 0; x < c.size(); x++)
		if (c[x].second->tag != Iex_HappensBefore)
			out.push_back(c[x]);
	for (auto it = hb.begin();
	     it != hb.end();
	     it++)
		out.push_back(NF_Atom(false, *it));

	c = out;

	return true;
}

/* Check whether the ordering in @c is consistent with a total
   ordering over threads.  Those don't actually enforce any
   concurrency, so aren't very interesting. */
static bool
consistentOrdering(DNF_Conjunction &c)
{
	int thread_a;
	int thread_b;
	bool found_a_thread;
	for (auto it = c.begin(); it != c.end(); it++) {
		if (it->second->tag == Iex_HappensBefore) {
			IRExprHappensBefore *e = (IRExprHappensBefore *)it->second;
			if (!found_a_thread) {
				thread_a = e->before.tid;
				thread_b = e->after.tid;
				found_a_thread = true;
			} else {
				if (thread_a != e->before.tid ||
				    thread_b != e->after.tid)
					return false;
			}
		}
	}
	return true;
}

/* Munge a side condition to make it easier to evaluate.  This is
   allowed to slightly change the value of the condition if that makes
   the eval much easier, but shouldn't push things too far. */
/* Generally, taking a true expression and making it false is more
   dangerous than taking a false expression and making it true */
static IRExpr *
heuristicSimplify(IRExpr *e)
{
	bool done_something = false;
	if (e->tag != Iex_Binop ||
	    ((IRExprBinop *)e)->op != Iop_CmpEQ64)
		return e;

	/* First rule: 0 == a - b -> a == b */
	IRExprBinop *ieb = (IRExprBinop *)e;
	if (ieb->arg1->tag == Iex_Const &&
	    ((IRExprConst *)ieb->arg1)->con->Ico.U64 == 0 &&
	    ieb->arg2->tag == Iex_Associative &&
	    ((IRExprAssociative *)ieb->arg2)->op == Iop_Add64 &&
	    ((IRExprAssociative *)ieb->arg2)->nr_arguments == 2 &&
	    ((IRExprAssociative *)ieb->arg2)->contents[1]->tag == Iex_Unop &&
	    ((IRExprUnop *)((IRExprAssociative *)ieb->arg2)->contents[1])->op == Iop_Neg64) {
		ieb->arg1 = ((IRExprAssociative *)ieb->arg2)->contents[0];
		ieb->arg2 = ((IRExprUnop *)((IRExprAssociative *)ieb->arg2)->contents[1])->arg;
		done_something = true;
	}

	/* Second rule: f(a) == f(b) -> a == b, if f is sufficiently
	   injective. */
	if (ieb->arg1->tag == ieb->arg2->tag) {
		switch (ieb->arg1->tag) {
		case Iex_Binop: {
			IRExprBinop *l = (IRExprBinop *)ieb->arg1;
			IRExprBinop *r = (IRExprBinop *)ieb->arg2;
			if (l->op != r->op)
				break;
			switch (l->op) {
			case Iop_Shl64: /* x << k is treated as
					 * injective if k is a small
					 * constant, because most of
					 * the time you don't get
					 * overflow. */
				if (r->arg2->tag == Iex_Const &&
				    l->arg2->tag == Iex_Const &&
				    ((IRExprConst *)r->arg2)->con->Ico.U8 ==
				         ((IRExprConst *)l->arg2)->con->Ico.U8 &&
				    ((IRExprConst *)l->arg2)->con->Ico.U8 < 8) {
					ieb->arg1 = l->arg1;
					ieb->arg2 = r->arg1;
					done_something = true;
				}
				break;
			default:
				break;
			}
			break;
		}
		case Iex_Unop: {
			IRExprUnop *l = (IRExprUnop *)ieb->arg1;
			IRExprUnop *r = (IRExprUnop *)ieb->arg2;
			if (l->op != r->op)
				break;
			switch (l->op) {
			case Iop_32Sto64:
				/* This one actually is injective */
				ieb->arg1 = l->arg;
				ieb->arg2 = r->arg;
				done_something = true;
				break;
			default:
				break;
			}
			break;
		}
		default:
			break;
		}
	}

	if (done_something)
		return heuristicSimplify(e);
	return e;
}

/* We can't get at the values of free variables from the run-time
   enforcer, so we might as well remove them now. */
static IRExpr *
removeFreeVariables(IRExpr *what)
{
	switch (what->tag) {
	case Iex_Get:
		return what;
	case Iex_GetI: {
		auto *i = (IRExprGetI *)what;
		IRExpr *ix = removeFreeVariables(i->ix);
		if (!ix)
			return NULL;
		if (ix == i->ix)
			return i;
		return IRExpr_GetI(i->descr, ix,  i->bias, i->tid);
	}
	case Iex_Qop: {
		abort();
		auto *i = (IRExprQop *)what;
		auto arg1 = removeFreeVariables(i->arg1);
		if (!arg1)
			return NULL;
		auto arg2 = removeFreeVariables(i->arg2);
		if (!arg2)
			return NULL;
		auto arg3 = removeFreeVariables(i->arg3);
		if (!arg3)
			return NULL;
		auto arg4 = removeFreeVariables(i->arg4);
		if (!arg4)
			return NULL;
		if (arg1 == i->arg1 && arg2 == i->arg2 && arg3 == i->arg3 && arg4 == i->arg4)
			return i;
		return IRExpr_Qop(
			i->op, arg1, arg2, arg3, arg4);
	}
	case Iex_Triop: {
		abort();
		auto *i = (IRExprTriop *)what;
		auto arg1 = removeFreeVariables(i->arg1);
		if (!arg1)
			return NULL;
		auto arg2 = removeFreeVariables(i->arg2);
		if (!arg2)
			return NULL;
		auto arg3 = removeFreeVariables(i->arg3);
		if (!arg3)
			return NULL;
		if (arg1 == i->arg1 && arg2 == i->arg2 && arg3 == i->arg3)
			return i;
		return IRExpr_Triop(
			i->op, arg1, arg2, arg3);
	}
	case Iex_Binop: {
		auto i = (IRExprBinop *)what;
		auto arg1 = removeFreeVariables(i->arg1);
		auto arg2 = removeFreeVariables(i->arg2);
		if (arg1 == i->arg1 && arg2 == i->arg2)
			return what;
		if (arg1 && arg2)
			return IRExpr_Binop(i->op, arg1, arg2);
		switch (i->op) {
		case Iop_CmpEQ8:
		case Iop_CmpEQ16:
		case Iop_CmpEQ32:
		case Iop_CmpEQ64:
		case Iop_CmpLT8U:
		case Iop_CmpLT16U:
		case Iop_CmpLT32U:
		case Iop_CmpLT64U:
			return NULL;
		default:
			abort();
		}
		break;
	}
	case Iex_Unop: {
		auto i = (IRExprUnop *)what;
		auto arg = removeFreeVariables(i->arg);
		if (!arg)
			return NULL;
		if (arg == i->arg)
			return i;
		return IRExpr_Unop(i->op, arg);
	}
	case Iex_Load:
		/* Should arguably recurse into addr here, but the
		   rest of the pipeline will never look at it, so
		   don't bother. */
		return what;
	case Iex_Const:
		return what;
	case Iex_CCall:
		/* The interpreter can't evaluate these, so might as
		   well get rid of them as well. */
		return NULL;
	case Iex_Mux0X: {
		/* mux0x is unevaluatable if any of the arguments are
		   unevaluatable.  That's not ideal; it'd be better to
		   try to preserve whichever arguments are eval-able.
		   The problem is that we don't have any ``preferred''
		   value at this stage, so we can't put in a sensible
		   default for the other one. */
		auto i = (IRExprMux0X *)what;
		auto cond = removeFreeVariables(i->cond);
		if (!cond)
			return NULL;
		auto expr0 = removeFreeVariables(i->expr0);
		if (!expr0)
			return NULL;
		auto exprX = removeFreeVariables(i->exprX);
		if (!exprX)
			return NULL;
		if (cond == i->cond && expr0 == i->expr0 && exprX == i->exprX)
			return i;
		return IRExpr_Mux0X(cond, expr0, exprX);
	}
	case Iex_Associative: {
		auto i = (IRExprAssociative *)what;
		int idx;
		IRExpr *a;
		for (idx = 0; idx < i->nr_arguments; idx++) {
			a = removeFreeVariables(i->contents[idx]);
			if (a != i->contents[idx])
				break;
		}
		if (idx == i->nr_arguments)
			return i;
		IRExprAssociative *newI = (IRExprAssociative *)IRExpr_Associative(i->nr_arguments, i->op);
		int idx2 = idx;
		memcpy(newI->contents, i->contents, idx * sizeof(IRExpr *));
		if (a) {
			newI->contents[idx2] = a;
			idx2++;
		}
		idx++;
		while (idx < i->nr_arguments) {
			a = removeFreeVariables(i->contents[idx]);
			if (a) {
				newI->contents[idx2] = a;
				idx2++;
			}
			idx++;
		}
		if (idx2 == 0)
			return NULL;
		newI->nr_arguments = idx2;
		return newI;
	}
	case Iex_HappensBefore:
		return what;
	case Iex_FreeVariable:
		return NULL;
	}
	abort();
}

static crashEnforcementData
enforceCrashForMachine(VexPtr<CrashSummary, &ir_heap> summary,
		       VexPtr<Oracle> &oracle,
		       GarbageCollectionToken token,
		       ThreadAbstracter &abs,
		       int &next_hb_id,
		       simulationSlotT &next_slot)
{
	summary = internCrashSummary(summary);

	printf("Machines to enforce:\n");
	printCrashSummary(summary, stdout);

	VexPtr<OracleInterface> oracleI(oracle);

	IRExpr *requirement = summary->verificationCondition;
	requirement = removeFreeVariables(requirement);
	requirement = internIRExpr(simplifyIRExpr(requirement, AllowableOptimisations::defaultOptimisations));
	fprintf(_logfile, "After free variable removal:\n");
	ppIRExpr(requirement, _logfile);
	fprintf(_logfile, "\n");
	if (TIMEOUT) {
		fprintf(_logfile, "Killed by a timeout during simplification\n");
		exit(1);
	}
	DNF_Disjunction d;
	if (!dnf(requirement, d)) {
		fprintf(_logfile, "failed to convert to DNF\n");
		exit(1);
	}

	for (unsigned x = 0; x < d.size(); x++)
		for (unsigned y = 0; y < d[x].size(); y++)
			d[x][y].second = heuristicSimplify(d[x][y].second);

	for (unsigned x = 0; x < d.size(); ) {
		if (analyseHbGraph(d[x], summary) &&
		    !consistentOrdering(d[x])) {
			x++;
		} else {
			d.erase(d.begin() + x);
		}
	}

	printDnf(d, _logfile);

	if (d.size() == 0)
		return crashEnforcementData();

	std::map<unsigned, std::set<CfgLabel> > rootsCfg;
	for (auto it = summary->loadMachine->cfg_roots.begin();
	     it != summary->loadMachine->cfg_roots.end();
	     it++)
		rootsCfg[it->first].insert(it->second->label);
	for (auto it = summary->storeMachine->cfg_roots.begin();
	     it != summary->storeMachine->cfg_roots.end();
	     it++)
		rootsCfg[it->first].insert(it->second->label);

	crashEnforcementData accumulator;
	for (unsigned x = 0; x < d.size(); x++) {
		crashEnforcementData tmp;
		if (buildCED(d[x], rootsCfg, summary, &tmp, abs, next_hb_id, oracle->ms->addressSpace, next_slot)) {
			printf("Intermediate CED:\n");
			tmp.prettyPrint(stdout, true);
			accumulator |= tmp;
		}
	}
	return accumulator;
}

/* Try to delay stashing registers until we actually need to do so.
   We start off trying to stash them at the roots of the CFG and we
   can delay if:

   -- The node doesn't modify the register
   -- We don't try to eval anything at the node.
   -- The node isn't the before end of a happens-before edge
*/
static void
optimiseStashPoints(crashEnforcementData &ced, Oracle *oracle)
{
	expressionStashMapT newMap;
	for (auto it = ced.exprStashPoints.begin();
	     it != ced.exprStashPoints.end();
	     it++) {
		const ThreadCfgLabel &label(it->first);
		const std::set<IRExprGet *> &exprsToStash(it->second);
		std::set<Instruction<ThreadCfgLabel> *> frozenStashPoints;
		std::set<Instruction<ThreadCfgLabel> *> unfrozenStashPoints;

		assert(ced.crashCfg.findInstr(label));
		unfrozenStashPoints.insert(ced.crashCfg.findInstr(label));
		while (!unfrozenStashPoints.empty()) {			
			auto *node = *unfrozenStashPoints.begin();
			assert(node);
			unfrozenStashPoints.erase(node);
			const ThreadCfgLabel &label(node->rip);

			/* Can't be an eval point */
			if (ced.expressionEvalPoints.count(label)) {
				frozenStashPoints.insert(node);
				break;
			}

			/* Can't be a happens-before before point */
			{
				auto it2 = ced.happensBeforePoints.find(label);
				if (it2 != ced.happensBeforePoints.end()) {
					bool b = false;
					for (auto it3 = it2->second.begin();
					     !b && it3 != it2->second.end();
					     it3++)
						if ((*it3)->before->rip == label)
							b = true;
					if (b) {
						frozenStashPoints.insert(node);
						break;
					}
				}
			}


			/* Can't stash a register which this
			 * instruction might modify */
			IRSB *irsb = oracle->ms->addressSpace->getIRSBForAddress(ThreadRip(Oracle::STATIC_THREAD, ced.crashCfg.labelToRip(node->label)), true);
			std::set<threadAndRegister, threadAndRegister::partialCompare> modified_regs;
			for (int x = 0; x < irsb->stmts_used && irsb->stmts[x]->tag != Ist_IMark; x++) {
				if (irsb->stmts[x]->tag == Ist_Put)
					modified_regs.insert( ((IRStmtPut *)irsb->stmts[x])->target );
			}
			bool b = false;
			for (auto it2 = it->second.begin();
			     !b && it2 != it->second.end();
			     it2++) {
				if (modified_regs.count((*it2)->reg))
					b = true;
			}
			if (b) {
				frozenStashPoints.insert(node);
				break;
			}

			/* Advance this stash point */
			for (auto it2 = node->successors.begin(); it2 != node->successors.end(); it2++)
				unfrozenStashPoints.insert(it2->instr);
		}

		for (auto it2 = frozenStashPoints.begin(); it2 != frozenStashPoints.end(); it2++) {
			auto *node = *it2;
			ThreadCfgLabel label(it->first.thread, node->label);
			std::set<IRExprGet *> &newStash(newMap[label]);
			for (auto it3 = exprsToStash.begin();
			     it3 != exprsToStash.end();
			     it3++)
				newStash.insert(*it3);
		}
	}

	ced.exprStashPoints = newMap;
}

/* We sometimes find that the CFG has a prefix which is completely
   irrelevant.  Try to remove it. */
static void
optimiseCfg(crashEnforcementData &ced)
{
	struct {
		crashEnforcementData *ced;
		bool operator()(const ThreadCfgLabel &label) {
			return ced->exprStashPoints.count(label) != 0 ||
				ced->happensBeforePoints.count(label) != 0 ||
				ced->expressionEvalPoints.count(label) != 0 ||
				ced->threadExitPoints.count(label) != 0;
		}
	} hasSideEffect = {&ced};
	crashEnforcementRoots newRoots;
	for (auto it = ced.roots.begin(); !it.finished(); it.advance()) {
		const AbstractThread thread(it.get().thread);
		auto root = ced.crashCfg.findInstr(it.get());
		while (1) {
			/* We can advance a root if it has a single
			   successor, and it has no stash points, and
			   it has no HB points, and it has no eval
			   points, and it isn't an exit point. */
			if (root->successors.size() != 1)
                               break;
			ThreadCfgLabel l(thread, root->label);
			if (hasSideEffect(l))
				break;
			root = root->successors[0].instr;
		}

		/* If all of the paths forwards from root N issue
		   their first side-effect at node N' then N can be
		   replaced by N'. */
		bool haveFirstSideEffect = false;
		bool failed = false;
		ThreadCfgLabel firstSideEffect;
		std::set<const Instruction<ThreadCfgLabel> *> visited;
		std::queue<const Instruction<ThreadCfgLabel> *> pending;
		pending.push(root);
		while (!failed && !pending.empty()) {
			auto n = pending.front();
			pending.pop();
			ThreadCfgLabel l(thread, n->label);

			if (hasSideEffect(l)) {
				if (haveFirstSideEffect) {
					if (firstSideEffect != l)
						failed = true;
				} else {
					firstSideEffect = l;
					haveFirstSideEffect = true;
				}
			} else {
				for (auto it = n->successors.begin();
				     it != n->successors.end();
				     it++)
					pending.push(it->instr);
			}
		}
		if (haveFirstSideEffect) {
			if (failed)
				newRoots.insert(it.concrete_tid(), it.get());
			else
				newRoots.insert(it.concrete_tid(), firstSideEffect);
		}
	}
	ced.roots = newRoots;

	/* Anything which isn't reachable from a root can be removed
	 * from the CFG. */
	std::set<Instruction<ThreadCfgLabel> *> retain;
	std::queue<Instruction<ThreadCfgLabel> *> pending;
	for (auto it = ced.roots.begin(); !it.finished(); it.advance())
		pending.push(ced.crashCfg.findInstr(it.get()));
	while (!pending.empty()) {
		auto n = pending.front();
		pending.pop();
		if (!retain.insert(n).second)
			continue;
		for (auto it = n->successors.begin(); it != n->successors.end(); it++)
			pending.push(it->instr);
	}
	ced.crashCfg.removeAllBut(retain);
}

/* We need to patch the program to jump to our instrumentation at
 * every entry point.  Those jump instructions are five bytes, so
 * could clobber a following instruction.  We need to make sure that
 * the program doesn't jump to one of those clobbered instructions.
 * The way we do so is by making sure that anything which might jump
 * to one of them is itself handled by the interpreter.  Sometimes, we
 * can do that by marking the branch instruction as being a root
 * itself, but sometimes we can't find it (e.g. an indirect call from
 * a library back to a function in the main program), and in that case
 * we find all of the places in the program which might branch to
 * *that* instruction and recurse to protect them.
 */
static void
avoidBranchToPatch(crashEnforcementData &ced, Oracle *oracle)
{
	/* Instructions which we've decided need to be patched as
	   interpreter entry points but which we haven't gotten around
	   to doing yet. */
	std::set<unsigned long> neededEntryPoints;
	/* Instructions which we now set up as entry points */
	std::set<unsigned long> entryPoints;
	/* Not entry points, and not part of the main CFG, but the
	   interpreter should keep interpreting if it hits one
	   anyway. */
	std::set<unsigned long> keepInterpretingInstrs;
	/* Instructions which are entry points because of the explicit
	   CFG. */
	std::set<unsigned long> basicEntryPoints;

	if (debug_declobber_instructions)
		printf("Computing clobbered instructions set\n");
	for (auto it = ced.roots.begin(); !it.finished(); it.advance()) {
		Instruction<ThreadCfgLabel> *instr = ced.crashCfg.findInstr(it.get());
		assert(instr);
		const VexRip &vr(ced.crashCfg.labelToRip(instr->label));
		unsigned long r = vr.unwrap_vexrip();
		if (debug_declobber_instructions)
			printf("%lx is a root\n", r);
		neededEntryPoints.insert(r);
		basicEntryPoints.insert(r);
	}

	while (!neededEntryPoints.empty()) {
		unsigned long e = *neededEntryPoints.begin();
		neededEntryPoints.erase(e);

		if (debug_declobber_instructions)
			printf("Considering entry point %lx\n", e);

		/* Are there any branches which we don't know about to
		   this instruction's clobbered set?  We approximate
		   that by saying that external branches will only
		   ever target function heads. */
		bool hasExternalBranches = false;
		for (unsigned x = 1; !hasExternalBranches && x < 5; x++) {
			if (oracle->isFunctionHead(StaticRip(e + x)))
				hasExternalBranches = true;
		}
		if (hasExternalBranches) {
			/* We can't make e an entry point, because
			   there's not space before the end of the
			   function, so try to cover its predecessors
			   instead. */
			keepInterpretingInstrs.insert(e);
			std::set<unsigned long> predecessors;
			oracle->findPredecessors(e, predecessors);
			if (debug_declobber_instructions) {
				printf("%lx cannot be patched due to potential external branches to the clobber zone; predecessors = [",
				       e);
				for (auto it = predecessors.begin(); it != predecessors.end(); it++) {
					if (it != predecessors.begin())
						printf(", ");
					printf("%lx", *it);
				}
				printf("]\n");
			}
			neededEntryPoints.insert(predecessors.begin(), predecessors.end());
		} else {
			entryPoints.insert(e);
			for (unsigned x = 1; x < 5; x++) {
				std::set<unsigned long> predecessors;
				oracle->findPredecessors(e + x, predecessors);
				for (unsigned y = 0; y < x; y++)
					predecessors.erase(e + y);
				if (predecessors.empty())
					continue;
				if (debug_declobber_instructions) {
					printf("Entry point %lx clobbers %lx; predecessors = [",
					       e, e + x);
					for (auto it = predecessors.begin(); it != predecessors.end(); it++) {
						if (it != predecessors.begin())
							printf(", ");
						printf("%lx", *it);
					}
					printf("]\n");
				}
				neededEntryPoints.insert(predecessors.begin(), predecessors.end());
			}
		}
	}

	std::set<unsigned long> dummyEntryPoints;
	for (auto it = entryPoints.begin(); it != entryPoints.end(); it++)
		if (!basicEntryPoints.count(*it))
			dummyEntryPoints.insert(*it);
	if (debug_declobber_instructions) {
		printf("Dummy entry points = [");
		for (auto it = dummyEntryPoints.begin(); it != dummyEntryPoints.end(); it++) {
			if (it != dummyEntryPoints.begin())
				printf(", ");
			printf("0x%lx", *it);
		}
		printf("], keepInterpreting = [");
		for (auto it = keepInterpretingInstrs.begin(); it != keepInterpretingInstrs.end(); it++) {
			if (it != keepInterpretingInstrs.begin())
				printf(", ");
			printf("0x%lx", *it);
		}
		printf("]\n");
	}

	ced.dummyEntryPoints = dummyEntryPoints;
	ced.keepInterpretingInstrs = keepInterpretingInstrs;
}

static void
optimiseHBEdges(crashEnforcementData &ced)
{
	/* If an instruction receives a message from thread X then it
	   then binds to thread X and from that point on can only ever
	   send or receive with X.  That allows us to eliminate some
	   message operations. */
	for (auto it = ced.happensBeforePoints.begin();
	     it != ced.happensBeforePoints.end();
	     it++) {
		std::set<AbstractThread> mightReceiveFrom;
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			const happensBeforeEdge *hbe = *it2;
			if (hbe->after->rip == it->first)
				mightReceiveFrom.insert(hbe->before->rip.thread);
		}
		if (mightReceiveFrom.empty())
			continue;
		/* Now we know that we've definitely received from one
		   of the threads in @mightReceiveFrom, so we can only
		   send to them.  Kill off any other edges. */
		for (auto it2 = it->second.begin(); it2 != it->second.end(); ) {
			const happensBeforeEdge *hbe = *it2;
			if (hbe->before->rip == it->first &&
			    !mightReceiveFrom.count(hbe->after->rip.thread))
				it->second.erase(it2++);
			else
				it2++;
		}
	}

	/* And now get rid of any messages which are sent but never
	   received or received but never sent. */
	std::set<unsigned> sent;
	std::set<unsigned> received;
	for (auto it = ced.happensBeforePoints.begin();
	     it != ced.happensBeforePoints.end();
	     it++) {
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			if ((*it2)->before->rip == it->first)
				sent.insert( (*it2)->msg_id);
			else
				received.insert( (*it2)->msg_id);
		}
	}
	for (auto it = ced.happensBeforePoints.begin();
	     it != ced.happensBeforePoints.end();
		) {
		for (auto it2 = it->second.begin(); it2 != it->second.end(); ) {
			unsigned id = (*it2)->msg_id;
			if (!sent.count(id) || !received.count(id))
				it->second.erase(it2++);
			else
				it2++;
		}
		if (it->second.empty())
			ced.happensBeforePoints.erase(it++);
		else
			it++;
	}
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);

	int next_hb_id = 0xaabb;
	simulationSlotT next_slot(1);

	VexPtr<CrashSummary, &ir_heap> summary(readBugReport(argv[5], NULL));
	ThreadAbstracter abs;
	crashEnforcementData accumulator = enforceCrashForMachine(summary, oracle, ALLOW_GC, abs, next_hb_id, next_slot);

	optimiseHBEdges(accumulator);
	optimiseStashPoints(accumulator, oracle);
	optimiseCfg(accumulator);

	avoidBranchToPatch(accumulator, oracle);

	FILE *f = fopen(argv[4], "w");
	accumulator.prettyPrint(f);
	accumulator.prettyPrint(stdout);
	fclose(f);

	return 0;
}


/* For the compiler to instantiate CFG<ThreadRip>::print, so that it's
   available in gdb. */
void
force_compilation(CFG<ThreadRip> *r)
{
	r->print(stdout);
}
