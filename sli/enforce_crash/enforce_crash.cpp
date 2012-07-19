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

unsigned long
__trivial_hash_function(const VexRip &vr)
{
	return vr.hash();
}

void
instrToInstrSetMap::print(FILE *f)
{
	for (iterator it = begin(); it != end(); it++) {
		fprintf(f, "%s[%p] -> {", it->first->rip.name(), it->first);
		for (auto it2 = it->second.begin();
		     it2 != it->second.end();
		     it2++) {
			if (it2 != it->second.begin())
				fprintf(f, ", ");
			fprintf(f, "%s[%p]", (*it2)->rip.name(), *it2);
		}
		fprintf(f, "}\n");
	}
}

abstractThreadExitPointsT::abstractThreadExitPointsT(
	ThreadCfgDecode &cfg,
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

	for (auto it = cfg.begin(); it != cfg.end(); it++)
		if (it.value())
			forwardReachable[it.value()].insert(it.value());

	bool progress;
	do {
		progress = false;
		for (auto it = cfg.begin(); it != cfg.end(); it++) {
			instrT *i = it.value();
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
	for (auto it = cfg.begin(); it != cfg.end(); it++) {
		instrT *i = it.value();
		if (!i)
			continue;

		int thread = it.thread();

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
				if (hbe->before.tid == thread) {
					/* Can we send this message? */
					instrT *sender = cfg(hbe->before);
					if (forwardReachable[i].count(sender))
						should_be_present = true;
				} else if (hbe->after.tid == thread) {
					/* Can we receive this message? */
					instrT *receiver = cfg(hbe->after);
					if (forwardReachable[i].count(receiver))
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
				if (hbe->after.tid == thread) {
					instrT *receiver = cfg(hbe->after);
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
			if (it2->type == instrT::successor_t::succ_call)
				continue;
			if (it2->instr && !instructionPresence.count(it2->instr))
				insert(it2->instr->rip);
		}
	}

}

static bool
buildCED(DNF_Conjunction &c,
	 std::map<unsigned, CfgLabel> &rootsCfg,
	 StateMachine *probeMachine,
	 StateMachine *storeMachine,
	 crashEnforcementData *out,
	 int &next_hb_id,
	 simulationSlotT &next_slot)
{
	ThreadCfgDecode cfg;
	cfg.addMachine(probeMachine);
	cfg.addMachine(storeMachine);

	/* Figure out what we actually need to keep track of */
	std::set<IRExpr *> neededExpressions;
	for (unsigned x = 0; x < c.size(); x++)
		enumerateNeededExpressions(c[x].second, neededExpressions);

	/* and where the needed expressions are calculated */
	std::set<ThreadCfgLabel> neededRips;
	{
		/* XXX keep this in sync with
		 * expressionStashMapT::expressionStashMapT() */
		std::set<IRExprGet *> neededTemporaries;
		for (auto it = neededExpressions.begin();
		     it != neededExpressions.end();
		     it++) {
			IRExpr *e = *it;
			if (e->tag == Iex_Get) {
				IRExprGet *ieg = (IRExprGet *)e;
				if (ieg->reg.isReg()) {
					auto it_r = rootsCfg.find(ieg->reg.tid());
					assert(it_r != rootsCfg.end());
					neededRips.insert(ThreadCfgLabel(ieg->reg.tid(), it_r->second));
				} else {
					neededTemporaries.insert(ieg);
				}
			} else {
				assert(e->tag == Iex_HappensBefore);
				IRExprHappensBefore *ieh = (IRExprHappensBefore *)e;
				neededRips.insert(ieh->before);
				neededRips.insert(ieh->after);
			}
		}
		if (!neededTemporaries.empty()) {
			std::set<StateMachineSideEffectLoad *> loads;
			enumSideEffects(probeMachine, loads);
			enumSideEffects(storeMachine, loads);
			for (auto it = neededTemporaries.begin();
			     it != neededTemporaries.end();
			     it++) {
				StateMachineSideEffectLoad *l = NULL;
				for (auto it2 = loads.begin(); it2 != loads.end(); it2++) {
					if ( threadAndRegister::fullEq((*it2)->target, (*it)->reg) ) {
						assert(!l);
						l = *it2;
					}
				}
				assert(l);
				neededRips.insert(l->rip);
			}
		}
	}

	/* Figure out where the various expressions should be
	 * evaluated. */
	expressionDominatorMapT exprDominatorMap(c, cfg, neededRips);

	*out = crashEnforcementData(neededExpressions, rootsCfg, exprDominatorMap, probeMachine, storeMachine, c, cfg, next_hb_id, next_slot);
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

static crashEnforcementData
enforceCrashForMachine(VexPtr<CrashSummary, &ir_heap> summary,
		       VexPtr<Oracle> &oracle,
		       GarbageCollectionToken token,
		       int &next_hb_id,
		       simulationSlotT &next_slot)
{
	summary = internCrashSummary(summary);

	printf("Machines to enforce:\n");
	printCrashSummary(summary, stdout);

	VexPtr<OracleInterface> oracleI(oracle);

	IRExpr *requirement =
		findHappensBeforeRelations(summary, oracleI,
					   AllowableOptimisations::defaultOptimisations
						.setAddressSpace(oracle->ms->addressSpace),
					   MemoryAccessIdentifierAllocator(),
					   token);
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

	for (unsigned x = 0; x < d.size(); ) {
		if (analyseHbGraph(d[x], summary)) {
			x++;
		} else {
			d.erase(d.begin() + x);
		}
	}

	printDnf(d, _logfile);

	if (d.size() == 0)
		return crashEnforcementData(summary);

	std::map<unsigned, CfgLabel> rootsCfg;
	assert(summary->loadMachine->origin.size() == 1);
	assert(summary->storeMachine->origin.size() == 1);
	assert(summary->loadMachine->cfg_roots.size() == 1);
	assert(summary->storeMachine->cfg_roots.size() == 1);
	rootsCfg.insert(std::pair<unsigned, CfgLabel>(
				summary->loadMachine->origin[0].first,
				summary->loadMachine->cfg_roots[0]->label));
	rootsCfg.insert(std::pair<unsigned, CfgLabel>(
				summary->storeMachine->origin[0].first,
				summary->storeMachine->cfg_roots[0]->label));

	crashEnforcementData accumulator(summary);
	for (unsigned x = 0; x < d.size(); x++) {
		crashEnforcementData tmp;
		if (buildCED(d[x], rootsCfg, summary->loadMachine, summary->storeMachine, &tmp, next_hb_id, next_slot))
			accumulator |= tmp;
	}
	return accumulator;
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
	crashEnforcementData accumulator = enforceCrashForMachine(summary, oracle, ALLOW_GC, next_hb_id, next_slot);

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
