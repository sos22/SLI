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
static bool debug_build_cfg = false;
#else
#define debug_build_cfg false
#endif

void
instrToInstrSetMap::print(FILE *f)
{
	for (iterator it = begin(); it != end(); it++) {
		fprintf(f, "%s[%p] -> {", it->first->rip.name(), it->first);
		for (std::set<Instruction<ThreadRip> *>::iterator it2 = it->second.begin();
		     it2 != it->second.end();
		     it2++) {
			if (it2 != it->second.begin())
				fprintf(f, ", ");
			fprintf(f, "%s[%p]", (*it2)->rip.name(), *it2);
		}
		fprintf(f, "}\n");
	}
}

unsigned long __trivial_hash_function(const ClientRip &k)
{
	return k.rip;
}

abstractThreadExitPointsT::abstractThreadExitPointsT(
	CfgDecode &decode,
	EnforceCrashCFG *cfg,
	happensBeforeMapT &happensBeforePoints)
{
	/* We need to exit thread X if we reach instruction Y and
	   there is some message which is needed by thread X such that
	   Y cannot have already received that message and cannot
	   subsequently send it.  We also exit if Y can neither send
	   nor receive any further messages. */

	typedef Instruction<ThreadRip> instrT;

	/* Step one: build control-flow reachability maps */

	/* forwardReachable[x] -> the set of instructions y such that
	   there's some control flow path from x to y */
	instrToInstrSetMap forwardReachable;
	/* backwardReachable[x] -> the set of instructions y such that
	   there's some control flow path from y to x */
	instrToInstrSetMap backwardReachable;

	for (auto it = cfg->ripToInstr->begin(); it != cfg->ripToInstr->end(); it++)
		if (it.value())
			forwardReachable[it.value()].insert(it.value());

	bool progress;
	do {
		progress = false;
		for (auto it = cfg->ripToInstr->begin(); it != cfg->ripToInstr->end(); it++) {
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
	for (auto it = cfg->ripToInstr->begin(); it != cfg->ripToInstr->end(); it++) {
		instrT *i = it.value();
		if (!i)
			continue;

		int thread = it.key().thread;

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
					instrT *sender = cfg->ripToInstr->get(ThreadRip(hbe->before.tid, decode(hbe->before.where)->rip));
					if (forwardReachable[i].count(sender))
						should_be_present = true;
				} else if (hbe->after.tid == thread) {
					/* Can we receive this message? */
					instrT *receiver = cfg->ripToInstr->get(ThreadRip(hbe->after.tid, decode(hbe->after.where)->rip));
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
					instrT *receiver = cfg->ripToInstr->get(ThreadRip(hbe->after.tid, decode(hbe->after.where)->rip));
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
				(*this)[it2->instr->rip.rip.unwrap_vexrip()].insert(i->rip.thread);
			if (it2->rip.rip.isValid() && !it2->instr)
				(*this)[it2->rip.rip.unwrap_vexrip()].insert(i->rip.thread);
		}
	}

}

static bool
buildCED(CfgLabelAllocator &allocLabel,
	 CfgDecode &decode,
	 DNF_Conjunction &c,
	 std::map<unsigned, ThreadRip> &roots,
	 AddressSpace *as,
	 StateMachine *probeMachine,
	 StateMachine *storeMachine,
	 crashEnforcementData *out,
	 int &next_hb_id,
	 simulationSlotT &next_slot)
{
	/* Figure out what we actually need to keep track of */
	std::set<IRExpr *> neededExpressions;
	for (unsigned x = 0; x < c.size(); x++)
		enumerateNeededExpressions(c[x].second, neededExpressions);

	/* and where the needed expressions are calculated */
	std::set<ThreadRip> neededRips;
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
					neededRips.insert(roots[ieg->reg.tid()]);
				} else {
					neededTemporaries.insert(ieg);
				}
			} else {
				assert(e->tag == Iex_HappensBefore);
				IRExprHappensBefore *ieh = (IRExprHappensBefore *)e;
				neededRips.insert(ThreadRip(ieh->before.tid, decode(ieh->before.where)->rip));
				neededRips.insert(ThreadRip(ieh->after.tid, decode(ieh->after.where)->rip));
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
				neededRips.insert(ThreadRip(l->rip.tid, decode(l->rip.where)->rip));
			}
		}
	}

	/* and which threads are relevant */
	std::set<unsigned> neededThreads;
	for (std::set<ThreadRip>::iterator it = neededRips.begin();
	     it != neededRips.end();
	     it++)
		neededThreads.insert(it->thread);

	/* Build the CFG */
	EnforceCrashCFG *cfg = new EnforceCrashCFG(as, neededRips);
	for (std::map<unsigned, ThreadRip>::iterator it = roots.begin();
	     it != roots.end();
	     it++) {
		printf("Root %s\n", it->second.name());
		cfg->add_root(it->second, 1000);
	}
	cfg->doit(allocLabel);
	
	if (cfg->ripToInstr->size() > 1000) {
		printf("CFG is too big to work with\n");
		return false;
	}

	for (auto it = neededRips.begin(); it != neededRips.end(); it++) {
		if (!cfg->ripToInstr->hasKey(*it)) {
			printf("Failed to build sufficiently complete CFG!\n");
			return false;
		}
	}

	if (debug_build_cfg) {
		printf("Needed RIPs:\n");
		for (auto it = neededRips.begin(); it != neededRips.end(); it++)
			printf("\t%s\n", it->name());
		printf("CFG:\n");
		cfg->print(stdout);
	}

	/* Figure out where the various expressions should be
	 * evaluated. */
	expressionDominatorMapT exprDominatorMap;
	if (!exprDominatorMap.init(decode, c, cfg, neededRips))
		return false;

	*out = crashEnforcementData(decode, neededExpressions, roots, exprDominatorMap, probeMachine, storeMachine, c, cfg, next_hb_id, next_slot);
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

	CfgDecode decode;
	decode.addMachine(summary->loadMachine);
	decode.addMachine(summary->storeMachine);

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
		return crashEnforcementData();

	std::map<unsigned, ThreadRip> roots;
	assert(summary->loadMachine->origin.size() == 1);
	assert(summary->storeMachine->origin.size() == 1);
	roots[summary->loadMachine->origin[0].first] =
		ThreadRip::mk(summary->loadMachine->origin[0].first,
			      summary->loadMachine->origin[0].second);
	roots[summary->storeMachine->origin[0].first] =
		ThreadRip::mk(summary->storeMachine->origin[0].first,
			      summary->storeMachine->origin[0].second);

	CfgLabelAllocator allocLabel;

	crashEnforcementData accumulator;
	for (unsigned x = 0; x < d.size(); x++) {
		crashEnforcementData tmp;
		if (buildCED(allocLabel, decode, d[x], roots, oracle->ms->addressSpace, summary->loadMachine, summary->storeMachine, &tmp, next_hb_id, next_slot))
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
	crashEnforcementData accumulator;
	for (int i = 5; i < argc; i++) {
		VexPtr<CrashSummary, &ir_heap> summary(readBugReport(argv[i], NULL));
		accumulator |= enforceCrashForMachine(summary, oracle, ALLOW_GC, next_hb_id, next_slot);
	}

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
