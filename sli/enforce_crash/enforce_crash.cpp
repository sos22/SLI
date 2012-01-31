#include <sys/fcntl.h>
#include <err.h>
#include <stdio.h>
#include <unistd.h>

#include "sli.h"
#include "inferred_information.hpp"
#include "oracle.hpp"
#include "offline_analysis.hpp"
#include "cnf.hpp"
#include "genfix.hpp"
#include "dnf.hpp"
#include "simplify_ordering.hpp"
#include "zapBindersAndFreeVariables.hpp"
#include "enforce_crash.hpp"

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

abstractThreadExitPointsT::abstractThreadExitPointsT(EnforceCrashCFG *cfg,
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
			instrT *successors[2];
			int nr_successors;
			nr_successors = 0;
			if (i->defaultNextI)
				successors[nr_successors++] = i->defaultNextI;
			if (i->branchNextI)
				successors[nr_successors++] = i->branchNextI;
			if (nr_successors == 0)
				continue;

			/* Forward reachability: look at our
			   successors, and make sure that anything
			   which they can reach is reachable from us
			   as well. */
			std::set<instrT *> &f(forwardReachable[i]);
			for (int j = 0; j < nr_successors; j++) {
				instrT *successor = successors[j];
				std::set<instrT *> &f2(forwardReachable[successor]);
				for (auto it2 = f2.begin(); it2 != f2.end(); it2++) {
					if (!f.count(*it2)) {
						progress = true;
						f.insert(*it2);
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

		unsigned thread = it.key().thread;

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
				if (hbe->before.thread == thread) {
					/* Can we send this message? */
					instrT *sender = cfg->ripToInstr->get(hbe->before);
					if (forwardReachable[i].count(sender))
						should_be_present = true;
				} else if (hbe->after.thread == thread) {
					/* Can we receive this message? */
					instrT *receiver = cfg->ripToInstr->get(hbe->after);
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
				if (hbe->after.thread == thread) {
					instrT *receiver = cfg->ripToInstr->get(hbe->after);
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

		if (i->defaultNextI && !instructionPresence.count(i->defaultNextI))
			(*this)[i->defaultNextI->rip.rip].insert(i->rip.thread);
		if (i->defaultNext.rip && !i->defaultNextI)
			(*this)[i->defaultNext.rip].insert(i->rip.thread);
		if (i->branchNextI && !instructionPresence.count(i->branchNextI))
			(*this)[i->branchNextI->rip.rip].insert(i->rip.thread);
		if (!i->isCall && i->branchNext.rip && !i->branchNextI)
			(*this)[i->branchNext.rip].insert(i->rip.thread);
	}

}

static bool
buildCED(DNF_Conjunction &c, FreeVariableMap &fv,
	 std::map<unsigned, ThreadRip> &roots,
	 AddressSpace *as, crashEnforcementData *out,
	 int &next_hb_id)
{
	/* Figure out what we actually need to keep track of */
	std::set<IRExpr *> neededExpressions;
	for (unsigned x = 0; x < c.size(); x++)
		enumerateNeededExpressions(c[x].second, neededExpressions);

	/* and where the needed expressions are calculated */
	std::set<ThreadRip> neededRips;
	for (std::set<IRExpr *>::iterator it = neededExpressions.begin();
	     it != neededExpressions.end();
	     it++) {
		IRExpr *e = *it;
		if (e->tag == Iex_Get) {
			neededRips.insert(roots[((IRExprGet *)e)->reg.tid()]);
		} else if (e->tag == Iex_ClientCall) {
			neededRips.insert(((IRExprClientCall *)e)->callSite);
		} else if (e->tag == Iex_Load) {
			neededRips.insert(((IRExprLoad *)e)->rip);
		} else if (e->tag == Iex_HappensBefore) {
			neededRips.insert(((IRExprHappensBefore *)e)->before);
			neededRips.insert(((IRExprHappensBefore *)e)->after);
		} else {
			abort();
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
	cfg->doit();
	
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

	/* Figure out where the various expressions should be
	 * evaluated. */
	expressionDominatorMapT exprDominatorMap;
	if (!exprDominatorMap.init(c, cfg, neededRips))
		return false;

	*out = crashEnforcementData(neededExpressions, roots, exprDominatorMap, c, cfg, next_hb_id);
	return true;
}

static bool
analyseHbGraph(DNF_Conjunction &c, CrashSummary *summary)
{
	std::set<IRExprHappensBefore *, HBOrdering> hb;
	std::set<IRExprHappensBefore *, HBOrdering> assumption;

	extractImplicitOrder(summary->loadMachine, assumption);
	for (unsigned x = 0; x < summary->storeMachines.size(); x++)
		extractImplicitOrder(summary->storeMachines[x]->machine, assumption);
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
		       int &next_hb_id)
{
	printf("Machines to enforce:\n");
	printCrashSummary(summary, stdout);

	IRExpr *requirement =
		findHappensBeforeRelations(summary, oracle,
					   AllowableOptimisations::defaultOptimisations,
					   token);
	fprintf(_logfile, "Crash requirement:\n");
	ppIRExpr(requirement, _logfile);
	fprintf(_logfile, "\n");

	std::map<unsigned, ThreadRip> roots;
	roots[summary->loadMachine->tid] = ThreadRip::mk(summary->loadMachine->tid, summary->loadMachine->origin);
	
	FreeVariableMap m(summary->loadMachine->freeVariables);
	zapBindersAndFreeVariables(m, summary->loadMachine);
	for (unsigned x = 0; x < summary->storeMachines.size(); x++) {
		FreeVariableMap n(summary->storeMachines[x]->machine->freeVariables);
		zapBindersAndFreeVariables(n, summary->storeMachines[x]->machine);
		m.merge(n);
		roots[summary->storeMachines[x]->machine->tid] =
			ThreadRip::mk(summary->storeMachines[x]->machine->tid,
				      summary->storeMachines[x]->machine->origin);
	}

	requirement = internIRExpr(zapFreeVariables(requirement, m));
	requirement = simplifyIRExpr(requirement, AllowableOptimisations::defaultOptimisations);
	fprintf(_logfile, "After free variable removal:\n");
	ppIRExpr(requirement, _logfile);
	fprintf(_logfile, "\n");

	if (TIMEOUT) {
		fprintf(_logfile, "Killed by a timeout during simplification\n");
		exit(1);
	}
	DNF_Disjunction d;
	auto dnfres(dnf(requirement, d));
	if (!dnfres.valid) {
		fprintf(_logfile, "failed to convert to DNF\n");
		exit(1);
	}
	if (!dnfres.content) {
		/* Okay, so once we've converted to DNF we find that
		   the expression is always true and that the program
		   will always crash.  That seems kind of unlikely,
		   but it's fortunately easy to handle: just don't add
		   any more enforcement infrastructure. */
		fprintf(_logfile, "program is doomed to die?\n");
		return crashEnforcementData();
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

	crashEnforcementData accumulator;
	for (unsigned x = 0; x < d.size(); x++) {
		crashEnforcementData tmp;
		if (buildCED(d[x], m, roots, oracle->ms->addressSpace, &tmp, next_hb_id))
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
	crashEnforcementData accumulator;
	for (int i = 5; i < argc; i++) {
		int fd = open(argv[i], O_RDONLY);
		if (fd < 0)
			err(1, "opening %s", argv[i]);
		VexPtr<CrashSummary, &ir_heap> summary(readCrashSummary(fd));
		close(fd);

		accumulator |= enforceCrashForMachine(summary, oracle, ALLOW_GC, next_hb_id);
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
