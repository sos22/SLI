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

class EnforceCrashCFG : public CFG<ThreadRip> {
	std::set<ThreadRip> &neededInstructions;
public:
	bool instructionUseful(Instruction<ThreadRip> *i) {
		return neededInstructions.count(i->rip) != 0;
	}
	EnforceCrashCFG(AddressSpace *as, std::set<ThreadRip> &ni)
		: CFG<ThreadRip>(as), neededInstructions(ni)
	{}
};

void
instrToInstrSetMap::print(FILE *f)
{
	for (iterator it = begin(); it != end(); it++) {
		fprintf(f, "%d:%lx[%p] -> {", it->first->rip.thread, it->first->rip.rip, it->first);
		for (std::set<Instruction<ThreadRip> *>::iterator it2 = it->second.begin();
		     it2 != it->second.end();
		     it2++) {
			if (it2 != it->second.begin())
				fprintf(f, ", ");
			fprintf(f, "%d:%lx[%p]", (*it2)->rip.thread, (*it2)->rip.rip, *it2);
		}
		fprintf(f, "}\n");
	}
}

ClientRip threadRipToClientRip(const ThreadRip &k)
{
	return ClientRip(k.rip);
}
unsigned long __trivial_hash_function(const ClientRip &k)
{
	return k.rip;
}

static EarlyRelocation<ClientRip> *
duplicateEarlyRelocAtNewThreadSet(EarlyRelocation<ClientRip> *er, const std::set<unsigned> &threads)
{
	if (RipRelativeRelocation<ClientRip> *rrr =
	    dynamic_cast<RipRelativeRelocation<ClientRip> *>(er)) {
		return new RipRelativeRelocation<ClientRip>(rrr->offset, rrr->size,
							    ClientRip(rrr->target.rip, threads),
							    rrr->nrImmediateBytes);
	} else if (RipRelativeBranchRelocation<ClientRip> *rrbr =
		   dynamic_cast<RipRelativeBranchRelocation<ClientRip> *>(er)) {
		return new RipRelativeBranchRelocation<ClientRip>(rrbr->offset, rrbr->size,
								  ClientRip(rrbr->target.rip, threads));

	} else {
		abort();
	}
}

template <typename k, typename v> void
mapKeys(std::set<k> &out, std::map<k, v> &m)
{
	for (typename std::map<k, v>::iterator it = m.begin();
	     it != m.end();
	     it++)
		out.insert(it->first);
}

template <typename t> void
powerSet(const std::set<t> &_in, std::set<std::set<t> > &out)
{
	/* It's useful to be able to refer to the elements of @_in by
	   index, which means we really want to put them in a
	   vector. */
	std::vector<t> in;
	in.reserve(_in.size());
	for (typename std::set<t>::iterator it = _in.begin();
	     it != _in.end();
	     it++)
		in.push_back(*it);
	/* @live tells you which elements of @in you want to include
	   in the next item.  It's pretty much the binary
	   representation of the number of items currently in @out,
	   and counts from 0 to 1111..., with an appropriate number of
	   ones, and hence covers every possible subvector of @in. */
	std::vector<bool> live;
	live.resize(in.size());
	while (1) {
		/* Insert new item */
		std::set<t> item;
		for (unsigned x = 0; x < live.size(); x++)
			if (live[x])
				item.insert(in[x]);
		out.insert(item);

		/* Advance @live.  This is just the add-one algorithm
		   in binary.  There might be a more efficient way to
		   do this. :) */
		unsigned x;
		for (x = 0; x < live.size(); x++) {
			if (live[x]) {
				live[x] = false;
			} else {
				live[x] = true;
				break;
			}
		}
		if (x == live.size())
			break;
	}
}

static void
duplicateCFGAtThreadSet(CFG<ClientRip> *cfg, std::set<unsigned long> &rips, const std::set<unsigned> &threads)
{
	std::map<Instruction<ClientRip> *, Instruction<ClientRip> *> m;

	for (std::set<unsigned long>::iterator it = rips.begin();
	     it != rips.end();
	     it++) {
		Instruction<ClientRip> *orig = cfg->ripToInstr->get(ClientRip(*it));
		ClientRip newRip(*it, threads);
		assert(!cfg->ripToInstr->hasKey(newRip));
		Instruction<ClientRip> *nr = new Instruction<ClientRip>(*orig);
		nr->rip = newRip;
		if (nr->defaultNext.rip)
			nr->defaultNext = ClientRip(nr->defaultNext.rip, threads);
		if (nr->branchNext.rip)
			nr->branchNext = ClientRip(nr->branchNext.rip, threads);
		for (unsigned x = 0; x < nr->relocs.size(); x++)
			nr->relocs[x] = duplicateEarlyRelocAtNewThreadSet(nr->relocs[x], threads);
		cfg->ripToInstr->set(newRip, nr);
		m[orig] = nr;
	}

	for (std::set<unsigned long>::iterator it = rips.begin();
	     it != rips.end();
	     it++) {
		ClientRip newRip(*it, threads);
		Instruction<ClientRip> *n = cfg->ripToInstr->get(newRip);
		assert(n);
		if (n->defaultNextI) {
			n->defaultNextI = m[n->defaultNextI];
			assert(n->defaultNextI);
		}
		if (n->branchNextI) {
			n->branchNextI = m[n->branchNextI];
			assert(n->branchNextI);
		}
	}
}

static CFG<ClientRip> *
convertCFGFromThreadRipToClientRips(CFG<ThreadRip> *cfg,
				    std::set<unsigned> &neededThreads,
				    expressionDominatorMapT &exprDominatorMap)
{
	CFG<ClientRip> *degradedCfg = cfg->degrade<ClientRip, threadRipToClientRip>();

	/* And now expand it again so that we can do the power-set
	 * construction. */
	std::set<std::set<unsigned> > threadPower;
	{
		std::set<std::set<unsigned> > threadPower1;
		powerSet(neededThreads, threadPower1);
		for (std::set<std::set<unsigned> >::iterator it = threadPower1.begin();
		     it != threadPower1.end();
		     it++)
			threadPower.insert(*it);
	}
	printf("Power threads:\n");
	for (std::set<std::set<unsigned> >::iterator it = threadPower.begin();
	     it != threadPower.end();
	     it++) {
		printf("\t");
		for (std::set<unsigned>::const_iterator it2 = it->begin();
		     it2 != it->end();
		     it2++)
			printf("%d ", *it2);
		printf("\n");
	}
	std::set<unsigned long> rawRips;
	for (CFG<ClientRip>::ripToInstrT::iterator it = degradedCfg->ripToInstr->begin();
	     it != degradedCfg->ripToInstr->end();
	     it++)
		rawRips.insert(it.key().rip);
	for (std::set<std::set<unsigned> >::iterator it = threadPower.begin();
	     it != threadPower.end();
	     it++) {
		if (it->size() != 0)
			duplicateCFGAtThreadSet(degradedCfg, rawRips, *it);
	}

	return degradedCfg;
}

static void
partitionCrashCondition(DNF_Conjunction &c, FreeVariableMap &fv,
			std::map<unsigned, ThreadRip> &roots,
			AddressSpace *as)
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
			neededRips.insert(roots[e->Iex.Get.tid]);
		} else if (e->tag == Iex_ClientCall) {
			neededRips.insert(e->Iex.ClientCall.callSite);
		} else if (e->tag == Iex_Load) {
			neededRips.insert(e->Iex.Load.rip);
		} else if (e->tag == Iex_HappensBefore) {
			neededRips.insert(e->Iex.HappensBefore.before);
			neededRips.insert(e->Iex.HappensBefore.after);
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
		printf("Root %d:%lx\n", it->second.thread, it->second.rip);
		cfg->add_root(it->second, 100);
	}
	cfg->doit();
	
	/* Figure out where the various expressions should be
	 * evaluated. */
	expressionDominatorMapT exprDominatorMap(c, cfg, neededRips);

	/* Figure out where we need to stash the various necessary
	 * expressions.  This is a map from RIPs to <thread,expr>
	 * pairs, where we need to stash @expr if we execute
	 * instruction @RIP in thread @thread. */
	expressionStashMapT exprStashPoints(neededExpressions, roots);

	/* And where we need to calculate them. */
	expressionEvalMapT exprEvalPoints(exprDominatorMap);

	/* Find out where the happens-before edges start and end. */
	std::map<unsigned long, std::set<happensBeforeEdge *> > happensBeforePoints;
	for (unsigned x = 0; x < c.size(); x++) {
		IRExpr *e = c[x].second;
		bool invert = c[x].first;
		if (e->tag == Iex_HappensBefore) {
			IRExpr::HappensBefore *hb = &e->Iex.HappensBefore;
			happensBeforeEdge *hbe = new happensBeforeEdge(invert, *hb, exprDominatorMap.idom,
								       cfg, exprStashPoints);
			happensBeforePoints[hbe->before.rip].insert(hbe);
			happensBeforePoints[hbe->after.rip].insert(hbe);
		}
	}

	/* The patch needs to be built in direct RIP space, rather
	 * than in ThreadRip space.  That means we need to degrade the
	 * CFG. */
	CFG<ClientRip> *degradedCfg = convertCFGFromThreadRipToClientRips(cfg, neededThreads, exprDominatorMap);

	/* Figure out what slots to use for the various
	 * expressions. */
	slotMapT slotMap(exprStashPoints, happensBeforePoints);

	/* Now build the patch */
	EnforceCrashPatchFragment *pf = new EnforceCrashPatchFragment(slotMap, exprStashPoints, exprEvalPoints, happensBeforePoints);
	pf->fromCFG(degradedCfg);
	std::set<ClientRip> entryPoints;
	std::map<unsigned long, std::set<unsigned> > threadsRelevantAtEachEntryPoint;
	for (std::map<unsigned, ThreadRip>::iterator it = roots.begin();
	     it != roots.end();
	     it++)
		threadsRelevantAtEachEntryPoint[it->second.rip].insert(it->first);
	for (std::map<unsigned, ThreadRip>::iterator it = roots.begin();
	     it != roots.end();
	     it++) {
		std::set<unsigned> &threads(threadsRelevantAtEachEntryPoint[it->second.rip]);
		entryPoints.insert(ClientRip(it->second.rip, threads));
	}
	printf("Fragment:\n");
	printf("%s", pf->asC("ident", entryPoints));
}

static bool
analyseHbGraph(DNF_Conjunction &c, CrashSummary *summary)
{
	std::set<IRExpr::HappensBefore> hb;
	std::set<IRExpr::HappensBefore> assumption;

	extractImplicitOrder(summary->loadMachine, assumption);
	for (unsigned x = 0; x < summary->storeMachines.size(); x++)
		extractImplicitOrder(summary->storeMachines[x]->machine, assumption);
	for (unsigned x = 0; x < c.size(); x++) {
		if (c[x].second->tag == Iex_HappensBefore) {
			IRExpr::HappensBefore h;
			if (c[x].first) {
				h.before = c[x].second->Iex.HappensBefore.after;
				h.after = c[x].second->Iex.HappensBefore.before;
			} else {
				h = c[x].second->Iex.HappensBefore;
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
	for (std::set<IRExpr::HappensBefore>::iterator it = hb.begin();
	     it != hb.end();
	     it++)
		out.push_back(std::pair<bool, IRExpr *>(
				      false,
				      IRExpr_HappensBefore(it->before, it->after)));

	c = out;

	return true;
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);

	int fd = open(argv[4], O_RDONLY);
	if (fd < 0)
		err(1, "opening %s", argv[4]);
	VexPtr<CrashSummary, &ir_heap> summary(readCrashSummary(fd));
	close(fd);

	printf("Machines to enforce:\n");
	printCrashSummary(summary, stdout);

	IRExpr *requirement = findHappensBeforeRelations(summary, oracle, ALLOW_GC);
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
	fprintf(_logfile, "After free variable removal:\n");
	ppIRExpr(requirement, _logfile);
	fprintf(_logfile, "\n");

	DNF_Disjunction d;
	if (TIMEOUT || !dnf(requirement, d)) {
		fprintf(_logfile, "failed to convert to DNF\n");
		return 1;
	}
	for (unsigned x = 0; x < d.size(); ) {
		if (analyseHbGraph(d[x], summary)) {
			x++;
		} else {
			d.erase(d.begin() + x);
		}
	}

	printDnf(d, _logfile);
       
	for (unsigned x = 0; x < d.size(); x++) {
		printf("Examine clause %d\n", x);
		partitionCrashCondition(d[x], m, roots, ms->addressSpace);
	}

	return 0;
}
