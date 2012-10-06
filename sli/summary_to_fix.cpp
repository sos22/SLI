/* Somewhat annoyingly, we actually need _GNU_SOURCE for correctness,
   because of the call to basename().  If it's not there then
   compilation will succeed but the resulting program will be
   buggy. */
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
/* Make sure this gets #include'd before libgen.h, including
   #include's from other headers, or you get the buggy version of
   basename() */
#include <string.h>

#include "sli.h"

#include "genfix.hpp"
#include "inferred_information.hpp"
#include "oracle.hpp"

#include "cfgnode_tmpl.cpp"

#ifndef NDEBUG
static bool debug_find_dominator = false;
#else
#define debug_find_dominator false
#endif

template <typename t> static bool
operator &=(std::set<t> &a, const std::set<t> &b)
{
	bool res = false;
	for (auto it = a.begin(); it != a.end(); ) {
		if (!b.count(*it)) {
			a.erase(it++);
			res = true;
		} else {
			it++;
		}
	}
	return res;
}

static void
enumerateCFG(_CFGNode<StaticRip> *root, std::set<_CFGNode<StaticRip> *> &instrs)
{
	std::vector<_CFGNode<StaticRip> *> q;
	q.push_back(root);
	while (!q.empty()) {
		_CFGNode<StaticRip> *e = q.back();
		q.pop_back();
		if (instrs.insert(e).second) {
			for (auto it = e->successors.begin();
			     it != e->successors.end();
			     it++)
				if (it->instr)
					q.push_back(it->instr);
		}
	}
}

static VexRip
findDominator(Oracle *oracle, const std::set<VexRip> &neededInstrs, unsigned min_size)
{
	assert(!neededInstrs.empty());

	if (debug_find_dominator) {
		printf("findDominator({");
		for (auto it = neededInstrs.begin(); it != neededInstrs.end(); it++) {
			if (it != neededInstrs.begin())
				printf(", ");
			printf("%s", it->name());
		}
		printf("}, min_size = %d)\n", min_size);
	}

	/* First strip the needed instructions back so that they
	 * contain just the entry in the last common frame.  That
	 * means removing any common prefix of the stack, then mapping
	 * nested function calls to their call instructions. */
	std::vector<unsigned long> common_prefix;
	auto it = neededInstrs.begin();
	common_prefix = it->stack;
	it++;

	/* Never want to remove the bit of the stack which identifies
	   the actual instruction, only its context. */
	common_prefix.pop_back();

	while (it != neededInstrs.end()) {
		unsigned x;
		for (x = 0;
		     x < common_prefix.size() &&
			     x + 1 < it->stack.size() &&
			     it->stack[x] == common_prefix[x];
		     x++)
			;
		assert(x <= common_prefix.size());
		common_prefix.resize(x);
		it++;
	}
	if (debug_find_dominator) {
		printf("Common prefix: ");
		for (auto it = common_prefix.begin();
		     it != common_prefix.end();
		     it++) {
			if (it != common_prefix.begin())
				printf(", ");
			printf("0x%lx", *it);
		}
		printf("\n");
	}
	std::set<StaticRip> strippedInstrs;
	for (auto it = neededInstrs.begin(); it != neededInstrs.end(); it++) {
		assert(it->stack.size() > common_prefix.size());
		for (unsigned x = 0; x < common_prefix.size(); x++)
			assert(it->stack[x] == common_prefix[x]);

		/* This is the instruction in the common frame. */
		unsigned long r1 = it->stack[common_prefix.size()];

		if (it->stack.size() > common_prefix.size() + 1) {
			/* This instruction is the return point of a
			   call, and we need to get the call
			   instruction itself. */
			unsigned long r2 = oracle->findCallPredecessor(r1);
			if (r2 == 0) {
				printf("Huh?  %lx should be a call return, because %s is a valid rip, but oracle doesn't know about its call predecessor?\n",
				       r1, it->name());
				abort();
			}
			r1 = r2;
		} else {
			/* This is the instruction itself. */
		}
		strippedInstrs.insert(StaticRip(r1));
	}

	if (debug_find_dominator) {
		printf("Stripped instrs: {");
		for (auto it = strippedInstrs.begin();
		     it != strippedInstrs.end();
		     it++) {
			if (it != strippedInstrs.begin())
				printf(", ");
			printf("%s", it->name());
		}
		printf("}\n");
	}
			
	/* Now we need those to all be in the same function. */
	auto it2 = strippedInstrs.begin();
	StaticRip headRip(oracle->functionHeadForInstruction(*it2));
	for (it2++; it2 != strippedInstrs.end(); it2++) {
		StaticRip thisHead(oracle->functionHeadForInstruction(*it2));
		if (thisHead != headRip) {
			printf("Failed to find dominator: %s and %s are in different functions (%s vs %s)\n",
			       strippedInstrs.begin()->name(),
			       it->name(),
			       headRip.name(),
			       thisHead.name());
			return VexRip();
		}
	}

	if (debug_find_dominator)
		printf("headRip %s\n", headRip.name());

	/* So headRip is now definitely a valid dominator.  Build a
	 * CFG forwards from there and see if we can find anything
	 * better. */
	CfgLabelAllocator allocLabel;
	CfgSuccMap<StaticRip, StaticRip> succMap;
	std::map<_CFGNode<StaticRip> *, unsigned> sizeMap;
	std::map<StaticRip, _CFGNode<StaticRip> *> cfgNodes;
	std::vector<StaticRip> pending;
	pending.push_back(headRip);
	while (!pending.empty()) {
		StaticRip sr(pending.back());
		pending.pop_back();
		if (cfgNodes.count(sr))
			continue;
		_CFGNode<StaticRip> *n = CfgNodeForRip<StaticRip>(
			allocLabel(),
			oracle,
			VexRip::invent_vex_rip(sr.rip),
			sr,
			succMap,
			&sizeMap);
		if (!n) {
			printf("Warning: Cannot decode %s\n", sr.name());
			continue;
		}
		cfgNodes[sr] = n;
		assert(succMap.count(n));
		std::vector<CfgSuccessorT<StaticRip> > &succ(succMap[n]);
		for (auto it = succ.begin(); it != succ.end(); it++)
			pending.push_back(it->instr);
	}
	resolveReferences(succMap, cfgNodes);

	assert(cfgNodes.count(headRip));
	_CFGNode<StaticRip> *cfgRoot = cfgNodes[headRip];
	if (debug_find_dominator) {
		printf("CFG:\n");
		printCFG(cfgRoot, stdout);
	}

	std::set<_CFGNode<StaticRip> *> allInstrs;
	enumerateCFG(cfgRoot, allInstrs);

	/* So now we have the CFG.  Next step is to find the
	 * instructions in the CFG which dominate the instructions in
	 * strippedInstrs i.e. the set of instructions D such that
	 * every path from the root to any member of strippedInstrs
	 * passes through each member of D at least once.  Doing this
	 * properly requires a full dominator table, so build that
	 * instead.  When we're done, dominatorMap[x] is the set of
	 * instructions S such that every path to x passes through
	 * every member of S i.e. S is the set of dominators of x. */
	/* Need a predecessor map for this */
	std::map<_CFGNode<StaticRip> *, std::set<_CFGNode<StaticRip> *> > predecessors;
	for (auto it = allInstrs.begin(); it != allInstrs.end(); it++) {
		auto i = *it;
		for (auto it2 = i->successors.begin(); it2 != i->successors.end(); it2++) {
			if (it2->instr)
				predecessors[it2->instr].insert(i);
		}
	}
	predecessors[cfgRoot].clear();

	/* Start by assumming that everything dominates everything and
	 * then fix things up.  A dominates B if either A == B or A
	 * dominates every predecessor of B. */
	std::map<_CFGNode<StaticRip> *, std::set<_CFGNode<StaticRip> *> > dominatorMap;
	for (auto it = allInstrs.begin(); it != allInstrs.end(); it++)
		dominatorMap[*it] = allInstrs;
	dominatorMap[cfgRoot].clear();
	dominatorMap[cfgRoot].insert(cfgRoot);
	std::set<_CFGNode<StaticRip> *> need_recheck;
	need_recheck.insert(allInstrs.begin(), allInstrs.end());
	while (!need_recheck.empty()) {
		_CFGNode<StaticRip> *n = *need_recheck.begin();
		need_recheck.erase(n);
		assert(dominatorMap.count(n));
		assert(predecessors.count(n));
		const std::set<_CFGNode<StaticRip> *> &pred(predecessors[n]);
		auto it = pred.begin();
		std::set<_CFGNode<StaticRip> *> desiredDom;
		if (it != pred.end()) {
			assert(dominatorMap.count(*it));
			desiredDom = dominatorMap[*it];
			if (it != pred.end()) {
				for (it++; it != pred.end(); it++) {
					assert(dominatorMap.count(*it));
					desiredDom &= dominatorMap[*it];
				}
			}
		}
		desiredDom.insert(n);
		if (debug_find_dominator) {
			printf("%s -> {", n->label.name());
			for (auto it = dominatorMap[n].begin();
			     it != dominatorMap[n].end();
			     it++) {
				if (it != dominatorMap[n].begin())
					printf(", ");
					printf("%s", (*it)->label.name());
			}
			printf("}\n");
		}
		if (dominatorMap[n] &= desiredDom) {
			if (debug_find_dominator) {
				printf("Updated %s to {", n->label.name());
				for (auto it = dominatorMap[n].begin();
				     it != dominatorMap[n].end();
				     it++) {
					if (it != dominatorMap[n].begin())
						printf(", ");
					printf("%s", (*it)->label.name());
				}
				printf("}\n");
			}
			for (auto it = n->successors.begin();
			     it != n->successors.end();
			     it++)
				if (it->instr)
					need_recheck.insert(it->instr);
		}
	}

	if (debug_find_dominator) {
		printf("Dominator map:\n");
		for (auto it = dominatorMap.begin(); it != dominatorMap.end(); it++) {
			printf("%s -> {", it->first->label.name());
			for (auto it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++) {
				if (it2 != it->second.begin())
					printf(", ");
				printf("%s", (*it2)->label.name());
			}
			printf("}\n");
		}
	}

	/* Find all of the candidates.  These are instructions which
	   are of the minimum length and dominate all of the needed
	   instructions. */
	std::set<_CFGNode<StaticRip> *> candidates;
	for (auto it = strippedInstrs.begin(); it != strippedInstrs.end(); it++) {
		assert(cfgNodes.count(*it));
		_CFGNode<StaticRip> *n = cfgNodes[*it];
		assert(n);
		assert(dominatorMap.count(n));
		const std::set<_CFGNode<StaticRip> *> &dom(dominatorMap[n]);
		if (it == strippedInstrs.begin()) {
			for (auto it = dom.begin(); it != dom.end(); it++) {
				assert(sizeMap.count(*it));
				if (sizeMap[*it] >= min_size)
					candidates.insert(*it);
			}
		} else {
			candidates &= dom;
		}
	}

	if (debug_find_dominator) {
		printf("Candidates: {");
		for (auto it = candidates.begin();
		     it != candidates.end();
		     it++) {
			if (it != candidates.begin())
				printf(", ");
			printf("%s", (*it)->label.name());
		}
		printf("}\n");
	}

	/* Anything in the candidates set would now be a correct
	 * choice.  For performance reasons, we want to pick the
	 * ``latest'' possible candidate, so as to keep the number of
	 * instructions in the patch down.  That means we don't want
	 * to pick anything which is dominated by another
	 * candidate. */
	bool progress = true;
	while (progress) {
		progress = false;
		for (auto it = candidates.begin(); !progress && it != candidates.end(); it++) {
			assert(dominatorMap.count(*it));
			const std::set<_CFGNode<StaticRip> *> &dominates(dominatorMap[*it]);
			for (auto it2 = dominates.begin(); it2 != dominates.end(); it2++) {
				if (*it2 != *it && candidates.count(*it2)) {
					candidates.erase(*it2);
					progress = true;
				}
			}
		}
	}

	if (debug_find_dominator) {
		printf("Optimal candidates: {");
		for (auto it = candidates.begin();
		     it != candidates.end();
		     it++) {
			if (it != candidates.begin())
				printf(", ");
			printf("%s", (*it)->label.name());
		}
		printf("}\n");
	}

	/* There should now be precisely one valid answer. */
	assert(candidates.size() == 1);

	/* Take it. */
	std::vector<unsigned long> stack(common_prefix);
	stack.push_back((*candidates.begin())->rip.rip);
	return VexRip(stack);
}

class AddExitCallPatch : public PatchFragment<ThreadRip> {
protected:
	void generateEpilogue(const CfgLabel &l, ThreadRip exitRip);
	/* XXX should really override emitInstruction here to catch
	   indirect jmp and ret instructions; oh well. */
public:
	AddExitCallPatch(const std::set<ThreadRip> &roots)
		: PatchFragment<ThreadRip>(roots)
	{}
};

void
AddExitCallPatch::generateEpilogue(const CfgLabel &l, ThreadRip exitRip)
{
	Instruction<ThreadRip> *i = Instruction<ThreadRip>::pseudo(l, exitRip);

	cfg->registerInstruction(i);
	registerInstruction(i, content.size());

	emitCallSequence("(unsigned long)release_lock");
	emitJmpToRipHost(exitRip.rip.unwrap_vexrip());
}

class DcdCFG : public CFG<ThreadRip> {
	std::set<VexRip> &neededInstructions;
public:
	bool instructionUseful(Instruction<ThreadRip> *i) { return neededInstructions.count(i->rip.rip) != 0; }
	DcdCFG(AddressSpace *as, std::set<VexRip> &ni)
		: CFG<ThreadRip>(as), neededInstructions(ni)
	{}
};
char *
buildPatchForCrashSummary(Oracle *oracle, CrashSummary *summary, const char *ident)
{
	AddressSpace *as = oracle->ms->addressSpace;

	/* What instructions do we need to cover? */
	std::set<MemoryAccessIdentifier> neededMais;
	summary->loadMachine->root->enumerateMentionedMemoryAccesses(neededMais);
	assert(summary->loadMachine->cfg_roots.size() >= 1);
	unsigned tid = summary->loadMachine->cfg_roots[0].first;
	for (unsigned x = 1; x < summary->loadMachine->cfg_roots.size(); x++)
		assert(tid == summary->loadMachine->cfg_roots[x].first);
	std::set<VexRip> neededInstructions;
	for (auto it = neededMais.begin(); it != neededMais.end(); it++) {
		for (auto it2 = summary->mai->begin(*it); !it2.finished(); it2.advance())
			neededInstructions.insert(it2.node()->rip);
	}
	/* 5 bytes is the size of a 32-bit relative jump. */
	ThreadVexRip root(tid, findDominator(oracle, neededInstructions, 5));
	if (!root.rip.isValid()) {
		fprintf(_logfile, "Patch generation fails because we can't find an appropriate dominating instruction for load machine.\n");
		return NULL;
	}

	summary->storeMachine->root->enumerateMentionedMemoryAccesses(neededMais);
	for (auto it = neededMais.begin(); it != neededMais.end(); it++) {
		for (auto it2 = summary->mai->begin(*it); !it2.finished(); it2.advance())
			neededInstructions.insert(it2.node()->rip);
	}

	DcdCFG *cfg = new DcdCFG(as, neededInstructions);

	std::set<ThreadRip> roots;
	/* What are the entry points of the patch? */
	cfg->add_root(root, 100);
	roots.insert(root);

	std::set<MemoryAccessIdentifier> mais;
	summary->storeMachine->root->enumerateMentionedMemoryAccesses(mais);
	std::set<VexRip> instrs;
	for (auto it = mais.begin(); it != mais.end(); it++) {
		for (auto it2 = summary->mai->begin(*it); !it2.finished(); it2.advance())
			instrs.insert(it2.node()->rip);
	}
	assert( summary->storeMachine->cfg_roots.size() >= 1);
	unsigned store_tid = summary->storeMachine->cfg_roots[0].first;
	for (unsigned x = 1; x < summary->storeMachine->cfg_roots.size(); x++)
		assert(store_tid == summary->storeMachine->cfg_roots[x].first);
	ThreadVexRip r(store_tid, findDominator(oracle, instrs, 5));
	if (!r.rip.isValid()) {
	  fprintf(_logfile, "Patch generation fails because we can't find an appropriate dominator instruction for one of the store machines.\n");
	  return NULL;
	}
	cfg->add_root(r, 100);
	roots.insert(r);

	CfgLabelAllocator allocLabel;
	try {
		cfg->doit(allocLabel);
	} catch (NotImplementedException &e) {
		/* This means that there's some instruction we can't
		   decode.  Dump a diagnostic and just continue on. */
		fprintf(_logfile,
			"Cannot build patch for crash summary.  Instruction decoder said %s\n",
			e.what());
		return NULL;
	}
	PatchFragment<ThreadRip> *pf = new AddExitCallPatch(roots);
	pf->fromCFG(allocLabel, cfg);

	return pf->asC(ident);
}

int
main(int argc, char *argv[])
{
	if (argc != 6)
		errx(1, "need four arguments: binary, types table, callgraph, summary, and output filename");

	const char *binary = argv[1];
	const char *types_table = argv[2];
	const char *callgraph = argv[3];
	const char *summary_fname = argv[4];
	const char *output_fname = argv[5];

	init_sli();

	VexPtr<Oracle> oracle;
	{
		MachineState *ms = MachineState::readELFExec(binary);
		Thread *thr = ms->findThread(ThreadId(1));
		oracle = new Oracle(ms, thr, types_table);
	}
	oracle->loadCallGraph(oracle, callgraph, ALLOW_GC);

	VexPtr<CrashSummary, &ir_heap> summary(readBugReport(summary_fname, NULL));
	char *patch = buildPatchForCrashSummary(oracle, summary, "patch");
	printf("Patch is:\n%s\n", patch);

	FILE *output = fopen(output_fname, "w");
	fprintf(output, "/* SLI fix generated for %s */\n", binary);
	fprintf(output,
		"/* Compile as gcc -Wall -g -shared -fPIC -Isli <this_file> -o %s.so */\n",
		binary);
	fprintf(output, "/* Crash summary:\n");
	printCrashSummary(summary, output);
	fprintf(output, "*/\n");
	fprintf(output, "#define BINARY_PATCH_FOR \"%s\"\n",
		basename(binary));
	fprintf(output, "#include \"patch_head.h\"\n\n");
	fprintf(output, "%s\n\n", patch);
	fprintf(output, "#include \"patch_skeleton_jump.c\"\n");
	if (fclose(output) == EOF)
		err(1, "writing output");
	return 0;
}
