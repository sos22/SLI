#include <map>
#include <set>

#include "sli.h"
#include "genfix.hpp"
#include "oracle.hpp"
#include "inferred_information.hpp"

LateRelocation
late_relocation(unsigned offset, unsigned size,
		const char *target, unsigned nrImmediateBytes,
		bool relative)
{
	return vex_asprintf("{%d, %d, %d, %d, %s}",
			    offset, size,
			    relative ? -nrImmediateBytes - size : 0,
			    relative, target);
}

void
__genfix_add_array_summary(std::vector<const char *> &out,
			   const char *t_ptr,
			   const char *nr_entries,
			   const char *table)
{
	out.push_back(
		vex_asprintf(
			"\t.%s = %s, .%s = sizeof(%s)/sizeof(%s[0]),\n",
			t_ptr,
			table,
			nr_entries,
			table,
			table));
}

class DcdCFG : public CFG<ThreadRip> {
	std::set<unsigned long> &neededInstructions;
public:
	bool instructionUseful(Instruction<ThreadRip> *i) { return neededInstructions.count(i->rip.rip) != 0; }
	DcdCFG(AddressSpace *as, std::set<unsigned long> &ni)
		: CFG<ThreadRip>(as), neededInstructions(ni)
	{}
};
char *
buildPatchForCrashSummary(Oracle *oracle, CrashSummary *summary, const char *ident)
{
	AddressSpace *as = oracle->ms->addressSpace;

	/* What instructions do we need to cover? */
	std::set<unsigned long> neededInstructions;
	summary->loadMachine->root->enumerateMentionedMemoryAccesses(neededInstructions);
	/* 5 bytes is the size of a 32-bit relative jump. */
	ThreadRip root = ThreadRip::mk(summary->loadMachine->tid, oracle->dominator(neededInstructions, as, 5));
	if (!root.rip) {
		fprintf(_logfile, "Patch generation fails because we can't find an appropriate dominating instruction for load machine.\n");
		return NULL;
	}
	for (std::vector<CrashSummary::StoreMachineData *>::iterator it = summary->storeMachines.begin();
	     it != summary->storeMachines.end();
	     it++)
		(*it)->machine->root->enumerateMentionedMemoryAccesses(neededInstructions);

	DcdCFG *cfg = new DcdCFG(as, neededInstructions);

	std::set<ThreadRip> roots;
	/* What are the entry points of the patch? */
	cfg->add_root(root, 100);
	roots.insert(root);
	for (std::vector<CrashSummary::StoreMachineData *>::iterator it = summary->storeMachines.begin();
	     it != summary->storeMachines.end();
	     it++) {
		std::set<unsigned long> instrs;
		(*it)->machine->root->enumerateMentionedMemoryAccesses(instrs);
		ThreadRip r = ThreadRip::mk((*it)->machine->tid, oracle->dominator(instrs, as, 5));
		if (!r.rip) {
			fprintf(_logfile, "Patch generation fails because we can't find an appropriate dominator instruction for one of the store machines.\n");
			return NULL;
		}
		cfg->add_root(r, 100);
		roots.insert(r);
	}
	try {
		cfg->doit();
	} catch (NotImplementedException &e) {
		/* This means that there's some instruction we can't
		   decode.  Dump a diagnostic and just continue on. */
		fprintf(_logfile,
			"Cannot build patch for crash summary.  Instruction decoder said %s\n",
			e.what());
		return NULL;
	}
	PatchFragment<ThreadRip> *pf = new PatchFragment<ThreadRip>();
	pf->fromCFG(cfg);

	return pf->asC(ident, roots);
}

unsigned long __trivial_hash_function(const ThreadRip &k)
{
	return k.rip;
}

unsigned long __trivial_hash_function(const unsigned long &k)
{
	return k;
}
