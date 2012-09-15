#include "sli.h"
#include "mapping.hpp"
#include "oracle.hpp"

static void
validate_trace(Oracle *oracle, std::vector<unsigned long> rips)
{
	CfgLabelAllocator allocLabel;

	assert(!rips.empty());

	printf("Check trace {");
	for (auto it2 = rips.begin(); it2 != rips.end(); it2++) {
		if (it2 != rips.begin())
			printf(", ");
		printf("0x%lx", *it2);
	}
	printf("} -> ");

	if (!oracle->type_index->ripPresent(DynAnalysisRip(VexRip::invent_vex_rip(rips.back())))) {
		printf("Invalid; no type information for %lx\n", rips.back());
		return;
	}

	HashedSet<HashedPtr<CFGNode> > roots;
	HashedSet<HashedPtr<const CFGNode> > targetNodes;
	getProbeCFGs(allocLabel, oracle, DynAnalysisRip(VexRip::invent_vex_rip(rips.back())),
		     roots, targetNodes, rips.size(), rips.size());

	std::set<CFGNode *> live;
	for (auto it = roots.begin(); !it.finished(); it.advance())
		live.insert(*it);
	for (auto it = rips.begin(); it != rips.end(); it++) {
		if (live.empty()) {
			printf("Fail\n");
			return;
		}
		std::set<CFGNode *> newLive;
		for (auto it2 = live.begin(); it2 != live.end(); it2++) {
			CFGNode *n = *it2;
			if (n->rip.unwrap_vexrip() == *it) {
				for (auto it3 = n->successors.begin();
				     it3 != n->successors.end();
				     it3++)
					newLive.insert(it3->instr);
			}
		}
	}

	printf("Pass\n");
}

int
main(int argc, char *argv[])
{
	init_sli();
	if (argc != 5)
		errx(1, "bad arguments");

	const char *binary = argv[1];
	const char *types = argv[2];
	const char *callgraph = argv[3];
	const char *trace_file = argv[4];
	Mapping traces;

	if (traces.init(trace_file) < 0)
		err(1, "mapping %s", trace_file);

	VexPtr<Oracle> oracle;
	{
		MachineState *ms = MachineState::readELFExec(binary);
		Thread *thr = ms->findThread(ThreadId(1));
		oracle = new Oracle(ms, thr, types);
	}
	oracle->loadCallGraph(oracle, callgraph, ALLOW_GC);

	unsigned long offset;
	offset = 0;
	while (1) {
		const unsigned long *magic = traces.get<unsigned long>(offset);
		if (!magic)
			break;
		if (*magic != 0xaabbccddeeff8844ul)
			errx(1, "bad magic number in traces file");
		offset += 8;
		std::vector<unsigned long> trace;
		while (1) {
			const unsigned long *slot = traces.get<unsigned long>(offset);
			if (!slot)
				break;
			if (*slot == 0xaabbccddeeff8844ul)
				break;
			trace.push_back(*slot);
			offset += 8;
		}
		validate_trace(oracle, trace);
	}

	return 0;
}
