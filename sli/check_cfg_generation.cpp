#include "sli.h"
#include "mapping.hpp"
#include "oracle.hpp"

static FILE *
success_log;
static FILE *
fail_log;
static FILE *
invalid_log;

static long
nr_success;
static long
nr_fail;
static long
nr_invalid;

static void
dump_trace(FILE *f, const std::vector<unsigned long> &trace)
{
	fprintf(f, "{");
	for (auto it2 = trace.begin(); it2 != trace.end(); it2++) {
		if (it2 != trace.begin())
			fprintf(f, ", ");
		fprintf(f, "0x%lx", *it2);
	}
	fprintf(f, "}\n");
}

static void
validate_trace(Oracle *oracle, const std::vector<unsigned long> &rips)
{
	CfgLabelAllocator allocLabel;

	assert(!rips.empty());

	if (!oracle->type_index->ripPresent(DynAnalysisRip(VexRip::invent_vex_rip(rips.back())))) {
		dump_trace(invalid_log, rips);
		nr_invalid++;
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
			dump_trace(fail_log, rips);
			nr_fail++;
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

	dump_trace(success_log, rips);
	nr_success++;
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

	success_log = fopen("success.txt", "w");
	fail_log = fopen("fail.txt", "w");
	invalid_log = fopen("invalid.txt", "w");
	if (!success_log || !fail_log || !invalid_log)
		err(1, "opening one of the log files");

	unsigned long offset;
	long cntr = 0;
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
		cntr++;
		assert(cntr == nr_success + nr_fail + nr_invalid);
		printf("Done %ld (%f%%).  %f%% success, %f%% invalid, %f%% failed\n",
		       cntr,
		       (offset * 100.0) / traces.size,
		       (double)nr_success / cntr * 100,
		       (double)nr_invalid / cntr * 100,
		       (double)nr_fail / cntr * 100);
	}

	return 0;
}
