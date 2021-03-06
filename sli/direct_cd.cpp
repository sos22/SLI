/* Re-implementation of direct which tries to work off of just a core
   dump, rather than needing the full trace. */
#include <err.h>
#include <errno.h>

#include <algorithm>
#include <queue>
#include <map>
#include <set>

#include "sli.h"
#include "range_tree.h"
#include "state_machine.hpp"
#include "oracle.hpp"
#include "simplify_irexpr.hpp"
#include "eval_state_machine.hpp"
#include "inferred_information.hpp"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"
#include "timers.hpp"

static VexRip
getThreadRip(Oracle *oracle, unsigned long rip, unsigned long rsp)
{
	std::vector<unsigned long> callStack;

	callStack.push_back(rip);
	while (1) {
		unsigned offset = stack_offset(oracle, rip);
		if (offset == 0)
			break;
		printf("RIP %lx, rsp %lx, offset 0x%x\n", rip, rsp, offset);
		unsigned long ra = oracle->ms->addressSpace->fetch<unsigned long>(rsp + offset);
		callStack.push_back(ra);
		rsp += offset + 8;
		rip = ra;
	}
	std::reverse(callStack.begin(), callStack.end());
	return VexRip(callStack);
}

class DumpFix : public FixConsumer {
public:
	int cntr;
	const char *fname;
	DynAnalysisRip dr;
	DumpFix(const char *_fname, const DynAnalysisRip &_dr)
		: cntr(0), fname(_fname), dr(_dr)
	{
	}
	void operator()(VexPtr<CrashSummary, &ir_heap> &probeMachine,
			int, int,
			GarbageCollectionToken token);
};

void
DumpFix::operator()(VexPtr<CrashSummary, &ir_heap> &summary,
		    int, int,
		    GarbageCollectionToken )
{
	printCrashSummary(summary, _logfile);

	int fd;
	char *buf = NULL;
	do {
		free(buf);
		buf = my_asprintf("%s_%d", fname, cntr);
		cntr++;
		fd = open(buf, O_WRONLY|O_EXCL|O_CREAT, 0600);
	} while (fd == -1 && errno == EEXIST);
	if (fd == -1)
		err(1, "opening %s", buf);
	printf("Write summary to %s\n", buf);
	free(buf);
	FILE *f = fdopen(fd, "w");
	if (!f)
		err(1, "fdopen()");

	fprintf(f, "summary from dyn rip %s\n", dr.name());
	printCrashSummary(summary, f);
	fclose(f);
}

int
main(int argc, char *argv[])
{
	if (argc <= 4)
		errx(1, "need more arguments");

	init_sli();

	VexPtr<MachineState> ms(MachineState::readCoredump(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(CRASHED_THREAD)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));
	oracle->loadCallGraph(oracle, argv[3], argv[4], ALLOW_GC);

	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack()
		.setAddressSpace(ms->addressSpace);
	CfgLabelAllocator allocLabel;

	VexRip vr(getThreadRip(oracle, thr->regs.rip(), thr->regs.rsp()));

	printf("Crash rip %s\n", vr.name());
		     
	VexPtr<MaiMap, &ir_heap> mai(MaiMap::empty());
	VexPtr<StateMachine, &ir_heap> probeMachine;
	SMScopes scopes;
	probeMachine = buildProbeMachine(&scopes,
					 allocLabel,
					 oracle,
					 vr,
					 thr->tid,
					 opt,
					 mai,
					 ALLOW_GC);

	DumpFix df(argv[5], DynAnalysisRip(vr));
	TimeoutTimer ignTimer;
	diagnoseCrash(&scopes, allocLabel, DynAnalysisRip(vr),
		      probeMachine, oracle, df,
		      opt, mai, ignTimer, -1, -1, ALLOW_GC);

	return 0;
}
