#include <vector>
#include <set>

#include "sli.h"
#include "oracle.hpp"
#include "crash_reason.hpp"
#include "inferred_information.hpp"

class DumpFix : public FixConsumer {
public:
	unsigned long rip;
	VexPtr<MachineState> &ms;
	DumpFix(unsigned long r, VexPtr<MachineState> &_ms)
		: rip(r), ms(_ms)
	{}
	void operator()(VexPtr<CrashSummary, &ir_heap> &probeMachine,
			GarbageCollectionToken token);
};

void
DumpFix::operator()(VexPtr<CrashSummary, &ir_heap> &summary,
		    GarbageCollectionToken token)
{
	dbg_break("Hello\n");
	printCrashSummary(summary, stdout);
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle;

	std::set<unsigned long> examined_loads;

	while (1) {
		oracle = NULL;

		LibVEX_maybe_gc(ALLOW_GC);
		
		oracle = new Oracle(ms, thr, argv[2], argv[3]);
		unsigned long my_rip = oracle->selectRandomLoad();
		while (examined_loads.count(my_rip))
			my_rip = oracle->selectRandomLoad();
		examined_loads.insert(my_rip);

		printf("Considering %lx...\n", my_rip);
		VexPtr<CrashReason, &ir_heap> proximal(getProximalCause(ms, my_rip, thr));
		if (!proximal) {
			printf("No proximal cause -> can't do anything\n");
			continue;
		}
		proximal = backtrackToStartOfInstruction(1, proximal, ms->addressSpace);

		VexPtr<InferredInformation> ii(new InferredInformation(oracle));
		ii->addCrashReason(proximal);

		std::vector<unsigned long> previousInstructions;
		oracle->findPreviousInstructions(previousInstructions,
						 /*thr->regs.rip()*/ 0x5fd088,  /* we know where main() is */
						 my_rip);

		DumpFix df(my_rip, ms);
		considerInstructionSequence(previousInstructions, ii, oracle, my_rip, ms, df, ALLOW_GC);
	}
}
