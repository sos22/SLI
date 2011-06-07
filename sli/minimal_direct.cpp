#include <vector>
#include <set>

#include "sli.h"
#include "oracle.hpp"
#include "crash_reason.hpp"
#include "inferred_information.hpp"

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle;

	std::set<unsigned long> examined_loads;

	while (1) {
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

		printf("%d predecessors.\n", previousInstructions.size());
		considerInstructionSequence(previousInstructions, ii, oracle, my_rip, ms);
	}
}
