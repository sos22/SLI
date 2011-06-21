#include <vector>
#include <set>

#include "sli.h"
#include "oracle.hpp"
#include "crash_reason.hpp"
#include "inferred_information.hpp"

class DumpFix : public FixConsumer {
public:
	VexPtr<Oracle> &oracle;
	int cntr;
	FILE *output;
	DumpFix(VexPtr<Oracle> &_oracle, FILE *_output)
		: oracle(_oracle), cntr(0), output(_output)
	{
		fputs("#include \"patch_head.h\"\n", output);
	}
	void finish(void);
	void operator()(VexPtr<CrashSummary, &ir_heap> &probeMachine,
			GarbageCollectionToken token);
};

void
DumpFix::operator()(VexPtr<CrashSummary, &ir_heap> &summary,
		    GarbageCollectionToken token)
{
	printCrashSummary(summary, stdout);
	char *fragment = buildPatchForCrashSummary(oracle, summary,
						   vex_asprintf("patch%d", cntr++));
	fputs(fragment, output);
}

void
DumpFix::finish(void)
{
	fprintf(output, "static const struct patch *const patches[] = {\n");
	for (int x = 0; x < cntr; x++)
		fprintf(output, "\t&patch%d,\n", x);
	fprintf(output, "};\n\n#include \"patch_skeleton_jump.c\"\n");
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle;

	oracle = new Oracle(ms, thr, argv[2]);
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);

	std::set<unsigned long> examined_loads;

	FILE *output = fopen("generated_patch.c", "w");
	DumpFix df(oracle, output);
	for (int cntr = 0; cntr < 100; cntr++) {
		LibVEX_maybe_gc(ALLOW_GC);
		
		unsigned long my_rip = oracle->selectRandomLoad();
		while (examined_loads.count(my_rip))
			my_rip = oracle->selectRandomLoad();
		examined_loads.insert(my_rip);

		my_rip = 0x9ad264;

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
		oracle->findPreviousInstructions(previousInstructions, my_rip);

		considerInstructionSequence(previousInstructions, ii, oracle, my_rip, ms, df, ALLOW_GC);
	}

	df.finish();
	fclose(output);

	return 0;
}
