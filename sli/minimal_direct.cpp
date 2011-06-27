#include <sys/time.h>
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
	if (fragment)
		fputs(fragment, output);
	else
		printf("No patch generated!\n");
}

void
DumpFix::finish(void)
{
	fprintf(output, "static const struct patch *const patches[] = {\n");
	for (int x = 0; x < cntr; x++)
		fprintf(output, "\t&patch%d,\n", x);
	fprintf(output, "};\n\n#include \"patch_skeleton_jump.c\"\n");
}

static void
timer_handler(int ignore)
{
	timed_out = true;
}

static void
shuffle(std::vector<unsigned long> &vect)
{
	for (unsigned x = 0; x < vect.size(); x++) {
		unsigned idx = (random() % (vect.size() - x)) + x;
		unsigned long t = vect[x];
		vect[x] = vect[idx];
		vect[idx] = t;
	}
}

int
main(int argc, char *argv[])
{
	signal(SIGPROF, timer_handler);

	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle;

	oracle = new Oracle(ms, thr, argv[2]);
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);

	FILE *output = fopen("generated_patch.c", "w");
	FILE *timings = fopen("timings.txt", "w");
	DumpFix df(oracle, output);
	std::vector<unsigned long> possiblyRacingLoads;

	oracle->getAllPossiblyRacingLoads(possiblyRacingLoads);
	shuffle(possiblyRacingLoads);
	for (std::vector<unsigned long>::iterator it = possiblyRacingLoads.begin() + 1890 + 620 + 630 + 140 + 480;
	     it != possiblyRacingLoads.end();
	     it++) {
		unsigned long my_rip = *it;

		LibVEX_maybe_gc(ALLOW_GC);
		
		printf("Considering %lx...\n", my_rip);
		VexPtr<CrashReason, &ir_heap> proximal(getProximalCause(ms, my_rip, thr));
		if (!proximal) {
			printf("No proximal cause -> can't do anything\n");
			continue;
		}
		proximal = backtrackToStartOfInstruction(1, proximal, ms->addressSpace);
		if (!proximal) {
			printf("Can't backtrack proximal cause\n");
			continue;
		}

		VexPtr<InferredInformation> ii(new InferredInformation(oracle));
		ii->addCrashReason(proximal);

		std::vector<unsigned long> previousInstructions;
		oracle->findPreviousInstructions(previousInstructions, my_rip);

		struct itimerval itv;
		struct timeval start;

		memset(&itv, 0, sizeof(itv));
		itv.it_value.tv_sec = 120;
		setitimer(ITIMER_PROF, &itv, NULL);

		gettimeofday(&start, NULL);

		considerInstructionSequence(previousInstructions, ii, oracle, my_rip, ms, df, false, ALLOW_GC);

		struct timeval end;
		gettimeofday(&end, NULL);

		memset(&itv, 0, sizeof(itv));
		setitimer(ITIMER_PROF, &itv, NULL);

		double time_taken = end.tv_sec - start.tv_sec;
		time_taken += (end.tv_usec - start.tv_usec) * 1e-6;
		if (timed_out) {
			fprintf(timings, "%lx timed out after %f\n", my_rip, time_taken);
			printf("%lx timed out after %f\n", my_rip, time_taken);
		} else {
			fprintf(timings, "%lx took %f\n", my_rip, time_taken);
			printf("%lx took %f\n", my_rip, time_taken);
		}
		timed_out = false;

		fflush(NULL);
	}

	df.finish();
	fclose(output);

	return 0;
}
