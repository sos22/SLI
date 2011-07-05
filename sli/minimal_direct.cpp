#include <sys/time.h>
#include <err.h>
#include <time.h>

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
	_timed_out = true;
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

static void
consider_rip(unsigned long my_rip,
	     VexPtr<MachineState> &ms,
	     VexPtr<Thread> &thr,
	     VexPtr<Oracle> &oracle,
	     DumpFix &df,
	     FILE *timings,
	     GarbageCollectionToken token)
{
	LibVEX_maybe_gc(token);

	fprintf(_logfile, "Considering %lx...\n", my_rip);
	VexPtr<CrashReason, &ir_heap> proximal(getProximalCause(ms, my_rip, thr));
	if (!proximal) {
		fprintf(_logfile, "No proximal cause -> can't do anything\n");
		return;
	}
	proximal = backtrackToStartOfInstruction(1, proximal, ms->addressSpace);
	if (!proximal) {
		fprintf(_logfile, "Can't backtrack proximal cause\n");
		return;
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

	considerInstructionSequence(previousInstructions, ii, oracle, my_rip, ms, df, false, token);

	struct timeval end;
	gettimeofday(&end, NULL);

	memset(&itv, 0, sizeof(itv));
	setitimer(ITIMER_PROF, &itv, NULL);

	double time_taken = end.tv_sec - start.tv_sec;
	time_taken += (end.tv_usec - start.tv_usec) * 1e-6;
	if (_timed_out) {
		if (timings)
			fprintf(timings, "%lx timed out after %f\n", my_rip, time_taken);
		printf("%lx timed out after %f\n", my_rip, time_taken);
	} else {
		if (timings)
			fprintf(timings, "%lx took %f\n", my_rip, time_taken);
		printf("%lx took %f\n", my_rip, time_taken);
	}
	_timed_out = false;

	fflush(NULL);
		
}

static double
now(void)
{
	struct timeval tv;
	gettimeofday(&tv, NULL);
	return tv.tv_sec + tv.tv_usec * 1e-6;
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

	signal(SIGPROF, timer_handler);

	FILE *output = fopen("generated_patch.c", "w");
	DumpFix df(oracle, output);

	if (argc == 5) {
		consider_rip(strtoul(argv[4], NULL, 16), ms, thr, oracle, df, NULL, ALLOW_GC);
	} else {
		FILE *timings = fopen("timings.txt", "w");
		std::vector<unsigned long> targets;
		oracle->getAllMemoryAccessingInstructions(targets);
		shuffle(targets);
		printf("%zd instructions to protect\n", targets.size());
		double start = now();
		for (std::vector<unsigned long>::iterator it = targets.begin();
		     it != targets.end();
		     it++) {
			_logfile = fopenf("w", "logs/%lx", *it);
			if (!_logfile) err(1, "opening logs/%lx", *it);
			consider_rip(*it, ms, thr, oracle, df, timings, ALLOW_GC);
			fclose(_logfile);
			_logfile = stdout;

			double completion = (it - targets.begin()) / double(targets.size());
			double elapsed = now() - start;
			double total_estimated = elapsed / completion;
			time_t end = total_estimated + start;
			printf("Done %zd/%zd(%f%%) in %f seconds (%f each); %f left; finish at %s",
			       it - targets.begin(),
			       targets.size(),
			       completion * 100,
			       elapsed,
			       elapsed / (it - targets.begin()),
			       total_estimated - elapsed,
			       ctime(&end));
		}
	}

	df.finish();
	fclose(output);

	return 0;
}
