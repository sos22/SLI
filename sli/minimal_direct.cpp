#include <sys/time.h>
#include <err.h>
#include <errno.h>
#include <math.h>
#include <time.h>

#include <vector>
#include <set>

#include "sli.h"
#include "oracle.hpp"
#include "inferred_information.hpp"
#include "libvex_prof.hpp"
#include "offline_analysis.hpp"
#include "typesdb.hpp"
#include "timers.hpp"
#include "profile.hpp"

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
		    GarbageCollectionToken )
{
	__set_profiling(dumpfix);

	printCrashSummary(summary, _logfile);

	int fd;
	static int cntr;
	char *buf = NULL;
	do {
		free(buf);
		buf = my_asprintf("crash_summaries/%d", cntr);
		cntr++;
		fd = open(buf, O_WRONLY|O_EXCL|O_CREAT, 0600);
	} while (fd == -1 && errno == EEXIST);
	if (fd == -1)
		err(1, "opening %s", buf);
	fprintf(_logfile, "Write summary to %s\n", buf);
	free(buf);
	FILE *f = fdopen(fd, "w");
	if (!f)
		err(1, "fdopen()");

	printCrashSummary(summary, f);
	fclose(f);
}

void
DumpFix::finish(void)
{
	fprintf(output, "static const struct patch *const patches[] = {\n");
	for (int x = 0; x < cntr; x++)
		fprintf(output, "\t&patch%d,\n", x);
	fprintf(output, "};\n\n#include \"patch_skeleton_jump.c\"\n");
}

class TimeoutTimer : public Timer {
public:
	void fired() {
		_timed_out = true;
	}
};

static TimeoutTimer timeoutTimer;

static void
consider_rip(const DynAnalysisRip &my_rip,
	     unsigned tid,
	     VexPtr<Oracle> &oracle,
	     DumpFix &df,
	     FILE *timings,
	     GarbageCollectionToken token)
{
	__set_profiling(consider_rip);

	LibVEX_maybe_gc(token);

	fprintf(_logfile, "Considering %s...\n", my_rip.name());

	timeoutTimer.nextDue = now() + 45;
	timeoutTimer.schedule();

	struct timeval start;
	gettimeofday(&start, NULL);

	checkWhetherInstructionCanCrash(my_rip, tid, oracle, df, token);

	struct timeval end;
	gettimeofday(&end, NULL);

	timeoutTimer.cancel();

	double time_taken = end.tv_sec - start.tv_sec;
	time_taken += (end.tv_usec - start.tv_usec) * 1e-6;
	if (_timed_out) {
		if (timings)
			fprintf(timings, "%s timed out after %f\n", my_rip.name(), time_taken);
		printf("%s timed out after %f\n", my_rip.name(), time_taken);
	} else {
		if (timings)
			fprintf(timings, "%s took %f\n", my_rip.name(), time_taken);
		printf("%s took %f\n", my_rip.name(), time_taken);
	}
	_timed_out = false;
	__timer_message_filter::reset();

	fflush(NULL);
		
}

void startProfiling();

int
main(int argc, char *argv[])
{
	init_sli();

	__set_profiling(root);

	VexPtr<Oracle> oracle;
	{
		MachineState *ms = MachineState::readELFExec(argv[1]);
		Thread *thr = ms->findThread(ThreadId(1));
		oracle = new Oracle(ms, thr, argv[2]);
	}
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);

	FILE *output = fopen("generated_patch.c", "w");
	DumpFix df(oracle, output);

	LibVEX_gc(ALLOW_GC);

	int start_percentage;
	int end_percentage;

	start_percentage = 0;
	end_percentage = 100;

	if (argc == 5) {
		DynAnalysisRip vr;
		const char *succ;
		if (parseDynAnalysisRip(&vr, argv[4], &succ)) {
			consider_rip(vr, 1, oracle, df, NULL, ALLOW_GC);
			df.finish();
			return 0;
		}
		if (sscanf(argv[4], "%d...%d", &start_percentage, &end_percentage) != 2)
			errx(1, "expect final argument to be either a VexRip or s...d where s and d are start and end percentages");
	}

	FILE *timings = fopen("timings.txt", "w");
	VexPtr<TypesDb::all_instrs_iterator> instrIterator(oracle->type_index->enumerateAllInstructions());
	unsigned long total_instructions = oracle->type_index->nrDistinctInstructions();
	unsigned long instructions_processed = 0;
	printf("%ld instructions to protect\n", total_instructions);

	/* There are a couple of important properties here:

	   -- 0...100 must precisely cover the entire range
	   -- a...b and b...c must, between them, cover precisely the
              same range as a...c i.e. no duplicates or gaps.
	*/
	unsigned long start_instr = total_instructions / 100 * start_percentage;
	unsigned long end_instr = end_percentage == 100 ? total_instructions : total_instructions / 100 * end_percentage - 1;
	unsigned long instructions_to_process = end_instr - start_instr + 1;

	printf("Processing instructions %ld to %ld\n", start_instr, end_instr);

	/* Skip the ones we've been told to skip. */
	for (unsigned long a = 0; a < start_instr; a++)
		instrIterator->advance();

	double start = now();
	double low_end_time;
	double high_end_time;
	bool first = true;
	unsigned long cntr = 0;
	while (cntr < instructions_to_process) {
		assert(!instrIterator->finished());
		DynAnalysisRip dar;
		instrIterator->fetch(&dar);
		_logfile = fopenf("w", "logs/%ld", cntr + start_instr);
		if (!_logfile) err(1, "opening logs/%ld", cntr + start_instr);
		printf("Considering %s, log logs/%ld\n", dar.name(), cntr + start_instr);
		fprintf(_logfile, "Log for %s:\n", dar.name());
		cntr++;
		consider_rip(dar, 1, oracle, df, timings, ALLOW_GC);
		fclose(_logfile);
		_logfile = stdout;

		instrIterator->advance();
		instructions_processed++;

		double completion = instructions_processed / double(instructions_to_process);
		double elapsed = now() - start;
		double total_estimated = elapsed / completion;
		double endd = total_estimated + start;
		if (isinf(endd))
			continue;

		dump_profiling_data();

		time_t end = endd;
		char *times;
		if (first) {
			low_end_time = endd;
			high_end_time = endd;
			first = false;
			times = my_asprintf("finish at %s", ctime(&end));
		} else {
			low_end_time = low_end_time * .99 + endd * 0.01;
			high_end_time = high_end_time * .99 + endd * 0.01;
			if (low_end_time > endd)
				low_end_time = endd;
			if (high_end_time < endd)
				high_end_time = endd;
			char *t = strdup(ctime(&end));
			t[strlen(t)-1] = 0;
			end = low_end_time;
			char *t2 = strdup(ctime(&end));
			t2[strlen(t2)-1] = 0;
			end = high_end_time;
			char *t3 = strdup(ctime(&end));
			t3[strlen(t3)-1] = 0;
			times = my_asprintf("finish at %s [%s,%s]\n",
					    t, t2, t3);
			free(t);
			free(t2);
			free(t3);
		}
		printf("Done %ld/%ld(%f%%) in %f seconds (%f each); %f left; %s",
		       instructions_processed,
		       total_instructions,
		       completion * 100,
		       elapsed,
		       elapsed / instructions_processed,
		       total_estimated - elapsed,
		       times);
		free(times);
	}

	df.finish();
	fclose(output);

	return 0;
}
