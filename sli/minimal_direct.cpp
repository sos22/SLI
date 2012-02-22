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

static void
timer_handler(int ignore)
{
	_timed_out = true;
}

template <typename typ> static void
shuffle(std::vector<typ> &vect)
{
	for (unsigned x = 0; x < vect.size(); x++) {
		unsigned idx = (random() % (vect.size() - x)) + x;
		typ t = vect[x];
		vect[x] = vect[idx];
		vect[idx] = t;
	}
}

static void
consider_rip(const VexRip &my_rip,
	     VexPtr<MachineState> &ms,
	     VexPtr<Thread> &thr,
	     VexPtr<Oracle> &oracle,
	     DumpFix &df,
	     FILE *timings,
	     GarbageCollectionToken token)
{
	__set_profiling(consider_rip);

	LibVEX_maybe_gc(token);

	fprintf(_logfile, "Considering %s...\n", my_rip.name());
	VexPtr<StateMachineEdge, &ir_heap> proximal(getProximalCause(ms, ThreadRip::mk(thr->tid._tid(), my_rip), thr));
	if (!proximal) {
		fprintf(_logfile, "No proximal cause -> can't do anything\n");
		return;
	}

	VexPtr<InferredInformation, &ir_heap> ii(new InferredInformation());
	ii->set(my_rip, new StateMachineProxy(my_rip, proximal));

	std::vector<VexRip> previousInstructions;
	oracle->findPreviousInstructions(previousInstructions, my_rip);

	struct itimerval itv;
	struct timeval start;

	memset(&itv, 0, sizeof(itv));
	itv.it_value.tv_sec = 45;
	setitimer(ITIMER_PROF, &itv, NULL);

	gettimeofday(&start, NULL);

	VexPtr<StateMachine, &ir_heap> probeMachine;
	probeMachine = buildProbeMachine(previousInstructions, ii, oracle, my_rip, thr->tid, token);
	if (probeMachine) {
		VexPtr<CrashSummary, &ir_heap> summary;
		summary = diagnoseCrash(probeMachine, oracle, ms, false, token);
		if (summary)
			df(summary, token);
	}

	struct timeval end;
	gettimeofday(&end, NULL);

	memset(&itv, 0, sizeof(itv));
	setitimer(ITIMER_PROF, &itv, NULL);

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

	__set_profiling(root);

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle;

	oracle = new Oracle(ms, thr, argv[2]);
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);

	signal(SIGPROF, timer_handler);

	FILE *output = fopen("generated_patch.c", "w");
	DumpFix df(oracle, output);

	LibVEX_gc(ALLOW_GC);

	if (argc == 5) {
		VexRip vr;
		const char *succ;
		if (!parseVexRip(&vr, argv[4], &succ))
			errx(1, "cannot parse %s as VexRip", argv[4]);
		consider_rip(vr, ms, thr, oracle, df, NULL, ALLOW_GC);
	} else {
		FILE *timings = fopen("timings.txt", "w");
		VexPtr<TypesDb::all_instrs_iterator> instrIterator(oracle->type_index->enumerateAllInstructions());
		unsigned long total_instructions = oracle->type_index->nrDistinctInstructions();
		unsigned long instructions_processed = 0;
		printf("%ld instructions to protect\n", total_instructions);
		double start = now();
		double low_end_time;
		double high_end_time;
		bool first = true;
		int cntr = 0;
		while (!instrIterator->finished()) {
			VexRip rip;
			instrIterator->fetch(&rip);
			_logfile = fopenf("w", "logs/%d", cntr);
			if (!_logfile) err(1, "opening logs/%d", cntr);
			printf("Considering %s, log logs/%d\n", rip.name(), cntr);
			fprintf(_logfile, "Log for %s:\n", rip.name());
			cntr++;
			consider_rip(rip, ms, thr, oracle, df, timings, ALLOW_GC);
			fclose(_logfile);
			_logfile = stdout;

			instrIterator->advance();

			double completion = instructions_processed / double(total_instructions);
			double elapsed = now() - start;
			double total_estimated = elapsed / completion;
			double endd = total_estimated + start;
			if (isinf(endd))
				continue;

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
	}

	df.finish();
	fclose(output);

	return 0;
}
