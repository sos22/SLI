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
	__set_profiling(consider_rip);

	LibVEX_maybe_gc(token);

	fprintf(_logfile, "Considering %lx...\n", my_rip);
	VexPtr<StateMachine, &ir_heap> proximal(getProximalCause(ms, my_rip, thr));
	if (!proximal) {
		fprintf(_logfile, "No proximal cause -> can't do anything\n");
		return;
	}

	VexPtr<InferredInformation> ii(new InferredInformation(oracle));
	ii->addCrashReason(proximal);

	std::vector<unsigned long> previousInstructions;
	oracle->findPreviousInstructions(previousInstructions, my_rip);

	struct itimerval itv;
	struct timeval start;

	memset(&itv, 0, sizeof(itv));
	itv.it_value.tv_sec = 45;
	setitimer(ITIMER_PROF, &itv, NULL);

	gettimeofday(&start, NULL);

	VexPtr<StateMachine, &ir_heap> probeMachine;
	probeMachine = buildProbeMachine(previousInstructions, ii, oracle, my_rip, token);
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

	__set_profiling(root);

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
		double low_end_time;
		double high_end_time;
		bool first = true;
		for (std::vector<unsigned long>::iterator it = targets.begin();
		     it != targets.end();
		     it++) {
			_logfile = fopenf("w", "logs/%lx", *it);
			if (!_logfile) err(1, "opening logs/%lx", *it);
			printf("Considering %lx\n", *it);
			consider_rip(*it, ms, thr, oracle, df, timings, ALLOW_GC);
			fclose(_logfile);
			_logfile = stdout;

			double completion = (it - targets.begin()) / double(targets.size());
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
			printf("Done %zd/%zd(%f%%) in %f seconds (%f each); %f left; %s",
			       it - targets.begin(),
			       targets.size(),
			       completion * 100,
			       elapsed,
			       elapsed / (it - targets.begin()),
			       total_estimated - elapsed,
			       times);
			free(times);
		}
	}

	df.finish();
	fclose(output);

	return 0;
}
