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
#include "allowable_optimisations.hpp"
#include "stacked_cdf.hpp"

extern FILE *bubble_plot_log;
extern FILE *bubble_plot2_log;

extern const char *__warning_tag;

struct size_limited_file {
	FILE *f;
	size_t remaining_quota;
};

class DumpFix : public FixConsumer {
public:
	VexPtr<Oracle> &oracle;
	int cntr;
	FILE *output;
	DynAnalysisRip dr;
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

	fprintf(f, "summary from dyn rip %s\n", dr.name());
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

static ssize_t
size_limited_write(void *_slf, const char *buf, size_t sz)
{
	struct size_limited_file *slf = (struct size_limited_file *)_slf;
	if (slf->remaining_quota < sz)
		sz = slf->remaining_quota;
	if (sz == slf->remaining_quota && slf->remaining_quota != 0) {
		fprintf(slf->f, "<log truncated>\n");
		fflush(slf->f);
	}
	size_t s = fwrite(buf, 1, sz, slf->f);
	slf->remaining_quota -= s;
	return s;
}

static int
size_limited_close(void *_slf)
{
	struct size_limited_file *slf = (struct size_limited_file *)_slf;
	int res = fclose(slf->f);
	free(slf);
	return res;
}

static FILE *
open_logfile(size_t sz, const char *fmt, ...)
{
	static cookie_io_functions_t funcs = {
		NULL,
		size_limited_write,
		NULL,
		size_limited_close
	};
	va_list args;
	va_start(args, fmt);
	char *path;
	int r = vasprintf(&path, fmt, args);
	(void)r;
	va_end(args);
	FILE *f = fopen(path, "w");
	free(path);
	if (!f)
		return NULL;
	struct size_limited_file *slf = (struct size_limited_file *)malloc(sizeof(struct size_limited_file));
	slf->remaining_quota = sz;
	slf->f = f;
	FILE *res = fopencookie(slf, "w", funcs);
	if (!res) {
		fclose(f);
		free(slf);
		return NULL;
	}
	return res;
}

static void
consider_rip(const DynAnalysisRip &my_rip,
	     unsigned tid,
	     VexPtr<Oracle> &oracle,
	     DumpFix &df,
	     const AllowableOptimisations &opt,
	     GarbageCollectionToken token)
{
	__set_profiling(consider_rip);

	__warning_tag = my_rip.name();

	df.dr = my_rip;

	LibVEX_maybe_gc(token);

	fprintf(_logfile, "Considering %s...\n", my_rip.name());

	stackedCdf::start();
	fprintf(bubble_plot_log, "%f: start crashing thread\n", now());
	if (oracle->isPltCall(my_rip.toVexRip())) {
		fprintf(bubble_plot_log, "%f: Dismiss early, PLT\n", now());
		fprintf(_logfile, "Is in PLT, so ignore\n");
	} else {
		checkWhetherInstructionCanCrash(my_rip, tid, oracle, df, opt, token);
	}
	fprintf(bubble_plot_log, "%f: finish crashing thread\n", now());
	stackedCdf::stop(_timed_out);

	fflush(NULL);

	__warning_tag = "<lost_tag>";
}

void startProfiling();

class InstructionConsumer {
	unsigned long start_instr;
	unsigned long instructions_to_process;
	unsigned long instructions_processed;
	unsigned long total_instructions;
	double start;
	double low_end_time;
	double high_end_time;
	bool first;
	const AllowableOptimisations &opt;
public:
	InstructionConsumer(unsigned long _start_instr, unsigned long _instructions_to_process,
			    unsigned long _total_instructions, const AllowableOptimisations &_opt)
		: start_instr(_start_instr), instructions_to_process(_instructions_to_process),
		  instructions_processed(0), total_instructions(_total_instructions),
		  start(now()), first(true), opt(_opt)
	{}
	void operator()(VexPtr<Oracle> &oracle, DumpFix &df, const DynAnalysisRip &dar, unsigned long cntr);
};

void
InstructionConsumer::operator()(VexPtr<Oracle> &oracle, DumpFix &df, const DynAnalysisRip &dar, unsigned long cntr)
{
	_logfile = open_logfile(1000000, "logs/%ld", cntr + start_instr);
	if (!_logfile) err(1, "opening logs/%ld", cntr + start_instr);
	printf("Considering %s, log logs/%ld\n", dar.name(), cntr + start_instr);
	fprintf(_logfile, "Log for %s:\n", dar.name());
	fflush(0);

	consider_rip(dar, 1, oracle, df, opt, ALLOW_GC);
	fclose(_logfile);
	_logfile = stdout;

	instructions_processed++;

	double completion = instructions_processed / double(instructions_to_process);
	double elapsed = now() - start;
	double total_estimated = elapsed / completion;
	double endd = total_estimated + start;
	if (isinf(endd))
		return;

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

static void
loadSchedule(const char *path, std::vector<DynAnalysisRip> &out)
{
	int fd = open(path, O_RDONLY);
	if (fd < 0)
		err(1, "opening %s", path);
	char *cont = readfile(fd);
	close(fd);
	if (!cont)
		err(1, "reading %s", path);
	DynAnalysisRip dr;
	const char *buf = cont;
	while (parseDynAnalysisRip(&dr, buf, &buf) &&
	       parseThisChar('\n', buf, &buf))
		out.push_back(dr);
	if (buf[0] != 0)
		errx(1, "junk at end of %s", path);
	free(cont);
}

int
main(int argc, char *argv[])
{
	init_sli();

	__set_profiling(root);

	if (argc < 5)
		errx(1, "not enough arguments");
	argv++;
	argc--;
	const char *binary = argv[0];
	const char *typesdb = argv[1];
	const char *callgraph = argv[2];
	const char *staticdb = argv[3];

	argv += 4;
	argc -= 4;

	bool assert_mode = false;
	bool double_free_mode = false;
	bool indirect_call_mode = false;
	if (!strcmp(argv[argc - 1], "assertions")) {
		assert_mode = true;
		argc--;
	} else if (!strcmp(argv[argc - 1], "doublefree")) {
		double_free_mode = true;
		argc--;
	} else if (!strcmp(argv[argc - 1], "icall")) {
		indirect_call_mode = true;
		argc--;
	}

	if (argc > 1)
		errx(1, "Too many arguments");

	VexPtr<Oracle> oracle;
	{
		MachineState *ms = MachineState::readELFExec(binary);
		Thread *thr = ms->findThread(ThreadId(1));
		oracle = new Oracle(ms, thr, typesdb);
	}
	oracle->loadCallGraph(oracle, callgraph, staticdb, ALLOW_GC);

	FILE *output = fopen("generated_patch.c", "w");
	DumpFix df(oracle, output);

	LibVEX_gc(ALLOW_GC);

	int start_percentage;
	int end_percentage;

	start_percentage = 0;
	end_percentage = 100;

	bubble_plot_log = fopen("bubble_data.log", "w");
	bubble_plot2_log = fopen("bubble_data2.log", "w");

	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack()
		.setAddressSpace(oracle->ms->addressSpace);
	if (assert_mode || double_free_mode)
		opt = opt.enableallPointersGood();
	if (double_free_mode)
		opt = opt.enablefreeMightRace();

	if (argc == 1) {
		DynAnalysisRip vr;
		const char *succ;
		if (parseDynAnalysisRip(&vr, argv[0], &succ)) {
			consider_rip(vr, 1, oracle, df, opt, ALLOW_GC);
			df.finish();
			return 0;
		}
		if (sscanf(argv[0], "%d...%d", &start_percentage, &end_percentage) != 2)
			errx(1, "expect final argument to be either a VexRip or s...d where s and d are start and end percentages");
	}

	std::vector<DynAnalysisRip> schedule;
	VexPtr<TypesDb::all_instrs_iterator> instrIterator;
	unsigned long total_instructions;
	bool use_schedule = false;

	/* Shut compiler up */
	total_instructions = -1;

	if (getenv("SOS22_MINIMAL_DIRECT_INSTR_SCHEDULE")) {
		loadSchedule(getenv("SOS22_MINIMAL_DIRECT_INSTR_SCHEDULE"),
			     schedule);
		use_schedule = true;
	} else if (assert_mode) {
		oracle->findAssertions(schedule);
		use_schedule = true;
	} else if (double_free_mode) {
		oracle->findFrees(schedule);
		use_schedule = true;
	} else if (indirect_call_mode) {
		oracle->findIndirectCalls(schedule);
		use_schedule = true;
	} else {
		instrIterator = oracle->type_db->enumerateAllInstructions();
		total_instructions = oracle->type_db->nrDistinctInstructions();
	}

	if (use_schedule)
		total_instructions = schedule.size();

	printf("%ld instructions to protect\n", total_instructions);

	/* There are a couple of important properties here:
	   
	   -- 0...100 must precisely cover the entire range
	   -- a...b and b...c must, between them, cover precisely the
	      same range as a...c i.e. no duplicates or gaps.
	*/
	unsigned long start_instr = (total_instructions * start_percentage) / 100;
	unsigned long end_instr = end_percentage == 100 ? total_instructions - 1: (total_instructions * end_percentage) / 100 - 1;
	unsigned long instructions_to_process = end_instr - start_instr;

	printf("Processing instructions %ld to %ld\n", start_instr, end_instr);

	unsigned long cntr = 0;

	InstructionConsumer ic(start_instr, instructions_to_process, total_instructions, opt);
	if (use_schedule) {
		initialise_profiling();
		start_profiling();
		for (unsigned long idx = start_instr; idx <= end_instr; idx++) {
			ic(oracle, df, schedule[idx], cntr);
			cntr++;
		}
		stop_profiling();
		dump_profiling_data();
	} else {
		/* Skip the ones we've been told to skip. */
		for (unsigned long a = 0; a < start_instr; a++)
			instrIterator->advance();

		while (cntr < instructions_to_process) {
			assert(!instrIterator->finished());
			DynAnalysisRip dar;
			instrIterator->fetch(&dar);
			instrIterator->advance();
			ic(oracle, df, dar, cntr);
			cntr++;

		}
	}

	df.finish();
	fclose(output);

	return 0;
}
