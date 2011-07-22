#include <sys/time.h>
#include <err.h>
#include <math.h>
#include <time.h>

#include <vector>
#include <set>

#include "sli.h"
#include "oracle.hpp"
#include "crash_reason.hpp"
#include "inferred_information.hpp"
#include "libvex_prof.hpp"
#include "offline_analysis.hpp"

/* bool is whether to invert it or not. */
typedef std::pair<bool, IRExpr *> DNF_Atom;
typedef std::vector<DNF_Atom> DNF_Conjunction;
typedef std::vector<DNF_Conjunction> DNF_Disjunction;

static void dnf(IRExpr *e, DNF_Disjunction &out);

/* Convert @out to @out & @this_one, maintaining disjunctive normal
 * form. */
static void
dnf_and(const DNF_Disjunction &this_one, DNF_Disjunction &out)
{
	DNF_Disjunction new_out;
	new_out.reserve(out.size() * this_one.size());
	for (unsigned x = 0; x < out.size(); x++) {
		DNF_Conjunction &existing_conj(out[x]);
		for (unsigned z = 0; z < this_one.size(); z++) {
			const DNF_Conjunction &new_conj(this_one[z]);
			new_out.push_back(new_conj);
			DNF_Conjunction &output_conj(new_out.back());
			output_conj.insert(output_conj.end(),
					   existing_conj.begin(),
					   existing_conj.end());
		}
	}
	out = new_out;
}

/* conjoin the fragments together, convert to DNF, and then place the
   results in @out */
static void
dnf_and(IRExpr **fragments, int nr_fragments, DNF_Disjunction &out)
{
	if (nr_fragments == 0)
		return;
	if (out.size() == 0) {
		dnf(fragments[0], out);
		dnf_and(fragments + 1, nr_fragments - 1, out);
		return;
	}
	DNF_Disjunction this_one;
	dnf(fragments[0], this_one);
	dnf_and(this_one, out);

	dnf_and(fragments + 1, nr_fragments - 1, out);
}

/* Invert @conf and store it in @out, which must start out empty. */
static void
dnf_invert(const DNF_Conjunction &conj, DNF_Disjunction &out)
{
	assert(out.size() == 0);
	for (unsigned x = 0; x < conj.size(); x++) {
		DNF_Conjunction c;
		c.push_back(DNF_Atom(!conj[x].first, conj[x].second));
		out.push_back(c);
	}
}

static void
dnf_invert(const DNF_Disjunction &in, DNF_Disjunction &out)
{
	assert(out.size() == 0);
	assert(in.size() != 0);

	/* Start by converting the first clause */
	dnf_invert(in[0], out);

	/* Now we convert the remaining clauses one at a time, and'ing
	   them in as we go.  The invariant here is that out = ~(in[0:x]),
	   where the slice notation is supposed to mean that we consider
	   the first x clauses only. */
	for (unsigned x = 1; x < in.size(); x++) {
		DNF_Disjunction r;
		dnf_invert(in[x], r);

		/* out = ~(in[0:x-1]), r = ~in[x]. */
		dnf_and(r, out);
		/* out = ~in[x] & ~(in[0:x-1])
		       = ~(in[x] | in[0:x-1])
		       = ~(in[0:x])

		   so invariant is preserved.
		*/
	}
}

/* Convert @e to disjunctive normal form. */
static void
dnf(IRExpr *e, DNF_Disjunction &out)
{
	out.clear();
	if (e->tag == Iex_Unop &&
	    e->Iex.Unop.op == Iop_Not1) {
		DNF_Disjunction r;
		dnf(e->Iex.Unop.arg, r);
		dnf_invert(r, out);
		return;
	}

	if (e->tag == Iex_Associative) {
		if (e->Iex.Associative.op == Iop_Or1) {
			for (int x = 0; x < e->Iex.Associative.nr_arguments; x++) {
				DNF_Disjunction r;
				dnf(e->Iex.Associative.contents[x], r);
				out.insert(out.end(), r.begin(), r.end());
			}
			return;
		} else if (e->Iex.Associative.op == Iop_And1) {
			dnf_and(e->Iex.Associative.contents,
				e->Iex.Associative.nr_arguments,
				out);
			return;
		}
	}

	/* Anything else cannot be represented in DNF, so gets an
	 * atom */
	DNF_Conjunction c;
	c.push_back(DNF_Atom(false, e));
	out.push_back(c);
}

static void
printDnf(DNF_Disjunction &dnf, FILE *f)
{
	for (unsigned x = 0; x < dnf.size(); x++) {
		for (unsigned y = 0; y < dnf[x].size(); y++) {
			if (dnf[x][y].first)
				fprintf(f, "-");
			else
				fprintf(f, "+");
			ppIRExpr(dnf[x][y].second, f);
			if (y != dnf[x].size() - 1)
				fprintf(f, "  &&&&&\n");
		}
		if (x != dnf.size() - 1)
			fprintf(f, "\n|||||||||||||||\n");
	}
	fprintf(f, "\n");
}

class getMentionedTidsTransformer : public IRExprTransformer {
protected:
	IRExpr *transformIexGet(IRExpr *e, bool *done_something) {
		out.insert(e->Iex.Get.tid);
		return IRExprTransformer::transformIexGet(e, done_something);
	}
	IRExpr *transformIexGetI(IRExpr *e, bool *done_something) {
		out.insert(e->Iex.GetI.tid);
		return IRExprTransformer::transformIexGetI(e, done_something);
	}
	IRExpr *transformIexRdTmp(IRExpr *e, bool *done_something) {
		out.insert(e->Iex.RdTmp.tid);
		return IRExprTransformer::transformIexGet(e, done_something);
	}
	IRExpr *transformIexBinder(IRExpr *e, bool *done_something) {
		/* Shouldn't have binders at this stage */
		abort();
	}
	IRExpr *transformIexFreeVariable(IRExpr *e, bool *done_something) {
		return IRExprTransformer::transformIRExpr(fv.get(e->Iex.FreeVariable.key), done_something);
	}
	StateMachineSideEffectMemoryAccess *transformStateMachineSideEffectMemoryAccess(StateMachineSideEffectMemoryAccess *x,
											bool *done_soemthing)
	{
		return x;
	}
public:
	FreeVariableMap &fv;
	std::set<unsigned> &out;
	getMentionedTidsTransformer(FreeVariableMap &_fv,
				    std::set<unsigned> &_out)
		: fv(_fv), out(_out)
	{}
};

static void
getMentionedTids(IRExpr *e, FreeVariableMap &fv, std::set<unsigned> &out)
{
	getMentionedTidsTransformer t(fv, out);
	t.transformIRExpr(e);
}

static void
partitionCrashCondition(DNF_Conjunction &c, FreeVariableMap &fv)
{
	for (unsigned x = 0; x < c.size(); x++) {
		std::set<unsigned> tids;
		tids.clear();
		getMentionedTids(c[x].second, fv, tids);
		ppIRExpr(c[x].second, _logfile);
		fprintf(_logfile, " needs threads ");
		for (std::set<unsigned>::iterator it = tids.begin();
		     it != tids.end();
		     it++) {
			if (it != tids.begin())
				fprintf(_logfile, ", ");
			fprintf(_logfile, "%d", *it);
		}
		fprintf(_logfile, "\n");
	}
}

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
	IRExpr *requirement = findHappensBeforeRelations(summary, oracle, token);
	fprintf(_logfile, "Crash requirement:\n");
	ppIRExpr(requirement, _logfile);
	fprintf(_logfile, "\n");

	DNF_Disjunction d;
	dnf(requirement, d);
	printDnf(d, _logfile);
	FreeVariableMap m(summary->loadMachine->freeVariables);
	for (unsigned x = 0; x < summary->storeMachines.size(); x++)
		m.merge(summary->storeMachines[x]->machine->freeVariables);
	for (unsigned x = 0; x < d.size(); x++)
		partitionCrashCondition(d[x], m);
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
	itv.it_value.tv_sec = 20;
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
