#include <sys/fcntl.h>
#include <err.h>
#include <stdio.h>
#include <unistd.h>

#include "sli.h"
#include "inferred_information.hpp"
#include "oracle.hpp"
#include "offline_analysis.hpp"

/* bool is whether to invert it or not. */
typedef std::pair<bool, IRExpr *> DNF_Atom;
typedef std::vector<DNF_Atom> DNF_Conjunction;
typedef std::vector<DNF_Conjunction> DNF_Disjunction;

#define DNF_MAX_DISJUNCTION 1000000

static bool dnf(IRExpr *e, DNF_Disjunction &out);

static void
check_memory_usage(void)
{
	FILE *f = fopen("/proc/self/stat", "r");
	int pid;
	char *name;
	char state;
	int ppid;
	int pgrp;
	int session;
	int tty;
	int tpgid;
	int flags;
	long minflt;
	long cminflt;
	long majflt;
	long cmajflt;
	long utime;
	long stime;
	long cstime;
	long priority;
	long nice;
	long num_threads;
	long itrealvalue;
	long long starttime;
	long vsize;

	vsize = 0;
	fscanf(f, "%d %as %c %d %d %d %d %d %d %ld %ld %ld %ld %ld %ld %ld %ld %ld %ld %ld %lld %ld",
	       &pid, &name, &state, &ppid, &pgrp, &session, &tty, &tpgid, &flags,
	       &minflt, &cminflt, &majflt, &cmajflt, &utime, &stime, &cstime,
	       &priority, &nice, &num_threads, &itrealvalue, &starttime,
	       &vsize);
	fclose(f);
	/* Get out if we have a vsize bigger than 6GiB */
	if (vsize >= (6l << 30)) {
		if (!_timed_out)
			fprintf(_logfile, "Forcing timeout because vsize 0x%lx\n",
				vsize);
		_timed_out = true;
	}
}

/* Set @out to @src1 & @src2.  Return false if we find a contradiction
   and true otherwise. */
static bool
merge_conjunctions(const DNF_Conjunction &src1,
		   const DNF_Conjunction &src2,
		   DNF_Conjunction &out)
{
	out.reserve(src1.size() + src2.size());
	DNF_Conjunction::const_iterator it1 = src1.begin();
	DNF_Conjunction::const_iterator it2 = src2.begin();
	while (it1 != src1.end() && it2 != src2.end()) {
		if (it1->second == it2->second) {
			if (it1->first != it2->first) {
				/* x & ~x -> nothing */
				return false;
			} else {
				out.push_back(*it1);
				it1++;
				it2++;
			}
		} else if (it1->second < it2->second) {
			out.push_back(*it1);
			it1++;
		} else {
			assert(it1->second > it2->second);
			out.push_back(*it2);
			it2++;
		}
	}
	while (it1 != src1.end()) {
		out.push_back(*it1);
		it1++;
	}
	while (it2 != src2.end()) {
		out.push_back(*it2);
		it2++;
	}
	return true;
}

/* Convert @out to @out & @this_one, maintaining disjunctive normal
 * form. */
static bool
dnf_and(const DNF_Disjunction &this_one, DNF_Disjunction &out)
{
	DNF_Disjunction new_out;
	check_memory_usage();
	if (TIMEOUT || out.size() * this_one.size() > DNF_MAX_DISJUNCTION)
		return false;
	new_out.reserve(out.size() * this_one.size());
	for (unsigned x = 0; x < out.size(); x++) {
		DNF_Conjunction &existing_conj(out[x]);
		for (unsigned z = 0; z < this_one.size(); z++) {
			new_out.resize(new_out.size() + 1);
			if (!merge_conjunctions(this_one[z], existing_conj, new_out.back())) {
				/* The conjunctions contradict each
				 * other.  That means that it can be
				 * removed completely. */
				new_out.resize(new_out.size() - 1);
			}
		}
	}
	out = new_out;
	return true;
}

/* conjoin the fragments together, convert to DNF, and then place the
   results in @out.  Can fail if @out looks ``too big'', in which case
   we return false; otherwise return true. */
static bool
dnf_and(IRExpr **fragments, int nr_fragments, DNF_Disjunction &out)
{
	check_memory_usage();
	if (TIMEOUT)
		return false;
	if (nr_fragments == 0)
		return true;
	if (out.size() == 0) {
		dnf(fragments[0], out);
		return dnf_and(fragments + 1, nr_fragments - 1, out);
	}
	DNF_Disjunction this_one;
	dnf(fragments[0], this_one);
	if (!dnf_and(this_one, out))
		return false;

	return dnf_and(fragments + 1, nr_fragments - 1, out);
}

/* Invert @conf and store it in @out, which must start out empty. */
static bool
dnf_invert(const DNF_Conjunction &conj, DNF_Disjunction &out)
{
	assert(out.size() == 0);
	for (unsigned x = 0; x < conj.size(); x++) {
		DNF_Conjunction c;
		c.push_back(DNF_Atom(!conj[x].first, conj[x].second));
		out.push_back(c);
	}
	return true;
}

static bool
dnf_invert(const DNF_Disjunction &in, DNF_Disjunction &out)
{
	assert(out.size() == 0);
	assert(in.size() != 0);

	check_memory_usage();
	/* Start by converting the first clause */
	if (!dnf_invert(in[0], out))
		return false;

	/* Now we convert the remaining clauses one at a time, and'ing
	   them in as we go.  The invariant here is that out = ~(in[0:x]),
	   where the slice notation is supposed to mean that we consider
	   the first x clauses only. */
	for (unsigned x = 1; x < in.size(); x++) {
		DNF_Disjunction r;
		if (TIMEOUT || !dnf_invert(in[x], r))
			return false;

		/* out = ~(in[0:x-1]), r = ~in[x]. */
		if (!dnf_and(r, out))
			return false;

		/* out = ~in[x] & ~(in[0:x-1])
		       = ~(in[x] | in[0:x-1])
		       = ~(in[0:x])

		   so invariant is preserved.
		*/
	}
	return true;
}

/* Convert @e to disjunctive normal form. */
static bool
dnf(IRExpr *e, DNF_Disjunction &out)
{
	check_memory_usage();
	out.clear();
	if (e->tag == Iex_Unop &&
	    e->Iex.Unop.op == Iop_Not1) {
		DNF_Disjunction r;
		if (!dnf(e->Iex.Unop.arg, r))
			return false;
		return dnf_invert(r, out);
	}

	if (e->tag == Iex_Associative) {
		if (e->Iex.Associative.op == Iop_Or1) {
			for (int x = 0; x < e->Iex.Associative.nr_arguments; x++) {
				if (TIMEOUT)
					return false;
				DNF_Disjunction r;
				if (!dnf(e->Iex.Associative.contents[x], r))
					return false;
				out.insert(out.end(), r.begin(), r.end());
			}
			return true;
		} else if (e->Iex.Associative.op == Iop_And1) {
			return dnf_and(e->Iex.Associative.contents,
				       e->Iex.Associative.nr_arguments,
				       out);
		}
	}

	/* Anything else cannot be represented in DNF, so gets an
	 * atom */
	DNF_Conjunction c;
	c.push_back(DNF_Atom(false, e));
	out.push_back(c);
	return true;
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

static void
zapBinders(FreeVariableMap &m, StateMachine *sm)
{
	std::set<StateMachineSideEffectLoad *> loads;
	findAllLoads(sm, loads);
	bool done_something;
	do {
		done_something = false;
		for (std::set<StateMachineSideEffectLoad *>::iterator it = loads.begin();
		     it != loads.end();
		     it++)
			applySideEffectToFreeVariables(*it, m, &done_something);
	} while (done_something);
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);

	int fd = open(argv[4], O_RDONLY);
	if (fd < 0)
		err(1, "opening %s", argv[4]);
	VexPtr<CrashSummary, &ir_heap> summary(readCrashSummary(fd));
	close(fd);

	printf("Machines to enforce:\n");
	printCrashSummary(summary, stdout);

	IRExpr *requirement = findHappensBeforeRelations(summary, oracle, ALLOW_GC);
	fprintf(_logfile, "Crash requirement:\n");
	ppIRExpr(requirement, _logfile);
	fprintf(_logfile, "\n");

	DNF_Disjunction d;
	if (TIMEOUT || !dnf(requirement, d)) {
		fprintf(_logfile, "failed to convert to DNF\n");
		return 1;
	}
	printDnf(d, _logfile);
	FreeVariableMap m(summary->loadMachine->freeVariables);
	zapBinders(m, summary->loadMachine);
	for (unsigned x = 0; x < summary->storeMachines.size(); x++) {
		FreeVariableMap n(summary->storeMachines[x]->machine->freeVariables);
		zapBinders(n, summary->storeMachines[x]->machine);
		m.merge(n);
	}
       
	for (unsigned x = 0; x < d.size(); x++)
		partitionCrashCondition(d[x], m);

	return 0;
}
