#include <sys/fcntl.h>
#include <err.h>
#include <stdio.h>
#include <unistd.h>

#include "sli.h"
#include "inferred_information.hpp"
#include "oracle.hpp"
#include "offline_analysis.hpp"
#include "cnf.hpp"
#include "genfix.hpp"

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

/* The ordering we use for DNF conjunctions works like this:

   -- If a is a subset of b then a is less than b.
   -- If a is a superset of b then a is greather than b.
   -- Otherwise, if they're unordered by the subset ordering, we
      using a per-element dictionary ordering.

   This enumeration gives every possible result.
*/
enum dnf_ordering {
	dnf_subset = -2,
	dnf_less = -1,
	dnf_eq = 0,
	dnf_greater = 1,
	dnf_superset = 2
};

static int
compare_dnf_atom(const DNF_Atom &a, const DNF_Atom &b)
{
	if (a.second < b.second)
		return -1;
	if (a.second > b.second)
		return 1;
	if (a.first < b.first)
		return -1;
	if (a.first > b.first)
		return 1;
	return 0;
}

static dnf_ordering
compare_dnf_conjunctions(const DNF_Conjunction &a, const DNF_Conjunction &b)
{
	DNF_Conjunction::const_iterator it1 = a.begin();
	DNF_Conjunction::const_iterator it2 = b.begin();

	while (it1 != a.end() && it2 != b.end()) {
		switch (compare_dnf_atom(*it1, *it2)) {
		case -1:
			/* Here we have an element of a which less
			   than the matching element of b.  Either a
			   is a superset of b or a is less than b.
			   Find out which. */
			while (it1 != a.end() && it2 != b.end()) {
				switch (compare_dnf_atom(*it1, *it2)) {
				case -1:
					it1++;
					break;
				case 0:
					it1++;
					it2++;
					break;
				case 1:
					return dnf_less;
				}
			}
			if (it2 == b.end())
				return dnf_superset;
			else
				return dnf_less;
		case 0:
			it1++;
			it2++;
			break;
		case 1:
			/* Opposite case: an element of a which is
			   greater than the matching element of b.  a
			   is either a subset of b or greater than
			   b. */
			while (it1 != a.end() && it2 != b.end()) {
				switch (compare_dnf_atom(*it1, *it2)) {
				case -1:
					return dnf_greater;
				case 0:
					it1++;
					it2++;
					break;
				case 1:
					it2++;
					break;
				}
			}
			if (it1 == a.end())
				return dnf_subset;
			else
				return dnf_greater;
		default:
			abort();
		}
	}
	if (it1 == a.end() && it2 == b.end())
		return dnf_eq;
	if (it1 == a.end() && it2 != b.end())
		return dnf_subset;
	if (it1 != a.end() && it2 == b.end())
		return dnf_superset;
	abort();
}

static void
sanity_check(const DNF_Conjunction &a)
{
	assert(a.size() > 0);
	for (unsigned x = 0; x < a.size() - 1; x++) {
		assert(a[x].second != a[x+1].second);
		assert(a[x].second < a[x+1].second);
	}
}
static void
sanity_check(const DNF_Disjunction &a)
{
	if (a.size() == 0)
		return;
	unsigned x;
	for (x = 0; x < a.size() - 1; x++) {
		sanity_check(a[x]);
		assert(compare_dnf_conjunctions(a[x], a[x+1]) < 0);
	}
	sanity_check(a[x]);
}

/* Set @out to @src1 & @src2.  Return false if we find a contradiction
   and true otherwise. */
static bool
merge_conjunctions(const DNF_Conjunction &src1,
		   const DNF_Conjunction &src2,
		   DNF_Conjunction &out)
{
	sanity_check(src1);
	sanity_check(src2);
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
	sanity_check(out);
	return true;
}

/* Set @out to @src1 | @src2. */
static void
merge_disjunctions(const DNF_Disjunction &src1,
		   const DNF_Disjunction &src2,
		   DNF_Disjunction &out)
{
	sanity_check(src1);
	sanity_check(src2);
	out.clear();
	out.reserve(src1.size() + src2.size());
	DNF_Disjunction::const_iterator it1 = src1.begin();
	DNF_Disjunction::const_iterator it2 = src2.begin();
	while (it1 != src1.end() && it2 != src2.end()) {
		switch (compare_dnf_conjunctions(*it1, *it2)) {
		case dnf_subset: /* *it1 subsumes *it2, so drop *it2 */
		case dnf_eq: /* They're equal, it doesn't matter which one we pick */
			sanity_check(out);
			out.push_back(*it1);
			sanity_check(out);
			it1++;
			it2++;
			break;
		case dnf_superset: /* *it2 subsumes *it1, so drop *it1 */
			out.push_back(*it2);
			it1++;
			it2++;
			break;
		case dnf_less:
			sanity_check(out);
			out.push_back(*it1);
			sanity_check(out);
			it1++;
			break;
		case dnf_greater:
			sanity_check(out);
			out.push_back(*it2);
			sanity_check(out);
			it2++;
			break;
		}
	}
	sanity_check(out);
	while (it1 != src1.end()) {
		out.push_back(*it1);
		it1++;
	}
	sanity_check(out);
	while (it2 != src2.end()) {
		out.push_back(*it2);
		it2++;
	}
	sanity_check(out);
}

/* Set @out to @src | @out */
static void
insert_conjunction(const DNF_Conjunction &src, DNF_Disjunction &out)
{
	unsigned x;
	unsigned nr_killed = 0;
	sanity_check(out);
	for (x = 0; x < out.size(); x++) {
		switch (compare_dnf_conjunctions(out[x], src)) {
		case dnf_subset:
		case dnf_eq:
			/* This existing output clause subsumes the
			 * new one we want to insert. */
			return;
		case dnf_superset:
			/* The new clause subsumes this existing
			   output clause, so replace it. */
			out[x].clear();
			nr_killed ++;
			break;
		case dnf_less:
			assert(compare_dnf_conjunctions(src, out[x]) == dnf_greater);
			continue;
		case dnf_greater:
			assert(compare_dnf_conjunctions(src, out[x]) == dnf_less);
			goto out1;
		}
	}
out1:
	if (nr_killed > out.size() / 2) {
		DNF_Disjunction new_out;
		new_out.reserve(out.size() - nr_killed + 1);
		for (unsigned y = 0; y < out.size(); y++) {
			sanity_check(new_out);
			if (y == x) {
				new_out.push_back(src);
				sanity_check(new_out);
			}
			if (out[y].size() != 0) {
				new_out.push_back(out[y]);
				sanity_check(new_out);
			}
		}
		if (x == out.size())
			new_out.push_back(src);
		out = new_out;
	} else {
		for (unsigned y = 0; y < out.size(); y++) {
			if (x == y)
				out.insert(out.begin() + y, src);
			if (out[y].size() == 0) {
				if (y < x)
					x--;
				out.erase(out.begin() + y);
				y--;
			}
		}
		sanity_check(out);
		if (x == out.size())
			out.insert(out.begin() + x, src);
		sanity_check(out);
	}
}


/* Convert @out to @out & @this_one, maintaining disjunctive normal
 * form. */
static bool
dnf_and(const DNF_Disjunction &this_one, DNF_Disjunction &out)
{
	DNF_Disjunction new_out;
	check_memory_usage();
	sanity_check(out);
	if (TIMEOUT || out.size() * this_one.size() > DNF_MAX_DISJUNCTION)
		return false;
	new_out.reserve(out.size() * this_one.size());
	for (unsigned x = 0; x < out.size(); x++) {
		DNF_Conjunction &existing_conj(out[x]);
		for (unsigned z = 0; z < this_one.size(); z++) {
			sanity_check(new_out);
			DNF_Conjunction new_conj;
			if (merge_conjunctions(this_one[z], existing_conj, new_conj)) {
				sanity_check(new_out);
				insert_conjunction(new_conj, new_out);
				sanity_check(new_out);
			} else {
				/* the conjunction includes both x and
				   !x, for some x, so should be
				   dropped */
			}
		}
	}
	out = new_out;
	sanity_check(out);
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
		return dnf(fragments[0], out) &&
			dnf_and(fragments + 1, nr_fragments - 1, out);
	}
	sanity_check(out);
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
	out.reserve(conj.size());
	for (unsigned x = 0; x < conj.size(); x++) {
		DNF_Conjunction c;
		c.push_back(DNF_Atom(!conj[x].first, conj[x].second));
		insert_conjunction(c, out);
	}
	sanity_check(out);
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
	sanity_check(out);
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
		return dnf(e->Iex.Unop.arg, r) &&
			dnf_invert(r, out);
	}

	if (e->tag == Iex_Associative) {
		if (e->Iex.Associative.op == Iop_Or1) {
			for (int x = 0; x < e->Iex.Associative.nr_arguments; x++) {
				if (TIMEOUT)
					return false;
				DNF_Disjunction r;
				if (!dnf(e->Iex.Associative.contents[x], r))
					return false;
				DNF_Disjunction t(out);
				merge_disjunctions(r, t, out);
			}
			sanity_check(out);
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
	sanity_check(out);
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

class ShortCircuitFvTransformer : public IRExprTransformer {
public:
	FreeVariableMap &fv;
	ShortCircuitFvTransformer(FreeVariableMap &_fv)
		: fv(_fv)
	{}
	IRExpr *transformIexFreeVariable(IRExpr *e, bool *done_something)
	{
		*done_something = true;
		return transformIRExpr(fv.get(e->Iex.FreeVariable.key), done_something);
	}
};

static void
zapBindersAndFreeVariables(FreeVariableMap &m, StateMachine *sm)
{
	std::set<StateMachineSideEffectLoad *> loads;
	findAllLoads(sm, loads);
	bool done_something;
	do {
		done_something = false;
		/* Step one: zap binders */
		for (std::set<StateMachineSideEffectLoad *>::iterator it = loads.begin();
		     it != loads.end();
		     it++)
			applySideEffectToFreeVariables(*it, m, &done_something);
		/* Step two: short-circuit free variables */
		ShortCircuitFvTransformer trans(m);
		m.applyTransformation(trans, &done_something);
	} while (done_something);
}

class EnumNeededExpressionsTransformer : public IRExprTransformer {
public:
	std::set<IRExpr *> &out;
	EnumNeededExpressionsTransformer(std::set<IRExpr *> &_out)
		: out(_out)
	{}
	IRExpr *transformIexRdTmp(IRExpr *e, bool *done_something) {
		abort(); /* Should all have been eliminated by now */
	}
	IRExpr *transformIexGet(IRExpr *e, bool *done_something) {
		out.insert(e);
		return e;
	}
	IRExpr *transformIexLoad(IRExpr *e, bool *done_something) {
		out.insert(e);
		/* Note that we don't recurse into the address
		   calculation here.  We can always evaluate this
		   expression after seeing the load itself, regardless
		   of where the address came from. */
		return e;
	}
	IRExpr *transformIexHappensBefore(IRExpr *e, bool *done_something) {
		out.insert(e);
		/* Again, we don't recurse into the details of the
		   happens before expression, because we only need the
		   two instructions, and not details of their
		   side-effects. */
		return e;
	}
	IRExpr *transformIexClientCall(IRExpr *e, bool *done_something) {
		out.insert(e);
		return e;
	}
};
static void
enumerateNeededExpressions(IRExpr *e, std::set<IRExpr *> &out)
{
	EnumNeededExpressionsTransformer trans(out);
	trans.transformIRExpr(e);
}

class EnforceCrashCFG : public CFG<ThreadRip> {
	std::set<ThreadRip> &neededInstructions;
public:
	bool instructionUseful(Instruction<ThreadRip> *i) {
		bool r = (neededInstructions.count(i->rip) != 0);
		printf("%d:%lx %s\n", i->rip.thread, i->rip.rip,
		       r ? "useful" : "not useful");
		return r;
	}
	EnforceCrashCFG(AddressSpace *as, std::set<ThreadRip> &ni)
		: CFG<ThreadRip>(as), neededInstructions(ni)
	{}
};

class instrToInstrSetMap : public std::map<Instruction<ThreadRip> *, std::set<Instruction<ThreadRip> *> > {
public:
	void print(FILE *f);
};
void
instrToInstrSetMap::print(FILE *f)
{
	for (iterator it = begin(); it != end(); it++) {
		fprintf(f, "%d:%lx[%p] -> {", it->first->rip.thread, it->first->rip.rip, it->first);
		for (std::set<Instruction<ThreadRip> *>::iterator it2 = it->second.begin();
		     it2 != it->second.end();
		     it2++) {
			if (it2 != it->second.begin())
				fprintf(f, ", ");
			fprintf(f, "%d:%lx[%p]", (*it2)->rip.thread, (*it2)->rip.rip, *it2);
		}
		fprintf(f, "}\n");
	}
}

/* An encoding of the happens-before edges in a DNF clause into a map
   over Instructions. */
class happensAfterMapT {
public:
	/* happensBefore[i] -> the set of all instructions ordered before i */
	instrToInstrSetMap happensBefore;
	/* happensBefore[i] -> the set of all instructions ordered after i */
	instrToInstrSetMap happensAfter;
	happensAfterMapT(DNF_Conjunction &c, CFG<ThreadRip> *cfg);
	void print(FILE *f) {
		fprintf(f, "before:\n");
		happensBefore.print(f);
		fprintf(f, "after:\n");
		happensAfter.print(f);
	}
};
happensAfterMapT::happensAfterMapT(DNF_Conjunction &c, CFG<ThreadRip> *cfg)
{
	for (unsigned x = 0; x < c.size(); x++) {
		if (c[x].second->tag == Iex_HappensBefore) {
			ThreadRip beforeRip = c[x].second->Iex.HappensBefore.before->rip;
			ThreadRip afterRip = c[x].second->Iex.HappensBefore.after->rip;
			Instruction<ThreadRip> *before = cfg->ripToInstr->get(beforeRip);
			Instruction<ThreadRip> *after = cfg->ripToInstr->get(afterRip);
			assert(before);
			assert(after);
			if (c[x].first) {
				Instruction<ThreadRip> *t = before;
				before = after;
				after = t;
			}
			happensAfter[before].insert(after);
			happensBefore[after].insert(before);
		}
	}
}

/* Map from instructions to instructions which happen immediately
   before them, including those ordered by happens-before
   relationships. */
class predecessorMapT : public instrToInstrSetMap {
public:
	predecessorMapT(CFG<ThreadRip> *cfg) {
		for (CFG<ThreadRip>::ripToInstrT::iterator it = cfg->ripToInstr->begin();
		     it != cfg->ripToInstr->end();
		     it++) {
			Instruction<ThreadRip> *v = it.value();
			if (!count(v))
				(*this)[v];
			if (v->defaultNextI)
				(*this)[v->defaultNextI].insert(v);
			if (v->branchNextI)
				(*this)[v->branchNextI].insert(v);
		}
	}
};

class cfgRootSetT : public std::set<Instruction<ThreadRip> *> {
public:
	cfgRootSetT(CFG<ThreadRip> *cfg, predecessorMapT &pred, happensAfterMapT &happensAfter);
};
cfgRootSetT::cfgRootSetT(CFG<ThreadRip> *cfg, predecessorMapT &pred, happensAfterMapT &happensBefore)
{
	std::set<Instruction<ThreadRip> *> toEmit;
	for (CFG<ThreadRip>::ripToInstrT::iterator it = cfg->ripToInstr->begin();
	     it != cfg->ripToInstr->end();
	     it++)
		toEmit.insert(it.value());
	while (!toEmit.empty()) {
		/* Find one with no predecessors and emit that */
		std::set<Instruction<ThreadRip> *>::iterator it;
		for (it = toEmit.begin(); it != toEmit.end(); it++) {
			assert(pred.count(*it));
			if (pred[*it].size() == 0)
				break;
		}
		if (it == toEmit.end()) {
			/* Every instruction is part of a cycle.
			   Arbitrarily declare that the first one is
			   the root and emit that. */
			it = toEmit.begin();
		}
		/* We're going to use *it as a root.  Purge it and
		   everything reachable from it from the toEmit
		   set. */
		std::vector<Instruction<ThreadRip> *> toPurge;
		std::set<Instruction<ThreadRip> *> donePurge;
		toPurge.push_back(*it);
		while (!toPurge.empty()) {
			Instruction<ThreadRip> *purge = toPurge.back();
			toPurge.pop_back();
			if (donePurge.count(purge))
				continue;
			/* The loop breaking heuristic, above, isn't
			   terribly clever, and can sometimes choose a
			   bad node in a way which leads to one root
			   being reachable from another.  Fortunately,
			   it's easy to fix by just purging the
			   pseudo-root here. */
			erase(purge);

			toEmit.erase(purge);
			if (toEmit.count(purge)) {
				if (purge->branchNextI)
					toPurge.push_back(purge->branchNextI);
				if (purge->defaultNextI)
					toPurge.push_back(purge->defaultNextI);
			}
			donePurge.insert(purge);
		}
		/* Emit the new root */
		insert(*it);
	}
}

/* A map from Instruction * to the set of instructions which must
 * complete before that instruction, based purely on the control flow
 * graph. */
class instructionDominatorMapT : public instrToInstrSetMap {
public:
	instructionDominatorMapT(CFG<ThreadRip> *cfg,
				 predecessorMapT &predecessors,
				 happensAfterMapT &happensAfter,
				 const std::set<Instruction<ThreadRip> *> &neededInstructions);
	/* Find all of the instructions at which the set of dominators
	   changes i.e. does not match that of any of its
	   predecessors. */
	void getChangePoints(predecessorMapT &predecessors, std::set<Instruction<ThreadRip> *> &out);
};
instructionDominatorMapT::instructionDominatorMapT(CFG<ThreadRip> *cfg,
						   predecessorMapT &predecessors,
						   happensAfterMapT &happensAfter,
						   const std::set<Instruction<ThreadRip> *> &neededInstructions)
{
	/* Start by assuming that everything dominates everything */
	cfgRootSetT entryPoints(cfg, predecessors, happensAfter);
	std::set<Instruction<ThreadRip> *> needingRecompute;
	for (CFG<ThreadRip>::ripToInstrT::iterator it = cfg->ripToInstr->begin();
	     it != cfg->ripToInstr->end();
	     it++) {
		insert(std::pair<Instruction<ThreadRip> *, std::set<Instruction<ThreadRip> *> >(
			       it.value(),
			       neededInstructions));
		needingRecompute.insert(it.value());
	}

	/* Now iterate to a fixed point. */
	while (!needingRecompute.empty()) {
		Instruction<ThreadRip> *i;
		{
			std::set<Instruction<ThreadRip> *>::iterator it = needingRecompute.begin();
			i = *it;
			needingRecompute.erase(it);
		}

		std::set<Instruction<ThreadRip> *> &slot( (*this)[i] );

		/* new entry domination set is intersection of all of
		 * the predecessor's exit sets.  If there are no
		 * predecessor sets then the entry domination set is
		 * empty. */
		std::set<Instruction<ThreadRip> *> newDominators;
		std::set<Instruction<ThreadRip> *> &allPreds(predecessors[i]);
		if (!allPreds.empty()) {
			newDominators = slot;

			for (std::set<Instruction<ThreadRip> *>::iterator predIt = allPreds.begin();
			     predIt != allPreds.end();
			     predIt++) {
				Instruction<ThreadRip> *predecessor = *predIt;
				assert(count(predecessor));
				std::set<Instruction<ThreadRip> *> &pred_dominators((*this)[predecessor]);
				for (std::set<Instruction<ThreadRip> *>::iterator it2 = newDominators.begin();
				     it2 != newDominators.end();
					) {
					if (pred_dominators.count(*it2)) {
						it2++;
					} else {
						/* *it2 is dominated
						   by us, but not by
						   our predecessor.
						   That's a
						   contradiction.
						   Resolve it by
						   erasing *it2 from
						   our dominator
						   set. */
						newDominators.erase(it2++);
					}
				}
			}
		}

		/* Every instruction dominates itself. */
		if (neededInstructions.count(i))
			newDominators.insert(i);

		/* Anything dominated by something which is ordered
		   before us is also dominated by us.  Happens-before
		   edges are different to ordinary edges, because
		   happens-before edges are always satisfied, whereas
		   for ordinary control edges only one per instruction
		   will be satisfied. */
		std::set<Instruction<ThreadRip> *> &orderedBefore(happensAfter.happensBefore[i]);
		for (std::set<Instruction<ThreadRip> *>::iterator it = orderedBefore.begin();
		     it != orderedBefore.end();
		     it++) {
			std::set<Instruction<ThreadRip> *> &predecessor_dominates( (*this)[*it] );
			for (std::set<Instruction<ThreadRip> *>::iterator it2 = predecessor_dominates.begin();
			     it2 != predecessor_dominates.end();
			     it2++)
				newDominators.insert(*it2);
			if (neededInstructions.count(*it))
				newDominators.insert(*it);
		}

		if (newDominators != slot) {
			slot = newDominators;
			if (i->branchNextI)
				needingRecompute.insert(i->branchNextI);
			if (i->defaultNextI)
				needingRecompute.insert(i->defaultNextI);
			if (happensAfter.happensAfter.count(i)) {
				std::set<Instruction<ThreadRip> *> &orderedAfter(happensAfter.happensAfter[i]);
				for (std::set<Instruction<ThreadRip> *>::iterator it = orderedAfter.begin();
				     it != orderedAfter.end();
				     it++)
					needingRecompute.insert(*it);
			}
		}
	}
}
void
instructionDominatorMapT::getChangePoints(predecessorMapT &predecessors, std::set<Instruction<ThreadRip> *> &out)
{
	for (iterator it = begin(); it != end(); it++) {
		assert(predecessors.count(it->first));
		std::set<Instruction<ThreadRip> *> &pred(predecessors[it->first]);
		bool includeThisOne = true;
		for (std::set<Instruction<ThreadRip> *>::iterator it2 = pred.begin();
		     includeThisOne && it2 != pred.end();
		     it2++) {
			if ((*this)[*it2] == it->second)
				includeThisOne = false;
		}
		if (includeThisOne)
			out.insert(it->first);
	}
}

class expressionDominatorMapT : public std::map<Instruction<ThreadRip> *, std::set<IRExpr *> > {
	class trans1 : public IRExprTransformer {
		std::set<Instruction<ThreadRip> *> &avail;
		std::set<unsigned> &availThreads;
		CFG<ThreadRip> *cfg;
		bool isAvail(ThreadRip rip) {
			Instruction<ThreadRip> *i = cfg->ripToInstr->get(rip);
			assert(i);
			return avail.count(i) != 0;
		}
		IRExpr *transformIexGet(IRExpr *e, bool *done_something) {
			if (!availThreads.count(e->Iex.Get.tid))
				isGood = false;
			return e;
		}
		IRExpr *transformIexLoad(IRExpr *e, bool *done_something) {
			if (!isAvail(e->Iex.Load.rip))
				isGood = false;
			return e;
		}
		IRExpr *transformIexHappensBefore(IRExpr *e, bool *done_something) {
			isGood = false;
			return e;
		}
		IRExpr *transformIexClientCall(IRExpr *e, bool *done_something) {
			if (!isAvail(e->Iex.ClientCall.callSite))
				isGood = false;
			return e;
		}
	public:
		bool isGood;
		trans1(std::set<Instruction<ThreadRip> *> &_avail, std::set<unsigned> &_availThreads, CFG<ThreadRip> *_cfg)
			: avail(_avail), availThreads(_availThreads), cfg(_cfg), isGood(true) 
		{}
	};
	static bool evaluatable(IRExpr *e, std::set<Instruction<ThreadRip> *> &avail, std::set<unsigned> &availThreads, CFG<ThreadRip> *cfg) {
		trans1 t(avail, availThreads, cfg);
		t.transformIRExpr(e);
		return t.isGood;
	}
public:
	expressionDominatorMapT(instructionDominatorMapT &, DNF_Conjunction &,
				predecessorMapT &, happensAfterMapT &, CFG<ThreadRip> *);
};
expressionDominatorMapT::expressionDominatorMapT(instructionDominatorMapT &idom,
						 DNF_Conjunction &c,
						 predecessorMapT &pred,
						 happensAfterMapT &happensBefore,
						 CFG<ThreadRip> *cfg)
{
	/* First, figure out where the various expressions could in
	   principle be evaluated. */
	std::map<Instruction<ThreadRip> *, std::set<IRExpr *> > evalable;
	for (instructionDominatorMapT::iterator it = idom.begin();
	     it != idom.end();
	     it++) {
		evalable[it->first].clear();
		for (unsigned x = 0; x < c.size(); x++) {
			std::set<unsigned> availThreads;
			for (std::set<Instruction<ThreadRip> *>::iterator it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++)
				availThreads.insert((*it2)->rip.thread);
			if (evaluatable(c[x].second, it->second, availThreads, cfg))
				evalable[it->first].insert(c[x].second);
		}
	}


	/* Just find all of the things which are evaluatable at X but
	   not at some of X's predecessors, for any instruction X.  I'm
	   not entirely convinced that that's *precisely* what we're
	   after, but it's a pretty reasonable approximation. */
	for (std::map<Instruction<ThreadRip> *, std::set<IRExpr *> >::iterator it = evalable.begin();
	     it != evalable.end();
	     it++) {
		Instruction<ThreadRip> *i = it->first;
		std::set<IRExpr *> &theoreticallyEvaluatable(evalable[i]);
		std::set<IRExpr *> &actuallyEvalHere((*this)[i]);
		std::set<Instruction<ThreadRip> *> &predecessors(pred[i]);
		std::set<Instruction<ThreadRip> *> *orderingPredecessors;

		if (happensBefore.happensBefore.count(i))
			orderingPredecessors = &happensBefore.happensBefore[i];
		for (std::set<IRExpr *>::iterator it2 = theoreticallyEvaluatable.begin();
		     it2 != theoreticallyEvaluatable.end();
		     it2++) {
			IRExpr *expr = *it2;
			bool takeIt = false;
			for (std::set<Instruction<ThreadRip> *>::iterator it3 = predecessors.begin();
			     !takeIt && it3 != predecessors.end();
			     it3++) {
				Instruction<ThreadRip> *predecessor = *it3;
				if (!evalable[predecessor].count(expr))
					takeIt = true;
			}
			/* If it's evaluatable at *any* happens-before
			   predecessor then we don't want to take it,
			   because happens-before edges are always
			   satisfied and it's therefore certain that
			   it will have already been evaluated. */
			if (takeIt && orderingPredecessors) {
				for (std::set<Instruction<ThreadRip> *>::iterator it3 = orderingPredecessors->begin();
				     takeIt && it3 != orderingPredecessors->end();
				     it3++) {
					if (evalable[*it3].count(expr))
						takeIt = false;
				}
			}
			if (takeIt) {
				printf("Eval ");
				ppIRExpr(expr, stdout);
				printf(" at %d:%lx\n", i->rip.thread, i->rip.rip);
				actuallyEvalHere.insert(expr);
			}
		}
	}
}

class ClientRip {
public:
	unsigned long rip;
	ClientRip(unsigned long _rip)
		: rip(_rip)
	{}

	ClientRip()
		: rip(0)
	{}
	bool operator<(const ClientRip &k) const { return rip < k.rip; }
	bool operator!=(const ClientRip &k) const { return *this < k || k < *this; }
	bool operator==(const ClientRip &k) const { return !(*this != k); }
};

class EnforceCrashPatchFragment : public PatchFragment<ClientRip> {
	struct slot_t {
		slot_t(int _i) : i(_i) {}
		int i;
	};
	slot_t next_slot;
	/* Mapping from expressions to the slots in which we've
	 * stashed them. */
	std::map<IRExpr *, slot_t> exprsToSlots;
	/* Mapping from instructions to the expressions which we need
	   to stash at those instructions. */
	std::map<Instruction<ClientRip> *, std::set<IRExpr *> > &neededExpressions;

	void emitInstruction(Instruction<ClientRip> *i);
	slot_t allocateSlot() {
		slot_t r = next_slot;
		next_slot.i++;
		return r;
	}
	void emitMovRegToSlot(unsigned offset, slot_t slot);
	
public:
	EnforceCrashPatchFragment(std::map<Instruction<ClientRip> *, std::set<IRExpr *> > &_neededExpressions)
		: PatchFragment<ClientRip>(),
		  next_slot(0),
		  exprsToSlots(),
		  neededExpressions(_neededExpressions)
	{}
};

static unsigned
vexRegOffsetToRegIdx(unsigned offset)
{
	switch (offset) {
	case OFFSET_amd64_RAX: return 0;
	case OFFSET_amd64_RCX: return 1;
	case OFFSET_amd64_RDX: return 2;
	case OFFSET_amd64_RBX: return 3;
	case OFFSET_amd64_RSP: return 4;
	case OFFSET_amd64_RBP: return 5;
	case OFFSET_amd64_RSI: return 6;
	case OFFSET_amd64_RDI: return 7;
	case OFFSET_amd64_R8: return 8;
	case OFFSET_amd64_R9: return 9;
	case OFFSET_amd64_R10: return 10;
	case OFFSET_amd64_R11: return 11;
	case OFFSET_amd64_R12: return 12;
	case OFFSET_amd64_R13: return 13;
	case OFFSET_amd64_R14: return 14;
	case OFFSET_amd64_R15: return 15;
	default:
		abort();
	}

}
void
EnforceCrashPatchFragment::emitMovRegToSlot(unsigned offset, slot_t slot)
{
	/* gs prefix */
	emitByte(0x65);
	emitMovRegisterToModrm(vexRegOffsetToRegIdx(offset),
			       PatchFragment<ClientRip>::ModRM::absoluteAddress(slot.i * 8));
}

void
EnforceCrashPatchFragment::emitInstruction(Instruction<ClientRip> *i)
{
	std::set<IRExpr *> *neededExprs = NULL;
	if (neededExpressions.count(i)) {
		neededExprs = &neededExpressions[i];
		/* Need to emit gunk to store the appropriate
		   generated expression.  That'll either be a simple
		   register access or a memory load of some sort. */
		for (std::set<IRExpr *>::iterator it = neededExprs->begin();
		     it != neededExprs->end();
		     it++) {
			IRExpr *e = *it;
			assert(!exprsToSlots.count(e));
			if (e->tag == Iex_Get) {
				/* Easy case: just store the register in its slot */
				slot_t s = allocateSlot();
				exprsToSlots.insert(
					std::pair<IRExpr *, slot_t>(e, s));
				emitMovRegToSlot(e->Iex.Get.offset, s);
			} else if (e->tag == Iex_ClientCall) {
				/* Do this after emitting the instruction */
			} else {
				assert(e->tag == Iex_Load);
				/* Much more difficult case.  This
				   depends on the type of instruction
				   which we're looking at. */
#warning write me
			}
		}
	}

#if 0
	if (expressionEvalPoints.count(i->rip)) {
		std::set<IRExpr *> &expressionsToEval(expressionEvalPoints[i->rip]);

		for (std::set<IRExpr *>::iterator it = expressionsToEval.begin();
		     it != expresionsToEval.end();
		     it++)
			emitCheckExpressionOrEscape(*it, i->rip);
	}
#endif

	PatchFragment<ClientRip>::emitInstruction(i);

	if (neededExprs) {
		for (std::set<IRExpr *>::iterator it = neededExprs->begin();
		     it != neededExprs->end();
		     it++) {
			IRExpr *e = *it;
			if (e->tag == Iex_Get) {
				/* Already handled */
			} else if (e->tag == Iex_ClientCall) {
				/* The result of the call should now be in %rax */
				slot_t s = allocateSlot();
				exprsToSlots.insert(
					std::pair<IRExpr *, slot_t>(e, s));
				emitMovRegToSlot(0, s);
			} else {
				assert(e->tag == Iex_Load);
			}
		}
	}
}

ClientRip threadRipToClientRip(const ThreadRip &k)
{
	return ClientRip(k.rip);
}
unsigned long __trivial_hash_function(const ClientRip &k)
{
	return k.rip;
}

static void
partitionCrashCondition(DNF_Conjunction &c, FreeVariableMap &fv,
			std::map<unsigned, ThreadRip> &roots,
			AddressSpace *as)
{
	/* Figure out what we actually need to keep track of */
	std::set<IRExpr *> neededExpressions;
	for (unsigned x = 0; x < c.size(); x++)
		enumerateNeededExpressions(c[x].second, neededExpressions);

	/* and where the needed expressions are calculated */
	std::set<ThreadRip> neededRips;
	for (std::set<IRExpr *>::iterator it = neededExpressions.begin();
	     it != neededExpressions.end();
	     it++) {
		IRExpr *e = *it;
		if (e->tag == Iex_Get) {
			neededRips.insert(roots[e->Iex.Get.tid]);
			printf("Demand rip %d:%lx for register expression\n",
			       roots[e->Iex.Get.tid].thread,
			       roots[e->Iex.Get.tid].rip);
		} else if (e->tag == Iex_ClientCall) {
			neededRips.insert(e->Iex.ClientCall.callSite);
		} else if (e->tag == Iex_Load) {
			neededRips.insert(e->Iex.Load.rip);
		} else if (e->tag == Iex_HappensBefore) {
			printf("Demand RIPs %d:%lx, %d:%lx\n",
			       e->Iex.HappensBefore.before->rip.thread,
			       e->Iex.HappensBefore.before->rip.rip,
			       e->Iex.HappensBefore.after->rip.thread,
			       e->Iex.HappensBefore.after->rip.rip);
			neededRips.insert(e->Iex.HappensBefore.before->rip);
			neededRips.insert(e->Iex.HappensBefore.after->rip);
		} else {
			abort();
		}
	}

	/* Build the CFG */
	EnforceCrashCFG *cfg = new EnforceCrashCFG(as, neededRips);
	for (std::map<unsigned, ThreadRip>::iterator it = roots.begin();
	     it != roots.end();
	     it++) {
		printf("Root %d:%lx\n", it->second.thread, it->second.rip);
		cfg->add_root(it->second, 100);
	}
	cfg->doit();
	
	happensAfterMapT happensAfter(c, cfg);

	/* Build an instruction predecessor map */
	predecessorMapT predecessorMap(cfg);

	std::set<Instruction<ThreadRip> *> neededInstructions;
	for (std::set<ThreadRip>::iterator it = neededRips.begin();
	     it != neededRips.end();
	     it++)
		neededInstructions.insert(cfg->ripToInstr->get(*it));

	/* Figure out where the various instructions become
	 * available. */
	instructionDominatorMapT instrDominatorMap(cfg, predecessorMap, happensAfter, neededInstructions);

	/* Now turn that into a map showing where the actual
	 * expressions become available. */
	expressionDominatorMapT exprDominatorMap(instrDominatorMap, c, predecessorMap, happensAfter, cfg);

	/* The patch needs to be built in direct RIP space, rather
	 * than in ThreadRip space.  That means we need to degrade the
	 * CFG. */
	CFG<ClientRip> *degradedCfg;
	degradedCfg = cfg->degrade<ClientRip, threadRipToClientRip>();

	/* Figure out where we need to stash the various necessary
	 * expressions. */
	std::map<Instruction<ClientRip> *, std::set<IRExpr *> > exprStashPoints;
	for (std::set<IRExpr *>::iterator it = neededExpressions.begin();
	     it != neededExpressions.end();
	     it++) {
		IRExpr *e = *it;
		if (e->tag == Iex_Get) {
			exprStashPoints[degradedCfg->ripToInstr->get(threadRipToClientRip(roots[e->Iex.Get.tid]))].insert(e);
		} else if (e->tag == Iex_ClientCall) {
			exprStashPoints[degradedCfg->ripToInstr->get(threadRipToClientRip(e->Iex.ClientCall.callSite))].insert(e);
		} else if (e->tag == Iex_Load) {
			exprStashPoints[degradedCfg->ripToInstr->get(threadRipToClientRip(e->Iex.Load.rip))].insert(e);
		} else if (e->tag == Iex_HappensBefore) {
			/* These don't really get stashed in any useful sense */
		} else {
			abort();
		}
	}

	/* Now build the patch */
	EnforceCrashPatchFragment *pf = new EnforceCrashPatchFragment(exprStashPoints);
	pf->fromCFG(degradedCfg);
	std::set<ClientRip> entryPoints;
	for (std::map<unsigned, ThreadRip>::iterator it = roots.begin();
	     it != roots.end();
	     it++)
		entryPoints.insert(threadRipToClientRip(it->second));
	printf("Fragment: %s\n", pf->asC("ident", entryPoints));
}

static IRExpr *
zapFreeVariables(IRExpr *src, FreeVariableMap &fv)
{
	ShortCircuitFvTransformer trans(fv);
	return trans.transformIRExpr(src);
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

	std::map<unsigned, ThreadRip> roots;
	roots[summary->loadMachine->tid] = ThreadRip::mk(summary->loadMachine->tid, summary->loadMachine->origin);
	
	FreeVariableMap m(summary->loadMachine->freeVariables);
	zapBindersAndFreeVariables(m, summary->loadMachine);
	for (unsigned x = 0; x < summary->storeMachines.size(); x++) {
		FreeVariableMap n(summary->storeMachines[x]->machine->freeVariables);
		zapBindersAndFreeVariables(n, summary->storeMachines[x]->machine);
		m.merge(n);
		roots[summary->storeMachines[x]->machine->tid] =
			ThreadRip::mk(summary->storeMachines[x]->machine->tid,
				      summary->storeMachines[x]->machine->origin);
	}

	requirement = internIRExpr(zapFreeVariables(requirement, m));
	fprintf(_logfile, "After free variable removal:\n");
	ppIRExpr(requirement, _logfile);
	fprintf(_logfile, "\n");

	DNF_Disjunction d;
	if (TIMEOUT || !dnf(requirement, d)) {
		fprintf(_logfile, "failed to convert to DNF\n");
		return 1;
	}
	printDnf(d, _logfile);
       
	for (unsigned x = 0; x < d.size(); x++) {
		printf("Examine clause %d\n", x);
		partitionCrashCondition(d[x], m, roots, ms->addressSpace);
	}

	return 0;
}
