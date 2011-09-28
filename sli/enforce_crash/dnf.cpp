#include <stdio.h>

#include "sli.h"
#include "dnf.hpp"

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
#ifndef NDEBUG
	assert(a.size() > 0);
	for (unsigned x = 0; x < a.size() - 1; x++) {
		assert(a[x].second != a[x+1].second);
		assert(a[x].second < a[x+1].second);
	}
#endif
}
static void
sanity_check(const DNF_Disjunction &a)
{
#ifndef NDEBUG
	if (a.size() == 0)
		return;
	unsigned x;
	for (x = 0; x < a.size() - 1; x++) {
		sanity_check(a[x]);
		assert(compare_dnf_conjunctions(a[x], a[x+1]) < 0);
	}
	sanity_check(a[x]);
#endif
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
bool
dnf(IRExpr *e, DNF_Disjunction &out)
{
	check_memory_usage();
	out.clear();
	if (e->tag == Iex_Unop &&
	    ((IRExprUnop *)e)->op == Iop_Not1) {
		DNF_Disjunction r;
		return dnf(((IRExprUnop *)e)->arg, r) &&
			dnf_invert(r, out);
	}

	if (e->tag == Iex_Associative) {
		if (((IRExprAssociative *)e)->op == Iop_Or1) {
			for (int x = 0; x < ((IRExprAssociative *)e)->nr_arguments; x++) {
				if (TIMEOUT)
					return false;
				DNF_Disjunction r;
				if (!dnf(((IRExprAssociative *)e)->contents[x], r))
					return false;
				DNF_Disjunction t(out);
				merge_disjunctions(r, t, out);
			}
			sanity_check(out);
			return true;
		} else if (((IRExprAssociative *)e)->op == Iop_And1) {
			return dnf_and(((IRExprAssociative *)e)->contents,
				       ((IRExprAssociative *)e)->nr_arguments,
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

void
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
