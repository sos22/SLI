/* Various bits for manipulating expressions in explicit CNF form. */
#include <map>

#include "sli.h"
#include "cnf.hpp"
#include "offline_analysis.hpp"
#include "intern.hpp"

#include "libvex_prof.hpp"

#define CNF_MAX_DISJUNCTION 10000

/* Do this with a macro to avoid confusing emacs */
#define START_NAMESPACE(name) namespace name {
#define END_NAMESPACE(name) }
START_NAMESPACE(__cnf)

/* The ordering we use for CNF disjunctions works like this:

   -- If a is a subset of b (i.e. a implies b) then a is less than b.
   -- If a is a superset of b (i.e. b implies a) then a is greather than b.
   -- Otherwise, if they're unordered by the subset ordering, we
      using a per-element dictionary ordering.

   This enumeration gives every possible result.
*/
enum cnf_ordering {
	cnf_subset = -2,
	cnf_less = -1,
	cnf_eq = 0,
	cnf_greater = 1,
	cnf_superset = 2
};

class CNF_Disjunction;

static cnf_ordering compare_cnf_disjunctions(const CNF_Disjunction &a, const CNF_Disjunction &b);

class CNF_Atom : public std::pair<bool, IRExpr *>, public PrettyPrintable {
public:
	CNF_Atom(bool b, IRExpr *e)
		: std::pair<bool, IRExpr *>(b, e)
	{}
	void prettyPrint(FILE *f) const {
		if (first)
			fprintf(f, "!");
		else
			fprintf(f, " ");
		ppIRExpr(second, f);
	}
};
class CNF_Disjunction : public std::vector<CNF_Atom>, public PrettyPrintable {
public:
	void prettyPrint(FILE *f) const {
		for (auto it = begin(); it != end(); it++) {
			if (it != begin())
				fprintf(f, "|||||||||||\n");
			it->prettyPrint(f);
		}
		fprintf(f, "\n");
	}
};
class CNF_Conjunction : public std::vector<CNF_Disjunction>, public PrettyPrintable {
public:
	void prettyPrint(FILE *f) const {
		for (auto it = begin(); it != end(); it++) {
			if (it != begin())
				fprintf(f, "\n&&&&&&&&&&&&\n");
			it->prettyPrint(f);
		}
		fprintf(f, "\n");
	}
};

static void
sanity_check(const CNF_Disjunction &a)
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
sanity_check(const CNF_Conjunction &a)
{
#ifndef NDEBUG
	if (a.size() == 0)
		return;
	for (unsigned x = 0; x < a.size(); x++)
		sanity_check(a[x]);
	for (unsigned x = 0; x < a.size() - 1; x++)
		assert(compare_cnf_disjunctions(a[x], a[x+1]) < 0);
#endif
}

static bool cnf(IRExpr *e, CNF_Conjunction &out);

static int
compare_cnf_atom(const CNF_Atom &a, const CNF_Atom &b)
{
	/* Use an ordering which puts A and ~A together. */
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

static cnf_ordering
compare_cnf_disjunctions(const CNF_Disjunction &a, const CNF_Disjunction &b)
{
	auto it1 = a.begin();
	auto it2 = b.begin();

	while (it1 != a.end() && it2 != b.end()) {
		switch (compare_cnf_atom(*it1, *it2)) {
		case -1:
			/* Here we have an element of a which less
			   than the matching element of b.  Either a
			   is a superset of b or a is less than b.
			   Find out which. */
			while (it1 != a.end() && it2 != b.end()) {
				switch (compare_cnf_atom(*it1, *it2)) {
				case -1:
					it1++;
					break;
				case 0:
					it1++;
					it2++;
					break;
				case 1:
					return cnf_less;
				}
			}
			if (it2 == b.end())
				return cnf_superset;
			else
				return cnf_less;
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
				switch (compare_cnf_atom(*it1, *it2)) {
				case -1:
					return cnf_greater;
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
				return cnf_subset;
			else
				return cnf_greater;
		default:
			abort();
		}
	}
	if (it1 == a.end() && it2 == b.end())
		return cnf_eq;
	if (it1 == a.end() && it2 != b.end())
		return cnf_subset;
	if (it1 != a.end() && it2 == b.end())
		return cnf_superset;
	abort();
}

/* Set @out to @src1 | @src2.  Return false if we find that the result
   is definitely true, and true otherwise. */
static bool
merge_disjunctions(const CNF_Disjunction &src1,
		   const CNF_Disjunction &src2,
		   CNF_Disjunction &out)
{
	sanity_check(src1);
	sanity_check(src2);
	out.reserve(src1.size() + src2.size());
	auto it1 = src1.begin();
	auto it2 = src2.begin();
	while (it1 != src1.end() && it2 != src2.end()) {
		if (it1->second == it2->second) {
			if (it1->first != it2->first) {
				/* x | ~x -> definitely true */
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

/* Set @out to @src1 & @src2. */
static void
merge_conjunctions(const CNF_Conjunction &src1,
		   const CNF_Conjunction &src2,
		   CNF_Conjunction &out)
{
	sanity_check(src1);
	sanity_check(src2);
	out.clear();
	out.reserve(src1.size() + src2.size());
	auto it1 = src1.begin();
	auto it2 = src2.begin();
	while (it1 != src1.end() && it2 != src2.end()) {
		switch (compare_cnf_disjunctions(*it1, *it2)) {
		case cnf_subset: /* *it1 subsumes *it2, so drop *it2 */
		case cnf_eq: /* They're equal, it doesn't matter which one we pick */
			sanity_check(out);
			out.push_back(*it1);
			sanity_check(out);
			it1++;
			it2++;
			break;
		case cnf_superset: /* *it2 subsumes *it1, so drop *it1 */
			out.push_back(*it2);
			it1++;
			it2++;
			break;
		case cnf_less:
			sanity_check(out);
			out.push_back(*it1);
			sanity_check(out);
			it1++;
			break;
		case cnf_greater:
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

/* Set @out to @src & @out */
static void
insert_disjunction(const CNF_Disjunction &src, CNF_Conjunction &out)
{
	unsigned x;
	unsigned nr_killed = 0;
	sanity_check(out);
	sanity_check(src);
	for (x = 0; x < out.size(); x++) {
		switch (compare_cnf_disjunctions(out[x], src)) {
		case cnf_subset:
		case cnf_eq:
			/* This existing output clause subsumes the
			 * new one we want to insert. */
			return;
		case cnf_superset:
			/* The new clause subsumes this existing
			   output clause, so replace it. */
			out[x].clear();
			nr_killed ++;
			break;
		case cnf_less:
			assert(compare_cnf_disjunctions(src, out[x]) == cnf_greater);
			continue;
		case cnf_greater:
			assert(compare_cnf_disjunctions(src, out[x]) == cnf_less);
			goto out1;
		}
	}
out1:
	if (nr_killed > out.size() / 2) {
		CNF_Conjunction new_out;
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


/* Convert @out to @out | @this_one, maintaining conjunctive normal
 * form. */
static bool
cnf_or(const CNF_Conjunction &this_one, CNF_Conjunction &out)
{
	CNF_Conjunction new_out;
	sanity_check(out);
	sanity_check(this_one);
	if (TIMEOUT || out.size() * this_one.size() > CNF_MAX_DISJUNCTION)
		return false;
	new_out.reserve(out.size() * this_one.size());
	for (unsigned x = 0; x < out.size(); x++) {
		CNF_Disjunction &existing_disj(out[x]);
		for (unsigned z = 0; z < this_one.size(); z++) {
			sanity_check(new_out);
			CNF_Disjunction new_disj;
			if (merge_disjunctions(this_one[z], existing_disj, new_disj)) {
				sanity_check(new_out);
				insert_disjunction(new_disj, new_out);
				sanity_check(new_out);
			} else {
				/* the disjunction includes both x and
				   !x, for some x, so should be
				   dropped */
			}
		}
	}
	out = new_out;
	sanity_check(out);
	return true;
}

/* Disjoin the fragments together, convert to CNF, and then place the
   results in @out.  Can fail if @out looks ``too big'', in which case
   we return false; otherwise return true. */
static bool
cnf_or(IRExpr **fragments, int nr_fragments, CNF_Conjunction &out)
{
	if (TIMEOUT)
		return false;
	if (nr_fragments == 0)
		return true;
	if (out.size() == 0) {
		return cnf(fragments[0], out) &&
			cnf_or(fragments + 1, nr_fragments - 1, out);
	}
	sanity_check(out);
	CNF_Conjunction this_one;
	cnf(fragments[0], this_one);
	if (!cnf_or(this_one, out))
		return false;

	return cnf_or(fragments + 1, nr_fragments - 1, out);
}

/* Invert @conf and store it in @out, which must start out empty. */
static bool
cnf_invert(const CNF_Disjunction &conj, CNF_Conjunction &out)
{
	assert(out.size() == 0);
	out.reserve(conj.size());
	for (unsigned x = 0; x < conj.size(); x++) {
		CNF_Disjunction c;
		c.push_back(CNF_Atom(!conj[x].first, conj[x].second));
		insert_disjunction(c, out);
	}
	sanity_check(out);
	return true;
}

static bool
cnf_invert(const CNF_Conjunction &in, CNF_Conjunction &out)
{
	assert(out.size() == 0);
	assert(in.size() != 0);

	/* Start by converting the first clause */
	if (!cnf_invert(in[0], out))
		return false;

	/* Now we convert the remaining clauses one at a time, or'ing
	   them in as we go.  The invariant here is that out = ~(in[0:x]),
	   where the slice notation is supposed to mean that we consider
	   the first x clauses only. */
	for (unsigned x = 1; x < in.size(); x++) {
		CNF_Conjunction r;
		if (TIMEOUT || !cnf_invert(in[x], r))
			return false;

		/* out = ~(in[0:x-1]), r = ~in[x]. */
		if (!cnf_or(r, out))
			return false;

		/* out = ~in[x] | ~(in[0:x-1])
		       = ~(in[x] & in[0:x-1])
		       = ~(in[0:x])

		   so invariant is preserved.
		*/
	}
	sanity_check(out);
	return true;
}

/* Convert @e to conjunctive normal form. */
static bool
cnf(IRExpr *e, CNF_Conjunction &out)
{
	out.clear();
	if (e->tag == Iex_Unop &&
	    ((IRExprUnop *)e)->op == Iop_Not1) {
		CNF_Conjunction r;
		return cnf(((IRExprUnop *)e)->arg, r) &&
			cnf_invert(r, out);
	}

	if (e->tag == Iex_Associative) {
		if (((IRExprAssociative *)e)->op == Iop_And1) {
			for (int x = 0; x < ((IRExprAssociative *)e)->nr_arguments; x++) {
				if (TIMEOUT)
					return false;
				CNF_Conjunction r;
				if (!cnf(((IRExprAssociative *)e)->contents[x], r))
					return false;
				CNF_Conjunction t(out);
				merge_conjunctions(r, t, out);
			}
			sanity_check(out);
			return true;
		} else if (((IRExprAssociative *)e)->op == Iop_Or1) {
			return cnf_or(((IRExprAssociative *)e)->contents,
				       ((IRExprAssociative *)e)->nr_arguments,
				       out);
		}
	}

	/* Anything else cannot be represented in DNF, so gets an
	 * atom */
	CNF_Disjunction c;
	c.push_back(CNF_Atom(false, e));
	out.push_back(c);
	sanity_check(out);
	return true;
}

#if 0
/* A different kind of simplification: assume that @inp is a boolean
   expression, and consists of some tree of And1, Or1, and Not1
   expressions with other stuff at the leaves.  Treat all of the other
   stuff as opaque boolean variables, and then convert to CNF.  Try to
   simplify it there.  If we make any reasonable progress, convert
   back to the standard IRExpr form and return the result.  Otherwise,
   just return @inp. */
IRExpr *
simplifyIRExprAsBoolean(IRExpr *inp, bool *done_something)
{
	__set_profiling(simplifyIRExprAsBoolean);
	
	if (!((inp->tag == Iex_Unop &&
	       ((IRExprUnop *)inp)->op == Iop_Not1) ||
	      (inp->tag == Iex_Associative &&
	       (((IRExprAssociative *)inp)->op == Iop_Or1 ||
		((IRExprAssociative *)inp)->op == Iop_And1))))
		return inp;

	inp = internIRExpr(inp);

	std::map<int, IRExpr *> varsToExprs;
	CnfExpression *root;
	IRExprToCnf(inp, &root, varsToExprs);
	IRExprTransformer t;
	IRExpr *r;
	{
		__set_profiling(cnf_as_irexpr);
		r = root->asIRExpr(varsToExprs, t);
	}
	if (exprComplexity(r) < exprComplexity(inp)) {
		*done_something = true;
		return r;
	} else
		return inp;
}

#endif

END_NAMESPACE(__cnf)

int
main(int argc, char **argv)
{
	init_sli();

	IRExpr *exp = readIRExpr(open(argv[1], O_RDONLY));

	printf("Input expression: ");
	ppIRExpr(exp, stdout);
	printf("\n");

	__cnf::CNF_Conjunction res;

	__cnf::cnf(exp, res);

	res.prettyPrint(stdout);

	return 0;
}
