/* Various bits for manipulating expressions in explicit CNF form. */
#include <map>

#include "sli.h"
#include "cnf.hpp"
#include "offline_analysis.hpp"
#include "intern.hpp"

#include "libvex_prof.hpp"

#define NF_MAX_DISJUNCTION 10000

/* Do this with a macro to avoid confusing emacs */
#define START_NAMESPACE(name) namespace name {
#define END_NAMESPACE(name) }
START_NAMESPACE(__cnf)

#include "nf.hpp"

static void check_memory_usage(void) {}
static bool nf(IRExpr *e, NF_Expression &out, IROp expressionOp, IROp termOp);

static nf_ordering compare_nf_terms(const NF_Term &a, const NF_Term &b);

void
NF_Term::prettyPrint(FILE *f) const
{
	for (auto it = begin(); it != end(); it++) {
		if (it != begin())
			fprintf(f, "|||||||||||\n");
		it->prettyPrint(f);
	}
	fprintf(f, "\n");
}

void
NF_Expression::prettyPrint(FILE *f) const
{
	for (auto it = begin(); it != end(); it++) {
		if (it != begin())
			fprintf(f, "\n&&&&&&&&&&&&\n");
		it->prettyPrint(f);
	}
	fprintf(f, "\n");
}

static void
sanity_check(const NF_Term &a)
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
sanity_check(const NF_Expression &a)
{
#ifndef NDEBUG
	if (a.size() == 0)
		return;
	for (unsigned x = 0; x < a.size(); x++)
		sanity_check(a[x]);
	for (unsigned x = 0; x < a.size() - 1; x++)
		assert(compare_nf_terms(a[x], a[x+1]) < 0);
#endif
}

static int
compare_nf_atom(const NF_Atom &a, const NF_Atom &b)
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

static nf_ordering
compare_nf_terms(const NF_Term &a, const NF_Term &b)
{
	auto it1 = a.begin();
	auto it2 = b.begin();

	while (it1 != a.end() && it2 != b.end()) {
		switch (compare_nf_atom(*it1, *it2)) {
		case -1:
			/* Here we have an element of a which less
			   than the matching element of b.  Either a
			   is a superset of b or a is less than b.
			   Find out which. */
			while (it1 != a.end() && it2 != b.end()) {
				switch (compare_nf_atom(*it1, *it2)) {
				case -1:
					it1++;
					break;
				case 0:
					it1++;
					it2++;
					break;
				case 1:
					return nf_less;
				}
			}
			if (it2 == b.end())
				return nf_superset;
			else
				return nf_less;
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
				switch (compare_nf_atom(*it1, *it2)) {
				case -1:
					return nf_greater;
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
				return nf_subset;
			else
				return nf_greater;
		default:
			abort();
		}
	}
	if (it1 == a.end() && it2 == b.end())
		return nf_eq;
	if (it1 == a.end() && it2 != b.end())
		return nf_subset;
	if (it1 != a.end() && it2 == b.end())
		return nf_superset;
	abort();
}

/* Set @out to @src1 | @src2.  Return false if we find that the result
   is definitely true, and true otherwise. */
static bool
merge_terms(const NF_Term &src1,
	    const NF_Term &src2,
	    NF_Term &out)
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
merge_expressions(const NF_Expression &src1,
		  const NF_Expression &src2,
		  NF_Expression &out)
{
	sanity_check(src1);
	sanity_check(src2);
	out.clear();
	out.reserve(src1.size() + src2.size());
	auto it1 = src1.begin();
	auto it2 = src2.begin();
	while (it1 != src1.end() && it2 != src2.end()) {
		switch (compare_nf_terms(*it1, *it2)) {
		case nf_subset: /* *it1 subsumes *it2, so drop *it2 */
		case nf_eq: /* They're equal, it doesn't matter which one we pick */
			sanity_check(out);
			out.push_back(*it1);
			sanity_check(out);
			it1++;
			it2++;
			break;
		case nf_superset: /* *it2 subsumes *it1, so drop *it1 */
			out.push_back(*it2);
			it1++;
			it2++;
			break;
		case nf_less:
			sanity_check(out);
			out.push_back(*it1);
			sanity_check(out);
			it1++;
			break;
		case nf_greater:
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
insert_term(const NF_Term &src, NF_Expression &out)
{
	unsigned x;
	unsigned nr_killed = 0;
	sanity_check(out);
	sanity_check(src);
	for (x = 0; x < out.size(); x++) {
		switch (compare_nf_terms(out[x], src)) {
		case nf_subset:
		case nf_eq:
			/* This existing output clause subsumes the
			 * new one we want to insert. */
			return;
		case nf_superset:
			/* The new clause subsumes this existing
			   output clause, so replace it. */
			out[x].clear();
			nr_killed ++;
			break;
		case nf_less:
			assert(compare_nf_terms(src, out[x]) == nf_greater);
			continue;
		case nf_greater:
			assert(compare_nf_terms(src, out[x]) == nf_less);
			goto out1;
		}
	}
out1:
	if (nr_killed > out.size() / 2) {
		NF_Expression new_out;
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


/* Convert @out to @out {op} @this_one, maintaining conjunctive normal
 * form.  {op} is or for CNF, or and for DNF. */
static bool
nf_countermerge(const NF_Expression &this_one, NF_Expression &out)
{
	NF_Expression new_out;
	check_memory_usage();
	sanity_check(out);
	if (TIMEOUT || out.size() * this_one.size() > NF_MAX_EXPRESSION)
		return false;
	new_out.reserve(out.size() * this_one.size());
	for (unsigned x = 0; x < out.size(); x++) {
		NF_Term &existing_term(out[x]);
		for (unsigned z = 0; z < this_one.size(); z++) {
			sanity_check(new_out);
			NF_Term new_term;
			if (merge_terms(this_one[z], existing_term, new_term)) {
				sanity_check(new_out);
				insert_term(new_term, new_out);
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

/* Disjoin or conjoin the fragments together, convert to NF, and then
   place the results in @out.  Can fail if @out looks ``too big'', in
   which case we return false; otherwise return true.  Disjoin for
   CNF, and conjoin for DNF. */
static bool
nf_counterjoin(IRExpr **fragments, int nr_fragments, NF_Expression &out,
	       IROp expressionOp, IROp termOp)
{
	check_memory_usage();
	if (TIMEOUT)
		return false;
	if (nr_fragments == 0)
		return true;
	if (out.size() == 0) {
		return nf(fragments[0], out, expressionOp, termOp) &&
			nf_counterjoin(fragments + 1, nr_fragments - 1, out,
				       expressionOp, termOp);
	}
	sanity_check(out);
	NF_Expression this_one;
	nf(fragments[0], this_one, expressionOp, termOp);
	if (!nf_countermerge(this_one, out))
		return false;

	return nf_counterjoin(fragments + 1, nr_fragments - 1, out,
			      expressionOp, termOp);
}

/* Invert @conf and store it in @out, which must start out empty. */
static bool
nf_invert(const NF_Term &conj, NF_Expression &out)
{
	assert(out.size() == 0);
	out.reserve(conj.size());
	for (unsigned x = 0; x < conj.size(); x++) {
		NF_Term c;
		c.push_back(NF_Atom(!conj[x].first, conj[x].second));
		insert_term(c, out);
	}
	sanity_check(out);
	return true;
}

static bool
nf_invert(const NF_Expression &in, NF_Expression &out)
{
	assert(out.size() == 0);
	assert(in.size() != 0);

	check_memory_usage();
	/* Start by converting the first clause */
	if (!nf_invert(in[0], out))
		return false;

	/* Now we convert the remaining clauses one at a time, or'ing
	   them in as we go.  The invariant here is that out = ~(in[0:x]),
	   where the slice notation is supposed to mean that we consider
	   the first x clauses only. */
	for (unsigned x = 1; x < in.size(); x++) {
		NF_Expression r;
		if (TIMEOUT || !nf_invert(in[x], r))
			return false;

		/* out = ~(in[0:x-1]), r = ~in[x]. */
		if (!nf_countermerge(r, out))
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
nf(IRExpr *e, NF_Expression &out, IROp expressionOp, IROp termOp)
{
	check_memory_usage();
	out.clear();
	if (e->tag == Iex_Unop &&
	    ((IRExprUnop *)e)->op == Iop_Not1) {
		NF_Expression r;
		return nf(((IRExprUnop *)e)->arg, r, expressionOp, termOp) &&
			nf_invert(r, out);
	}

	if (e->tag == Iex_Associative) {
		if (((IRExprAssociative *)e)->op == expressionOp) {
			for (int x = 0; x < ((IRExprAssociative *)e)->nr_arguments; x++) {
				if (TIMEOUT)
					return false;
				NF_Expression r;
				if (!nf(((IRExprAssociative *)e)->contents[x], r,
					expressionOp, termOp))
					return false;
				NF_Expression t(out);
				merge_expressions(r, t, out);
			}
			sanity_check(out);
			return true;
		} else if (((IRExprAssociative *)e)->op == termOp) {
			return nf_counterjoin(((IRExprAssociative *)e)->contents,
					      ((IRExprAssociative *)e)->nr_arguments,
					      out,
					      expressionOp,
					      termOp);
		}
	}

	/* Anything else cannot be represented in DNF, so gets an
	 * atom */
	NF_Term c;
	c.push_back(NF_Atom(false, e));
	out.push_back(c);
	sanity_check(out);
	return true;
}

static bool
cnf(IRExpr *e, NF_Expression &out)
{
	return nf(e, out, Iop_And1, Iop_Or1);
}

#if 0
/* A different kind of simplification: assume that @inp is a boolean
   expression, and consists of some tree of And1, Or1, and Not1
   expressions with other stuff at the leaves.  Treat all of the other
   stuff as opaque boolean variables, and then convert to NF.  Try to
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
	NfExpression *root;
	IRExprToNf(inp, &root, varsToExprs);
	IRExprTransformer t;
	IRExpr *r;
	{
		__set_profiling(nf_as_irexpr);
		r = root->asIRExpr(varsToExprs, t);
	}
	if (exprComplexity(r) < exprComplexity(inp)) {
		*done_something = true;
		return r;
	} else
		return inp;
}

#endif

END_NAMESPACE(__nf)

int
main(int argc, char **argv)
{
	init_sli();

	IRExpr *exp = readIRExpr(open(argv[1], O_RDONLY));

	printf("Input expression: ");
	ppIRExpr(exp, stdout);
	printf("\n");

	__cnf::NF_Expression res;

	__cnf::cnf(exp, res);

	res.prettyPrint(stdout);

	return 0;
}
