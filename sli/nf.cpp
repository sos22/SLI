#include "sli.h"
#include "nf.hpp"

/* Lots and lots of calls to sanity_check().  This makes things very
   slow, but can catch some bugs much more quickly. */
#undef EXTRA_SANITY

/* There are two interesting normal forms here, CNF and DNF.  They are
   very similar, except for using different operators and ``neutral''
   values.

   CNF:

   Term operator        == ||
   Empty term           == 0
   Unrepresentable term == 1
   Expression operator  == &&
   Empty expression     == 1
   Contradiction expression == 0
   
   DNF:

   Term operator        == &&
   Empty term           == 1
   Unrepresentable term == 0
   Expression operator  == ||
   Empty expression     == 0
   Contradiction expression == 1

   A contradiction expression means an expression which contains a
   single term where that term is empty.
*/
namespace __nf {
#if 0
}
#endif

#define NF_MAX_EXPRESSION 10000

static bool convert_to_nf(IRExpr *e, NF_Expression &out, IROp expressionOp, IROp termOp);
static void insert_term_destruct(NF_Term &src, NF_Expression &out);

/* The ordering we use for NF disjunctions works like this:

   -- If a is a subset of b (i.e. a implies b) then a is less than b.
   -- If a is a superset of b (i.e. b implies a) then a is greather than b.
   -- Otherwise, if they're unordered by the subset ordering, we compare
      them using a fallback ordering.  This reports a < b if a is smaller
      than b, a > b if a is larger than b, and uses a dictionary ordering
      if they're exactly the same size.

   This produces a total ordering.  The important property for proving
   this is that a \subset b implies that a is less than b under the
   fallback ordering.  If that's not true (e.g. if you use a pure
   dictionary order as your fallback, without the size qualification)
   then you potentially lose transitivity, which makes everything much
   harder.

   Proof that this is transitive:

   We need to show that if a < b and b < c then a < c.  If a is a
   subset of b and b is a subset of c then a must be a subset of c so
   this is trivial.  Likewise, if neither subsetting relationship
   holds then a must be less than b and b less than c under the
   fallback relationship, so a must be less than c under the fallback,
   and a < c, as desired.

   Assume that a \subset b but !(b \subset c).  We know that b < c, so
   b must be less than c under the fallback ordering, and we have a is
   less than b under the fallback ordering by the ``important
   property'' above, so a is less than c under the fallback property
   and a < c.  Conversely, if !(a \subset b) but b \subset c then we
   can establish a < c under the fallback the other way around and
   everything is still fine.
*/
enum nf_ordering {
	nf_subset = -2,
	nf_less = -1,
	nf_eq = 0,
	nf_greater = 1,
	nf_superset = 2
};

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

/* Compare two normal form terms according to the nf_ordering.  This
   is much more subtle than it looks. */
static nf_ordering
compare_nf_terms(const NF_Term &a, const NF_Term &b)
{
	if (a.size() < b.size()) {
		/* a is smaller than b.  Either a is less than b or a
		   is a subset of b.  Do a quick check to see if the
		   bloom filter can tell us which it is. */
		if (a.bloom.definitelyNotSubset(b.bloom)) {
			/* a is not a subset of b, so it must be less
			   than b. */
			return nf_less;
		}
	} else if (a.size() > b.size()) {
		/* Converse case. */
		if (b.bloom.definitelyNotSubset(a.bloom))
			return nf_greater;
	}
	
	auto it1 = a.begin();
	auto it2 = b.begin();

	while (it1 != a.end() && it2 != b.end()) {
		switch (compare_nf_atom(*it1, *it2)) {
		case -1:
			/* Here we have an element of a which less
			   than the matching element of b.  Either a
			   is a superset of b or we have to use the
			   fallback ordering.  This is moderately
			   fiddly, because we try to test both at the
			   same time. */

			if (a.size() <= b.size()) {
				/* a is smaller than b, so there's no
				   way that a can be greater than b
				   under the ordering or that a can be
				   a superset of b.  By control flow,
				   the only possible return values
				   from here are nf_greater, nf_less,
				   and nf_superset; combining the two
				   bits of knowledge, we know that
				   we're ultimately going to return
				   nf_less, so bypass it and just
				   return here. */
				return nf_less;
			}

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
					/* This element of b is
					   greater than the matching
					   element of a, and because
					   the elements are ordered we
					   know it has no match in a.
					   Therefore, b is not a
					   subset of a. */
					return nf_greater;
				default: abort();
				}
			}
			/* We've hit the end of one of a and b.  If
			   we've hit the end of b then that indicates
			   that a is b with at least one more thing
			   added i.e. a is a superset of b (this still
			   works if we hit the end of both at the same
			   time, because we must have found one such
			   extra element for the outer switch to take
			   us here). */
			if (it2 == b.end())
				return nf_superset;
			/* Hit end of a without consuming b, so we
			   don't have a subset or superset
			   relationship. */
			assert(it1 == a.end());
			return nf_greater;
		case 0:
			it1++;
			it2++;
			break;
		case 1:
			/* Opposite case: an element of a which is
			   greater than the matching element of b.  a
			   is either a subset of b or we must use the
			   fallback relationship. */
			if (a.size() >= b.size())
				return nf_greater;

			while (it1 != a.end() && it2 != b.end()) {
				switch (compare_nf_atom(*it1, *it2)) {
				case -1:
					/* Note that this one is
					   less-than rather than
					   less-than-or-equal, because
					   the outer switch found
					   something bigger in b. */
					return nf_less;
				case 0:
					it1++;
					it2++;
					break;
				case 1:
					it2++;
					break;
				default: abort();
				}
			}
			if (it1 == a.end())
				return nf_subset;
			else
				return nf_less;
		default:
			abort();
		}
	}
	/* Okay, we've hit the end of one or both of the expressions.
	   i.e. [a.begin(),it1) == [b.begin(), it2).  That means that
	   either a == b or a \subset b or b \subset a, depending on
	   whether it1 == a.end() and it2 == b.end().  Figure out
	   which. */
	if (it1 == a.end() && it2 == b.end()) {
		/* [a.begin(),a.end()) == [b.begin(), b.end()) implies
		   a == b */
		return nf_eq;
	}
	if (it1 == a.end() && it2 != b.end()) {
		/* [a.begin(),a.end()) == [b.begin(), !b.end()) means
		   that every element in a has a matching element in
		   b, but some elements in b have no match in a, i.e.
		   a is a subset of b. */
		return nf_subset;
	}
	if (it1 != a.end() && it2 == b.end()) {
		/* Converse case */
		return nf_superset;
	}
	abort();
}

static void
sanity_check(const NF_Term &a)
{
#ifndef NDEBUG
	if (a.size() == 0)
		return;
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
	if (a[0].size() == 0) {
		assert(a.size() == 1);
		return;
	}
	for (unsigned x = 0; x < a.size(); x++) {
		assert(a[x].size() > 0);
		sanity_check(a[x]);
	}
	for (unsigned x = 0; x < a.size() - 1; x++)
		assert(compare_nf_terms(a[x], a[x+1]) < 0);
#endif
}

static void
extra_sanity(const NF_Term &a
#ifndef EXTRA_SANITY
	     __attribute__((unused))
#endif
	     )
{
#ifdef EXTRA_SANITY
	sanity_check(a);
#endif
}

static void
extra_sanity(const NF_Expression &a
#ifndef EXTRA_SANITY
	     __attribute__((unused))
#endif
	     )
{
#ifdef EXTRA_SANITY
	sanity_check(a);
#endif
}

/* Set @out to @src1 `termOp` @src2.  Return false if the result is
   unrepresentable as a term in this normal norm (i.e. is definitely
   true for CNF or definitely false for DNF) and true otherwise. */
static bool
merge_terms(const NF_Term &src1,
	    const NF_Term &src2,
	    NF_Term &out)
{
	extra_sanity(src1);
	extra_sanity(src2);
	out.reserve(src1.size() + src2.size());
	auto it1 = src1.begin();
	auto it2 = src2.begin();
	while (it1 != src1.end() && it2 != src2.end()) {
		if (it1->second == it2->second) {
			if (it1->first != it2->first) {
				/* x `termOp` ~x -> unrepresentable */
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
	extra_sanity(out);
	return true;
}

/* Set @out to @out `expressionOp` @src.  @src must contain a single
   atom. */
static void
insert_atomic_term(const NF_Term &src, NF_Expression &out)
{
top:
	assert(src.size() == 1);
	const NF_Atom &atom(src[0]);

	/* First, check whether @out already has a relevant
	 * single-atom term. */
	unsigned x;
	for (x = 0; x < out.size() && out[x].size() == 1; x++) {
		if (out[x][0].second == atom.second) {
			/* Yes.  This is the easy case. */
			if (out[x][0].first == atom.first) {
				/* The existing term precisely matches
				   the thing we're inserting ->
				   nothing to do. */
			} else {
				/* The existing term is the inverse of
				   the thing we're inserting.  For
				   CNF, we want to build x && ~x,
				   which is 0, or an expression
				   containing a single empty term.
				   Conversely, for DNF we want x ||
				   ~x, or 1, or, again, an expression
				   containing a single empty term. */
				out.clear();
				NF_Term emptyTerm;
				out.push_back(emptyTerm);
			}
			extra_sanity(out);
			return;
		}
	}

	/* No, there isn't currently a matching single-atom term in
	   @out.  See if we can simplify any of the existing terms in
	   @out. */
	std::vector<NF_Term> reinsert;
	for ( ; x < out.size(); ) {
		auto it = out[x].findMatchingAtom(atom);
		if (it != out[x].end()) {
			assert(it->second == atom.second);
			if (it->first != atom.first) {
				/* out[x] contains the inverse of the
				   atom which we're trying to insert.
				   If we're in CNF, we know that when
				   we evaluate out[x] atom is
				   definitely true, so !atom is
				   definitely false, and the !atom
				   atom in out[x] is pointless.
				   Conversely, in DNF, we know that
				   !atom is true, so, again, it's
				   pointless.  We can therefore purge
				   it.

				   We do this in a slightly awkward
				   way, removing out[x] from the list
				   completely and then putting it
				   back, because that makes it much
				   easier to keep @out sane.
				   (removing a term from an expression
				   never breaks sanity) */
				out[x].erase(it);
				assert(out[x].findMatchingAtom(atom) == out[x].end()); 
				reinsert.push_back(out[x]);
			} else {
				/* out[x] already contains an exact
				   duplicate of the thing we're
				   inserting, and so out[x] is
				   completely redundant.  Remove
				   it. */
			}
			out.erase(out.begin() + x);
		} else {
			x++;
		}
	}

	if (!reinsert.empty()) {
		/* This recursion must eventually bottom out, because
		   @out can only get simpler at each recursive
		   step. */
		for (auto it = reinsert.begin(); it != reinsert.end(); it++) {
			insert_term_destruct(*it, out);
			if (out.isContradiction()) {
				/* @out has been reduced to a
				 * contradiction.  Stop. */
				return;
			}
		}
				
		/* We start again from the beginning here, because
		   that restructuring might mean that there are more
		   single-atom terms in @out and we have to be certain
		   we'll consider them properly. */
		goto top;
	}

	/* Okay, now we do the actual insert. */
	for (x = 0; x < out.size() && out[x].size() == 1 && out[x][0].second < atom.second; x++)
		;
	out.insert(out.begin() + x, src);
}

/* Set @out to @src `expressionOp` @out, destroying @src as we do
   so. */
static void
insert_term_destruct(NF_Term &src, NF_Expression &out)
{
	unsigned x;
	unsigned nr_killed = 0;
	extra_sanity(out);
	extra_sanity(src);
	if (src.size() == 1)
		return insert_atomic_term(src, out);

	assert(!out.isContradiction());

	/* Simplify @src using the single-atom terms in @out. */
	for (x = 0; x < out.size() && out[x].size() == 1; x++) {
		const NF_Atom &outAtom(out[x][0]);
		auto it = src.findMatchingAtom(outAtom);
		if (it != src.end()) {
			assert(it->second == outAtom.second);
			if (it->first == outAtom.first) {
				/* Easy case: we already have (a `expressionOp` ...)
				   and we're inserting (a `termOp` ...).
				   That's a no-op. */
				return;
			} else {
				/* We have (a `expressionOp` ...) and
				   we're inserting (!a `termOp` X).  That's
				   equivalent to inserting just X, so
				   erase this bit of the thing to
				   insert. */
				src.erase(it);
			}
		}
	}

	if (src.size() == 0) {
		/* Inserting an empty term turns @out into a
		   contradiction, which is very easy. */
		out.clear();
		out.push_back(src);
		return;
	}

	if (src.size() == 1)
		return insert_atomic_term(src, out);

	for ( ; x < out.size(); x++) {
		nf_ordering order;

		if (out[x].size() > src.size()) {
			order = nf_greater;
		} else {
			if (out[x][0].second < src[0].second) {
				/* Atoms are ordered within terms, so
				   this means that the smallest
				   element of out[x] is less than the
				   smallest element of src i.e. the
				   smallest element of out[x] is not
				   present in src, and out[x] is not a
				   subset of src. */
				order = nf_less;
				assert(compare_nf_terms(out[x], src) ==
				       nf_less);
			} else {
				order = compare_nf_terms(out[x], src);
			}
		}
		switch (order) {
		case nf_subset:
		case nf_eq:
			/* This existing output clause subsumes the
			 * new one we want to insert. */

			return;
		case nf_less:
			assert(compare_nf_terms(src, out[x]) == nf_greater);
			continue;
		case nf_greater: 
		case nf_superset: {
			/* Split the initial out into regions
			   according to its relationship to src.  They
			   look like this:

			   a: terms with a smaller size than src
			   b: terms with the same size as src which are
			      lexicographically less than src
			   c: terms equal to src
			   d: terms with the same size as dest which are
			      lexicographically greater than src
			   e: terms with a greater size than src

			   Anything which is a subset of src must
			   necessarily have a smaller size than it, so
			   will fit entirely in region a, and anything
			   which is a superset will likewise fit in
			   region e, so this is necessary given the
			   ordering relationship.

			   Because we've gotten here, we know from
			   control flow that c is empty and there are
			   no subsets of src in the original out.

			   We also know that this is the first x such
			   that out[x] > src i.e. x points at the
			   first element of d (or the first element of
			   e, if d is empty) i.e. it points at where c
			   would have been if it hadn't been empty.  x
			   is therefore the right place in which to
			   insert src.

			   However, we don't know much about the
			   contents of region e.  In particular, it
			   might contain some supersets of src, which
			   will need to be purged.  Do so. */
			unsigned start_of_e;
			for (start_of_e = x + 1;
			     start_of_e < out.size() && out[start_of_e].size() == src.size();
			     start_of_e++)
				assert(compare_nf_terms(out[start_of_e], src) == nf_greater);
			unsigned y;
			for (y = start_of_e;
			     y < out.size();
			     y++) {
				nf_ordering o = compare_nf_terms(out[y], src);
				assert(o == nf_greater || o == nf_superset);
				if (o == nf_superset) {
					nr_killed++;
					out[y].clear();
				}
			}
			goto out1;
		}
		}
	}
	/* If we hit the end of that loop then we know that everything
	   in @out is less than @src, but nothing is a subset of it or
	   equal to it.  We must therefore insert @src at the end of
	   @out, which is precisely what the fall-through does. */

out1:
	if (nr_killed > out.size() / 2) {
		NF_Expression new_out;
		new_out.reserve(out.size() - nr_killed + 1);
		for (unsigned y = 0; y < out.size(); y++) {
			extra_sanity(new_out);
			if (y == x) {
				new_out.push_back(src);
				extra_sanity(new_out);
			}
			if (out[y].size() != 0) {
				new_out.push_back(out[y]);
				extra_sanity(new_out);
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
		extra_sanity(out);
		if (x == out.size())
			out.insert(out.begin() + x, src);
		extra_sanity(out);
	}
	extra_sanity(out);
}

/* Set @out to @src1 `expressionOp` @src2, destroying @src1 and @src2
   as we do so. */
static void
merge_expressions_destruct(NF_Expression &src1,
			   NF_Expression &src2,
			   NF_Expression &out)
{
	extra_sanity(src1);
	extra_sanity(src2);
	out.clear();
	out.reserve(src1.size() + src2.size());
	if (src1.size() < src2.size()) {
		out.insert(out.begin(), src2.begin(), src2.end());
		if (out.isContradiction())
			return;
		for (auto it = src1.begin(); it != src1.end(); it++) {
			insert_term_destruct(*it, out);
			if (out.isContradiction())
				return;
		}
		extra_sanity(out);
	} else {
		out.insert(out.begin(), src1.begin(), src1.end());
		if (out.isContradiction())
			return;
		for (auto it = src2.begin(); it != src2.end(); it++) {
			insert_term_destruct(*it, out);
			if (out.isContradiction())
				return;
		}
		extra_sanity(out);
	}
}

/* Convert @out to @out `termOp` @this_one, maintaining normal form.
 * Returns false on error or true otherwise. */
static bool
nf_countermerge(const NF_Expression &this_one, NF_Expression &out)
{
	NF_Expression new_out;
	extra_sanity(out);
	if (TIMEOUT || out.size() * this_one.size() > NF_MAX_EXPRESSION)
		return false;
	new_out.reserve(out.size() * this_one.size());
	for (unsigned x = 0; x < out.size(); x++) {
		NF_Term &existing_term(out[x]);
		extra_sanity(existing_term);
		for (unsigned z = 0; z < this_one.size(); z++) {
			extra_sanity(new_out);
			NF_Term new_term;
			if (merge_terms(this_one[z], existing_term, new_term)) {
				extra_sanity(new_out);
				insert_term_destruct(new_term, new_out);
				extra_sanity(new_out);
				if (new_out.isContradiction())
					goto out;
			} else {
				/* the term includes both x and !x,
				   for some x, so should be
				   dropped. */
			}
		}
	}
out:
	out = new_out;
	extra_sanity(out);
	return true;
}

/* Disjoin or conjoin the fragments together, convert to NF, and then
   place the results in @out.  Can fail if @out looks ``too big'', in
   which case we return false.  Otherwise return true. */
/* i.e. convert @out to
   @out `termOp` fragments[0] `termOp` fragments[1] ... `termOp` fragments[nr_fragments-1]
*/
static bool
nf_counterjoin(IRExpr **fragments, int nr_fragments, NF_Expression &out,
	       IROp expressionOp, IROp termOp)
{
top:
	if (TIMEOUT)
		return false;
	if (nr_fragments == 0) {
		sanity_check(out);
		return true;
	}
	if (out.size() == 0) {
		/* For CNF, an empty expression has value 1 and the termOp is ||,
		   so this is 1 || {fragments} and the result is just 1 i.e. an
		   empty expression.  For DNF, an empty expression is 0 and termOp
		   is &&, so this is 0 && {fragments} i.e. 0 i.e. also an empty
		   expression. */
		return true;
	}
	extra_sanity(out);
	{
		NF_Expression this_one;
		__nf::convert_to_nf(fragments[0], this_one, expressionOp, termOp);
		if (!nf_countermerge(this_one, out))
			return false;
	}

	/* gcc seems to have problems with tail call elimination in
	   this function.  Do it manually. */
	fragments++;
	nr_fragments--;
	goto top;
}

/* Invert @conf and store it in @out, which must start out empty. */
static void
nf_invert(const NF_Term &conj, NF_Expression &out)
{
	assert(out.size() == 0);
	out.reserve(conj.size());
	for (unsigned x = 0; x < conj.size(); x++) {
		NF_Term c;
		c.push_back(NF_Atom(!conj[x].first, conj[x].second));
		insert_term_destruct(c, out);
		if (out.isContradiction()) {
			/* It would be correct to just return here,
			   but if we ever get here then @conj cannot
			   have been properly normalised, so abort()
			   so that we can check what's going on. */
			abort();
			return;
		}
	}
	extra_sanity(out);
}

/* Set @out to ~@in.  Returns true on success or false if we hit a
 * timeout. */
static bool
nf_invert(const NF_Expression &in, NF_Expression &out)
{
	assert(out.size() == 0);

	if (in.size() == 0) {
		NF_Term t;
		out.push_back(t);
		assert(out.isContradiction());
		return true;
	}

	/* Start by converting the first clause */
	nf_invert(in[0], out);
	assert(!out.isContradiction());

	/* Now we convert the remaining clauses one at a time, or'ing
	   them in as we go.  The invariant here is that out = ~(in[0:x]),
	   where the slice notation is supposed to mean that we consider
	   the first x clauses only. */
	for (unsigned x = 1; x < in.size(); x++) {
		NF_Expression r;
		if (TIMEOUT)
			return false;
		nf_invert(in[x], r);
		assert(!r.isContradiction());

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

/* Convert @e to either CNF or DNF.  Returns false on timeout or true
 * otherwise. */
static bool
convert_to_nf(IRExpr *e, NF_Expression &out, IROp expressionOp, IROp termOp)
{
	assert(out.empty());
	if (e->tag == Iex_Unop &&
	    ((IRExprUnop *)e)->op == Iop_Not1) {
		NF_Expression r;
		if (!__nf::convert_to_nf(((IRExprUnop *)e)->arg, r, expressionOp, termOp))
			return false;
		nf_invert(r, out);
		return true;
	}

	if (e->tag == Iex_Associative) {
		if (((IRExprAssociative *)e)->op == expressionOp) {
			for (int x = 0; x < ((IRExprAssociative *)e)->nr_arguments; x++) {
				if (TIMEOUT)
					return false;
				NF_Expression r;
				if (!__nf::convert_to_nf(((IRExprAssociative *)e)->contents[x],
							 r,
							 expressionOp,
							 termOp))
					return false;
				NF_Expression t(out);
				merge_expressions_destruct(r, t, out);
			}
			sanity_check(out);
			return true;
		} else if (((IRExprAssociative *)e)->op == termOp) {
			NF_Term t;
			out.push_back(t);
			assert(out.isContradiction());
			return nf_counterjoin(((IRExprAssociative *)e)->contents,
					      ((IRExprAssociative *)e)->nr_arguments,
					      out,
					      expressionOp,
					      termOp);
		}
	}

	/* Anything else cannot be represented in NF, so gets an
	 * atom */
	NF_Term c;
	c.push_back(NF_Atom(false, e));
	out.push_back(c);
	sanity_check(out);
	return true;
}

/* Walk over the NF expression performing a final optimisation pass.
   This almost never does anything useful, but it's necessary to make
   the whole thing deterministic, which is necessary if you're working
   in an nd_choice pseudo-monad.  The problem occurs in expressions
   with at least three terms, a, b, and c, where a is a subset of c
   and no other subsetting relationships hold.  If the fallback
   relationship orders them as abc then we won't necessarily detect
   the subset relationship in the main construction pass, which only
   ever looks at neighbouring pairs of terms.  If they had instead
   been orderd bac (remember, the fallback relationship relies on the
   memory address of the expression, which is only semi-deterministic)
   then we would have detected the relationship and reduced the result
   to just ba.  The fix is just to do the full O(n^2) thing at the end
   to find *all* of the subset relationships and purge them. */
static bool
optimise_nf(NF_Expression &e)
{
	static int nr_useful_invocations;
	static int nr_invocations;

	nr_invocations++;

	for (auto it1 = e.begin(); it1 != e.end(); it1++) {
		for (auto it2 = it1 + 1; it2 != e.end(); ) {
			if (TIMEOUT)
				return false;
			switch (compare_nf_terms(*it1, *it2)) {
			case nf_subset:
				/* *it1 is a subset of *it2.  If we're
				   in CNF, that means that *it1
				   implies *it2, and b&c==b if b=>c,
				   so we should purge it2.
				   Conversely, if we're in DNF, *it2
				   implies *it1, and b|c==b if c=>b,
				   so we should purge it2.

				   i.e. in either case we purge
				   it2. */
				nr_useful_invocations++;
				if (nr_useful_invocations % 1000 == 0)
					printf("%d/%d useful invocations of optimise_nf\n",
					       nr_useful_invocations, nr_invocations);
				it2 = e.erase(it2);
				break;
			case nf_less:
				it2++;
				break;

				/* Shouldn't get any of these because
				   of the normalisation rules. */
			case nf_eq:
			case nf_greater:
			case nf_superset:
				abort();
			}
		}
	}
	return true;
}

/* I'm kind of disturbed that g++ allows this (implicit loss of
   const-ness on inp.second.  Oh well. */
static IRExpr *
convert_from_nf(const NF_Atom &inp)
{
	if (inp.first)
		return IRExpr_Unop(Iop_Not1, inp.second);
	else
		return inp.second;
}

static IRExpr *
convert_from_nf(NF_Term &inp, IROp op)
{
	if (inp.size() == 0)
		return IRExpr_Const(
			IRConst_U1(
				op == Iop_And1 ? 1 : 0));
	if (inp.size() == 1)
		return convert_from_nf(inp[0]);
	IRExprAssociative *acc = new IRExprAssociative();
	acc->op = op;
	acc->nr_arguments = inp.size();
	acc->nr_arguments_allocated = acc->nr_arguments * 2;
	static libvex_allocation_site __las = {0, __FILE__, __LINE__};
	acc->contents =
		(IRExpr **)__LibVEX_Alloc_Bytes(&ir_heap, sizeof(acc->contents[0]) * acc->nr_arguments, &__las);
	for (unsigned x = 0; x < inp.size(); x++)
		acc->contents[x] = convert_from_nf(inp[x]);
	return acc;
}

static IRExpr *
convert_from_nf(NF_Expression &inp, IROp expressionOp, IROp termOp)
{
	if (inp.size() == 0)
		return IRExpr_Const(
			IRConst_U1(
			        expressionOp == Iop_And1 ? 1 : 0));
	if (inp.size() == 1)
		return convert_from_nf(inp[0], termOp);
	IRExprAssociative *acc = new IRExprAssociative();
	acc->op = expressionOp;
	acc->nr_arguments = inp.size();
	acc->nr_arguments_allocated = acc->nr_arguments * 2;
	static libvex_allocation_site __las = {0, __FILE__, __LINE__};
	acc->contents =
		(IRExpr **)__LibVEX_Alloc_Bytes(&ir_heap, sizeof(acc->contents[0]) * acc->nr_arguments, &__las);
	for (unsigned x = 0; x < inp.size(); x++)
		acc->contents[x] = convert_from_nf(inp[x], termOp);
	return acc;
}

} /* End of namespace __nf */

void
NF_Term::prettyPrint(FILE *f, const char *sep) const
{
	for (auto it = begin(); it != end(); it++) {
		if (it != begin())
			fprintf(f, "%s\n", sep);
		it->prettyPrint(f);
	}
	fprintf(f, "\n");
}

void
NF_Expression::prettyPrint(FILE *f, const char *termSep, const char *sep) const
{
	for (auto it = begin(); it != end(); it++) {
		if (it != begin())
			fprintf(f, "\n%s\n", sep);
		it->prettyPrint(f, termSep);
	}
	fprintf(f, "\n");
}

NF_Term::iterator
NF_Term::findMatchingAtom(const NF_Atom &a)
{
	for (auto it = begin(); it != end(); it++) {
		if (a.second == it->second)
			return it;
		if (a.second < it->second) {
			/* You might say that, since the atoms are in
			   order, we should be using a binary chop,
			   rather than a linear scan, but since there
			   are rarely more than half a dozen items in
			   the list it makes basically no difference,
			   and linear scans are a bit easier.  We do,
			   however, stop early if we find something
			   greater than the needle, since that's
			   obviously correct and helps a bit. */
			break;
		}
	}
	return end();
}

bool
NF_Expression::isContradiction() const
{
	return size() == 1 && ((*this)[0].size() == 0);
}

/* Caution: this isn't completely deterministic, even with the
   optimisation pass, because the order of terms within the expression
   depends on the memory addresses of the underlying atom IRExprs.
   Converting back to an IRExpr and then running a simplification pass
   will fix that. */
bool
convert_to_nf(IRExpr *e, NF_Expression &out, IROp expressionOp, IROp termOp)
{
	if (!__nf::convert_to_nf(e, out, expressionOp, termOp))
		return false;
	return __nf::optimise_nf(out);
}

IRExpr *
convert_from_nf(NF_Expression &inp, IROp expressionOp, IROp termOp)
{
	return __nf::convert_from_nf(inp, expressionOp, termOp);
}

IRExpr *
convert_to_cnf(IRExpr *input)
{
	NF_Expression cnf;
	if (!convert_to_nf(input, cnf, Iop_And1, Iop_Or1))
		return NULL;
	return convert_from_nf(cnf, Iop_And1, Iop_Or1);
}

IRExpr *
convert_to_dnf(IRExpr *input)
{
	NF_Expression cnf;
	if (!convert_to_nf(input, cnf, Iop_Or1, Iop_And1))
		return NULL;
	return convert_from_nf(cnf, Iop_Or1, Iop_And1);
}
