/* Satisfiability checker.  This has quite a lot of overlap with the
   simplifier (and calls into it in a number of places), but is more
   powerful and more computationally expensive.  The idea is that you
   use the simplifier for most checks as you're running along, and
   then use this right at the end as a final check before reporting a
   bug. */
#include "sli.h"
#include "sat_checker.hpp"
#include "maybe.hpp"
#include "simplify_irexpr.hpp"
#include "nf.hpp"
#include "nd_chooser.h"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"

namespace _sat_checker {

static struct stats {
	unsigned nr_invoked;
	unsigned initial_constant;
	unsigned anf_resolved;
	unsigned cnf_resolved;
	unsigned dnf_resolved;
	unsigned exhaustive_resolved;
	unsigned failed;
	unsigned timeout;
	~stats() {
		if (nr_invoked == 0)
			return;
		printf("Sat checker invoked %d times.  Results:\n", nr_invoked);
#define do_field(name)							\
		printf("\t" # name ":\t%f%%\n", 100.0 * name / nr_invoked)
		do_field(initial_constant);
		do_field(anf_resolved);
		do_field(cnf_resolved);
		do_field(dnf_resolved);
		do_field(exhaustive_resolved);
		do_field(timeout);
		do_field(failed);
#undef do_field
	}
} sat_checker_counters;

static Maybe<bool>
isTrue(IRExpr *e)
{
	if (e->tag != Iex_Const)
		return Maybe<bool>::nothing();
	IRExprConst *iec = (IRExprConst *)e;
	if (iec->con->Ico.U1)
		return Maybe<bool>::just(true);
	else
		return Maybe<bool>::just(false);
}

static int
anf_depth(const IRExpr *a)
{
	while (a->tag == Iex_Unop &&
	       ((IRExprUnop *)a)->op == Iop_Not1)
		a = ((IRExprUnop *)a)->arg;
	if (a->tag != Iex_Associative)
		return 0;
	IRExprAssociative *iex = (IRExprAssociative *)a;
	if (iex->op != Iop_And1)
		return 0;
	int acc = 0;
	for (int i = 0; i < iex->nr_arguments; i++) {
		int j = anf_depth(iex->contents[i]);
		if (j >= acc)
			acc = j;
	}
	return acc + 1;
}

enum ordering {
	ord_lt,
	ord_eq,
	ord_gt
};

static ordering
_anf_sort_func(IRExpr *a, IRExpr *b)
{
	if (a == b)
		return ord_eq;
	bool inv_a = false;
	bool inv_b = false;
	while (a->tag == Iex_Unop &&
	       ((IRExprUnop *)a)->op == Iop_Not1) {
		inv_a = !inv_a;
		a = ((IRExprUnop *)a)->arg;
	}
	while (b->tag == Iex_Unop &&
	       ((IRExprUnop *)b)->op == Iop_Not1) {
		inv_b = !inv_b;
		b = ((IRExprUnop *)b)->arg;
	}
	if (a == b) {
		if (inv_a < inv_b)
			return ord_lt;
		else if (inv_a > inv_b)
			return ord_gt;
		else
			return ord_eq;
	}
	int a_depth = anf_depth(a);
	int b_depth = anf_depth(b);
	if (a_depth < b_depth)
		return ord_lt;
	if (a_depth > b_depth)
		return ord_gt;
	assert(a_depth == b_depth);
	if (a_depth != 0) {
		assert(a->tag == Iex_Associative);
		assert(b->tag == Iex_Associative);
		IRExprAssociative *iex_a = (IRExprAssociative *)a;
		IRExprAssociative *iex_b = (IRExprAssociative *)b;
		assert(iex_a->op == Iop_And1);
		assert(iex_b->op == Iop_And1);
		for (int i = 0; i < iex_a->nr_arguments && i < iex_b->nr_arguments; i++) {
			ordering a = _anf_sort_func(iex_a->contents[i], iex_b->contents[i]);
			if (a != ord_eq)
				return a;
		}
		if (iex_a->nr_arguments < iex_b->nr_arguments)
			return ord_lt;
		if (iex_a->nr_arguments > iex_b->nr_arguments)
			return ord_gt;
	}
	if (a < b)
		return ord_lt;
	if (a > b)
		return ord_gt;
	if (inv_a < inv_b)
		return ord_lt;
	else if (inv_a > inv_b)
		return ord_gt;
	else
		return ord_eq;
}

class compare_args {
public:
	bool operator()(IRExpr *a, IRExpr *b) {
		return _anf_sort_func(a, b) == ord_lt;
	}
};

static void
sort_and_arguments(IRExpr **args, int nr_args)
{
	compare_args comp;
	std::sort(&args[0], &args[nr_args], comp);
	for (int i = 1; i < nr_args; i++) {
		assert(args[i-1] == args[i] ||
		       comp(args[i-1], args[i]));
	}
}

static void
check_and_normal_form(const IRExpr *e)
{
	if (e->tag == Iex_Unop) {
		IRExprUnop *iex = (IRExprUnop *)e;
		if (iex->op != Iop_Not1)
			return;
		check_and_normal_form(iex->arg);
		return;
	}
	if (e->tag == Iex_Associative) {
		IRExprAssociative *iex = (IRExprAssociative *)e;
		assert(iex->op != Iop_Or1);
		assert(iex->op != Iop_Xor1);
		if (iex->op != Iop_And1)
			return;
		for (int i = 0; i < iex->nr_arguments; i++)
			check_and_normal_form(iex->contents[i]);
		for (int i = 1; i < iex->nr_arguments; i++)
			assert(_anf_sort_func(iex->contents[i-1], iex->contents[i]) != ord_gt);
	}
}

/* And normal form means that we can use Iop_And1 and Iop_Not1, but
   not Iop_Or1.  It's not quite as powerful as CNF, but converting to
   it is *much* cheaper. */
static IRExpr *
and_normal_form(IRExpr *e, internIRExprTable &intern)
{
	if (TIMEOUT)
		return NULL;

	e = internIRExpr(e, intern);
	if (e->tag == Iex_Unop) {
		IRExprUnop *ieu = (IRExprUnop *)e;
		if (ieu->op == Iop_Not1) {
			IRExpr *arg2 = and_normal_form(ieu->arg, intern);
			if (!arg2)
				return NULL;
			if (arg2->tag == Iex_Unop) {
				IRExprUnop *ieu2 = (IRExprUnop *)arg2;
				if (ieu2->op == Iop_Not1)
					e = ieu2->arg;
			} else {
				if (arg2 != ieu->arg)
					e = internIRExpr(IRExpr_Unop(
								 Iop_Not1,
								 arg2),
							 intern);
			}
		}
	} else if (e->tag == Iex_Associative) {
		IRExprAssociative *iea = (IRExprAssociative *)e;
		if (iea->op == Iop_And1) {
			IRExpr *newArgs[iea->nr_arguments];
			for (int x = 0; x < iea->nr_arguments; x++)
				newArgs[x] = and_normal_form(iea->contents[x], intern);
			if (TIMEOUT)
				return NULL;
			IRExprAssociative *res = IRExpr_Associative(iea->nr_arguments, iea->op);
			res->nr_arguments = iea->nr_arguments;
			memcpy(res->contents, newArgs, sizeof(IRExpr *) * iea->nr_arguments);
			sort_and_arguments(res->contents, iea->nr_arguments);
			e = internIRExpr(res, intern);
		} else if (iea->op == Iop_Or1) {
			IRExprAssociative *res = IRExpr_Associative(iea->nr_arguments, Iop_And1);
			for (int x = 0; x < iea->nr_arguments; x++)
				res->contents[x] =
					and_normal_form(
						IRExpr_Unop(
							Iop_Not1,
							iea->contents[x]),
						intern);
			if (TIMEOUT)
				return NULL;
			res->nr_arguments = iea->nr_arguments;
			sort_and_arguments(res->contents, res->nr_arguments);
			e = internIRExpr(IRExpr_Unop(Iop_Not1, res), intern);
		} else if (iea->op == Iop_Xor1) {
			/* This goes horribly wrong for large xor
			   expressions, due to the exponential
			   blow-up.  Fortunately, we never actually
			   generate any. */
			assert(iea->nr_arguments < 10);
			/* We convert (a ^ b ^ c ... ) into
			   !(!(a & b & c & ... ) & !(a & !b & !c & ... )
			   ...)
			   where each conjunction has an odd number of positive
			   terms. */
			IRExpr *positive_terms[iea->nr_arguments];
			IRExpr *negative_terms[iea->nr_arguments];
			for (int i = 0; i < iea->nr_arguments; i++) {
				positive_terms[i] = and_normal_form(iea->contents[i], intern);
				if (!positive_terms[i])
					return NULL;
				if (positive_terms[i]->tag == Iex_Unop &&
				    ((IRExprUnop *)positive_terms[i])->op == Iop_Not1)
					negative_terms[i] =
						((IRExprUnop *)positive_terms[i])->arg;
				else
					negative_terms[i] =
						internIRExpr(
							IRExpr_Unop(
								Iop_Not1,
								positive_terms[i]),
							intern);
			}
			int new_nr_args = 1 << (iea->nr_arguments - 1);
			IRExprAssociative *newAssoc =
				IRExpr_Associative(new_nr_args, Iop_And1);
			for (int i = 0; i < new_nr_args * 2; i++) {
				int nr_bits_set = 0;
				for (int j = 0; j < iea->nr_arguments; j++)
					if (i & (1 << j))
						nr_bits_set++;
				if (nr_bits_set % 2 == 0)
					continue;
				IRExprAssociative *arg = IRExpr_Associative(
					iea->nr_arguments, Iop_And1);
				for (int j = 0; j < iea->nr_arguments; j++) {
					if (i & (1 << j))
						arg->contents[j] = positive_terms[j];
					else
						arg->contents[j] = negative_terms[j];
				}
				arg->nr_arguments = iea->nr_arguments;
				arg = (IRExprAssociative *)internIRExpr(arg, intern);
				sort_and_arguments(arg->contents, arg->nr_arguments);
				newAssoc->contents[newAssoc->nr_arguments++] =
					IRExpr_Unop(
						Iop_Not1,
						arg);
			}
			newAssoc = (IRExprAssociative *)internIRExpr(newAssoc, intern);
			sort_and_arguments(newAssoc->contents, newAssoc->nr_arguments);
			e = internIRExpr(IRExpr_Unop(Iop_Not1, newAssoc), intern);
		}
	}
	check_and_normal_form(e);
	return e;
}

class anf_context {
	internIRExprTable &intern;
	std::set<std::pair<IRExpr *, IRExpr *> > eqRules;
	std::set<IRExpr *> definitelyTrue;
	std::set<IRExpr *> definitelyFalse;
	bool matches(const IRExpr *a, const IRExpr *b) const;
	void addAssumption(IRExpr *a);
	void introduceEqRule(IRExpr *a, IRExpr *b);
public:
	anf_context(internIRExprTable &_intern, IRExpr *assumption)
		: intern(_intern)
	{
		if (assumption)
			addAssumption(assumption);
	}
	IRExpr *simplify(IRExpr *input);
	void prettyPrint(FILE *);
};

void
anf_context::prettyPrint(FILE *f)
{
	fprintf(f, "ANF context:\n");
	fprintf(f, "\tdefinitely true:\n");
	for (auto it = definitelyTrue.begin(); it!= definitelyTrue.end(); it++) {
		fprintf(f, "\t\t");
		ppIRExpr(*it, f);
		fprintf(f, "\n");
	}
	fprintf(f, "\tdefinitely false:\n");
	for (auto it = definitelyFalse.begin(); it!= definitelyFalse.end(); it++) {
		fprintf(f, "\t\t");
		ppIRExpr(*it, f);
		fprintf(f, "\n");
	}
	fprintf(f, "\tEQ rules:\n");
	for (auto it = eqRules.begin(); it!= eqRules.end(); it++) {
		fprintf(f, "\t\t");
		ppIRExpr(it->first, f);
		fprintf(f, "\t==\t");
		ppIRExpr(it->second, f);
		fprintf(f, "\n");
	}
}

bool
anf_context::matches(const IRExpr *a, const IRExpr *b) const
{
	if (a == b)
		return true;
	for (auto it = eqRules.begin(); it != eqRules.end(); it++) {
		if ((it->first == a && it->second == b) ||
		    (it->first == b && it->second == a))
			return true;
	}
	if (a->tag != b->tag)
		return false;
	switch (a->tag) {
#define hdr1(name)							\
		case Iex_ ## name : {					\
			IRExpr ## name *ai = (IRExpr ## name *)a;	\
			IRExpr ## name *bi = (IRExpr ## name *)b
#define hdr(name) } hdr1(name)
		hdr1(GetI);
		return ai->descr == bi->descr && ai->bias == bi->bias && ai->tid == bi->tid && matches(ai->ix, bi->ix);
		hdr(Qop);
		return ai->op == bi->op && matches(ai->arg1, bi->arg1) && matches(ai->arg2, bi->arg2) &&
			matches(ai->arg3, bi->arg3) && matches(ai->arg4, bi->arg4);
		hdr(Triop);
		return ai->op == bi->op && matches(ai->arg1, bi->arg1) && matches(ai->arg2, bi->arg2) &&
			matches(ai->arg3, bi->arg3);
		hdr(Binop);
		return ai->op == bi->op && matches(ai->arg1, bi->arg1) && matches(ai->arg2, bi->arg2);
		hdr(Unop);
		return ai->op == bi->op && matches(ai->arg, bi->arg);
		hdr(Load);
		return ai->ty == bi->ty && matches(ai->addr, bi->addr);
		hdr(CCall);
		if (!(ai->cee == bi->cee && ai->retty == bi->retty))
			return false;
		int i;
		for (i = 0; ai->args[i] && bi->args[i]; i++)
			if (!matches(ai->args[i], bi->args[i]))
				return false;
		if (ai->args[i] || bi->args[i])
			return false;
		return true;
		hdr(Mux0X);
		return matches(ai->cond, bi->cond) && matches(ai->expr0, bi->expr0) && matches(ai->exprX, bi->exprX);
		hdr(Associative);
		if (ai->op != bi->op || ai->nr_arguments != bi->nr_arguments)
			return false;
		for (int i = 0; i < ai->nr_arguments; i++)
			if (!matches(ai->contents[i], bi->contents[i]))
				return false;
		return true;
	}
#undef hdr
#undef hdr1
        case Iex_FreeVariable:
	case Iex_HappensBefore:
	case Iex_Const:
	case Iex_Get:
	case Iex_EntryPoint:
	case Iex_ControlFlow:
		return false; /* by internment property */
        }
        abort();
}

static IRExpr *
pureSimplify(IRExpr *what, internIRExprTable &internTable)
{
	struct : public IRExprTransformer {
		internIRExprTable *internTable;
		IRExpr *transformIex(IRExprAssociative *ieb) {
			if (ieb->op == Iop_Add64 &&
			    ieb->nr_arguments == 2 &&
			    ieb->contents[1]->tag == Iex_Unop &&
			    ((IRExprUnop *)ieb->contents[1])->op == Iop_Neg64 &&
			    ((IRExprUnop *)ieb->contents[1])->arg == ieb->contents[0])
				return IRExpr_Const(IRConst_U64(0));
			if (ieb->op == Iop_And1) {
				IRExpr *new_args[ieb->nr_arguments];
				int new_nr_args = 0;
				for (int i = 0; i < ieb->nr_arguments; i++) {
					if (ieb->contents[i]->tag == Iex_Const) {
						IRExprConst *iec = (IRExprConst *)ieb->contents[i];
						if (!iec->con->Ico.U1)
							return IRExpr_Const(IRConst_U1(0));
					} else {
						new_args[new_nr_args++] = ieb->contents[i];
					}
				}
				if (new_nr_args == 1)
					return new_args[0];
				if (new_nr_args != ieb->nr_arguments) {
					IRExprAssociative *iea = IRExpr_Associative(new_nr_args, Iop_And1);
					memcpy(iea->contents, new_args, sizeof(IRExpr *) * new_nr_args);
					iea->nr_arguments = new_nr_args;
					return iea;
				}
			}
			return IRExprTransformer::transformIex(ieb);
		}
		IRExpr *transformIex(IRExprUnop *ieu) {
			if (ieu->op == Iop_Not1 &&
			    ieu->arg->tag == Iex_Const) {
				return IRExpr_Const(IRConst_U1(!((IRExprConst *)ieu->arg)->con->Ico.U1));
			}
			return IRExprTransformer::transformIex(ieu);
		}
		IRExpr *transformIex(IRExprBinop *ieb) {
			if (ieb->op == Iop_CmpEQ64 &&
			    ieb->arg1 == ieb->arg2)
				return IRExpr_Const(IRConst_U1(1));
			return IRExprTransformer::transformIex(ieb);
		}
		IRExpr *transformIRExpr(IRExpr *a, bool *done_something)
		{
			bool b = false;
			IRExpr *res = IRExprTransformer::transformIRExpr(a, &b);
			if (b)
				assert(res != a);
			if (res != a) {
				res = internIRExpr(res, *internTable);
				*done_something = true;
			}
			return res;
		}
	} doit;
	doit.internTable = &internTable;
	bool done_something = false;
	IRExpr *a = doit.doit(what, &done_something);
	if (done_something)
		return a;
	else
		return internIRExpr(a, internTable);
}

static IRExpr *
rewriteIRExpr(IRExpr *what, IRExpr *from, IRExpr *to, internIRExprTable &internTable)
{
	struct : public IRExprTransformer {
		IRExpr *from;
		IRExpr *to;
		IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
			if (e == from) {
				*done_something = true;
				return to;
			}
			return IRExprTransformer::transformIRExpr(e, done_something);
		}
	} doit;
	doit.from = from;
	doit.to = to;
	return pureSimplify(doit.doit(what), internTable);
}

void
anf_context::introduceEqRule(IRExpr *a, IRExpr *b)
{
	if (a == b)
		return;
	if (b < a) {
		IRExpr *t = a;
		a = b;
		b = t;
	}
	if (!eqRules.insert(std::pair<IRExpr *, IRExpr *>(a, b)).second)
		return;

	/* Now take the transitive closure. */
	std::set<std::pair<IRExpr *, IRExpr *> > oldEqRules(eqRules);
	for (auto it = oldEqRules.begin(); it != oldEqRules.end(); it++) {
		if (it->first == a)
			introduceEqRule(b, it->second);
		if (it->first == b)
			introduceEqRule(a, it->second);
		if (it->second == a)
			introduceEqRule(b, it->first);
		if (it->second == b)
			introduceEqRule(a, it->first);
	}
}

void
anf_context::addAssumption(IRExpr *a)
{
	if (a->tag == Iex_Const)
		return;
	if (a->tag == Iex_Binop) {
		IRExprBinop *ieb = (IRExprBinop *)a;
		if (ieb->op >= Iop_CmpEQ8 &&
		    ieb->op <= Iop_CmpEQ64) {
			if (ieb->op == Iop_CmpEQ64 &&
			    ieb->arg1->tag == Iex_Const &&
			    ((IRExprConst *)ieb->arg1)->con->Ico.U64 == 0 &&
			    ieb->arg2->tag == Iex_Associative &&
			    ((IRExprAssociative *)ieb->arg2)->op == Iop_Add64 &&
			    ((IRExprAssociative *)ieb->arg2)->nr_arguments == 2 &&
			    ((IRExprAssociative *)ieb->arg2)->contents[1]->tag == Iex_Unop &&
			    ((IRExprUnop *)((IRExprAssociative *)ieb->arg2)->contents[1])->op == Iop_Neg64) {
				introduceEqRule(((IRExprAssociative *)ieb->arg2)->contents[0],
						((IRExprUnop *)((IRExprAssociative *)ieb->arg2)->contents[1])->arg);
			} else {
				introduceEqRule(ieb->arg1, ieb->arg2);
			}
			return;
		}
	}
	if (a->tag == Iex_Associative &&
	    ((IRExprAssociative *)a)->op == Iop_And1) {
		IRExprAssociative *aa = (IRExprAssociative *)a;
		for (int i = 0; i < aa->nr_arguments; i++)
			addAssumption(aa->contents[i]);
		return;
	}
	if (a->tag == Iex_Unop &&
	    ((IRExprUnop *)a)->op == Iop_Not1)
		definitelyFalse.insert( ((IRExprUnop *)a)->arg );
	else
		definitelyTrue.insert(a);
}

IRExpr *
anf_context::simplify(IRExpr *a)
{
	if (TIMEOUT)
		return a;

	a = pureSimplify(a, intern);

	/* If we have a == k, for any constant k, go and do the
	 * rewrite. */
	for (auto it = eqRules.begin(); it != eqRules.end(); it++) {
		if (it->second->tag == Iex_Const)
			a = rewriteIRExpr(a, it->first, it->second, intern);
		if (it->first->tag == Iex_Const)
			a = rewriteIRExpr(a, it->second, it->first, intern);
	}

	/* Icky special case: rewrite a + -b to just 0 if we know that
	 * a == b,  */
	if (a->tag == Iex_Associative) {
		IRExprAssociative *ieb = (IRExprAssociative *)a;
		if (ieb->op == Iop_Add64 &&
		    ieb->nr_arguments == 2 &&
		    ieb->contents[1]->tag == Iex_Unop) {
			IRExprUnop *ieu = (IRExprUnop *)ieb->contents[1];
			if (ieu->op == Iop_Neg64) {
				for (auto it = eqRules.begin(); it != eqRules.end(); it++) {
					if ( (it->first == ieb->contents[0] && it->second == ieu->arg) ||
					     (it->second == ieb->contents[0] && it->first == ieu->arg) )
						return internIRExpr(IRExpr_Const(IRConst_U64(0)), intern);
				}
			}
		}
	}

	if (a->type() != Ity_I1)
		return a;
	if (definitelyTrue.count(a))
		return internIRExpr(IRExpr_Const(IRConst_U1(1)), intern);
	if (definitelyFalse.count(a))
		return internIRExpr(IRExpr_Const(IRConst_U1(0)), intern);
	for (auto it = definitelyTrue.begin(); it != definitelyTrue.end(); it++)
		if (matches(a, *it))
			return internIRExpr(IRExpr_Const(IRConst_U1(1)), intern);
	for (auto it = definitelyFalse.begin(); it != definitelyFalse.end(); it++)
		if (matches(a, *it))
			return internIRExpr(IRExpr_Const(IRConst_U1(0)), intern);

	if (a->tag == Iex_Unop) {
		IRExprUnop *ieu = (IRExprUnop *)a;
		if (ieu->op != Iop_Not1)
			return a;
		IRExpr *arg = simplify(ieu->arg);
		if (arg->tag == Iex_Const) {
			IRExprConst *iec = (IRExprConst *)arg;
			return internIRExpr(IRExpr_Const(IRConst_U1(!iec->con->Ico.U1)), intern);
		}
		if (arg->tag == Iex_Unop &&
		    ((IRExprUnop *)arg)->op == Iop_Not1)
			return ((IRExprUnop *)arg)->arg;
		if (arg == ieu->arg)
			return a;
		/* Don't need to check whether the result matches the
		   definitely true or definitely false lists.  If it
		   matched with definitely true, arg would have
		   matched with definitely false and we wouldn't be
		   here.  Likewise, if it matched with definitely
		   false, arg would have matched with definitely
		   true. */
		return internIRExpr(
			IRExpr_Unop(
				Iop_Not1,
				arg),
			intern);
	} else if (a->tag == Iex_Associative) {
		IRExprAssociative *iea = (IRExprAssociative *)a;
		assert(iea->op != Iop_Or1);
		assert(iea->op != Iop_Xor1);
		if (iea->op != Iop_And1)
			return a;
		anf_context sub_context(*this);
		IRExprAssociative *res = IRExpr_Associative(iea->nr_arguments, Iop_And1);
		for (int i = 0; i < iea->nr_arguments; i++) {
			IRExpr *arg = sub_context.simplify(iea->contents[i]);
			if (arg->tag == Iex_Const) {
				IRExprConst *iec = (IRExprConst *)arg;
				if (!iec->con->Ico.U1)
					return arg;
			} else if (arg->tag == Iex_Associative &&
			    ((IRExprAssociative *)arg)->op == Iop_And1) {
				IRExprAssociative *argA = (IRExprAssociative *)arg;
				for (int i = 0; i < argA->nr_arguments; i++) {
					sub_context.addAssumption(argA->contents[i]);
					addArgumentToAssoc(res, argA->contents[i]);
				}
			} else {
				sub_context.addAssumption(arg);
				addArgumentToAssoc(res, arg);
			}
		}
		if (res->nr_arguments == 1)
			return res->contents[0];
		if (res->nr_arguments == 0)
			return internIRExpr(IRExpr_Const(IRConst_U1(1)), intern);
		sort_and_arguments(res->contents, res->nr_arguments);
		a = internIRExpr(res, intern);

		/* Don't need to check against the definitely true
		   list, because this is an and expression and they
		   never get introduced into the list (components are
		   added instead).  Do need to check against
		   definitely false, though. */
		for (auto it = definitelyFalse.begin(); it != definitelyFalse.end(); it++)
			if (matches(a, *it))
				return internIRExpr(IRExpr_Const(IRConst_U1(0)), intern);
		return a;
	} else {
		return a;
	}
}

/* @a is in and-normal-form (i.e. the boolean level only uses Iop_And1
 * and Iop_Not1 operators, but not Iop_Or1).  See if there are any
 * interesting simplifications we can do based on that. */
static IRExpr *
anf_simplify(IRExpr *a, IRExpr *assumption, internIRExprTable &intern)
{
	a = internIRExpr(a, intern);
	while (!TIMEOUT) {
		anf_context ctxt(intern, assumption);
		IRExpr *a2 = ctxt.simplify(a);
		if (a == a2)
			break;
		a = a2;
	}
	return a;
}

static IRExpr *
simplify_via_anf(IRExpr *a, IRExpr *assumption = NULL)
{
	internIRExprTable table;
	a = internIRExpr(a, table);
	IRExpr *normed = and_normal_form(a, table);
	if (!normed)
		return a;
	IRExpr *normed_ass = NULL;
	if (assumption)
		normed_ass = and_normal_form(internIRExpr(assumption, table), table);
	return anf_simplify(normed, normed_ass, table);
}

static IRExpr *
conjunctive_normal_form(IRExpr *what)
{
	IRExpr *res = convert_to_cnf(what);
	if (res)
		return res;
	else
		return what;
}

static IRExpr *
disjunctive_normal_form(IRExpr *what)
{
	IRExpr *res = convert_to_dnf(what);
	if (res)
		return res;
	else
		return what;
}

static bool
evalExpression(IRExpr *e, NdChooser &chooser, bool preferred_result,
	       satisfier &sat)
{
	assert(e->type() == Ity_I1);
	if (e->tag == Iex_Const)
		return ((IRExprConst *)e)->con->Ico.U1 != 0;

	std::pair<bool, bool> falsefalse = std::pair<bool, bool>(false, false);
	auto it_did_insert = sat.memo.insert(std::pair<IRExpr *, std::pair<bool, bool> >(e, falsefalse));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (e->tag == Iex_Unop &&
		    ((IRExprUnop *)e)->op == Iop_Not1) {
			it->second.first = !evalExpression(((IRExprUnop *)e)->arg, chooser, !preferred_result, sat);
		} else if (e->tag == Iex_Associative &&
			   ((IRExprAssociative *)e)->op == Iop_And1) {
			IRExprAssociative *a = (IRExprAssociative *)e;
			bool acc = true;
			for (int i = 0; i < a->nr_arguments && acc; i++)
				acc &= evalExpression(a->contents[i], chooser, preferred_result, sat);
			it->second.first = acc;
		} else if (e->tag == Iex_Associative &&
			   ((IRExprAssociative *)e)->op == Iop_Or1) {
			IRExprAssociative *a = (IRExprAssociative *)e;
			bool acc = false;
			for (int i = 0; i < a->nr_arguments && !acc; i++)
				acc |= evalExpression(a->contents[i], chooser, preferred_result, sat);
			it->second.first = acc;
		} else if (e->tag == Iex_EntryPoint) {
			it->second.second = true;
			IRExprEntryPoint *a = (IRExprEntryPoint *)e;
			auto it2 = sat.entry.find(a->thread);
			if (it2 == sat.entry.end()) {
				if (preferred_result == !chooser.nd_choice(2)) {
					sat.entry.insert(std::pair<unsigned, CfgLabel>(a->thread, a->label));
					it->second.first = true;
				} else {
					it->second.first = false;
				}
			} else {
				/* Because otherwise we'd have found
				   it in the memo table, by the
				   internment property. */
				assert(it2->second != a->label);
				it->second.first = false;
			}
		} else {
			if (e->tag == Iex_Binop) {
				IRExprBinop *ieb = (IRExprBinop *)e;
				if (ieb->op >= Iop_CmpEQ8 &&
				    ieb->op <= Iop_CmpEQ64 &&
				    ieb->arg1->tag == Iex_Const) {
					/* We quite often get
					   expressions of the form
					   ``(k1 == var) && (k2 ==
					   var)'', where k1 != k2.
					   It's useful to return that
					   that's unsatisfiable.  The
					   trick is that if we say k1
					   == var is true then we say
					   that var is fixed, and then
					   any other equality on var
					   must be false (because
					   we're interned) */
					if (sat.fixedVariables.count(ieb->arg2)) {
						it->second.first = false;
						return it->second.first;
					}
					sat.fixedVariables.insert(ieb->arg2);
				}

				if (ieb->op >= Iop_CmpEQ8 &&
				    ieb->op <= Iop_CmpEQ64) {
					/* Compare that to all of the
					   CmpLTxU expressions which
					   we've already assigned
					   values to. */
					IRExpr *arg1 = ieb->arg1;
					IRExpr *arg2 = ieb->arg2;
					for (auto it2 = sat.memo.begin();
					     it2 != sat.memo.end();
					     it2++) {
						if (it2->first == ieb ||
						    it2->first->tag != Iex_Binop)
							continue;
						IRExprBinop *ieb2 = (IRExprBinop *)it2->first;
						if (ieb2->op < Iop_CmpLT8U ||
						    ieb2->op > Iop_CmpLT64U)
							continue;
						IRExpr *lt = ieb2->arg1;
						IRExpr *gt = ieb2->arg1;
						if (lt != arg1 && lt != arg2 &&
						    gt != arg1 && gt != arg2)
							continue;
						if ( (lt == arg1 && gt == arg2) ||
						     (lt == arg2 && gt == arg1) ) {
							/* Have either
							   A < B or B < A
							   and we're
							   evaluating
							   A == B */
							if (it2->second.first) {
								it->second.first = false;
								return false;
							}
						}
						if (arg1->tag == Iex_Const &&
						    ((lt->tag == Iex_Const && gt == arg2) ||
						     (gt->tag == Iex_Const && lt == arg2)) ) {
							unsigned long arg1_cnst =
								((IRExprConst *)arg1)->con->Ico.U64;
							if (lt->tag == Iex_Const) {
								unsigned long lt_cnst =
									((IRExprConst *)lt)->con->Ico.U64;
								if ((arg1_cnst <= lt_cnst) == it2->second.first) {
									it->second.first = false;
									return false;
								}
							}
							if (gt->tag == Iex_Const) {
								unsigned long gt_cnst =
									((IRExprConst *)gt)->con->Ico.U64;
								if ((arg1_cnst >= gt_cnst) == it2->second.first) {
									it->second.first = false;
									return false;
								}
							}
						}
					}
				}

				if (ieb->op >= Iop_CmpLT8U &&
				    ieb->op <= Iop_CmpLT64U) {
					IRExpr *arg1 = ieb->arg1;
					IRExpr *arg2 = ieb->arg2;
					for (auto it2 = sat.memo.begin();
					     it2 != sat.memo.end();
					     it2++) {
						if (it2->first->tag != Iex_Binop)
							continue;
						IRExprBinop *ieb2 = (IRExprBinop *)it2->first;
						if (it2->second.first &&
						    ieb2->op >= Iop_CmpEQ8 &&
						    ieb2->op <= Iop_CmpEQ64) {
							if ( (arg1 == ieb2->arg1 &&
							      arg2 == ieb2->arg2) ||
							     (arg1 == ieb2->arg2 &&
							      arg2 == ieb2->arg1) ) {
								it->second.first = false;
								return false;
							}
						}
						IRExpr *lt = ieb2->arg1;
						IRExpr *gt = ieb2->arg1;
						if (ieb2->op < Iop_CmpLT8U ||
						    ieb2->op > Iop_CmpLT64U)
							continue;
						if (lt != arg1 && lt != arg2 &&
						    gt != arg1 && gt != arg2)
							continue;
						if (lt == arg1 && gt == arg2) {
							/* By internment property */
							abort();
						}
						if (lt == arg2 && gt == arg1) {
							it->second.first = !it2->second.first;
							return it->second.first;
						}
						if (lt == arg1) {
							if (gt->tag != Iex_Const ||
							    arg2->tag != Iex_Const)
								continue;
							unsigned long k1 =
								((IRExprConst *)gt)->con->Ico.U64;
							unsigned long k2 =
								((IRExprConst *)arg2)->con->Ico.U64;
							if (k1 < k2) {
								it->second.first = it2->second.first;
								return it->second.first;
							}
						}
						if (lt == arg2) {
							if (gt->tag != Iex_Const ||
							    arg1->tag != Iex_Const)
								continue;
							unsigned long k1 =
								((IRExprConst *)gt)->con->Ico.U64;
							unsigned long k2 =
								((IRExprConst *)arg1)->con->Ico.U64;
							if (k1 <= k2 ||
							    k1 == k2 + 1) {
								it->second.first = !it2->second.first;
								return it->second.first;
							}
						}
						if (gt == arg2) {
							if (lt->tag != Iex_Const ||
							    arg1->tag != Iex_Const)
								continue;
							unsigned long k1 =
								((IRExprConst *)lt)->con->Ico.U64;
							unsigned long k2 =
								((IRExprConst *)arg1)->con->Ico.U64;
							if (k1 < k2) {
								it->second.first = !it2->second.first;
								return it2->second.first;
							}
						}
						if (gt == arg1) {
							if (lt->tag != Iex_Const ||
							    arg2->tag != Iex_Const)
								continue;
							unsigned long k1 =
								((IRExprConst *)lt)->con->Ico.U64;
							unsigned long k2 =
								((IRExprConst *)arg2)->con->Ico.U64;
							if (k1 >= k2 ||
							    k2 == k1 + 1) {
								it->second.first = !it2->second.first;
								return it->second.first;
							}
						}
					}
				}

			}
			it->second.first = !!chooser.nd_choice(2);
			if (preferred_result == true)
				it->second.first = !it->second.first;
			it->second.second = true;
		}
	}
	return it->second.first;
}

static bool
exhaustive_satisfiable(IRExpr *e, bool print_all)
{
	bool res = false;
	for (auto it = sat_enumerator(e); !it.finished(); it.advance()) {
		fprintf(_logfile, "Satisfying assignment:\n");
		it.get().prettyPrint(_logfile);
		if (!print_all) {
			sat_checker_counters.failed++;
			return true;
		}
		res = true;
	}
	if (res)
		sat_checker_counters.failed++;
	else if (TIMEOUT)
		sat_checker_counters.timeout++;
	else
		sat_checker_counters.exhaustive_resolved++;
	return res;
}

static IRExpr *
sat_simplify(IRExpr *a, const AllowableOptimisations &opt)
{
	sat_checker_counters.nr_invoked++;

	assert(a->type() == Ity_I1);
	Maybe<bool> res(isTrue(a));

	if (res.valid) {
		sat_checker_counters.initial_constant++;
		return a;
	}

	internIRExprTable intern;
	a = internIRExpr(a, intern);

	IRExpr *norm1 = and_normal_form(a, intern);
	if (!norm1)
		return a;
	check_and_normal_form(norm1);
	norm1 = anf_simplify(norm1, NULL, intern);
	norm1 = simplifyIRExpr(norm1, opt);
	res = isTrue(norm1);
	if (res.valid) {
		sat_checker_counters.anf_resolved++;
		return norm1;
	}

	IRExpr *norm2 = conjunctive_normal_form(norm1);
	norm2 = simplifyIRExpr(norm2, opt);
	res = isTrue(norm2);
	if (res.valid) {
		sat_checker_counters.cnf_resolved++;
		return norm2;
	}
	IRExpr *norm3 = disjunctive_normal_form(norm2);
	norm3 = simplifyIRExpr(norm3, opt);
	res = isTrue(norm3);
	if (res.valid)
		sat_checker_counters.dnf_resolved++;

	return norm3;
}

static bool
satisfiable(IRExpr *e, const AllowableOptimisations &opt)
{
	assert(e->type() == Ity_I1);

	e = _sat_checker::sat_simplify(e, opt);

	Maybe<bool> res(isTrue(e));
	if (res.valid)
		return res.content;

	return exhaustive_satisfiable(e, false);
}

/* End of namespace */
};

bool
satisfiable(IRExpr *e, const AllowableOptimisations &opt)
{
	return _sat_checker::satisfiable(e, opt);
}

IRExpr *
simplify_via_anf(IRExpr *a, IRExpr *assumption)
{
	return _sat_checker::simplify_via_anf(a, assumption);
}

IRExpr *
sat_simplify(IRExpr *a, const AllowableOptimisations &opt)
{
	return _sat_checker::sat_simplify(a, opt);
}

bool
sat_enumerator::finished() const
{
	return _finished;
}

void
sat_enumerator::skipToSatisfying()
{
	do {
		content.clear();
		if (_sat_checker::evalExpression(expr, chooser, true, content))
			return;
	} while (chooser.advance());
	_finished = true;
}

void
sat_enumerator::advance()
{
	if (!chooser.advance())
		_finished = true;
	skipToSatisfying();
}

void
satisfier::prettyPrint(FILE *f) const
{
	for (auto it = memo.begin(); it != memo.end(); it++) {
		if (it->second.second) {
			fprintf(f, "\t");
			ppIRExpr(it->first, f);
			fprintf(f, "\t-> %s\n",
				it->second.first ? "true" : "false");
		}
	}
	fprintf(f, "Fixed: {");
	for (auto it = fixedVariables.begin(); it != fixedVariables.end(); it++) {
		if (it != fixedVariables.begin())
			fprintf(f, ", ");
		ppIRExpr(*it, f);
	}
	fprintf(f, "}\nEntry map:\n");
	for (auto it = entry.begin(); it != entry.end(); it++)
		fprintf(f, "\t%d -> %s\n", it->first, it->second.name());
}
