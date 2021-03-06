/* Satisfiability checker.  This has quite a lot of overlap with the
   simplifier (and calls into it in a number of places), but is more
   powerful and more computationally expensive.  The idea is that you
   use the simplifier for most checks as you're running along, and
   then use this right at the end as a final check before reporting a
   bug. */
#include <climits>

#include "sli.h"
#include "sat_checker.hpp"
#include "maybe.hpp"
#include "simplify_irexpr.hpp"
#include "nf.hpp"
#include "nd_chooser.h"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"

#ifdef NDEBUG
#define debug_satisfier false
#else
static bool debug_satisfier = false;
#endif

#define UNEVALUATABLE ((IRExpr *)1)

namespace _sat_checker {

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

static int
expr_depth(const IRExpr *a)
{
	switch (a->tag) {
	case Iex_Get:
	case Iex_Const:
	case Iex_HappensBefore:
	case Iex_FreeVariable:
	case Iex_EntryPoint:
	case Iex_ControlFlow:
		return 1;
	case Iex_GetI:
		return expr_depth( ((IRExprGetI *)a)->ix) + 1;
	case Iex_Qop:
		return std::max( std::max(expr_depth( ((IRExprQop *)a)->arg1),
					  expr_depth( ((IRExprQop *)a)->arg2)),
				 std::max(expr_depth( ((IRExprQop *)a)->arg3),
					  expr_depth( ((IRExprQop *)a)->arg4)) ) + 1;
	case Iex_Triop:
		return std::max( std::max(expr_depth( ((IRExprTriop *)a)->arg1),
					  expr_depth( ((IRExprTriop *)a)->arg2)),
				 expr_depth( ((IRExprTriop *)a)->arg3) ) + 1;
	case Iex_Binop:
		return std::max(expr_depth( ((IRExprBinop *)a)->arg1),
				expr_depth( ((IRExprBinop *)a)->arg2) ) + 1;
	case Iex_Unop:
		return expr_depth( ((IRExprUnop *)a)->arg ) + (((IRExprUnop *)a)->op != Iop_Not1);
	case Iex_Mux0X:
		return std::max( std::max(expr_depth( ((IRExprMux0X *)a)->cond),
					  expr_depth( ((IRExprMux0X *)a)->expr0)),
				 expr_depth( ((IRExprMux0X *)a)->exprX) ) + 1;
	case Iex_Load:
		return expr_depth( ((IRExprLoad *)a)->addr) + 1;
	case Iex_Associative: {
		IRExprAssociative *e = (IRExprAssociative *)a;
		int m = 0;
		for (int i = 0; i < e->nr_arguments; i++) {
			int j = expr_depth(e->contents[i]);
			if (j > m)
				m = j;
		}
		return m + (e->op != Iop_And1 && e->op != Iop_Or1);
	}
	case Iex_CCall: {
		IRExprCCall *e = (IRExprCCall *)a;
		int m = 0;
		for (int i = 0; e->args[i]; i++) {
			int j = expr_depth(e->args[i]);
			if (j > m)
				m = j;
		}
		return m + 1;
	}
	}
	abort();
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
	int a_depth_e = expr_depth(a);
	int b_depth_e = expr_depth(b);
	if (a_depth_e < b_depth_e)
		return ord_lt;
	if (a_depth_e > b_depth_e)
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
and_normal_form(IRExpr *e)
{
	if (e->tag == Iex_Unop) {
		IRExprUnop *ieu = (IRExprUnop *)e;
		if (ieu->op == Iop_Not1) {
			IRExpr *arg2 = and_normal_form(ieu->arg);
			if (!arg2)
				return NULL;
			if (arg2->tag == Iex_Unop) {
				IRExprUnop *ieu2 = (IRExprUnop *)arg2;
				if (ieu2->op == Iop_Not1)
					e = ieu2->arg;
			} else {
				if (arg2 != ieu->arg)
					e = IRExpr_Unop(
						Iop_Not1,
						arg2);
			}
		}
	} else if (e->tag == Iex_Associative) {
		IRExprAssociative *iea = (IRExprAssociative *)e;
		if (iea->op == Iop_And1) {
			IRExpr *newArgs[iea->nr_arguments];
			for (int x = 0; x < iea->nr_arguments; x++)
				newArgs[x] = and_normal_form(iea->contents[x]);
			sort_and_arguments(newArgs, iea->nr_arguments);
			IRExpr *res = IRExpr_Associative_Copy(iea->op, iea->nr_arguments, newArgs);
			e = res;
		} else if (iea->op == Iop_Or1) {
			IRExpr *newArgs[iea->nr_arguments];
			for (int x = 0; x < iea->nr_arguments; x++)
				newArgs[x] =
					and_normal_form(
						IRExpr_Unop(
							Iop_Not1,
							iea->contents[x]));
			sort_and_arguments(newArgs, iea->nr_arguments);
			IRExprAssociative *res = IRExpr_Associative_Copy(Iop_And1, iea->nr_arguments, newArgs);
			e = IRExpr_Unop(Iop_Not1, res);
		}
	}
	check_and_normal_form(e);
	return e;
}

class anf_context {
	std::set<std::pair<IRExpr *, IRExpr *> > eqRules;
	std::set<IRExpr *> definitelyTrue;
	std::set<IRExpr *> definitelyFalse;
	std::set<IRExpr *> badPointers;
	bool matches(const IRExpr *a, const IRExpr *b) const;
	void addAssumption(IRExpr *a);
	void introduceEqRule(IRExpr *a, IRExpr *b);
	bool loadsBadPointer(IRExpr *a) const;
public:
	anf_context(IRExpr *assumption)
	{
		if (assumption)
			addAssumption(assumption);
	}
	IRExpr *simplify(IRExpr *input);
	void prettyPrint(FILE *);
};

bool
anf_context::loadsBadPointer(IRExpr *a) const
{
	switch (a->tag) {
	case Iex_Get:
		return false;
	case Iex_GetI:
		return loadsBadPointer(((IRExprGetI *)a)->ix);
	case Iex_Qop:
		if (loadsBadPointer( ((IRExprQop *)a)->arg4))
			return true;
	case Iex_Triop:
		if (loadsBadPointer( ((IRExprTriop *)a)->arg3))
			return true;
	case Iex_Binop:
		if (loadsBadPointer( ((IRExprBinop *)a)->arg2))
			return true;
	case Iex_Unop:
		return loadsBadPointer( ((IRExprUnop *)a)->arg);
	case Iex_Const:
		return false;
	case Iex_Mux0X:
		return loadsBadPointer( ((IRExprMux0X *)a)->cond ) ||
			(loadsBadPointer( ((IRExprMux0X *)a)->expr0 ) &&
			 loadsBadPointer( ((IRExprMux0X *)a)->exprX ) );
	case Iex_CCall: {
		IRExprCCall *cee = (IRExprCCall *)a;
		for (int i = 0; cee->args[i]; i++)
			if (loadsBadPointer(cee->args[i]))
				return true;
		return false;
	}
	case Iex_Associative: {
		IRExprAssociative *cee = (IRExprAssociative *)a;
		for (int i = 0; i < cee->nr_arguments; i++)
			if (loadsBadPointer(cee->contents[i]))
				return true;
		return false;
	}
	case Iex_Load:
		return badPointers.count( ((IRExprLoad *)a)->addr ) ||
			loadsBadPointer( ((IRExprLoad *)a)->addr );
	case Iex_HappensBefore:
		return false;
	case Iex_FreeVariable:
		return false;
	case Iex_EntryPoint:
		return false;
	case Iex_ControlFlow:
		return false;
	}
	abort();
}

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
	fprintf(f, "\tBad pointers:\n");
	for (auto it = badPointers.begin(); it != badPointers.end(); it++) {
		fprintf(f, "\t\t");
		ppIRExpr(*it, f);
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
pureSimplify(IRExpr *what)
{
	struct : public IRExprTransformer {
		IRExpr *transformIex(IRExprAssociative *ieb) {
			if (ieb->op == Iop_Add64 &&
			    ieb->nr_arguments == 2 &&
			    ieb->contents[1]->tag == Iex_Unop &&
			    ((IRExprUnop *)ieb->contents[1])->op == Iop_Neg64 &&
			    ((IRExprUnop *)ieb->contents[1])->arg == ieb->contents[0])
				return IRExpr_Const_U64(0);
			if (ieb->op == Iop_And1) {
				IRExpr *new_args[ieb->nr_arguments];
				int new_nr_args = 0;
				for (int i = 0; i < ieb->nr_arguments; i++) {
					if (ieb->contents[i]->tag == Iex_Const) {
						IRExprConst *iec = (IRExprConst *)ieb->contents[i];
						if (!iec->Ico.content.U1)
							return IRExpr_Const_U1(false);
					} else {
						new_args[new_nr_args++] = ieb->contents[i];
					}
				}
				if (new_nr_args == 1)
					return new_args[0];
				if (new_nr_args != ieb->nr_arguments)
					return IRExpr_Associative_Copy(Iop_And1, new_nr_args, new_args);
			}
			return IRExprTransformer::transformIex(ieb);
		}
		IRExpr *transformIex(IRExprUnop *ieu) {
			if (ieu->op == Iop_Not1 &&
			    ieu->arg->tag == Iex_Const) {
				return IRExpr_Const_U1(!((IRExprConst *)ieu->arg)->Ico.content.U1);
			}
			return IRExprTransformer::transformIex(ieu);
		}
		IRExpr *transformIex(IRExprBinop *ieb) {
			if (ieb->op == Iop_CmpEQ64 &&
			    ieb->arg1 == ieb->arg2)
				return IRExpr_Const_U1(true);
			return IRExprTransformer::transformIex(ieb);
		}
	} doit;
	return doit.doit(what);
}

static IRExpr *
rewriteIRExpr(IRExpr *what, IRExpr *from, IRExpr *to)
{
	struct : public IRExprTransformer {
		IRExpr *from;
		IRExpr *to;
		IRExpr *transformIRExpr(IRExpr *e) {
			if (e == from)
				return to;
			return IRExprTransformer::transformIRExpr(e);
		}
	} doit;
	doit.from = from;
	doit.to = to;
	return pureSimplify(doit.doit(what));
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
			    ((IRExprConst *)ieb->arg1)->Ico.content.U64 == 0 &&
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
	a = pureSimplify(a);

	/* If we have a == k, for any constant k, go and do the
	 * rewrite. */
	for (auto it = eqRules.begin(); it != eqRules.end(); it++) {
		if (it->second->tag == Iex_Const)
			a = rewriteIRExpr(a, it->first, it->second);
		if (it->first->tag == Iex_Const)
			a = rewriteIRExpr(a, it->second, it->first);
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
						return IRExpr_Const_U64(0);
				}
			}
		}
	}

	if (a->type() != Ity_I1)
		return a;
	if (definitelyTrue.count(a))
		return IRExpr_Const_U1(true);
	if (definitelyFalse.count(a))
		return IRExpr_Const_U1(false);
	for (auto it = definitelyTrue.begin(); it != definitelyTrue.end(); it++)
		if (matches(a, *it))
			return IRExpr_Const_U1(true);
	for (auto it = definitelyFalse.begin(); it != definitelyFalse.end(); it++)
		if (matches(a, *it))
			return IRExpr_Const_U1(false);

	if (!badPointers.empty() && loadsBadPointer(a))
		return UNEVALUATABLE;

	if (a->tag == Iex_Unop) {
		IRExprUnop *ieu = (IRExprUnop *)a;
		if (ieu->op != Iop_Not1)
			return a;
		IRExpr *arg = simplify(ieu->arg);
		if (arg == UNEVALUATABLE)
			return UNEVALUATABLE;
		if (arg->tag == Iex_Const) {
			IRExprConst *iec = (IRExprConst *)arg;
			return IRExpr_Const_U1(!iec->Ico.content.U1);
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
		return IRExpr_Unop(
			Iop_Not1,
			arg);
	} else if (a->tag == Iex_Associative) {
		IRExprAssociative *iea = (IRExprAssociative *)a;
		assert(iea->op != Iop_Or1);
		if (iea->op != Iop_And1)
			return a;
		anf_context sub_context(*this);
		std::vector<IRExpr *> newArgs;
		for (int i = 0; i < iea->nr_arguments; i++) {
			IRExpr *arg = sub_context.simplify(iea->contents[i]);
			if (arg != UNEVALUATABLE) {
				if (arg->tag == Iex_Const) {
					IRExprConst *iec = (IRExprConst *)arg;
					if (!iec->Ico.content.U1)
						return arg;
				} else if (arg->tag == Iex_Associative &&
					   ((IRExprAssociative *)arg)->op == Iop_And1) {
					IRExprAssociative *argA = (IRExprAssociative *)arg;
					for (int i = 0; i < argA->nr_arguments; i++) {
						sub_context.addAssumption(argA->contents[i]);
						newArgs.push_back(argA->contents[i]);
					}
				} else {
					sub_context.addAssumption(arg);
					newArgs.push_back(arg);
				}
			}
		}
		if (newArgs.size() == 1)
			return newArgs[0];
		if (newArgs.empty())
			return IRExpr_Const_U1(true);
		IRExpr *newArgs2[newArgs.size()];
		for (unsigned x = 0; x < newArgs.size(); x++) {
			newArgs2[x] = newArgs[x];
		}
		sort_and_arguments(newArgs2, newArgs.size());

		a = IRExpr_Associative_Copy(Iop_And1, newArgs.size(), newArgs2);

		/* Don't need to check against the definitely true
		   list, because this is an and expression and they
		   never get introduced into the list (components are
		   added instead).  Do need to check against
		   definitely false, though. */
		for (auto it = definitelyFalse.begin(); it != definitelyFalse.end(); it++)
			if (matches(a, *it))
				return IRExpr_Const_U1(false);
		return a;
	} else {
		return a;
	}
}

/* @a is in and-normal-form (i.e. the boolean level only uses Iop_And1
 * and Iop_Not1 operators, but not Iop_Or1).  See if there are any
 * interesting simplifications we can do based on that. */
static IRExpr *
anf_simplify(IRExpr *a, IRExpr *assumption)
{
	while (1) {
		anf_context ctxt(assumption);
		IRExpr *a2 = ctxt.simplify(a);
		if (a2 == UNEVALUATABLE || a == a2) {
			return a;
		}
		a = a2;
	}
}

static IRExpr *
simplify_via_anf(IRExpr *a, IRExpr *assumption = NULL)
{
	IRExpr *normed = and_normal_form(a);
	if (!normed)
		return a;
	IRExpr *normed_ass = NULL;
	if (assumption)
		normed_ass = and_normal_form(assumption);
	return anf_simplify(normed, normed_ass);
}

/* Is a rewrite from @from to @to preferred over one from @to to
   @from? */
static bool
preferredRewriteDir(IRExpr *from, IRExpr *to)
{
	/* Prefer to *expand* expressions */
	return expr_depth(to) > expr_depth(from);
}

static bool
expressionImpliesRewrite(IRExpr *what, IRExpr **from, IRExpr **to)
{
	if (what->tag != Iex_Binop)
		return false;
	IRExprBinop *whatb = (IRExprBinop *)what;
	if (whatb->op < Iop_CmpEQ8 || whatb->op > Iop_CmpEQ64)
		return false;
	if (whatb->op == Iop_CmpEQ64) {
		*to = whatb->arg1;
		*from = whatb->arg2;

		/* Special case: if we have 0 == k - x, we're
		   sometimes better off rewriting x to k or vice-versa
		   rather than rewriting k - x to 0. */
		if ( whatb->arg1->tag == Iex_Const &&
		     ((IRExprConst *)whatb->arg1)->Ico.content.U64 == 0 &&
		     whatb->arg2->tag == Iex_Associative &&
		     ((IRExprAssociative *)whatb->arg2)->op >= Iop_Add8 &&
		     ((IRExprAssociative *)whatb->arg2)->op <= Iop_Add64 &&
		     ((IRExprAssociative *)whatb->arg2)->nr_arguments == 2 &&
		     ((IRExprAssociative *)whatb->arg2)->contents[1]->tag == Iex_Unop &&
		     ((IRExprUnop *)((IRExprAssociative *)whatb->arg2)->contents[1])->op >= Iop_Neg8 &&
		     ((IRExprUnop *)((IRExprAssociative *)whatb->arg2)->contents[1])->op <= Iop_Neg64) {
			IRExpr *a = ((IRExprAssociative *)whatb->arg2)->contents[0];
			IRExpr *b = ((IRExprUnop *)((IRExprAssociative *)whatb->arg2)->contents[1])->arg;
			if (preferredRewriteDir(a, b)) {
				*from = a;
				*to = b;
			} else {
				*from = b;
				*to = a;
			}
		}
	} else {
		if (preferredRewriteDir(whatb->arg1, whatb->arg2)) {
			*from = whatb->arg1;
			*to = whatb->arg2;
		} else {
			*from = whatb->arg2;
			*to = whatb->arg1;
		}
	}
	return true;
}

static int
variableMultiplicity(IRExpr *expression, IRExpr *variable)
{
	IRExpr *from, *to;
	if (expressionImpliesRewrite(variable, &from, &to))
		variable = from;
	struct : public IRExprTransformer {
		int cntr;
		IRExpr *expr;
		IRExpr *transformIRExpr(IRExpr *a) {
			if (a == expr) {
				cntr++;
				return a;
			}
			return IRExprTransformer::transformIRExpr(a);
		}
	} doit;
	doit.cntr = 0;
	doit.expr = variable;
	doit.doit(expression);
	return doit.cntr;
}

static IRExpr *
setVariable(IRExpr *expression, IRExpr *variable, bool value)
{
	struct : public IRExprTransformer {
		IRExpr *variable;
		bool value;
		IRExpr *transformIex(IRExprControlFlow *e) {
			if (value &&
			    variable->tag == Iex_ControlFlow &&
			    ((IRExprControlFlow *)variable)->thread == e->thread &&
			    ((IRExprControlFlow *)variable)->cfg1 == e->cfg1) {
				/* We're supposed to be interned, so
				   the transformIRExpr() case should
				   catch this. */
				assert(e->cfg2 != ((IRExprControlFlow *)variable)->cfg2);
				return IRExpr_Const_U1(false);
			}
			return e;
		}
		IRExpr *transformIex(IRExprEntryPoint *e) {
			if (value &&
			    variable->tag == Iex_EntryPoint &&
			    ((IRExprEntryPoint *)variable)->thread == e->thread) {
				assert(e->label != ((IRExprEntryPoint *)variable)->label);
				return IRExpr_Const_U1(false);
			}
			return e;
		}
		IRExpr *transformIex(IRExprBinop *e) {
			if (e->op >= Iop_CmpLT8U &&
			    e->op <= Iop_CmpLT64U &&
			    variable->tag == Iex_Binop &&
			    ((IRExprBinop *)variable)->op >= Iop_CmpLT8U &&
			    ((IRExprBinop *)variable)->op <= Iop_CmpLT64U &&
			    (((IRExprBinop *)variable)->arg1 == e->arg1 ||
			     ((IRExprBinop *)variable)->arg2 == e->arg1 ||
			     ((IRExprBinop *)variable)->arg1 == e->arg2 ||
			     ((IRExprBinop *)variable)->arg2 == e->arg2)) {
				IRExpr *a = ((IRExprBinop *)variable)->arg1;
				IRExpr *b = ((IRExprBinop *)variable)->arg2;
				assert(a != e->arg1 || b != e->arg2);
				if (a == e->arg2 && b == e->arg1) {
					/* We're trying to set (a < b)
					   to @value and we just
					   encounted b < a.  Set
					   b < a to ~@value. */
					return IRExpr_Const_U1(!value);
				}
				if (value) {
					if (a->tag == Iex_Const) {
						unsigned long k = ((IRExprConst *)a)->Ico.content.U64;
						/* Our assumption is that k < b */
						if (e->arg1->tag == Iex_Const &&
						    e->arg2 == b) {
							unsigned long k2 = ((IRExprConst *)e->arg1)->Ico.content.U64;
							/* Trying to eval k2 < b */
							if (k2 >= k)
								return IRExpr_Const_U1(true);
						} else if (e->arg2->tag == Iex_Const &&
							   e->arg1 == b) {
							unsigned long k2 = ((IRExprConst *)e->arg2)->Ico.content.U64;
							/* Trying to eval b < k2 */
							if (k2 <= k + 1)
								return IRExpr_Const_U1(false);
						}
					} else if (b->tag == Iex_Const) {
						unsigned long k = ((IRExprConst *)b)->Ico.content.U64;
						/* Our assumption is that b < k */
						if (e->arg1->tag == Iex_Const &&
						    e->arg2 == b) {
							unsigned long k2 = ((IRExprConst *)e->arg1)->Ico.content.U64;
							/* Trying to eval k2 < b */
							if (k <= k2 + 1)
								return IRExpr_Const_U1(false);
						} else if (e->arg2->tag == Iex_Const &&
							   e->arg1 == b) {
							unsigned long k2 = ((IRExprConst *)e->arg2)->Ico.content.U64;
							/* Trying to eval b < k2 */
							if (k >= k2)
								return IRExpr_Const_U1(true);
						}
					}
				} else {
					if (a->tag == Iex_Const) {
						unsigned long k = ((IRExprConst *)a)->Ico.content.U64;
						/* Our assumption is that k >= b */
						if (e->arg1->tag == Iex_Const &&
						    e->arg2 == b) {
							unsigned long k2 = ((IRExprConst *)e->arg1)->Ico.content.U64;
							/* Trying to eval k2 < b */
							if (k <= k2)
								return IRExpr_Const_U1(false);
						} else if (e->arg2->tag == Iex_Const &&
							   e->arg1 == b) {
							unsigned long k2 = ((IRExprConst *)e->arg2)->Ico.content.U64;
							/* Trying to eval b < k2 */
							if (k > k2)
								return IRExpr_Const_U1(true);
						}
					} else if (b->tag == Iex_Const) {
						unsigned long k = ((IRExprConst *)b)->Ico.content.U64;
						/* Our assumption is that b >= k */
						if (e->arg1->tag == Iex_Const &&
						    e->arg2 == b) {
							unsigned long k2 = ((IRExprConst *)e->arg1)->Ico.content.U64;
							/* Trying to eval k2 < b */
							if (k + 1 < k2)
								return IRExpr_Const_U1(true);
						} else if (e->arg2->tag == Iex_Const &&
							   e->arg1 == b) {
							unsigned long k2 = ((IRExprConst *)e->arg2)->Ico.content.U64;
							/* Trying to eval b < k2 */
							if (k2 <= k)
								return IRExpr_Const_U1(false);
						}
					}
				}
			}
			return IRExprTransformer::transformIex(e);
		}
		IRExpr *transformIRExpr(IRExpr *e) {
			if (e == variable)
				return IRExpr_Const_U1(value);
			return IRExprTransformer::transformIRExpr(e);
		}
		IRExpr *transformIex(IRExprUnop *e) {
			IRExpr *e2 = IRExprTransformer::transformIex(e);
			if (!e2 || e2 == e || e2->tag != Iex_Unop)
				return e2;
			e = (IRExprUnop *)e2;
			if (e->op != Iop_Not1 || e->arg->tag != Iex_Const)
				return e;
			return IRExpr_Const_U1(!((IRExprConst *)e->arg)->Ico.content.U1);
		}
		IRExpr *transformIex(IRExprAssociative *e) {
			if (e->op != Iop_Or1 && e->op != Iop_And1)
				return IRExprTransformer::transformIex(e);
			/* identity is the identity element for this
			   operation (true for and, false for or), and
			   suppress is the ``suppressor'' element such
			   that x <op> suppressor = suppressor, for
			   any x (true for or, false for and). */
			bool identity = e->op == Iop_And1;
			bool suppress = e->op == Iop_Or1;
			bool t = false;
			IRExpr *newArgs[e->nr_arguments];
			int outIdx = 0;
			for (int inIdx = 0; inIdx < e->nr_arguments; inIdx++) {
				newArgs[outIdx] = transformIRExpr(e->contents[inIdx]);
				t |= newArgs[outIdx] != e->contents[inIdx];
				if (newArgs[outIdx]->tag == Iex_Const) {
					IRExprConst *c = (IRExprConst *)newArgs[outIdx];
					if (c->Ico.content.U1 == suppress)
						return c;
					assert(c->Ico.content.U1 == identity);
					t = true;
				} else {
					outIdx++;
				}
			}
			if (t)
				return IRExpr_Associative_Copy(e->op, outIdx, newArgs);
			else
				return e;
		}
	} boolRewrite;
	boolRewrite.variable = variable;
	boolRewrite.value = value;
	expression = boolRewrite.doit(expression);

	struct : public IRExprTransformer {
		IRExpr *from;
		IRExpr *to;
		IRExpr *transformIRExpr(IRExpr *e) {
			if (e == from)
				return to;
			return IRExprTransformer::transformIRExpr(e);
		}
	} arithRewrite;
	if (value && expressionImpliesRewrite(variable, &arithRewrite.from, &arithRewrite.to))
		expression = arithRewrite.doit(expression);
	return expression;
}

static bool
isSimpleBoolean(const IRExpr *e)
{
	assert(e->type() == Ity_I1);
	switch (e->tag) {
	case Iex_Binop:
		assert(((IRExprBinop *)e)->arg1->type() != Ity_I1);
		assert(((IRExprBinop *)e)->arg2->type() != Ity_I1);
		return true;
	case Iex_Unop:
		if ( ((IRExprUnop *)e)->op == Iop_Not1 )
			return false;
		assert(((IRExprUnop *)e)->arg->type() != Ity_I1);
		return true;
	case Iex_HappensBefore:
	case Iex_EntryPoint:
	case Iex_ControlFlow:
		return true;
	default:
		return false;
	}
}

static void
findBooleans(IRExpr *expr, std::set<IRExpr *> &booleans)
{
	struct _ : public IRExprTransformer {
		std::set<IRExpr *> &booleans;
		IRExpr *transformIRExpr(IRExpr *a) {
			if (a->type() == Ity_I1 && isSimpleBoolean(a))
				booleans.insert(a);
			return IRExprTransformer::transformIRExpr(a);
		}
		_(std::set<IRExpr *> &_booleans)
			: booleans(_booleans)
		{}
	} doit(booleans);
	doit.doit(expr);
}

/* End of namespace */
};

IRExpr *
simplify_via_anf(IRExpr *a, IRExpr *assumption)
{
	return _sat_checker::simplify_via_anf(a, assumption);
}

void
sat_enumerator::skipToSatisfying()
{
	while (1) {
		if (stack.empty()) /* No more satisfiers available. */
			return;
		/* Avoid reallocating the stack in an awkward
		 * place. */
		stack.reserve(stack.size() + 1);
		stack_entry &frame(stack.back());
		frame.remainder =
			simplifyIRExpr(
				frame.remainder,
				opt);
		if (debug_satisfier) {
			printf("Try to advance satisfier from:\n");
			frame.prettyPrint(stdout);
		}
		if (frame.remainder->tag == Iex_Const) {
			IRExprConst *c = (IRExprConst *)frame.remainder;
			if (c->Ico.content.U1) {
				/* We're done */
				if (debug_satisfier)
					printf("Satisfier complete\n");
				return;
			} else {
				/* Whoops, contradiction.  Give up on
				   this case split and try something
				   else. */
				stack.pop_back();
				if (debug_satisfier)
					printf("Satisfier contradiction\n");
				continue;
			}
		}

		if (frame.remainder->tag == Iex_Associative &&
		    ((IRExprAssociative *)frame.remainder)->op == Iop_And1) {
			IRExprAssociative *a = ((IRExprAssociative *)frame.remainder);
			bool done_something = false;
			for (int i = 0; i < a->nr_arguments; i++) {
				if (_sat_checker::isSimpleBoolean(a->contents[i])) {
					if (debug_satisfier)
						printf("Have a simple boolean at top level (%s)\n",
						       nameIRExpr(a->contents[i]));
					frame.partial_sat.makeTrue(a->contents[i]);
					frame.remainder = _sat_checker::setVariable(frame.remainder, a->contents[i], true);
					done_something = true;
				}
				if (a->contents[i]->tag == Iex_Unop &&
				    ((IRExprUnop *)a->contents[i])->op == Iop_Not1 &&
				    _sat_checker::isSimpleBoolean(((IRExprUnop *)a->contents[i])->arg)) {
					IRExpr *arg = ((IRExprUnop *)a->contents[i])->arg;
					if (debug_satisfier)
						printf("Have a simple false boolean at top level (%s)\n",
						       nameIRExpr(arg));
					frame.partial_sat.makeFalse(arg);
					frame.remainder = _sat_checker::setVariable(frame.remainder, arg, false);
					done_something = true;
				}
			}
			if (done_something) {
				if (debug_satisfier)
					printf("Advance by setting top-level simples\n");
				continue;
			}
		}

		/* Can't solve it with the simplifier, so do a case
		 * split.  We can do two kinds of case splits: boolean
		 * and arithmetic.  Arithmetic is used if we have
		 * something like (x == 5 && Z) || (x == 7 && Z'),
		 * where being able to subst in the value of x in Z
		 * and Z' is quite helpful.  The rules are like this:
		 *
		 * 1) We split on EntryPoints first.
		 * 2) We split on ControlFlow expressions next.
		 * 3) Then we split on == expressions.  
		 * 4) Finally split on anything else.
		 *
		 * Within a class we pick the thing with the highest
		 * multiplicity.  That's obvious for classes 1, 2, and
		 * 4, but 3 is a bit less obvious.  There, we start by
		 * figuring out what the rewrite rule is going to be,
		 * and pick whichever rule will fire most often.
		 */
		std::set<IRExpr *> allBooleans;
		_sat_checker::findBooleans(frame.remainder, allBooleans);
		/* Other simplifications can sometimes mean that we
		   end up with with things in the remainder which we
		   know to be true or false.  e.g. if we have the
		   initial condition !BadPtr(RBX) && !BadPtr(RDI) &&
		   (RBX == RDI) then we might graph BadPtr(RBX) first,
		   to get

		   (true = !BadPtr(RBX), remainder = !BadPtr(RDI) && (RBX == RDI))

		   Then grab RBX = RDI, to get

		   (true = !BadPtr(RBX), RBX = RDI, remainder = !BadPtr(RBX))

		   Make sure we handle that at least a little bit
		   sensibly. */
		{
			bool redo = false;
			for (auto it = allBooleans.begin();
			     it != allBooleans.end();
			     it++) {
				if (frame.partial_sat.trueBooleans.count(*it)) {
					redo = true;
					frame.remainder = _sat_checker::setVariable(frame.remainder, *it, true);
				}
				if (frame.partial_sat.falseBooleans.count(*it)) {
					redo = true;
					frame.remainder = _sat_checker::setVariable(frame.remainder, *it, false);
				}
			}
			if (redo)
				continue;
		}

		assert(!allBooleans.empty());
		IRExpr *chosenVar = NULL;
		int chosenVarMult;

		/* Shut compiler up */
		chosenVarMult = INT_MAX;

		for (auto it = allBooleans.begin();
		     it != allBooleans.end();
		     it++) {
			IRExpr *possible = *it;
			/* -1 -> don't take, 0 -> take on better mult,
			   1 -> always take */
			int take;
			assert(!frame.partial_sat.trueBooleans.count(possible));
			assert(!frame.partial_sat.falseBooleans.count(possible));
			if (!chosenVar) {
				take = 1;
			} else {
				if (chosenVar->tag == Iex_EntryPoint) {
					if ( (*it)->tag == Iex_EntryPoint )
						take = 0;
					else
						take = -1;
				} else if (chosenVar->tag == Iex_ControlFlow) {
					if ( (*it)->tag == Iex_EntryPoint) {
						take = 1;
					} else if ( (*it)->tag == Iex_ControlFlow ) {
						take = 0;
					} else {
						take = -1;
					}
				} else if (chosenVar->tag == Iex_Binop &&
					   ((IRExprBinop *)chosenVar)->op >= Iop_CmpEQ8 &&
					   ((IRExprBinop *)chosenVar)->op <= Iop_CmpEQ64) {
					if ( (*it)->tag == Iex_EntryPoint ||
					     (*it)->tag == Iex_ControlFlow ) {
						take = 1;
					} else if ( (*it)->tag == Iex_Binop &&
						    ((IRExprBinop *)*it)->op >= Iop_CmpEQ8 &&
						    ((IRExprBinop *)*it)->op <= Iop_CmpEQ64 ) {
						take = 0;
					} else {
						take = -1;
					}
				} else {
					if ( (*it)->tag == Iex_EntryPoint ||
					     (*it)->tag == Iex_ControlFlow ||
					     ( (*it)->tag == Iex_Binop &&
					       ((IRExprBinop *)*it)->op >= Iop_CmpEQ8 &&
					       ((IRExprBinop *)*it)->op <= Iop_CmpEQ64 ) )
						take = 1;
					else
						take = 0;
				}
			}
			switch (take) {
			case -1:
				break;
			case 0: {
				int mult = _sat_checker::variableMultiplicity(frame.remainder, possible);
				if (chosenVar == NULL || mult > chosenVarMult) {
					chosenVar = possible;
					chosenVarMult = mult;
				}
				break;
			}
			case 1:
				chosenVar = possible;
				chosenVarMult = _sat_checker::variableMultiplicity(frame.remainder, possible);
				break;
			default:
				abort();
			}
		}

		assert(chosenVar != NULL);

		/* Do a case split on this variable. */

		if (debug_satisfier)
			printf("Case split on %s\n", nameIRExpr(chosenVar));

		/* Doesn't realloc stack because of reserve() call at
		 * top of loop. */
		stack.push_back(frame);
		frame.partial_sat.makeFalse(chosenVar);
		frame.remainder = _sat_checker::setVariable(frame.remainder, chosenVar, false);
		stack.back().partial_sat.makeTrue(chosenVar);
		stack.back().remainder = _sat_checker::setVariable(stack.back().remainder, chosenVar, true);
		if (debug_satisfier) {
			printf("False case:\n");
			frame.prettyPrint(stdout);
			printf("True case:\n");
			stack.back().prettyPrint(stdout);
		}
	}
}

void
satisfier::prettyPrint(FILE *f) const
{
	fprintf(f, "True:\n");
	for (auto it = trueBooleans.begin(); it != trueBooleans.end(); it++) {
		fprintf(f, "\t");
		ppIRExpr(*it, f);
		fprintf(f, "\n");
	}
	fprintf(f, "False:\n");
	for (auto it = falseBooleans.begin(); it != falseBooleans.end(); it++) {
		fprintf(f, "\t");
		ppIRExpr(*it, f);
		fprintf(f, "\n");
	}
	fprintf(f, "Entry points:\n");
	for (auto it = entryPoints.begin(); it != entryPoints.end(); it++)
		fprintf(f, "\t%d -> %s\n", it->first, it->second.name());
}

sat_enumerator::sat_enumerator(IRExpr *what, const IRExprOptimisations &_opt)
	: opt(_opt)
{
	stack.push_back(stack_entry(satisfier(), what));
	skipToSatisfying();
}

void
satisfier::makeTrue(IRExpr *e)
{
	/* Only boolean assocs are Or1 and And1, and they should be
	   broken down before we get here. */
	assert(e->tag != Iex_Associative);
	/* Likewise Iop_Not1 */
	assert(e->tag != Iex_Unop ||
	       ((IRExprUnop *)e)->op != Iop_Not1);
	/* Shouldn't set something to true twice, or to both true and
	   false. */
	assert(!trueBooleans.count(e));
	assert(!falseBooleans.count(e));

	/* Special rule for entry points */
	if (e->tag == Iex_EntryPoint) {
		IRExprEntryPoint *ee = (IRExprEntryPoint *)e;
		assert(!entryPoints.count(ee->thread));
		entryPoints.insert(std::pair<unsigned, CfgLabel>(ee->thread, ee->label));
	}

	trueBooleans.insert(e);
}

void
satisfier::makeFalse(IRExpr *e)
{
	assert(e->tag != Iex_Associative);
	assert(e->tag != Iex_Unop ||
	       ((IRExprUnop *)e)->op != Iop_Not1);
	assert(!trueBooleans.count(e));
	assert(!falseBooleans.count(e));

	if (e->tag == Iex_EntryPoint) {
		IRExprEntryPoint *ee = (IRExprEntryPoint *)e;
		assert(!entryPoints.count(ee->thread));
	}

	falseBooleans.insert(e);
}

IRExpr *
setVariable(IRExpr *expression, IRExpr *variable, bool value)
{
	return _sat_checker::setVariable(expression, variable, value);
}

