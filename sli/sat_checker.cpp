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

namespace _sat_checker {

static struct stats {
	unsigned nr_invoked;
	unsigned initial_constant;
	unsigned anf_resolved;
	unsigned cnf_resolved;
	unsigned dnf_resolved;
	unsigned exhaustive_resolved;
	unsigned failed;
	~stats() {
		printf("Sat checker invoked %d times.  Results:\n", nr_invoked);
#define do_field(name)							\
		printf("\t" # name ":\t%f%%\n", 100.0 * name / nr_invoked)
		do_field(initial_constant);
		do_field(anf_resolved);
		do_field(cnf_resolved);
		do_field(dnf_resolved);
		do_field(exhaustive_resolved);
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

static bool
anf_sort_func(IRExpr *a, IRExpr *b)
{
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
	int a_depth = anf_depth(a);
	int b_depth = anf_depth(b);
	if (a_depth < b_depth)
		return true;
	if (a_depth > b_depth)
		return false;
	assert(a_depth == b_depth);
	if (a_depth != 0) {
		assert(a->tag == Iex_Associative);
		assert(b->tag == Iex_Associative);
		IRExprAssociative *iex_a = (IRExprAssociative *)a;
		IRExprAssociative *iex_b = (IRExprAssociative *)b;
		assert(iex_a->op == Iop_And1);
		assert(iex_b->op == Iop_And1);
		for (int i = 0; i < iex_a->nr_arguments && i < iex_b->nr_arguments; i++) {
			if ( anf_sort_func(iex_a->contents[i], iex_b->contents[i]) )
				return true;
			if ( anf_sort_func(iex_b->contents[i], iex_a->contents[i]) )
				return false;
		}
		if (iex_a->nr_arguments < iex_b->nr_arguments)
			return true;
		if (iex_a->nr_arguments > iex_b->nr_arguments)
			return false;
	}
	if (a < b)
		return true;
	if (a > b)
		return false;
	return inv_a < inv_b;		
}

class compare_args {
public:
	bool operator()(IRExpr *a, IRExpr *b) {
		return anf_sort_func(a, b);
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
			assert(iex->contents[i-1] == iex->contents[i] ||
			       anf_sort_func(iex->contents[i-1], iex->contents[i]));
	}
}

/* And normal form means that we can use Iop_And1 and Iop_Not1, but
   not Iop_Or1. */
static IRExpr *
and_normal_form(IRExpr *e, internIRExprTable &intern)
{
	e = internIRExpr(e, intern);
	if (e->tag == Iex_Unop) {
		IRExprUnop *ieu = (IRExprUnop *)e;
		if (ieu->op == Iop_Not1) {
			IRExpr *arg2 = and_normal_form(ieu->arg, intern);
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
			res->nr_arguments = iea->nr_arguments;
			sort_and_arguments(res->contents, res->nr_arguments);
			e = internIRExpr(IRExpr_Unop(Iop_Not1, res), intern);
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
	void directlyIntroduceExpression(IRExpr *a, bool isTrue);
	void directlyIntroduceExpression(std::set<IRExpr *>::iterator begin,
					 std::set<IRExpr *>::iterator end,
					 bool isTrue)
	{
		for (auto it = begin; it != end; it++)
			directlyIntroduceExpression(*it, isTrue);
	}
	void addAssumption(IRExpr *a);
	void saturateAndAdd(bool isTrue, IRExpr *what);
	void saturateAndAdd(std::set<IRExpr *> &out,
			    IRExpr *input,
			    IRExpr *a,
			    IRExpr *b);
	void introduceEqRule(IRExpr *a, IRExpr *b);
public:
	anf_context(internIRExprTable &_intern)
		: intern(_intern)
	{}
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
anf_context::directlyIntroduceExpression(IRExpr *what, bool isTrue)
{
	what = pureSimplify(what, intern);
	if (what->tag == Iex_Const)
		return;
	std::set<IRExpr *> newTrue;
	IRExpr *val = IRExpr_Const(IRConst_U1(isTrue));
	for (auto it = definitelyTrue.begin(); it != definitelyTrue.end(); it++)
		newTrue.insert(rewriteIRExpr(*it, what, val, intern));
	std::set<IRExpr *> newFalse;
	for (auto it = definitelyFalse.begin(); it != definitelyFalse.end(); it++)
		newFalse.insert(rewriteIRExpr(*it, what, val, intern));
	if (isTrue)
		newTrue.insert(what);
	else
		newFalse.insert(what);
	definitelyTrue = newTrue;
	definitelyFalse = newFalse;
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

	/* Generate new definitely-true and definitely-false terms, if necessary */
	std::set<IRExpr *> newDefinitelyTrue;
	for (auto it = definitelyTrue.begin(); it != definitelyTrue.end(); it++)
		saturateAndAdd(newDefinitelyTrue, *it, a, b);
	directlyIntroduceExpression(newDefinitelyTrue.begin(), newDefinitelyTrue.end(), true);
	std::set<IRExpr *> newDefinitelyFalse;
	for (auto it = definitelyFalse.begin(); it != definitelyFalse.end(); it++)
		saturateAndAdd(newDefinitelyFalse, *it, a, b);
	directlyIntroduceExpression(newDefinitelyFalse.begin(), newDefinitelyFalse.end(), false);

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
anf_context::saturateAndAdd(std::set<IRExpr *> &out,
			    IRExpr *what,
			    IRExpr *rule_a,
			    IRExpr *rule_b)
{
	NdChooser chooser;
	do {
		struct : public IRExprTransformer {
			IRExpr *a;
			IRExpr *b;
			NdChooser *chooser;
			IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
				if (e == a || e == b) {
					if (chooser->nd_choice(2)) {
						if (e != a)
							*done_something = true;
						return a;
					} else {
						if (e != b)
							*done_something = true;
						return b;
					}
				}
				return IRExprTransformer::transformIRExpr(e, done_something);
			}
		} doit;
		doit.a = (IRExpr *)rule_a;
		doit.b = (IRExpr *)rule_b;
		doit.chooser = &chooser;
		out.insert(internIRExpr(doit.doit((IRExpr *)what), intern));
	} while (chooser.advance());
}

void
anf_context::saturateAndAdd(bool isTrue, IRExpr *what)
{
	std::set<IRExpr *> saturated;
	saturated.insert(what);
	for (auto it = eqRules.begin(); it != eqRules.end(); it++) {
		std::set<IRExpr *> newSat;
		for (auto it2 = saturated.begin(); it2 != saturated.end(); it2++)
			saturateAndAdd(newSat, *it2, it->first, it->second);
		saturated = newSat;
	}
	directlyIntroduceExpression(saturated.begin(), saturated.end(), isTrue);
}

void
anf_context::addAssumption(IRExpr *a)
{
	if (a->tag == Iex_Const)
		return;
	if (a->tag == Iex_Unop &&
	    ((IRExprUnop *)a)->op == Iop_Not1)
		saturateAndAdd(false, ((IRExprUnop *)a)->arg);
	else
		saturateAndAdd(true, a);
	if (a->tag == Iex_Binop) {
		IRExprBinop *ieb = (IRExprBinop *)a;
		if (ieb->op == Iop_CmpEQ64) {
			if (ieb->arg1->tag == Iex_Const &&
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
		}
	}
}

IRExpr *
anf_context::simplify(IRExpr *a)
{
	if (0)
		prettyPrint(stdout);
	if (a->type() != Ity_I1)
		return a;
	if (definitelyTrue.count(a))
		return internIRExpr(IRExpr_Const(IRConst_U1(1)), intern);
	if (definitelyFalse.count(a))
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
		return internIRExpr(
			IRExpr_Unop(
				Iop_Not1,
				arg),
			intern);
	} else if (a->tag == Iex_Associative) {
		IRExprAssociative *iea = (IRExprAssociative *)a;
		assert(iea->op != Iop_Or1);
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
		return internIRExpr(res, intern);
	} else {
		return a;
	}
}

/* @a is in and-normal-form (i.e. the boolean level only uses Iop_And1
 * and Iop_Not1 operators, but not Iop_Or1).  See if there are any
 * interesting simplifications we can do based on that. */
static IRExpr *
anf_simplify(IRExpr *a, internIRExprTable &intern)
{
	a = internIRExpr(a, intern);
	while (1) {
		anf_context ctxt(intern);
		IRExpr *a2 = ctxt.simplify(a);
		if (a == a2)
			return a2;
		a = a2;
	}
}

static IRExpr *
simplify_via_anf(IRExpr *a)
{
	internIRExprTable table;
	a = internIRExpr(a, table);
	IRExpr *normed = and_normal_form(a, table);
	return anf_simplify(normed, table);
}

static IRExpr *
conjunctive_normal_form(IRExpr *what)
{
	NF_Expression ne;
	Maybe<bool> res = convert_to_nf(what, ne, Iop_And1, Iop_Or1);
	if (res == Maybe<bool>::just(true)) {
		if (ne.size() == 0)
			return IRExpr_Const(IRConst_U1(1));
		return convert_from_nf(ne, Iop_And1, Iop_Or1);
	}
	if (res == Maybe<bool>::just(false))
		return IRExpr_Const(IRConst_U1(0));
	return what;
}

static IRExpr *
disjunctive_normal_form(IRExpr *what)
{
	NF_Expression ne;
	Maybe<bool> res = convert_to_nf(what, ne, Iop_Or1, Iop_And1);
	if (res == Maybe<bool>::just(true)) {
		if (ne.size() == 0)
			return IRExpr_Const(IRConst_U1(0));
		return convert_from_nf(ne, Iop_Or1, Iop_And1);
	}
	if (res == Maybe<bool>::just(false))
		return IRExpr_Const(IRConst_U1(1));
	return what;
}

static bool
evalExpression(IRExpr *e, NdChooser &chooser, std::map<IRExpr *, std::pair<bool, bool> > &memo)
{
	assert(e->type() == Ity_I1);
	if (e->tag == Iex_Const)
		return ((IRExprConst *)e)->con->Ico.U1 != 0;

	std::pair<bool, bool> falsefalse = std::pair<bool, bool>(false, false);
	auto it_did_insert = memo.insert(std::pair<IRExpr *, std::pair<bool, bool> >(e, falsefalse));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (e->tag == Iex_Unop &&
		    ((IRExprUnop *)e)->op == Iop_Not1) {
			it->second.first = !evalExpression(((IRExprUnop *)e)->arg, chooser, memo);
		} else if (e->tag == Iex_Associative &&
			   ((IRExprAssociative *)e)->op == Iop_And1) {
			IRExprAssociative *a = (IRExprAssociative *)e;
			bool acc = true;
			for (int i = 0; i < a->nr_arguments && acc; i++)
				acc &= evalExpression(a->contents[i], chooser, memo);
			it->second.first = acc;
		} else if (e->tag == Iex_Associative &&
			   ((IRExprAssociative *)e)->op == Iop_Or1) {
			IRExprAssociative *a = (IRExprAssociative *)e;
			bool acc = false;
			for (int i = 0; i < a->nr_arguments && !acc; i++)
				acc |= evalExpression(a->contents[i], chooser, memo);
			it->second.first = acc;
		} else {
			it->second.first = !!chooser.nd_choice(2);
			it->second.second = true;
		}
	}
	return it->second.first;
}

static bool
evalExpression(IRExpr *e, NdChooser &chooser)
{
	std::map<IRExpr *, std::pair<bool, bool> > memo;
	bool r = evalExpression(e, chooser, memo);
	if (r) {
		fprintf(_logfile, "Satisfying assignment:\n");
		for (auto it = memo.begin(); it != memo.end(); it++) {
			if (it->second.second) {
				fprintf(_logfile, "\t");
				ppIRExpr(it->first, _logfile);
				fprintf(_logfile, "\t-> %s\n",
					it->second.first ? "true" : "false");
			}
		}
		dbg_break("HELLO\n");
	}
	return r;
}

static bool
satisfiable(IRExpr *e, const AllowableOptimisations &opt)
{
	sat_checker_counters.nr_invoked++;

	assert(e->type() == Ity_I1);
	Maybe<bool> res(isTrue(e));

	if (res.valid) {
		sat_checker_counters.initial_constant++;
		return res.content;
	}

	internIRExprTable intern;
	e = internIRExpr(e, intern);

	IRExpr *norm1 = and_normal_form(e, intern);
	check_and_normal_form(norm1);
	norm1 = anf_simplify(norm1, intern);
	norm1 = simplifyIRExpr(norm1, opt);
	res = isTrue(norm1);
	if (res.valid) {
		sat_checker_counters.anf_resolved++;
		return res.content;
	}

	IRExpr *norm2 = conjunctive_normal_form(norm1);
	norm2 = simplifyIRExpr(norm2, opt);
	res = isTrue(norm2);
	if (res.valid) {
		sat_checker_counters.cnf_resolved++;
		return res.content;
	}
	IRExpr *norm3 = disjunctive_normal_form(norm2);
	norm3 = simplifyIRExpr(norm3, opt);
	res = isTrue(norm3);
	if (res.valid) {
		sat_checker_counters.dnf_resolved++;
		return res.content;
	}

	/* Okay, that's about as far as we can push that.  Fall back
	   to an exhaustive search. */
	NdChooser chooser;
	do {
		if (evalExpression(norm3, chooser)) {
			sat_checker_counters.failed++;
			return true;
		}
	} while (chooser.advance());
	sat_checker_counters.exhaustive_resolved++;
	return true;
}

/* End of namespace */
};

bool
satisfiable(IRExpr *e, const AllowableOptimisations &opt)
{
	return _sat_checker::satisfiable(e, opt);
}

IRExpr *
simplify_via_anf(IRExpr *a)
{
	return _sat_checker::simplify_via_anf(a);
}

