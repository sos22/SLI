#include <stdlib.h>
#include <stdio.h>

#include "sli.h"
#include "nf.hpp"

#define max_nr_variables 8
#define iters_per_test_size 100

static IRExpr *
disjunctive_normal_form(IRExpr *what)
{
        NF_Expression ne;
 	if (!convert_to_nf(what, ne, Iop_Or1, Iop_And1))
		return what;
	return convert_from_nf(ne, Iop_Or1, Iop_And1);
}
	
static double
r()
{
	return (double)random() / RAND_MAX;
}

static IRExpr *
r_expr(int nr_variables, double expandProb)
{
	if (r() < expandProb) {
		if (random() % 3 == 0) {
			return IRExpr_Unop(
				Iop_Not1,
				r_expr(nr_variables, expandProb / 2));
		} else {
			int nr_args = random() % (nr_variables * 4) + 1;
			IROp op;
			if (random() % 2)
				op = Iop_Or1;
			else
				op = Iop_And1;
			IRExprAssociative *res = IRExpr_Associative(nr_args, op);
			for (int i = 0; i < nr_args; i++)
				res->contents[i] = r_expr(nr_variables, expandProb / 2);
			res->nr_arguments = nr_args;
			return res;
		}
	} else {
		return IRExpr_Get(
			threadAndRegister::reg(
				1,
				(random() % nr_variables) * 8,
				-1),
			Ity_I1);
	}
}

struct truth_table {
	bool results[1 << max_nr_variables];
	truth_table() {
		memset(results, 0, sizeof(results));
	}
	bool operator!=(const truth_table &other) const {
		if (memcmp(results, other.results, sizeof(results)))
			return true;
		else
			return false;
	}
};

struct variable_assignment {
	int vals;
};

static bool
eval_expression(IRExpr *what, const variable_assignment *var)
{
	if (what->tag == Iex_Unop) {
		IRExprUnop *ieu = (IRExprUnop *)what;
		assert(ieu->op == Iop_Not1);
		return !eval_expression(ieu->arg, var);
	}
	if (what->tag == Iex_Associative) {
		IRExprAssociative *iea = (IRExprAssociative *)what;
		bool subresults[iea->nr_arguments];
		for (int i = 0; i < iea->nr_arguments; i++)
			subresults[i] = eval_expression(iea->contents[i], var);
		bool acc;
		if (iea->op == Iop_And1) {
			acc = true;
			for (int i = 0; i < iea->nr_arguments; i++)
				acc &= subresults[i];
		} else {
			assert(iea->op == Iop_Or1);
			acc = false;
			for (int i = 0; i < iea->nr_arguments; i++)
				acc |= subresults[i];
		}
		return acc;
	}
	if (what->tag == Iex_Const)
		return ((IRExprConst *)what)->con->Ico.U1;

	assert(what->tag == Iex_Get);
	IRExprGet *ieg = (IRExprGet *)what;
	assert(ieg->reg.tid() == 1);
	assert(ieg->reg.gen() == (unsigned)-1);
	assert(ieg->reg.isReg());
	assert(ieg->reg.asReg() % 8 == 0);
	if (var->vals & (1 << (ieg->reg.asReg() / 8)))
		return true;
	else
		return false;
}

static truth_table
build_truth_table(IRExpr *what, int nr_vars)
{
	truth_table res;
	variable_assignment v;
	for (v.vals = 0; v.vals < (1 << nr_vars); v.vals++)
		res.results[v.vals] = eval_expression(what, &v);
	return res;
}

static void
test_expression(IRExpr *what, const std::map<const CFGNode *, int> &labels, int nr_vars)
{
	truth_table reference = build_truth_table(what, nr_vars);
	IRExpr *normed = disjunctive_normal_form(what);
	truth_table alternate = build_truth_table(normed, nr_vars);
	if (alternate != reference) {
		printf("\nTest failed!\nPre:");
		ppIRExpr(what, labels, stdout);
		printf("\nDNF: ");
		ppIRExpr(normed, labels, stdout);
		printf("\nTruth tables:\n");
		for (int i = 0; i < (1 << nr_vars); i++) {
			if (reference.results[i] == alternate.results[i])
				putc(' ', stdout);
			else if (reference.results[i])
				putc('-', stdout);
			else
				putc('+', stdout);
			for (int j = 0; j < nr_vars; j++)
				printf("%c ", (i & (1 << j)) ? '1' : '0');
			printf("    %c    %c\n",
			       reference.results[i] ? '1' : '0',
			       alternate.results[i] ? '1' : '0');
		}
		printf("\n");
	}
}

static void
test_at_size(int nr_vars)
{
	static internIRExprTable intern;
	static std::set<IRExpr *> alreadyDone;
	std::map<const CFGNode *, int> cfgLabels;

	printf("Test with %d variables...\r", nr_vars);
	for (int i = 0; i < (1 << nr_vars) * iters_per_test_size; i++) {
		if (i % 10 == 0)
			printf("Test with %d variables... (%02d%%)\r",
			       nr_vars,
			       100 * i / ((1 << nr_vars) * iters_per_test_size));
		IRExpr *e = r_expr(nr_vars, 0.5);
		e = internIRExpr(e, intern);
		if (!alreadyDone.insert(e).second) {
			i--;
			continue;
		}
		test_expression(e, cfgLabels, nr_vars);
	}
	printf("\n");
}

int
main()
{
	init_sli();
	for (int i = 1; i < max_nr_variables; i++)
		test_at_size(i);
	return 0;
}
