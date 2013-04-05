/* Bits for simplifying a BDD to take advantage of known-true
   equalities at interesting points in the graph. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "simplify_irexpr.hpp"
#include "bdd.hpp"
#include "allowable_optimisations.hpp"

#include "subst_eq_tmpl.cpp"

namespace substeq {

#ifndef NDEBUG
bool debug_subst_eq = false;
#else
#define debug_subst_eq false
#endif

void
printExprSet(const std::set<IRExpr *> &a, FILE *f)
{
	fprintf(f, "{");
	for (auto it = a.begin(); it != a.end(); it++) {
		if (it != a.begin()) {
			fprintf(f, ", ");
		}
		ppIRExpr(*it, f);
	}
	fprintf(f, "}");
}

/* Estimate of the amount of bytecode we need to emit to validate
   @what, or nothing if the expression can't be bytecode evaled. */
static Maybe<int>
complexity(IRExpr *what, sane_map<IRExpr *, Maybe<int> > &memo)
{
	/* A couple of easy cases without looking in the hash
	   table. */
	if (what->tag == Iex_EntryPoint) {
		/* EntryPoints can usually be done at compile time
		   without any bytecode at all. */
		return 0;
	}
	if (what->tag == Iex_Get || what->tag == Iex_Const ||
	    what->tag == Iex_HappensBefore || what->tag == Iex_ControlFlow) {
		return 1;
	}
	if (what->tag == Iex_CCall || what->tag == Iex_FreeVariable ||
	    what->tag == Iex_GetI) {
		return Maybe<int>::nothing();
	}
	auto it_did_insert = memo.insert(what, -99999);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second;
	}
	switch (what->tag) {
	case Iex_Get:
	case Iex_GetI:
		abort();
	case Iex_Qop: {
		IRExprQop *q = (IRExprQop *)what;
		it->second = complexity(q->arg1, memo) +
			complexity(q->arg2, memo) +
			complexity(q->arg3, memo) +
			complexity(q->arg4, memo) +
			1;
		break;
	}
	case Iex_Triop: {
		IRExprTriop *q = (IRExprTriop *)what;
		it->second = complexity(q->arg1, memo) +
			complexity(q->arg2, memo) +
			complexity(q->arg3, memo) +
			1;
		break;
	}
	case Iex_Binop: {
		IRExprBinop *q = (IRExprBinop *)what;
		it->second = complexity(q->arg1, memo) +
			complexity(q->arg2, memo) +
			1;
		break;
	}
	case Iex_Unop: {
		IRExprUnop *q = (IRExprUnop *)what;
		it->second = complexity(q->arg, memo) +
			1;
		break;
	}
	case Iex_Const:
		abort();
	case Iex_Mux0X:
		/* Shouldn't be any, because this is pulled out of a BDD */
		abort();
	case Iex_CCall:
		abort();
	case Iex_Associative: {
		IRExprAssociative *q = (IRExprAssociative *)what;
		Maybe<int> acc(0);
		if ((q->op >= Iop_And8 && q->op <= Iop_And64) ||
		    (q->op >= Iop_Or8 && q->op <= Iop_Or64) ||
		    q->op == Iop_Or1 || q->op == Iop_And1) {
			for (int i = 0; i < q->nr_arguments; i++) {
				auto j(complexity(q->contents[i], memo));
				if (j.valid) {
					acc = acc + j;
				}
			}
		} else {
			for (int i = 0; i < q->nr_arguments; i++) {
				acc = acc + complexity(q->contents[i], memo);
			}
		}
		it->second = acc;
		break;
	}
	case Iex_Load:
		it->second = complexity(((IRExprLoad *)what)->addr, memo) + 1;
		break;
	case Iex_HappensBefore:
	case Iex_FreeVariable:
	case Iex_EntryPoint:
	case Iex_ControlFlow:
		abort();
	}
	return it->second;
}

enum rewrite_order {
	rewrite_l2r, rewrite_eq, rewrite_r2l
};

/* Decide whether we want to rewrite from l to r or from r to l.  The
   aim here is to reduce the amount of bytecode we need to emit in
   order to validate them.  */
static rewrite_order
rewriteOrder(IRExpr *l, IRExpr *r)
{
	if (l == r) {
		return rewrite_eq;
	}
	sane_map<IRExpr *, Maybe<int> > complex_memo;
	auto l_complex = complexity(l, complex_memo);
	auto r_complex = complexity(r, complex_memo);
	if (l_complex.valid && r_complex.valid) {
		if (l_complex.content < r_complex.content) {
			return rewrite_r2l;
		} else if (r_complex.content < l_complex.content) {
			return rewrite_l2r;
		}
		/* Note fall-through */
	} else if (l_complex.valid && !r_complex.valid) {
		return rewrite_r2l;
	} else if (!l_complex.valid && r_complex.valid) {
		return rewrite_l2r;
	} else {
		assert(!l_complex.valid && !r_complex.valid);
	}

	if (l < r) {
		return rewrite_r2l;
	} else {
		return rewrite_l2r;
	}
}

bool
isEqConstraint(IRExpr *what)
{
	if (what->tag != Iex_Binop) {
		return false;
	}
	IROp op = ((IRExprBinop *)what)->op;
	return op >= Iop_CmpEQ8 && op <= Iop_CmpEQ64;
}

IRExpr *
do_rewrite(IRExpr *what, const std::map<IRExpr *, IRExpr *> &rewrites)
{
	struct : public IRExprTransformer {
		const std::map<IRExpr *, IRExpr *> *rewrites;
		IRExpr *transformIRExpr(IRExpr *e) {
			auto it = rewrites->find(e);
			if (it != rewrites->end()) {
				return it->second;
			}
			return IRExprTransformer::transformIRExpr(e);
		}
	} doit;
	doit.rewrites = &rewrites;
	return doit.doit(what);
}

void
addRewritesFor(std::map<IRExpr *, IRExpr *> &rules,
	       std::map<qs_args, IRExpr *> &simplMemo,
	       IRExpr *expr)
{
	assert(isEqConstraint(expr));
	IRExpr *arg1 = ((IRExprBinop *)expr)->arg1;
	IRExpr *arg2 = ((IRExprBinop *)expr)->arg2;

	if (arg1 == arg2) {
		/* Special case, to avoid a potential infinite loop. */
		rules[expr] = IRExpr_Const_U1(1);
		return;
	}

	if (arg1->tag == Iex_Const &&
	    arg2->tag == Iex_Associative &&
	    ((IRExprAssociative *)arg2)->op >= Iop_Add8 &&
	    ((IRExprAssociative *)arg2)->op <= Iop_Add64) {
		/* Bit of a special case: if we have k == x + y,
		   consider using the rule x == y - k instead,
		   because that sometimes helps a bit. */
		IRExprAssociative *arg2a = (IRExprAssociative *)arg2;
		Maybe<int> complexities[arg2a->nr_arguments];
		sane_map<IRExpr *, Maybe<int> > memo;
		int nr_uneval = 0;
		for (int i = 0; nr_uneval < 2 && i < arg2a->nr_arguments; i++) {
			complexities[i] = complexity(arg2a->contents[i], memo);
			nr_uneval += complexities[i].valid == false;
		}
		/* If we have multiple unevaluatable sub-expressions
		   then we just give up and rewrite the whole RHS to
		   the LHS. */
		if (nr_uneval > 1) {
			rules[arg2] = arg1;
			return;
		}
		IRExpr *args[arg2a->nr_arguments];
		IRExpr *lhs = NULL;
		int j = 0;
		if (nr_uneval == 1) {
			/* If we have precisely one unevalable then
			   that goes on the left and everything else
			   goes on the right. */
			for (int i = 0; i < arg2a->nr_arguments; i++) {
				if (complexities[i].valid) {
					args[j++] = arg2a->contents[i];
				} else {
					assert(!lhs);
					lhs = arg2a->contents[i];
				}
			}
		} else {
			/* Okay, all expressions evaluatable.  Rewrite
			   to remove the most complicated one. */
			int bestIdx = 0;
			assert(complexities[0].valid);
			for (int i = 1; i < arg2a->nr_arguments; i++) {
				assert(complexities[i].valid);
				if (complexities[i].content > complexities[bestIdx].content) {
					bestIdx = i;
				}
			}
			lhs = arg2a->contents[bestIdx];
			for (int i = 0; i < arg2a->nr_arguments; i++) {
				if (i != bestIdx) {
					args[j++] = arg2a->contents[i];
				}
			}
		}
		assert(lhs);
		switch (arg2a->op) {
		case Iop_Add8:
			lhs = IRExpr_Unop(Iop_Neg8, lhs);
			break;
		case Iop_Add16:
			lhs = IRExpr_Unop(Iop_Neg16, lhs);
			break;
		case Iop_Add32:
			lhs = IRExpr_Unop(Iop_Neg32, lhs);
			break;
		case Iop_Add64:
			lhs = IRExpr_Unop(Iop_Neg64, lhs);
			break;
		default:
			abort();
		}
		lhs = quickSimplify(qs_args(lhs), simplMemo);
		assert(j == arg2a->nr_arguments - 1);
		IRExprConst *arg1c = (IRExprConst *)arg1;
		IRExprConst *transConst = NULL;
		switch (arg1c->Ico.ty) {
		case Ity_I1:
			abort();
		case Ity_I8:
			if (arg1c->Ico.content.U8 != 0) {
				transConst = IRExpr_Const_U8(
					-arg1c->Ico.content.U8);
			}
			break;
		case Ity_I16:
			if (arg1c->Ico.content.U16 != 0) {
				transConst = IRExpr_Const_U16(
					-arg1c->Ico.content.U16);
			}
			break;
		case Ity_I32:
			if (arg1c->Ico.content.U32 != 0) {
				transConst = IRExpr_Const_U32(
					-arg1c->Ico.content.U32);
			}
			break;
		case Ity_I64:
			if (arg1c->Ico.content.U64 != 0) {
				transConst = IRExpr_Const_U64(
					-arg1c->Ico.content.U64);
			}
			break;
		case Ity_I128:
		case Ity_INVALID:
			abort();
		}
		if (transConst) {
			args[j++] = transConst;
		}
		IRExpr *rhs = quickSimplify(
			qs_args(IRExpr_Associative_Copy(
					arg2a->op,
					j,
					args)),
			simplMemo);
		rules[lhs] = rhs;
		return;
	}

	switch (rewriteOrder(arg1, arg2)) {
	case rewrite_l2r:
		rules[arg1] = arg2;
		return;
	case rewrite_r2l:
		rules[arg2] = arg1;
		return;
	case rewrite_eq:
		abort();
	}
	abort();
}

bool
bbdd_fbf(bbdd *n)
{
	return n->internal().falseBranch->isLeaf() &&
		!n->internal().falseBranch->leaf();
}

/* End of namespace */
}

bbdd *
subst_eq(bbdd::scope *scope, bbdd *what)
{
	return tmpl_subst_eq<bbdd::scope, bbdd, substeq::bbdd_fbf>(scope, what);
}
