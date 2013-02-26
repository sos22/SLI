#ifndef SIMPLIFY_IREXPR_HPP__
#define SIMPLIFY_IREXPR_HPP__

#include "bdd.hpp"

class IRExprOptimisations;
class Oracle;
class AllowableOptimisations;

bool definitelyEqual(IRExpr *a, IRExpr *b, const IRExprOptimisations &opt);
bool definitelyEqual(exprbdd *a, exprbdd *b, const IRExprOptimisations &opt);
bool definitelyNotEqual(IRExpr *a, IRExpr *b, const IRExprOptimisations &opt);
bool definitelyNotEqual(exprbdd *a, exprbdd *b, const IRExprOptimisations &opt);
IRExpr *simplifyIRExpr(IRExpr *a, const IRExprOptimisations &opt);
IRExpr *optimiseAssuming(IRExpr *iex, const IRExpr *assumption);
IRExpr *coerceTypes(IRType, IRExpr *);
IROp coerceTypesOp(IRType from, IRType to);
IRExpr *expr_eq(IRExpr *, IRExpr *);
IRExpr *optimise_condition_calculation(IRExpr *_cond,
				       IRExpr *cc_op,
				       IRExpr *dep1,
				       IRExpr *dep2);

#define INACCESSIBLE_ADDRESS ((exprbdd *)0xf001)
template <typename treeT, typename scopeT> treeT *simplifyBDD(scopeT *scope, bbdd::scope *, treeT *bdd, bool isAddress, const IRExprOptimisations &opt);
static inline bbdd *simplifyBDD(bbdd::scope *scope, bbdd *bdd, const IRExprOptimisations &opt)
{
	return simplifyBDD(scope, scope, bdd, false, opt);
}

void sanity_check_irexpr_sorter(void);
void sanity_check_optimiser(void);

bbdd *subst_eq(bbdd::scope *scope, bbdd *what);

#endif /* !SIMPLIFY_IREXPR_HPP__ */
