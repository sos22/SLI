#ifndef SIMPLIFY_IREXPR_HPP__
#define SIMPLIFY_IREXPR_HPP__

#include "bdd.hpp"

class IRExprOptimisations;
class Oracle;
class AllowableOptimisations;

bool isBadAddress(exprbdd *e);
bool definitelyEqual(IRExpr *a, IRExpr *b, const IRExprOptimisations &opt);
bool definitelyEqual(exprbdd *a, exprbdd *b, const IRExprOptimisations &opt);
bool definitelyNotEqual(IRExpr *a, IRExpr *b, const IRExprOptimisations &opt);
bool definitelyNotEqual(exprbdd *a, exprbdd *b, const IRExprOptimisations &opt);
IRExpr *simplifyIRExpr(IRExpr *a, const IRExprOptimisations &opt);
IRExpr *optimiseAssuming(IRExpr *iex, const IRExpr *assumption);
bool physicallyEqual(const IRExpr *a, const IRExpr *b);
IRExpr *coerceTypes(IRType, IRExpr *);
IROp coerceTypesOp(IRType from, IRType to);
IRExpr *expr_eq(IRExpr *, IRExpr *);

template <typename treeT, typename scopeT> treeT *simplifyBDD(scopeT *scope, bbdd::scope *, treeT *bdd, const IRExprOptimisations &opt);
static inline bbdd *simplifyBDD(bbdd::scope *scope, bbdd *bdd, const IRExprOptimisations &opt)
{
	return simplifyBDD(scope, scope, bdd, opt);
}

void sanity_check_irexpr_sorter(void);
void sanity_check_optimiser(void);

#endif /* !SIMPLIFY_IREXPR_HPP__ */
