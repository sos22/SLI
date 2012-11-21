#ifndef SIMPLIFY_IREXPR_HPP__
#define SIMPLIFY_IREXPR_HPP__

#include "bdd.hpp"

class IRExprOptimisations;
class Oracle;
class AllowableOptimisations;

IRExpr *optimiseIRExprFP(IRExpr *e, const IRExprOptimisations &opt, bool *done_something);
bool isBadAddress(IRExpr *e);
bool definitelyEqual(IRExpr *a, IRExpr *b, const IRExprOptimisations &opt);
bool definitelyNotEqual(IRExpr *a, IRExpr *b, const IRExprOptimisations &opt);
IRExpr *simplifyIRExpr(IRExpr *a, const IRExprOptimisations &opt);
IRExpr *optimiseAssuming(IRExpr *iex, const IRExpr *assumption);
void addArgumentToAssoc(IRExprAssociative *e, IRExpr *arg);
bool physicallyEqual(const IRExpr *a, const IRExpr *b);
IRExpr *coerceTypes(IRType, IRExpr *);
IRExpr *expr_eq(IRExpr *, IRExpr *);

template <typename treeT, typename scopeT> treeT *simplifyBDD(scopeT *scope, bbdd::scope *, treeT *bdd, const AllowableOptimisations &opt, bool *done_something);
static inline bbdd *simplifyBDD(bbdd::scope *scope, bbdd *bdd, const AllowableOptimisations &opt, bool *done_something)
{
	return simplifyBDD(scope, scope, bdd, opt, done_something);
}

void sanity_check_irexpr_sorter(void);
void sanity_check_optimiser(void);

#endif /* !SIMPLIFY_IREXPR_HPP__ */
