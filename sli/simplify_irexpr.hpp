#ifndef SIMPLIFY_IREXPR_HPP__
#define SIMPLIFY_IREXPR_HPP__

class AllowableOptimisations;
class Oracle;
class Oracle;

IRExpr *optimiseIRExprFP(IRExpr *e, const AllowableOptimisations &opt, bool *done_something);
bool isBadAddress(IRExpr *e);
bool definitelyUnevaluatable(IRExpr *e);
bool definitelyEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt);
bool definitelyNotEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt);
IRExpr *simplifyIRExpr(IRExpr *a, const AllowableOptimisations &opt);
void addArgumentToAssoc(IRExprAssociative *e, IRExpr *arg);
bool physicallyEqual(const IRConst *a, const IRConst *b);
bool physicallyEqual(const IRExpr *a, const IRExpr *b);
IRExpr *coerceTypes(IRType, IRExpr *);
IRExpr *expr_eq(IRExpr *, IRExpr *);

void sanity_check_irexpr_sorter(void);
void sanity_check_optimiser(void);

void quickcheck_exprs_eq(const IRExpr *a, const IRExpr *b);

#endif /* !SIMPLIFY_IREXPR_HPP__ */
