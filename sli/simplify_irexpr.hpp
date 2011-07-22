#ifndef SIMPLIFY_IREXPR_HPP__
#define SIMPLIFY_IREXPR_HPP__

class AllowableOptimisations;
class Oracle;
class OracleInterface;

IRExpr *optimiseIRExprFP(IRExpr *e, const AllowableOptimisations &opt, bool *done_something);
bool isBadAddress(IRExpr *e, const AllowableOptimisations &opt, OracleInterface *oracle);
bool definitelyUnevaluatable(IRExpr *e, const AllowableOptimisations &opt, OracleInterface *oracle);
bool definitelyEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt);
bool definitelyNotEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt);
IRExpr *simplifyIRExpr(IRExpr *a, const AllowableOptimisations &opt);
int exprComplexity(const IRExpr *e);
void addArgumentToAssoc(IRExpr *e, IRExpr *arg);
bool physicallyEqual(const IRConst *a, const IRConst *b);

void sanity_check_irexpr_sorter(void);
void sanity_check_optimiser(void);

#endif /* !SIMPLIFY_IREXPR_HPP__ */
