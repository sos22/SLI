#ifndef SIMPLIFY_IREXPR_HPP__
#define SIMPLIFY_IREXPR_HPP__

class AllowableOptimisations;
class Oracle;
class Oracle;

IRExpr *optimiseIRExprFP(IRExpr *e, const AllowableOptimisations &opt, bool *done_something);
bool isBadAddress(IRExpr *e, const AllowableOptimisations &opt, Oracle *oracle);
bool definitelyUnevaluatable(IRExpr *e, const AllowableOptimisations &opt, Oracle *oracle);
bool definitelyEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt);
bool definitelyNotEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt);
IRExpr *simplifyIRExpr(IRExpr *a, bool *done_something, const AllowableOptimisations &opt);
IRExpr *simplifyIRExpr(IRExpr *a, const AllowableOptimisations &opt);
int exprComplexity(const IRExpr *e);
void addArgumentToAssoc(IRExprAssociative *e, IRExpr *arg);
bool physicallyEqual(const IRConst *a, const IRConst *b);

bool operationCommutes(IROp op);
void sortAssociativeArguments(IRExprAssociative *ae, bool *done_something);

void sanity_check_irexpr_sorter(void);
void sanity_check_optimiser(void);

#endif /* !SIMPLIFY_IREXPR_HPP__ */
