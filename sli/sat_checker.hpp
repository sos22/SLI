#ifndef SAT_CHECKER_HPP__
#define SAT_CHECKER_HPP__

class AllowableOptimisations;
class IRExpr;

bool satisfiable(IRExpr *e, const AllowableOptimisations &opt);
IRExpr *simplify_via_anf(IRExpr *a);

#endif /* !SAT_CHECKER_HPP__ */
