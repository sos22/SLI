#ifndef SAT_CHECKER_HPP__
#define SAT_CHECKER_HPP__

class AllowableOptimisations;
class IRExpr;

bool satisfiable(IRExpr *e, const AllowableOptimisations &opt);

#endif /* !SAT_CHECKER_HPP__ */
