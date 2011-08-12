#ifndef SIMPLIFY_ORDERING_HPP__
#define SIMPLIFY_ORDERING_HPP__

#include <set>
class StateMachine;

bool simplifyOrdering(std::set<IRExpr::HappensBefore> &relations,
		      const std::set<IRExpr::HappensBefore> &assumptions);
void extractImplicitOrder(StateMachine *sm, std::set<IRExpr::HappensBefore> &out);

bool operator<(const IRExpr::HappensBefore &a, const IRExpr::HappensBefore &b);

#endif /* !SIMPLIFY_ORDERING_HPP__ */
