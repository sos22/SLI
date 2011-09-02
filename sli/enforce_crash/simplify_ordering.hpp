#ifndef SIMPLIFY_ORDERING_HPP__
#define SIMPLIFY_ORDERING_HPP__

#include <set>
class StateMachine;

class HBOrdering {
public:
	bool operator()(const IRExprHappensBefore *, const IRExprHappensBefore *);
};

bool simplifyOrdering(std::set<IRExprHappensBefore *, HBOrdering> &relations,
		      const std::set<IRExprHappensBefore *, HBOrdering> &assumptions);
void extractImplicitOrder(StateMachine *sm, std::set<IRExprHappensBefore *, HBOrdering> &out);

#endif /* !SIMPLIFY_ORDERING_HPP__ */
