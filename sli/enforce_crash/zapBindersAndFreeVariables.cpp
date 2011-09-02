#include "sli.h"
#include "zapBindersAndFreeVariables.hpp"
#include "offline_analysis.hpp"

class ShortCircuitFvTransformer : public IRExprTransformer {
public:
	FreeVariableMap &fv;
	ShortCircuitFvTransformer(FreeVariableMap &_fv)
		: fv(_fv)
	{}
	IRExpr *transformIex(IRExpr::FreeVariable *e)
	{
		return transformIRExpr(fv.get(e->key));
	}
};

void
zapBindersAndFreeVariables(FreeVariableMap &m, StateMachine *sm)
{
	std::set<StateMachineSideEffectLoad *> loads;
	findAllLoads(sm, loads);
	bool done_something;
	do {
		done_something = false;
		ShortCircuitFvTransformer trans(m);
		m.applyTransformation(trans, &done_something);
	} while (done_something);
}


IRExpr *
zapFreeVariables(IRExpr *src, FreeVariableMap &fv)
{
	ShortCircuitFvTransformer trans(fv);
	return trans.transformIRExpr(src);
}
