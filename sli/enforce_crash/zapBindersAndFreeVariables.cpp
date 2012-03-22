#include "sli.h"
#include "zapBindersAndFreeVariables.hpp"
#include "offline_analysis.hpp"

class ShortCircuitFvTransformer : public IRExprTransformer {
public:
	FreeVariableMap &fv;
	std::map<threadAndRegister, std::pair<IRExpr *, StateMachineSideEffectLoad *>,
		 threadAndRegister::fullCompare > loads;
	ShortCircuitFvTransformer(FreeVariableMap &_fv, std::set<StateMachineSideEffectLoad *> *_loads)
		: fv(_fv)
	{
		if (_loads) {
			for (auto it = _loads->begin(); it != _loads->end(); it++) {
				StateMachineSideEffectLoad *l = *it;
				assert(!loads.count(l->target));
				loads[l->target] = std::pair<IRExpr *, StateMachineSideEffectLoad *>((IRExpr *)NULL, l);
			}
		}
	}
	IRExpr *transformIex(IRExprFreeVariable *e)
	{
		bool done_something = false;
		return transformIRExpr(fv.get(e->key), &done_something);
	}
	IRExpr *transformIex(IRExprGet *e)
	{
		auto it = loads.find(e->reg);
		if (it != loads.end()) {
			assert(e->reg.isTemp());
			auto &res(it->second);
			if (!res.first)
				res.first =IRExpr_Load(Ity_I64, res.second->addr, res.second->rip);
			return res.first;
		}
		return IRExprTransformer::transformIex(e);
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
		ShortCircuitFvTransformer trans(m, &loads);
		m.applyTransformation(trans, &done_something);
	} while (done_something);
}


IRExpr *
zapFreeVariables(IRExpr *src, FreeVariableMap &fv)
{
	ShortCircuitFvTransformer trans(fv, NULL);
	return trans.doit(src);
}
