#include "sli.h"
#include "state_machine.hpp"

namespace _dupeStateMachine {

class duplication_context {
	typedef void *duplicator_t(duplication_context &ctxt,
				   const void *old);

	struct reloc_t {
		void **ptr;
		const void *old;
		duplicator_t *f;
	};
		
	std::map<const void *, void *> transTable;
	std::vector<reloc_t> relocs;

public:
	template <typename t> void operator()(t **out, const t *inp,
					      t *(*rawDupe)(duplication_context &ctxt,
							    const t *old))
	{
		reloc_t r;
		r.ptr = (void **)out;
		r.old = (const void *)inp;
		r.f = (duplicator_t *)rawDupe;
		relocs.push_back(r);
	}

	void doit(void)
	{
		while (!relocs.empty()) {
			reloc_t r = relocs.back();
			relocs.pop_back();
			auto it = transTable.find(r.old);
			if (it != transTable.end()) {
				*r.ptr = it->second;
				continue;
			}
			void *res = r.f(*this, r.old);
			transTable[r.old] = res;
			*r.ptr = res;
		}
	}
};

static StateMachineSideEffectLoad *
rawDupeS(const StateMachineSideEffectLoad *l)
{
	return new StateMachineSideEffectLoad(l, l->addr);
}

static StateMachineSideEffectStore *
rawDupeS(const StateMachineSideEffectStore *l)
{
	return new StateMachineSideEffectStore(l, l->addr, l->data);
}

static StateMachineSideEffectUnreached *
rawDupeS(const StateMachineSideEffectUnreached *)
{
	return StateMachineSideEffectUnreached::get();
}

static StateMachineSideEffectStartAtomic *
rawDupeS(const StateMachineSideEffectStartAtomic *)
{
	return StateMachineSideEffectStartAtomic::get();
}

static StateMachineSideEffectEndAtomic *
rawDupeS(const StateMachineSideEffectEndAtomic *)
{
	return StateMachineSideEffectEndAtomic::get();
}

static StateMachineSideEffectAssertFalse *
rawDupeS(const StateMachineSideEffectAssertFalse *l)
{
	return new StateMachineSideEffectAssertFalse(l->value, l->reflectsActualProgram);
}

static StateMachineSideEffectCopy *
rawDupeS(const StateMachineSideEffectCopy *l)
{
	return new StateMachineSideEffectCopy(l->target, l->value);
}

static StateMachineSideEffectPhi *
rawDupeS(const StateMachineSideEffectPhi *l)
{
	return new StateMachineSideEffectPhi(l->reg, l->ty, l->generations);
}

static StateMachineSideEffectStartFunction *
rawDupeS(const StateMachineSideEffectStartFunction *l)
{
	return new StateMachineSideEffectStartFunction(l->rsp, l->frame);
}

static StateMachineSideEffectEndFunction *
rawDupeS(const StateMachineSideEffectEndFunction *l)
{
	return new StateMachineSideEffectEndFunction(l->rsp, l->frame);
}

static StateMachineSideEffectImportRegister *
rawDupeS(const StateMachineSideEffectImportRegister *l)
{
	return new StateMachineSideEffectImportRegister(*l);
}

static StateMachineSideEffectStackLayout *
rawDupeS(const StateMachineSideEffectStackLayout *l)
{
	return new StateMachineSideEffectStackLayout(l->functions);
}

static StateMachineSideEffect *
rawDupe(const StateMachineSideEffect *smse)
{
	switch (smse->type) {
#define do_case(n)							\
		case StateMachineSideEffect::n:				\
			return rawDupeS((const StateMachineSideEffect ## n *)smse);
		all_side_effect_types(do_case);
#undef do_case
	}
	abort();
}

static StateMachineState *rawDupe(duplication_context &ctxt, const StateMachineState *inp);

static StateMachineState *
rawDupe(duplication_context &ctxt, const StateMachineState *inp)
{
	switch (inp->type) {
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)inp;
		StateMachineBifurcate *res = new StateMachineBifurcate(smb->dbg_origin, smb->condition, NULL, NULL);
		ctxt(&res->trueTarget, smb->trueTarget, rawDupe);
		ctxt(&res->falseTarget, smb->falseTarget, rawDupe);
		return res;
	}
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *sme = (StateMachineSideEffecting *)inp;
		StateMachineSideEffecting *res = new StateMachineSideEffecting(sme->dbg_origin,
									       sme->sideEffect ? rawDupe(sme->sideEffect) : NULL,
									       NULL);
		ctxt(&res->target, sme->target, rawDupe);
		return res;
	}
	case StateMachineState::Terminal: {
		StateMachineTerminal *smt = (StateMachineTerminal *)inp;
		return new StateMachineTerminal(smt->dbg_origin, smt->res);
	}
	}
	abort();
}

static StateMachine *
rawDupe(duplication_context &ctxt, const StateMachine *inp)
{
	StateMachine *res = new StateMachine((StateMachine *)inp, NULL);
	ctxt(&res->root, inp->root, rawDupe);
	return res;
}

static StateMachine *
duplicateStateMachine(const StateMachine *inp)
{
	duplication_context ctxt;
	StateMachine *res;
	ctxt(&res, inp, rawDupe);
	ctxt.doit();
	return res;
}

/* End of namespace */
};

StateMachine *
duplicateStateMachine(const StateMachine *inp)
{
	return _dupeStateMachine::duplicateStateMachine(inp);
}

