/* Simple dead code elimination: find binders and registers which are
   never accessed after being set and eliminate them. */
#include "sli.h"
#include "offline_analysis.hpp"

namespace _deadCode {
/* unconfuse emacs */
#if 0
}
#endif

class LivenessEntry : public std::set<threadAndRegister, threadAndRegister::fullCompare> {
	void killRegister(threadAndRegister r)
	{
		erase(r);
	}
public:
	void useExpression(IRExpr *e)
	{
		class _ : public IRExprTransformer {
			LivenessEntry &out;
			IRExpr *transformIex(IRExprGet *g) {
				out.insert(g->reg);
				return IRExprTransformer::transformIex(g);
			}
		public:
			_(LivenessEntry &_out) : out(_out) {}
		} t(*this);
		t.doit(e);
	}

	void useSideEffect(StateMachineSideEffect *smse)
	{
		switch (smse->type) {
		case StateMachineSideEffect::Load: {
			StateMachineSideEffectLoad *smsel =
				(StateMachineSideEffectLoad *)smse;
			killRegister(smsel->target);
			useExpression(smsel->addr);
			return;
		}
		case StateMachineSideEffect::Copy: {
			StateMachineSideEffectCopy *smsec =
				(StateMachineSideEffectCopy *)smse;
			killRegister(smsec->target);
			useExpression(smsec->value);
			return;
		}
		case StateMachineSideEffect::Store: {
			StateMachineSideEffectStore *smses =
				(StateMachineSideEffectStore *)smse;
			useExpression(smses->addr);
			useExpression(smses->data);
			return;
		}
		case StateMachineSideEffect::Unreached:
			return;
		case StateMachineSideEffect::AssertFalse: {
			StateMachineSideEffectAssertFalse *smseaf =
				(StateMachineSideEffectAssertFalse *)smse;
			useExpression(smseaf->value);
			return;
		}
		case StateMachineSideEffect::Phi: {
			StateMachineSideEffectPhi *smsep =
				(StateMachineSideEffectPhi *)smse;
			killRegister(smsep->reg);
			for (auto it = smsep->generations.begin();
			     it != smsep->generations.end();
			     it++) {
				if (it->second)
					useExpression(it->second);
				this->insert(smsep->reg.setGen(it->first));
			}
			return;
		}
		}
		abort();
	}

	void merge(const LivenessEntry &other) {
		for (auto it = other.begin();
		     it != other.end();
		     it++)
			insert(*it);
	}

	bool registerLive(threadAndRegister reg) { return count(reg); }
	bool assertionLive(IRExpr *assertion) {
		if (assertion->tag == Iex_Const)
			return false;
		else
			return true;
	}
};

static StateMachine *
deadCodeElimination(StateMachine *sm, bool *done_something)
{
	std::set<StateMachineState *> allStates;
	findAllStates(sm, allStates);

	/* Stuff referenced by the free variables map is considered to
	   be live everywhere in the program. */
	LivenessEntry alwaysLive;
	for (auto it = sm->freeVariables.content->begin();
	     it != sm->freeVariables.content->end();
	     it++)
		alwaysLive.useExpression(it.value());

	if (TIMEOUT)
		return sm;

	class LivenessMap : public std::map<StateMachineState *, LivenessEntry> {
		void buildResForEdge(LivenessEntry &out, StateMachineEdge *edge)
		{
			out = (*this)[edge->target];
			for (auto it = edge->rbeginSideEffects();
			     it != edge->rendSideEffects();
			     it++)
				out.useSideEffect(*it);
		}

		void updateState(StateMachineState *sm, bool *progress)
		{
			LivenessEntry res;
			switch (sm->type) {
			case StateMachineState::Proxy:
				buildResForEdge(res, ((StateMachineProxy *)sm)->target);
				break;
			case StateMachineState::Bifurcate: {
				StateMachineBifurcate *smb = (StateMachineBifurcate *)sm;
				buildResForEdge(res, smb->trueTarget);
				LivenessEntry res_false;
				buildResForEdge(res_false, smb->falseTarget);
				res.merge(res_false);
				res.useExpression(smb->condition);
				break;
			}
			case StateMachineState::Unreached:
			case StateMachineState::Stub:
			case StateMachineState::Crash:
			case StateMachineState::NoCrash:
				/* Nothing needed */
				break;
			}
			LivenessEntry &outputSlot( (*this)[sm] );
			if (expandSet(outputSlot, res))
				*progress = true;
		}

	public:
		LivenessMap(StateMachine *sm, std::set<StateMachineState *> &allStates) {
			bool progress;
			do {
				progress = false;
				for (auto it = allStates.begin();
				     it != allStates.end();
				     it++)
					updateState(*it, &progress);
			} while (progress && !TIMEOUT);
		}
	} livenessMap(sm, allStates);

	if (TIMEOUT)
		return sm;

	class _ {
		LivenessMap &livenessMap;
		LivenessEntry &alwaysLive;
		bool *done_something;
		FreeVariableMap &fvm;

		void doit(StateMachineEdge *edge, FreeVariableMap &fvm) {
			LivenessEntry alive = livenessMap[edge->target];
			if (edge->sideEffect) {
				StateMachineSideEffect *newEffect = NULL;
				StateMachineSideEffect *e = edge->sideEffect;
				bool dead = false;
				switch (e->type) {
				case StateMachineSideEffect::Load: {
					StateMachineSideEffectLoad *smsel =
						(StateMachineSideEffectLoad *)e;
					if (!alwaysLive.registerLive(smsel->target) &&
					    !alive.registerLive(smsel->target))
						newEffect = new StateMachineSideEffectAssertFalse(
							IRExpr_Unop(Iop_BadPtr, smsel->addr));
					break;
				}
				case StateMachineSideEffect::Store:
				case StateMachineSideEffect::Unreached:
					break;
				case StateMachineSideEffect::AssertFalse: {
					StateMachineSideEffectAssertFalse *a =
						(StateMachineSideEffectAssertFalse *)e;
					if (edge->target->isTerminal() ||
					    !alive.assertionLive(a->value))
						dead = true;
					break;
				}
				case StateMachineSideEffect::Copy: {
					StateMachineSideEffectCopy *smsec =
						(StateMachineSideEffectCopy *)e;
					if (smsec->value->tag == Iex_Get &&
					    threadAndRegister::fullEq(((IRExprGet *)smsec->value)->reg, smsec->target)) {
						/* Copying a register
						   or temporary back
						   to itself is always
						   dead, regardless of
						   what liveness
						   analysis proper
						   might say. */
						dead = true;
					} else {
						dead = !alive.registerLive(smsec->target) &&
							!alwaysLive.registerLive(smsec->target);
					}
					break;
				}
				case StateMachineSideEffect::Phi: {
					StateMachineSideEffectPhi *p =
						(StateMachineSideEffectPhi *)e;
					if (!alive.registerLive(p->reg) &&
					    !alwaysLive.registerLive(p->reg))
						dead = true;
					break;
				}
				}

				if (dead) {
					*done_something = true;
					edge->sideEffect = NULL;
				} else if (newEffect) {
					*done_something = true;
					edge->sideEffect = newEffect;
					alive.useSideEffect(newEffect);
				} else {
					alive.useSideEffect(e);
				}
			}
		}
	public:
		void operator()(StateMachineState *state) {
			switch (state->type) {
			case StateMachineState::Proxy:
				doit(((StateMachineProxy *)state)->target, fvm);
				return;
			case StateMachineState::Bifurcate: {
				StateMachineBifurcate *smb = (StateMachineBifurcate *)state;
				doit(smb->trueTarget, fvm);
				doit(smb->falseTarget, fvm);
				return;
			}
			case StateMachineState::Crash:
			case StateMachineState::NoCrash:
			case StateMachineState::Stub:
			case StateMachineState::Unreached:
				/* Nothing needed */
				return;
			}
			abort();
		}

		_(LivenessMap &_livenessMap, LivenessEntry &_alwaysLive,
		  bool *_done_something, FreeVariableMap &_fvm)
			: livenessMap(_livenessMap), alwaysLive(_alwaysLive),
			  done_something(_done_something), fvm(_fvm)
		{}
	} eliminateDeadCode(livenessMap, alwaysLive, done_something, sm->freeVariables);

	for (auto it = allStates.begin();
	     it != allStates.end();
	     it++) {
		if (TIMEOUT)
			return sm;
		eliminateDeadCode(*it);
	}

	return sm;
}

/* end of namespace */
}

StateMachine *
deadCodeElimination(StateMachine *sm, bool *done_something)
{
	return _deadCode::deadCodeElimination(sm, done_something);
}

