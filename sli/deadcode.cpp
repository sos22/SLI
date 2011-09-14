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
		t.transformIRExpr(e);
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
			     it++)
				this->insert(smsep->reg.setGen(*it));
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
		class _ : public IRExprTransformer {
			LivenessEntry *_this;

			IRExpr *transformIex(IRExprGet *g) {
				if (_this->registerLive(g->reg))
					res = true;
				return IRExprTransformer::transformIex(g);
			}
		public:
			bool res;
			_(LivenessEntry *__this)
				: _this(__this), res(false)
			{}
		} t(this);
		t.transformIRExpr(assertion);
		return t.res;
	}
};

static StateMachine *
deadCodeElimination(StateMachine *sm, bool *done_something)
{
	std::set<StateMachineState *> allStates;
	findAllStates(sm, allStates);

	class LivenessMap : public std::map<StateMachineState *, LivenessEntry> {
		void buildResForEdge(LivenessEntry &out, StateMachineEdge *edge)
		{
			out = (*this)[edge->target];
			for (auto it = edge->sideEffects.rbegin();
			     it != edge->sideEffects.rend();
			     it++)
				out.useSideEffect(*it);
		}

		void updateState(StateMachineState *sm, bool *progress)
		{
			LivenessEntry &outputSlot( (*this)[sm] );
			LivenessEntry res;
			if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm)) {
				buildResForEdge(res, smp->target);
			} else if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(sm)) {
				buildResForEdge(res, smb->trueTarget);
				LivenessEntry res_false;
				buildResForEdge(res_false, smb->falseTarget);
				res.merge(res_false);
				res.useExpression(smb->condition);
			} else if (StateMachineStub *sms = dynamic_cast<StateMachineStub *>(sm)) {
				res.useExpression(sms->target);
			} else if (dynamic_cast<StateMachineTerminal *>(sm)) {
				/* Nothing needed */
			} else {
				abort();
			}
			/* set != set doesn't work if the set uses a
			 * custom ordering predicate; grr.  Do it by
			 * hand. */
			bool eq = true;
			auto it1 = outputSlot.begin();
			auto it2 = res.begin();
			while (eq && it1 != outputSlot.end() && it2 != res.end()) {
				if (!threadAndRegister::fullEq(*it1, *it2))
					eq = false;
				it1++;
				it2++;
			}
			if (it1 != outputSlot.end())
				eq = false;
			if (it2 != res.end())
				eq = false;
			if (!eq) {
				/* If they're not equal, we've not yet
				 * converged. */
				*progress = true;
				outputSlot = res;
			}
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
			} while (progress);
		}
	} livenessMap(sm, allStates);

	class _ {
		LivenessMap &livenessMap;
		bool *done_something;
		FreeVariableMap &fvm;

		void doit(StateMachineEdge *edge, FreeVariableMap &fvm) {
			LivenessEntry alive = livenessMap[edge->target];
			/* Surprise! vector::erase doesn't work with a
			   reverse_iterator, so use a raw index. */
			for (int x = edge->sideEffects.size() - 1;
			     x >= 0;
			     x--) {
				StateMachineSideEffect *newEffect = NULL;
				StateMachineSideEffect *e = edge->sideEffects[x];
				bool dead = false;
				switch (e->type) {
				case StateMachineSideEffect::Load: {
					StateMachineSideEffectLoad *smsel =
						(StateMachineSideEffectLoad *)e;
					if (!alive.registerLive(smsel->target))
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
					if (dynamic_cast<StateMachineTerminal *>(edge->target) ||
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
						dead = !alive.registerLive(smsec->target);
					}
					break;
				}
				case StateMachineSideEffect::Phi: {
					StateMachineSideEffectPhi *p =
						(StateMachineSideEffectPhi *)e;
					if (!alive.registerLive(p->reg))
						dead = true;
					break;
				}
				}

				if (dead) {
					*done_something = true;
					edge->sideEffects.erase(edge->sideEffects.begin() + x);
				} else if (newEffect) {
					*done_something = true;
					edge->sideEffects[x] = newEffect;
					alive.useSideEffect(newEffect);
				} else {
					alive.useSideEffect(e);
				}
			}
		}
	public:
		void operator()(StateMachineState *state) {
			if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(state)) {
				doit(smp->target, fvm);
			} else if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(state)) {
				doit(smb->trueTarget, fvm);
				doit(smb->falseTarget, fvm);
			} else if (dynamic_cast<StateMachineTerminal *>(state)) {
				/* Nothing needed */
			} else {
				abort();
			}			
		}

		_(LivenessMap &_livenessMap, bool *_done_something, FreeVariableMap &_fvm)
			: livenessMap(_livenessMap), done_something(_done_something), fvm(_fvm)
		{}
	} eliminateDeadCode(livenessMap, done_something, sm->freeVariables);

	for (auto it = allStates.begin();
	     it != allStates.end();
	     it++)
		eliminateDeadCode(*it);

	return sm;
}

/* end of namespace */
}

StateMachine *
deadCodeElimination(StateMachine *sm, bool *done_something)
{
	return _deadCode::deadCodeElimination(sm, done_something);
}

