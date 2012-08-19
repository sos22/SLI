/* Simple dead code elimination: find binders and registers which are
   never accessed after being set and eliminate them. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"

namespace _deadCode {
/* unconfuse emacs */
#if 0
}
#endif

#ifdef NDEBUG
#define debug_dump_liveness_map 0
#else
static int debug_dump_liveness_map = 0;
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
		case StateMachineSideEffect::StartAtomic:
		case StateMachineSideEffect::EndAtomic:
		case StateMachineSideEffect::PointerAliasing:
		case StateMachineSideEffect::StackLeaked:
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
		case StateMachineSideEffect::StartFunction: {
			StateMachineSideEffectStartFunction *sf =
				(StateMachineSideEffectStartFunction *)smse;
			useExpression(sf->rsp);
			return;
		}
		case StateMachineSideEffect::EndFunction: {
			StateMachineSideEffectEndFunction *sf =
				(StateMachineSideEffectEndFunction *)smse;
			useExpression(sf->rsp);
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

	bool registerLive(threadAndRegister reg) const { return count(reg); }

	void print() const {
		for (auto it = begin(); it != end(); it++) {
			if (it != begin())
				printf(", ");
			printf("%s", it->name());
		}
	}
};

class LivenessMap {
	/* Map from states to what's live at the *start* of the state */
	std::map<const StateMachineState *, LivenessEntry> content;

	void updateState(StateMachineState *sm, bool *progress)
	{
		LivenessEntry res(liveAtEndOfState(sm));
		switch (sm->type) {
		case StateMachineState::SideEffecting: {
			StateMachineSideEffecting *sme = (StateMachineSideEffecting *)sm;
			if (sme->sideEffect)
				res.useSideEffect(sme->sideEffect);
			break;
		}
		case StateMachineState::Bifurcate: {
			StateMachineBifurcate *smb = (StateMachineBifurcate *)sm;
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
		if (expandSet(content[sm], res))
			*progress = true;
	}

public:
	LivenessMap(std::set<StateMachineState *> &allStates) {
		bool progress;
		do {
			progress = false;
			for (auto it = allStates.begin();
			     it != allStates.end();
			     it++)
				updateState(*it, &progress);
		} while (progress && !TIMEOUT);
	}
	LivenessEntry liveAtStartOfState(const StateMachineState *sm) const {
		auto it = content.find(sm);
		/* The base case for the Tarski iteration is that
		   nothing is live anywhere. */
		if (it == content.end())
			return LivenessEntry();
		else
			return it->second;
	}
	LivenessEntry liveAtEndOfState(const StateMachineState * sm) const {
		std::vector<const StateMachineState *> exits;
		sm->targets(exits);
		LivenessEntry res;
		if (exits.size() == 0)
			return res;
		res = liveAtStartOfState(exits[0]);
		for (unsigned x = 1; x < exits.size(); x++)
			res.merge(liveAtStartOfState(exits[x]));
		return res;
	}
	void print(const std::map<const StateMachineState *, int> &labels) const {
		printf("At starts of states:\n");
		for (auto it = content.begin(); it != content.end(); it++) {
			auto it2 = labels.find(it->first);
			assert(it2 != labels.end());
			printf("l%d: ", it2->second);
			it->second.print();
			printf("\n");
		}
	}
};

static StateMachine *
deadCodeElimination(StateMachine *sm, bool *done_something, const AllowableOptimisations &opt)
{
	std::map<const StateMachineState *, int> stateLabels;

	if (debug_dump_liveness_map) {
		printf("Input to deadCodeElimination:\n");
		printStateMachine(sm, stdout, stateLabels);
	}

	std::set<StateMachineState *> allStates;
	findAllStates(sm, allStates);

	LivenessMap livenessMap(allStates);

	if (TIMEOUT)
		return sm;

	if (TIMEOUT)
		return sm;

	if (debug_dump_liveness_map) {
		printf("Liveness map:\n");
		livenessMap.print(stateLabels);
	}

	class _ {
		LivenessMap &livenessMap;
		bool *done_something;
		const AllowableOptimisations &opt;

		StateMachineSideEffect *doit(StateMachineSideEffect *e,
					     const LivenessEntry &alive) {
			StateMachineSideEffect *newEffect = NULL;
			bool dead = false;
			switch (e->type) {
			case StateMachineSideEffect::Load: {
				StateMachineSideEffectLoad *smsel =
					(StateMachineSideEffectLoad *)e;
				if (!alive.registerLive(smsel->target))
					newEffect = new StateMachineSideEffectAssertFalse(
						IRExpr_Unop(Iop_BadPtr, smsel->addr),
						true);
				break;
			}
			case StateMachineSideEffect::Store:
			case StateMachineSideEffect::Unreached:
			case StateMachineSideEffect::StartAtomic:
			case StateMachineSideEffect::EndAtomic:
			case StateMachineSideEffect::StartFunction:
			case StateMachineSideEffect::EndFunction:
			case StateMachineSideEffect::AssertFalse:
			case StateMachineSideEffect::StackLeaked:
				break;
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
			case StateMachineSideEffect::PointerAliasing: {
				auto *p = (StateMachineSideEffectPointerAliasing *)e;
				if (!alive.registerLive(p->reg))
					dead = true;
				break;
			}
			}

			if (dead) {
				*done_something = true;
				return NULL;
			} else if (newEffect) {
				*done_something = true;
				return newEffect;
			} else {
				return e;
			}
		}
	public:
		void operator()(StateMachineState *state) {
			switch (state->type) {
			case StateMachineState::SideEffecting: {
				StateMachineSideEffecting *smse = (StateMachineSideEffecting *)state;
				if (smse->sideEffect)
					smse->sideEffect = doit(smse->sideEffect,
								livenessMap.liveAtEndOfState(smse));
				return;
			}
			case StateMachineState::Bifurcate:
			case StateMachineState::Crash:
			case StateMachineState::NoCrash:
			case StateMachineState::Stub:
			case StateMachineState::Unreached:
				/* Nothing needed */
				return;
			}
			abort();
		}

		_(LivenessMap &_livenessMap, bool *_done_something, const AllowableOptimisations &_opt)
			: livenessMap(_livenessMap), done_something(_done_something), opt(_opt)
		{}
	} eliminateDeadCode(livenessMap, done_something, opt);

	for (auto it = allStates.begin();
	     it != allStates.end();
	     it++) {
		if (TIMEOUT)
			return sm;
		eliminateDeadCode(*it);
	}

	if (debug_dump_liveness_map) {
		printf("Final result:\n");
		printStateMachine(sm, stdout);
	}
	return sm;
}

/* end of namespace */
}

StateMachine *
deadCodeElimination(StateMachine *sm, bool *done_something, const AllowableOptimisations &opt)
{
	return _deadCode::deadCodeElimination(sm, done_something, opt);
}

