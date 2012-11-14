/* Find any places in the machine where we load from a memory location
   which we definitely haven't stored to and replace the loads with
   copies of initial-memory expressions. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"

namespace _useInitialMemoryLoads {

template <typename t> static bool
mergeSets(std::set<t> &target, const std::set<t> &input)
{
	auto targ_it = target.begin();
	auto input_it = input.begin();
	bool res = false;

	while (input_it != input.end() && targ_it != target.end()) {
		if (*input_it < *targ_it) {
			targ_it = target.insert(targ_it, *input_it);
			res = true;
			input_it++;
		} else if (*targ_it < *input_it) {
			targ_it++;
		} else {
			targ_it++;
			input_it++;
		}
	}
	while (input_it != input.end()) {
		target.insert(target.end(), *input_it);
		input_it++;
		res = true;
	}
	return res;
}

/* Effectively a map from states which perform loads to the set of
   stores in this machine which might conceivably satisfy that
   load. */
class ReachingMap {
	std::map<const StateMachineState *, std::set<const StateMachineSideEffectStore *> > content;
	std::set<const StateMachineSideEffectStore *> nothingReaching;
public:
	bool initialise(const MaiMap &decode,
			StateMachine *sm,
			const AllowableOptimisations &opt,
			OracleInterface *oracle);
	const std::set<const StateMachineSideEffectStore *> &get(const StateMachineState *s) const;
};

bool
ReachingMap::initialise(const MaiMap &decode,
			StateMachine *sm,
			const AllowableOptimisations &opt,
			OracleInterface *oracle)
{
	struct {
		const AllowableOptimisations *opt;
		OracleInterface *oracle;
		const MaiMap *decode;
		bool operator()(StateMachineSideEffectStore *store) {
			if (!oracle->hasConflictingRemoteStores(*decode, *opt, store))
				return true;
			return false;
		}
		const StateMachineSideEffectStore *operator()(const StateMachineState *s) {
			const StateMachineSideEffect *se = s->getSideEffect();
			if (!se || se->type != StateMachineSideEffect::Store)
				return NULL;
			StateMachineSideEffectStore *store = (StateMachineSideEffectStore *)se;
			if (!(*this)(store))
				return NULL;
			return store;
		}
	} interestingStore = {&opt, oracle, &decode};

	/* Start by saying that every state needs updating. */
	std::vector<const StateMachineState *> needsUpdate;
	enumStates(sm, &needsUpdate);

	/* Now iterate making every state locally consistent.  The
	 * local rule is that a store is considered to reach a
	 * successor of state X if either:
	 *
	 * -- It reaches the start of state X and state X didn't
	 *    clobber it, or
	 * -- state X generates it.
	 *
	 * Once you iterate to a fixed point, a store reaches X if
	 * there is any possibility that the store might satisfy a
	 * load at X. */
	while (!needsUpdate.empty()) {
		if (TIMEOUT)
			return false;

		const StateMachineState *s = needsUpdate.back();
		needsUpdate.pop_back();

		/* Start with our entry state, and from that compute
		   our exit state. */
		std::set<const StateMachineSideEffectStore *> _result;
		std::set<const StateMachineSideEffectStore *> *result;
		const StateMachineSideEffectStore *store = interestingStore(s);
		if (store) {
			/* Have to compute a new output state. */
			_result = content[s];
			/* Remove anything which is definitely clobbered */
			for (auto it = _result.begin(); it != _result.end(); ) {
				if (definitelyEqual( (*it)->addr, store->addr, opt ) ) {
					_result.erase(it++);
				} else {
					it++;
				}
			}
			/* And introduce the new value */
			_result.insert(store);
			result = &_result;
		} else {
			/* Output state is the same as the input state */
			result = &content[s];
		}

		std::vector<const StateMachineState *> targets;
		s->targets(targets);
		for (auto it = targets.begin(); it != targets.end(); it++) {
			const StateMachineState *target = *it;
			if (mergeSets(content[target], *result))
				needsUpdate.push_back(target);
		}
	}

	/* Realtionship is now globally consistent, and can therefore
	 * be safely used. */
	return true;
}

const std::set<const StateMachineSideEffectStore *> &
ReachingMap::get(const StateMachineState *s) const
{
	auto it = content.find(s);
	assert(it != content.end());
	return it->second;
}

static StateMachine *
useInitialMemoryLoads(const MaiMap &mai, StateMachine *sm, const AllowableOptimisations &opt,
		      OracleInterface *oracle, bool *done_something)
{
	ReachingMap rm;
	if (!rm.initialise(mai, sm, opt, oracle))
		return sm;
	/* Figure out whether we're actually going to do any rewrites
	 * before we start */
	std::map<StateMachineState *, StateMachineState *> rewrites;
	{
		std::set<StateMachineSideEffecting *> states;
		enumStates(sm, &states);
		for (auto it = states.begin(); it != states.end(); it++) {
			StateMachineSideEffecting *s = *it;
			StateMachineSideEffect *se = s->sideEffect;
			if (!se || se->type != StateMachineSideEffect::Load)
				continue;
			StateMachineSideEffectLoad *load = (StateMachineSideEffectLoad *)se;
			if (oracle->hasConflictingRemoteStores(mai, opt, load))
				continue;
			const std::set<const StateMachineSideEffectStore *> &potentiallyRelevantStores(rm.get(s));
			bool hasConflictingStores = false;
			for (auto it = potentiallyRelevantStores.begin();
			     !hasConflictingStores && it != potentiallyRelevantStores.end();
			     it++) {
			if (oracle->memoryAccessesMightAlias(mai, opt, load, (StateMachineSideEffectStore *)*it))
				hasConflictingStores = true;
			}
			if (hasConflictingStores)
				continue;
			rewrites[s] = new StateMachineSideEffecting(
				s->dbg_origin,
				new StateMachineSideEffectAssertFalse(
					IRExpr_Unop(Iop_BadPtr, load->addr),
					true),
				new StateMachineSideEffecting(
					s->dbg_origin,
					new StateMachineSideEffectCopy(
						load->target,
						IRExpr_Load(load->type, load->addr)),
					s->target));
		}
	}

	if (rewrites.empty())
		return sm;

	/* Okay, have something to do.  Rewrite the machine. */
	std::map<StateMachineState *, StateMachineState *> rewritten;
	std::queue<StateMachineState **> pending;
	StateMachineState *newRoot = sm->root;
	pending.push(&newRoot);
	while (!pending.empty()) {
		StateMachineState **slot = pending.front();
		pending.pop();
		StateMachineState *s = *slot;
		auto it_did_insert = rewritten.insert(std::pair<StateMachineState *, StateMachineState *>(s, (StateMachineState *)NULL));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (!did_insert) {
			*slot = it->second;
			continue;
		}
		StateMachineState *newS = (StateMachineState *)0xf001ul;
		auto it2 = rewrites.find(s);
		if (it2 != rewrites.end()) {
			newS = it2->second;
		} else {
			switch (s->type) {
			case StateMachineState::Terminal:
				newS = s;
				break;
			case StateMachineState::Bifurcate:
				newS = new StateMachineBifurcate(*(StateMachineBifurcate *)s);
				break;
			case StateMachineState::SideEffecting:
				newS = new StateMachineSideEffecting(*(StateMachineSideEffecting *)s);
				break;
			}
		}

		it->second = newS;
		*slot = newS;
		std::vector<StateMachineState **> succ;
		newS->targets(succ);
		for (auto it = succ.begin(); it != succ.end(); it++)
			pending.push(*it);
	}
	assert(newRoot != sm->root);
	*done_something = true;
	return new StateMachine(sm, newRoot);
}

/* End of namespace */
};

StateMachine *
useInitialMemoryLoads(const MaiMap &mai, StateMachine *sm, const AllowableOptimisations &opt,
		      OracleInterface *oracle, bool *done_something)
{
	return _useInitialMemoryLoads::useInitialMemoryLoads(mai, sm, opt, oracle, done_something);
}
