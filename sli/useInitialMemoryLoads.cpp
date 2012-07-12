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
	bool initialise(CfgDecode &decode,
			StateMachine *sm,
			const AllowableOptimisations &opt,
			OracleInterface *oracle);
	const std::set<const StateMachineSideEffectStore *> &get(const StateMachineState *s) const;
};

bool
ReachingMap::initialise(CfgDecode &decode,
			StateMachine *sm,
			const AllowableOptimisations &opt,
			OracleInterface *oracle)
{
	struct {
		const AllowableOptimisations *opt;
		OracleInterface *oracle;
		CfgDecode *decode;
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

class UseReachingMap : public StateMachineTransformer {
	ReachingMap &rm;
	const AllowableOptimisations &opt;
	OracleInterface *oracle;
	StateMachineSideEffecting *transformOneState(
		CfgDecode &, StateMachineSideEffecting *, bool *);
	bool rewriteNewStates() const { return false; }
public:
	UseReachingMap(ReachingMap &_rm,
		       const AllowableOptimisations &_opt,
		       OracleInterface *_oracle)
		: rm(_rm), opt(_opt), oracle(_oracle)
	{}
};

StateMachineSideEffecting *
UseReachingMap::transformOneState(CfgDecode &decode, StateMachineSideEffecting *smse, bool *done_something)
{
	if (!smse->sideEffect || smse->sideEffect->type != StateMachineSideEffect::Load)
		return NULL;
	StateMachineSideEffectLoad *load = (StateMachineSideEffectLoad *)smse->sideEffect;
	if (oracle->hasConflictingRemoteStores(decode, opt, load))
		return NULL;
	const std::set<const StateMachineSideEffectStore *> &potentiallyRelevantStores(rm.get(smse));
	for (auto it = potentiallyRelevantStores.begin();
	     it != potentiallyRelevantStores.end();
	     it++) {
		if (oracle->memoryAccessesMightAlias(decode, opt, load, (StateMachineSideEffectStore *)*it))
			return NULL;
	}
	/* If we get here then there are definitely no stores which
	   could satisfy this load, so just use an initial-memory
	   expression for it. */
	*done_something = true;
	return new StateMachineSideEffecting(
		smse->origin,
		new StateMachineSideEffectCopy(
			load->target,
			IRExpr_Load(load->type, load->addr)),
		smse->target);
}

static StateMachine *
useInitialMemoryLoads(StateMachine *sm, const AllowableOptimisations &opt,
		      OracleInterface *oracle, bool *done_something)
{
	CfgDecode decode;
	decode.addMachine(sm);
	ReachingMap rm;
	if (!rm.initialise(decode, sm, opt, oracle))
		return sm;
	UseReachingMap urm(rm, opt, oracle);
	return urm.transform(sm, done_something);
}

/* End of namespace */
};

StateMachine *
useInitialMemoryLoads(StateMachine *sm, const AllowableOptimisations &opt,
		      OracleInterface *oracle, bool *done_something)
{
	return _useInitialMemoryLoads::useInitialMemoryLoads(sm, opt, oracle, done_something);
}
