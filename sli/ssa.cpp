/* Conversion to static single assignment form */
#include "sli.h"
#include "state_machine.hpp"
#include "ssa.hpp"
#include "offline_analysis.hpp"
#include "visitor.hpp"

namespace SSA {

/* Unconfuse emacs indent */
#if 0
}
#endif

/* Map from a source register to the set of output registers which
   might represent it. */
typedef std::map<threadAndRegister, std::set<threadAndRegister> > reachingAssignmentsT;
/* Map from register name post-conversion back to pre-conversion
 * name. */
typedef std::map<threadAndRegister, threadAndRegister> ssaCorrespondenceT;
/* Standard reloc queue */
typedef std::vector<std::pair<StateMachineState **, StateMachineState *> > relocQT;

static threadAndRegister
allocTemporary(const threadAndRegister &base,
	       ssaCorrespondenceT &correspondence,
	       reachingAssignmentsT &reaching)
{
	unsigned gen = 0;
	for (auto it = correspondence.begin(); it != correspondence.end(); it++) {
		if (base.isTemp() == it->first.isTemp() &&
		    base.tid() == it->first.tid() &&
		    (base.isTemp() ? (base.asTemp() == it->first.asTemp()) : (base.asReg() == it->first.asReg())) &&
		    gen <= it->first.gen()) {
			gen = it->first.gen() + 1;
		}
	}
	threadAndRegister res(
		base.isTemp() ?
		threadAndRegister::temp(base.tid(), base.asTemp(), gen) :
		threadAndRegister::reg(base.tid(), base.asReg(), gen));
	assert(!correspondence.count(res));
	correspondence[res] = base;
	reaching[base].clear();
	reaching[base].insert(res);
	return res;
}

class ConvertExprTrans : public IRExprTransformer {
	reachingAssignmentsT &reaching;
	ssaCorrespondenceT &correspondence;
	std::vector<StateMachineSideEffectPhi *> &neededPhis;
	std::map<threadAndRegister, IRType> &typeMap;
	SMScopes *const scopes;
	void note_type(const threadAndRegister &reg, IRType ty) {
		auto it = typeMap.insert(std::pair<threadAndRegister, IRType>(reg, ty)).first;
		if (it->second < ty)
			it->second = ty;
	}
public:
	ConvertExprTrans(reachingAssignmentsT &_reaching,
			 ssaCorrespondenceT &_correspondence,
			 std::vector<StateMachineSideEffectPhi *> &_neededPhis,
			 std::map<threadAndRegister, IRType> &_typeMap,
			 SMScopes *_scopes)
		: reaching(_reaching), correspondence(_correspondence),
		  neededPhis(_neededPhis), typeMap(_typeMap),
		  scopes(_scopes)
	{}
	IRExpr *transformIex(IRExprGet *);
};

IRExpr *
ConvertExprTrans::transformIex(IRExprGet *iex)
{
	auto it = reaching.find(iex->reg);
	if (it == reaching.end() || it->second.size() == 0) {
		/* No reaching assignments for this get, so just
		 * ignore it. */
		return iex;
	}
	if (it->second.size() == 1) {
		note_type(*it->second.begin(), iex->ty);
		return IRExprGet::mk(*it->second.begin(), iex->ty);
	}
	std::vector<StateMachineSideEffectPhi::input> inputs;
	for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
		inputs.push_back(
			StateMachineSideEffectPhi::input(
				*it2,
				exprbdd::var(&scopes->exprs, &scopes->bools,
					     IRExpr_Get(*it2, iex->ty))));
	}
	threadAndRegister newReg(allocTemporary(iex->reg, correspondence, reaching));
	note_type(newReg, iex->ty);
	neededPhis.push_back(
		new StateMachineSideEffectPhi(
			newReg,
			iex->ty,
			inputs));
	return IRExprGet::mk(newReg, iex->ty);
}

static exprbdd *
convertExprBdd(SMScopes *scopes,
	       exprbdd *what,
	       reachingAssignmentsT &reaching,
	       ssaCorrespondenceT &correspondence,
	       std::vector<StateMachineSideEffectPhi *> &neededPhis,
	       std::map<threadAndRegister, IRType> &typeMap)
{
	ConvertExprTrans trans(reaching, correspondence, neededPhis, typeMap, scopes);
	return trans.transform_exprbdd(&scopes->bools, &scopes->exprs, what);
}
static smrbdd *
convertSmrBdd(SMScopes *scopes,
	      smrbdd *what,
	      reachingAssignmentsT &reaching,
	      ssaCorrespondenceT &correspondence,
	      std::vector<StateMachineSideEffectPhi *> &neededPhis,
	      std::map<threadAndRegister, IRType> &typeMap)
{
	ConvertExprTrans trans(reaching, correspondence, neededPhis, typeMap, scopes);
	return trans.transform_smrbdd(&scopes->bools, &scopes->smrs, what);
}
static bbdd *
convertBBdd(SMScopes *scopes,
	    bbdd *what,
	    reachingAssignmentsT &reaching,
	    ssaCorrespondenceT &correspondence,
	    std::vector<StateMachineSideEffectPhi *> &neededPhis,
	    std::map<threadAndRegister, IRType> &typeMap)
{
	ConvertExprTrans trans(reaching, correspondence, neededPhis, typeMap, scopes);
	return trans.transform_bbdd(&scopes->bools, what);
}

static StateMachineState *
addPhis(StateMachineState *suffix, const std::vector<StateMachineSideEffectPhi *> &neededPhis)
{
	StateMachineState *res = suffix;
	for (auto it = neededPhis.begin(); it != neededPhis.end(); it++) {
		res = new StateMachineSideEffecting(
			res->dbg_origin,
			*it,
			res);
	}
	return res;
}

static StateMachineSideEffect *
_convertSideEffect(SMScopes *scopes,
		   StateMachineSideEffectLoad *sml,
		   reachingAssignmentsT &reaching,
		   ssaCorrespondenceT &correspondence,
		   std::vector<StateMachineSideEffectPhi *> &neededPhis,
		   std::map<threadAndRegister, IRType> &typeMap)
{
	auto addr = convertExprBdd(scopes, sml->addr, reaching, correspondence, neededPhis, typeMap);
	return new StateMachineSideEffectLoad(
		sml,
		allocTemporary(sml->target, correspondence, reaching),
		addr);
}
static StateMachineSideEffect *
_convertSideEffect(SMScopes *scopes,
		   StateMachineSideEffectStore *sms,
		   reachingAssignmentsT &reaching,
		   ssaCorrespondenceT &correspondence,
		   std::vector<StateMachineSideEffectPhi *> &neededPhis,
		   std::map<threadAndRegister, IRType> &typeMap)
{
	return new StateMachineSideEffectStore(
		sms,
		convertExprBdd(scopes, sms->addr, reaching, correspondence, neededPhis, typeMap),
		convertExprBdd(scopes, sms->data, reaching, correspondence, neededPhis, typeMap));
}
static StateMachineSideEffect *
_convertSideEffect(SMScopes *scopes,
		   StateMachineSideEffectCopy *smc,
		   reachingAssignmentsT &reaching,
		   ssaCorrespondenceT &correspondence,
		   std::vector<StateMachineSideEffectPhi *> &neededPhis,
		   std::map<threadAndRegister, IRType> &typeMap)
{
	auto val = convertExprBdd(scopes, smc->value, reaching, correspondence, neededPhis, typeMap);
	return new StateMachineSideEffectCopy(
		allocTemporary(smc->target, correspondence, reaching),
		val);
}
static StateMachineSideEffect *
_convertSideEffect(SMScopes *scopes,
		   StateMachineSideEffectAssertFalse *smaf,
		   reachingAssignmentsT &reaching,
		   ssaCorrespondenceT &correspondence,
		   std::vector<StateMachineSideEffectPhi *> &neededPhis,
		   std::map<threadAndRegister, IRType> &typeMap)
{
	return new StateMachineSideEffectAssertFalse(
		smaf,
		convertBBdd(scopes, smaf->value, reaching, correspondence, neededPhis, typeMap));
}
static StateMachineSideEffect *
_convertSideEffect(SMScopes *,
		   StateMachineSideEffectStartAtomic *smsa,
		   reachingAssignmentsT &,
		   ssaCorrespondenceT &,
		   std::vector<StateMachineSideEffectPhi *> &,
		   std::map<threadAndRegister, IRType> &)
{
	return smsa;
}
static StateMachineSideEffect *
_convertSideEffect(SMScopes *,
		   StateMachineSideEffectEndAtomic *smea,
		   reachingAssignmentsT &,
		   ssaCorrespondenceT &,
		   std::vector<StateMachineSideEffectPhi *> &,
		   std::map<threadAndRegister, IRType> &)
{
	return smea;
}
static StateMachineSideEffect *
_convertSideEffect(SMScopes *,
		   StateMachineSideEffectUnreached *smu,
		   reachingAssignmentsT &,
		   ssaCorrespondenceT &,
		   std::vector<StateMachineSideEffectPhi *> &,
		   std::map<threadAndRegister, IRType> &)
{
	return smu;
}
static StateMachineSideEffect *
_convertSideEffect(SMScopes *scopes,
		   StateMachineSideEffectPhi *smep,
		   reachingAssignmentsT &reaching,
		   ssaCorrespondenceT &correspondence,
		   std::vector<StateMachineSideEffectPhi *> &neededPhis,
		   std::map<threadAndRegister, IRType> &typeMap)
{
	/* This is a little tricky.  The old phi selects whichever old
	 * register R has been assigned to most recently out of some
	 * set {R0, R1, R2, ..., Rn}.  For each entry in that set Ri,
	 * @reaching will contain a set of registers {Ri_0, ..., Ri_m},
	 * and Ri is the most recently assigned member of that set.
	 * The phi therefore selects the most recently assigned member
	 * of any of the Ri sets.
	 *
	 * The phi also contains expressions showing the value of the
	 * expression when we select that register.  Those are more
	 * tricky, because there might be multiple, inconsistent,
	 * definitions in the various Ri.  We try to preserve the
	 * value whenever possible, but occasionally fail and fall back
	 * to the safe IRExpr_Get() alternative.
	 */
	std::map<threadAndRegister, exprbdd *> newInputs;
	for (auto it = smep->generations.begin(); it != smep->generations.end(); it++) {
		const threadAndRegister &oldReg(it->reg);
		exprbdd *oldVal = it->val;

		if (!reaching.count(oldReg)) {
			/* There is no way to select this input, so
			 * just drop it. */
			continue;
		}
		const std::set<threadAndRegister> &reach(reaching[oldReg]);
		if (reach.empty()) {
			/* No reaching assignments -> drop input */
			continue;
		}
		for (auto it2 = reach.begin(); it2 != reach.end(); it2++) {
			const threadAndRegister &newReg(*it2);
			auto it3_did_insert = newInputs.insert(std::pair<threadAndRegister, exprbdd *>(newReg, oldVal));
			auto it3 = it3_did_insert.first;
			auto did_insert = it3_did_insert.second;
			if (did_insert && it3->second != oldVal) {
				/* Inconsistent assignments -> use fallback */
				it3->second = NULL;
			}
		}
	}

	/* Flatten the map to a vector and generate the phis for the
	 * input expressions. */
	std::vector<StateMachineSideEffectPhi::input> inputs;
	for (auto it = newInputs.begin(); it != newInputs.end(); it++) {
		const threadAndRegister &reg(it->first);
		exprbdd *val = it->second;
		if (val) {
			val = convertExprBdd(scopes, val, reaching, correspondence,
					     neededPhis, typeMap);
		} else {
			val = exprbdd::var(&scopes->exprs,
					   &scopes->bools,
					   IRExpr_Get(reg, smep->ty));
		}
		inputs.push_back(StateMachineSideEffectPhi::input(reg, val));
	}

	return new StateMachineSideEffectPhi(
		allocTemporary(smep->reg, correspondence, reaching),
		smep->ty,
		inputs);
}
static StateMachineSideEffect *
_convertSideEffect(SMScopes *,
		   StateMachineSideEffectImportRegister *smei,
		   reachingAssignmentsT &reaching,
		   ssaCorrespondenceT &correspondence,
		   std::vector<StateMachineSideEffectPhi *> &,
		   std::map<threadAndRegister, IRType> &)
{
	return new StateMachineSideEffectImportRegister(
		smei,
		allocTemporary(smei->reg, correspondence, reaching));
}

static StateMachineSideEffect *
convertSideEffect(SMScopes *scopes,
		  StateMachineSideEffect *inp,
		  reachingAssignmentsT &reaching,
		  ssaCorrespondenceT &correspondence,
		  std::vector<StateMachineSideEffectPhi *> &neededPhis,
		  std::map<threadAndRegister, IRType> &typeMap)
{
	switch (inp->type) {
#define CASE(name)						\
	case StateMachineSideEffect:: name :			\
		return _convertSideEffect(			\
			scopes,					\
			(StateMachineSideEffect ## name *)inp,	\
			reaching,				\
			correspondence,				\
			neededPhis,				\
			typeMap);
	all_side_effect_types(CASE)
#undef CASE
	}
	abort();
}

static StateMachineState *
_convertState(SMScopes *scopes,
	      StateMachineTerminal *smt,
	      reachingAssignmentsT &reaching,
	      relocQT &,
	      ssaCorrespondenceT &correspondence,
	      std::map<threadAndRegister, IRType> &typeMap)
{
	std::vector<StateMachineSideEffectPhi *> neededPhis;
	smt->set_res(convertSmrBdd(scopes, smt->res, reaching, correspondence, neededPhis, typeMap));
	return addPhis(smt, neededPhis);
}

static StateMachineState *
_convertState(SMScopes *scopes,
	      StateMachineBifurcate *smb,
	      reachingAssignmentsT &reaching,
	      relocQT &relocs,
	      ssaCorrespondenceT &correspondence,
	      std::map<threadAndRegister, IRType> &typeMap)
{
	std::vector<StateMachineSideEffectPhi *> neededPhis;
	smb->set_condition(convertBBdd(scopes, smb->condition, reaching, correspondence, neededPhis, typeMap));
	relocs.push_back(std::pair<StateMachineState **, StateMachineState *>(&smb->trueTarget, smb->trueTarget));
	relocs.push_back(std::pair<StateMachineState **, StateMachineState *>(&smb->falseTarget, smb->falseTarget));
	return addPhis(smb, neededPhis);
}

static StateMachineState *
_convertState(SMScopes *scopes,
	      StateMachineSideEffecting *sme,
	      reachingAssignmentsT &reaching,
	      relocQT &relocs,
	      ssaCorrespondenceT &correspondence,
	      std::map<threadAndRegister, IRType> &typeMap)
{
	std::vector<StateMachineSideEffectPhi *> neededPhis;
	if (sme->sideEffect)
		sme->sideEffect = convertSideEffect(scopes, sme->sideEffect, reaching, correspondence, neededPhis, typeMap);
	relocs.push_back(std::pair<StateMachineState **, StateMachineState *>(&sme->target, sme->target));
	return addPhis(sme, neededPhis);
}

static StateMachineState *
convertState(SMScopes *scopes,
	     StateMachineState *state,
	     reachingAssignmentsT &reaching,
	     std::vector<std::pair<StateMachineState **, StateMachineState *> > &relocs,
	     std::map<threadAndRegister, threadAndRegister> &correspondence,
	     std::map<threadAndRegister, IRType> &typeMap)
{
	switch (state->type) {
#define CASE(name)					\
	case StateMachineState:: name :			\
		return _convertState(			\
			scopes,				\
			(StateMachine ## name *)state,	\
			reaching,			\
			relocs,				\
			correspondence,			\
			typeMap);
	all_state_types(CASE)
#undef CASE
	}
	abort();
}
	     
static void
fixupPhiTypes(SMScopes *scopes, StateMachine *inp, const std::map<threadAndRegister, IRType> &typeMap)
{
	std::vector<StateMachineSideEffecting *> states;
	enumStates(inp, &states);
	for (auto it = states.begin(); it != states.end(); it++) {
		StateMachineSideEffecting *s = *it;
		if (!s->sideEffect ||
		    s->sideEffect->type != StateMachineSideEffect::Phi) {
			continue;
		}
		StateMachineSideEffectPhi *phi =
			(StateMachineSideEffectPhi *)s->sideEffect;
		auto it2 = typeMap.find(phi->reg);
		if (it2 == typeMap.end() ||
		    phi->ty == it2->second) {
			continue;
		}
		std::vector<StateMachineSideEffectPhi::input> newInputs;
		newInputs.reserve(phi->generations.size());
		for (auto it3 = phi->generations.begin(); it3 != phi->generations.end(); it3++) {
			newInputs.push_back(
				StateMachineSideEffectPhi::input(
					it3->reg,
					exprbdd::var(
						&scopes->exprs,
						&scopes->bools,
						IRExprGet::mk(
							it3->reg,
							it2->second))));
		}
		s->sideEffect =
			new StateMachineSideEffectPhi(
				phi, newInputs);
	}
}

/* @correspondence is a map from the new register name to the old
 * one. */
static StateMachine *
convertToSSA(SMScopes *scopes, StateMachine *inp, std::map<threadAndRegister, threadAndRegister> &correspondence)
{
	std::map<StateMachineState *, int> nrPendingPredecessors;
	std::map<StateMachineState *, std::set<StateMachineState *> > predecessors;
	std::vector<StateMachineState *> states;
	enumStates(inp, &states);
	nrPendingPredecessors[inp->root] = 0;
	predecessors[inp->root]; /* Allocate with an empty set as
				  * value */
	for (auto it = states.begin(); it != states.end(); it++) {
		std::vector<StateMachineState *> targs;
		(*it)->targets(targs);
		for (auto it2 = targs.begin(); it2 != targs.end(); it2++) {
			nrPendingPredecessors[*it2]++;
			predecessors[*it2].insert(*it);
		}
	}

	/* Map from old states to new states */
	std::map<StateMachineState *, StateMachineState *> stateMap;
	/* Pending relocations */
	std::vector<std::pair<StateMachineState **, StateMachineState *> > relocs;
	/* State at each node in the machine, built as we go along. */
	std::map<StateMachineState *, reachingAssignmentsT> reachingTable;
	/* Queue of states to process */
	std::vector<StateMachineState *> pending;

	StateMachineState *newRoot;
	relocs.push_back(std::pair<StateMachineState **, StateMachineState *>(&newRoot, inp->root));
	pending.push_back(inp->root);

	std::map<threadAndRegister, IRType> typeMap;
	while (!pending.empty()) {
		StateMachineState *s = pending.back();
		pending.pop_back();
		assert(predecessors.count(s));
		assert(nrPendingPredecessors.count(s));
		assert(nrPendingPredecessors[s] == 0);
		assert(!reachingTable.count(s));
		assert(!stateMap.count(s));

		reachingAssignmentsT &thisStateReaching(reachingTable[s]);
		const std::set<StateMachineState *> &pred(predecessors[s]);
		for (auto it = pred.begin(); it != pred.end(); it++) {
			assert(reachingTable.count(*it));
			assert(stateMap.count(*it));
			const reachingAssignmentsT &predReaching(reachingTable[*it]);
			for (auto it2 = predReaching.begin(); it2 != predReaching.end(); it2++) {
				const threadAndRegister &r(it2->first);
				const std::set<threadAndRegister> &inp_reaching(it2->second);
				std::set<threadAndRegister> &out_reaching(thisStateReaching[r]);
				for (auto it3 = inp_reaching.begin(); it3 != inp_reaching.end(); it3++) {
					out_reaching.insert(*it3);
				}
			}
		}

		stateMap[s] = convertState(scopes, s, thisStateReaching, relocs, correspondence, typeMap);

		std::vector<StateMachineState *> targets;
		s->targets(targets);
		for (auto it = targets.begin(); it != targets.end(); it++) {
			assert(nrPendingPredecessors.count(*it));
			assert(nrPendingPredecessors[*it] != 0);
			if (--nrPendingPredecessors[*it] == 0) {
				pending.push_back(*it);
			}
		}
	}

	for (auto it = relocs.begin(); it != relocs.end(); it++) {
		assert(stateMap.count(it->second));
		assert(stateMap[it->second]);
		*it->first = stateMap[it->second];
	}

	fixupPhiTypes(scopes, inp, typeMap);

	return inp;
}

/* End of namespace SSA */
}

StateMachine *
convertToSSA(SMScopes *scopes, StateMachine *inp, std::map<threadAndRegister, threadAndRegister> &correspondence)
{
	return SSA::convertToSSA(scopes, inp, correspondence);
}

StateMachineSideEffect *
StateMachineSideEffectPhi::optimise(SMScopes *, const AllowableOptimisations &)
{
	if (generations.size() == 0)
		return StateMachineSideEffectUnreached::get();

	exprbdd *v = generations[0].val;
	for (unsigned x = 1; x < generations.size(); x++) {
		if (generations[x].val != v)
			return this;
	}
	return new StateMachineSideEffectCopy(reg, v);
}

