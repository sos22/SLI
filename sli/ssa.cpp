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

#ifndef NDEBUG
static bool debug_ssa_conversion = false;
#else
#define debug_ssa_conversion false
#endif

typedef std::map<threadAndRegister, std::set<unsigned>, threadAndRegister::partialCompare> usedGenerationsT;

static threadAndRegister
allocTemporary(usedGenerationsT &usedMap, const threadAndRegister &what)
{
	auto it = usedMap.find(what);
	assert(it != usedMap.end());
	const std::set<unsigned> &used(it->second);
	assert(!used.empty());
	assert(!used.count(*used.rbegin() + 1));
	threadAndRegister res(what.setGen(*used.rbegin() + 1));
	assert(!it->second.count(res.gen()));
	it->second.insert(res.gen());
	return res;
}

/* Figure out which register-defining side-effects need to be given
   new registers and what that new register should be. */
/* This also builds the initial usedGenerations table. */
static void
buildRegOutputReplacementTable(const StateMachine *sm,
			       usedGenerationsT &usedGenerations,
			       std::map<const StateMachineSideEffecting *, threadAndRegister> &newOutputVars)
{
	std::set<const StateMachineSideEffecting *> sideEffects;
	enumStates(sm, &sideEffects);
	std::map<threadAndRegister, std::set<const StateMachineSideEffecting *> > definitions;
	for (auto it = sideEffects.begin();
	     it != sideEffects.end();
	     it++) {
		const StateMachineSideEffecting *state = *it;
		const StateMachineSideEffect *se = state->sideEffect;
		if (!se)
			continue;
		threadAndRegister tr(threadAndRegister::invalid());
		if (se->definesRegister(tr)) {
			definitions[tr].insert(state);
			usedGenerations[tr].insert(tr.gen());
		}
	}
	for (auto it = definitions.begin();
	     it != definitions.end();
	     it++) {
		const threadAndRegister &reg(it->first);
		for (auto it2 = it->second.begin();
		     it2 != it->second.end();
		     it2++) {
			const StateMachineSideEffecting *state = *it2;
			threadAndRegister newReg(allocTemporary(usedGenerations, reg));
			assert(!newOutputVars.count(state));
			newOutputVars[state] = newReg;
		}
	}
}

/* Mapping from a register to a set of registers such that y is a
   member of regSet[x] precisely if an assignment to x has been
   replaced by one to y. i.e. regSet[x] is the set of versions of
   x. */
typedef std::map<threadAndRegister, std::set<threadAndRegister> > regSetsT;

/* A thing to capture the Phi operations needed by an expression.

   The idea is that if you need to replace register x at type ty with
   register y, and y should be a phi over {a,b,c}, you make
   neededPhisT[x,ty] be (y, {a,b,c}).

   (The extra level of indirection in @inputs is so that we can share
   the sets with the input regSetsT) */
struct neededPhisEntry {
	const std::set<threadAndRegister> *inputs;
	threadAndRegister newReg;

	/* This is just a cache of IRExpr_Get(newReg, type). */
	IRExprGet *iex;

	neededPhisEntry(const std::set<threadAndRegister> *_inputs,
			const threadAndRegister &_newReg,
			IRExprGet *_iex)
		: inputs(_inputs), newReg(_newReg), iex(_iex)
	{}

};
typedef std::map<std::pair<threadAndRegister, IRType>, neededPhisEntry> neededPhisT;

class replaceInputRegsT : public StateMachineTransformer {
	const regSetsT &rs;
	neededPhisT &out;
	usedGenerationsT &usedRegs;
	IRExpr *transformIex(IRExprGet *ieg) {
		auto it = rs.find(ieg->reg);
		if (it == rs.end())
			return ieg;
		if (it->second.size() == 1)
			return IRExpr_Get(*it->second.begin(), ieg->ty);
		auto it2 = out.find(std::pair<threadAndRegister, IRType>
				    (ieg->reg, ieg->ty));
		if (it2 != out.end())
			return it2->second.iex;
		threadAndRegister newReg(allocTemporary(usedRegs, ieg->reg));
		neededPhisEntry npe(&it->second,
				    newReg,
				    IRExpr_Get(newReg, ieg->ty));
		out.insert(std::pair<std::pair<threadAndRegister, IRType>,
			             neededPhisEntry>
			(std::pair<threadAndRegister, IRType>(ieg->reg, ieg->ty),
			 npe));
		return npe.iex;
	}
	bool rewriteNewStates() const { return false; }
public:
	replaceInputRegsT(const regSetsT &_rs,
			  neededPhisT &_out,
			  usedGenerationsT &_usedRegs)
		: rs(_rs), out(_out), usedRegs(_usedRegs)
	{}
};
static bbdd *
replaceInputRegs(bbdd::scope *scope,
		 const bbdd *what,
		 const regSetsT &regSets,
		 usedGenerationsT &usedGenerations,
		 neededPhisT &newInputs)
{
	replaceInputRegsT trans(regSets, newInputs, usedGenerations);
	return trans.transform_bbdd(scope, (bbdd *)what);
}
static smrbdd *
replaceInputRegs(bbdd::scope *scope,
		 smrbdd::scope *scope2,
		 const smrbdd *what,
		 const regSetsT &regSets,
		 usedGenerationsT &usedGenerations,
		 neededPhisT &newInputs)
{
	replaceInputRegsT trans(regSets, newInputs, usedGenerations);
	return trans.transform_smrbdd(scope, scope2, (smrbdd *)what);
}
static exprbdd *
replaceInputRegs(bbdd::scope *scope,
		 exprbdd::scope *scope2,
		 const exprbdd *what,
		 const regSetsT &regSets,
		 usedGenerationsT &usedGenerations,
		 neededPhisT &newInputs)
{
	replaceInputRegsT trans(regSets, newInputs, usedGenerations);
	return trans.transform_exprbdd(scope, scope2, (exprbdd *)what);
}

static StateMachineSideEffect *
replaceRegs(SMScopes *scopes,
	    const StateMachineSideEffect *what,
	    const regSetsT &regSets,
	    usedGenerationsT &usedGenerations,
	    neededPhisT &newInputs,
	    const threadAndRegister *newOutput)
{
	if (TIMEOUT)
		return NULL;
	switch (what->type) {
	case StateMachineSideEffect::Unreached:
	case StateMachineSideEffect::StackLayout:
	case StateMachineSideEffect::Store:
	case StateMachineSideEffect::AssertFalse:
	case StateMachineSideEffect::StartAtomic:
	case StateMachineSideEffect::EndAtomic:
	case StateMachineSideEffect::StartFunction:
	case StateMachineSideEffect::EndFunction: {
		replaceInputRegsT trans(regSets, newInputs, usedGenerations);
		bool b = false;
		StateMachineSideEffect *n = trans.transformSideEffect(scopes, (StateMachineSideEffect *)what, &b);
		if (n)
			return n;
		else
			return (StateMachineSideEffect *)what;
	}
	case StateMachineSideEffect::Load:
		return new StateMachineSideEffectLoad(
			(const StateMachineSideEffectLoad *)what,
			newOutput ? *newOutput : ((const StateMachineSideEffectLoad *)what)->target,
			replaceInputRegs(&scopes->bools, &scopes->exprs,
					 ((const StateMachineSideEffectLoad *)what)->addr,
					 regSets, usedGenerations, newInputs));
	case StateMachineSideEffect::Copy:
		return new StateMachineSideEffectCopy(
			newOutput ? *newOutput : ((const StateMachineSideEffectCopy *)what)->target,
			replaceInputRegs(&scopes->bools, &scopes->exprs,
					 ((const StateMachineSideEffectCopy *)what)->value,
					 regSets, usedGenerations, newInputs));
	case StateMachineSideEffect::Phi: {
		const StateMachineSideEffectPhi *ph = (const StateMachineSideEffectPhi *)what;
		std::vector<StateMachineSideEffectPhi::input> inputs;
		for (auto it = ph->generations.begin();
		     it != ph->generations.end();
		     it++) {
			StateMachineSideEffectPhi::input newInp;
			auto it2 = regSets.find(it->reg);
			if (it2 == regSets.end()) {
				newInp.reg = it->reg;
			} else if (it2->second.size() == 1) {
				newInp.reg = *it2->second.begin();
			} else {
				auto it3 = newInputs.find(std::pair<threadAndRegister, IRType>
							  (it->reg, ph->ty));
				if (it3 == newInputs.end()) {
					threadAndRegister newReg(allocTemporary(usedGenerations, ph->reg));
					neededPhisEntry npe(&it2->second,
							    newReg,
							    IRExpr_Get(newReg, ph->ty));
					newInputs.insert(
						std::pair<std::pair<threadAndRegister, IRType>,
						          neededPhisEntry>
						(std::pair<threadAndRegister, IRType>(it->reg, ph->ty),
						 npe));
					newInp.reg = newReg;
				} else {
					newInp.reg = it3->second.newReg;
				}
			}
			newInp.val = replaceInputRegs(&scopes->bools, &scopes->exprs, it->val, regSets, usedGenerations, newInputs);
			inputs.push_back(newInp);
		}
		return new StateMachineSideEffectPhi(
			newOutput ? *newOutput : ph->reg,
			ph->ty,
			inputs);
	}
	case StateMachineSideEffect::ImportRegister:
		return new StateMachineSideEffectImportRegister(
			(const StateMachineSideEffectImportRegister *)what,
			newOutput ? *newOutput : ((const StateMachineSideEffectImportRegister *)what)->reg);
	}
	abort();
}

static StateMachineState *
addPhiPrefix(SMScopes *scopes, StateMachineState *end, const neededPhisT &neededPhis)
{
	StateMachineState *res = end;
	for (auto it = neededPhis.begin();
	     it != neededPhis.end();
	     it++) {
		const neededPhisEntry &npe(it->second);
		std::vector<StateMachineSideEffectPhi::input> inp;
		inp.reserve(npe.inputs->size());
		for (auto it2 = npe.inputs->begin();
		     it2 != npe.inputs->end();
		     it2++) {
			StateMachineSideEffectPhi::input item;
			item.reg = *it2;
			item.val = exprbdd::var(&scopes->exprs,
						&scopes->bools,
						IRExpr_Get(*it2, it->first.second));
			inp.push_back(item);
		}
		res = new StateMachineSideEffecting(
			res->dbg_origin,
			new StateMachineSideEffectPhi(
				npe.newReg,
				it->first.second,
				inp),
			res);
	}
	return res;
}

typedef std::pair<StateMachineState **, const StateMachineState *> relocT;

static StateMachineState *
buildReplacement(SMScopes *scopes,
		 const StateMachineBifurcate *smb,
		 std::vector<relocT> &relocs,
		 usedGenerationsT &usedGens,
		 const regSetsT &regSets,
		 const std::map<const StateMachineSideEffecting *, threadAndRegister> &)
{
	neededPhisT neededPhis;
	bbdd *cond = replaceInputRegs(&scopes->bools, smb->condition,
				      regSets, usedGens, neededPhis);
	if (TIMEOUT)
		return NULL;
	StateMachineBifurcate *res =
		new StateMachineBifurcate(
			smb->dbg_origin,
			cond,
			NULL,
			NULL);
	relocs.push_back(relocT(&res->trueTarget, smb->trueTarget));
	relocs.push_back(relocT(&res->falseTarget, smb->falseTarget));
	return addPhiPrefix(scopes, res, neededPhis);
}

static StateMachineState *
buildReplacement(SMScopes *scopes,
		 const StateMachineTerminal *smt,
		 std::vector<relocT> &,
		 usedGenerationsT &usedGens,
		 const regSetsT &regSets,
		 const std::map<const StateMachineSideEffecting *, threadAndRegister> &)
{
	neededPhisT neededPhis;
	smrbdd *r = replaceInputRegs(&scopes->bools, &scopes->smrs, smt->res, regSets, usedGens, neededPhis);
	if (TIMEOUT)
		return NULL;
	StateMachineTerminal *res = new StateMachineTerminal(smt->dbg_origin, r);
	return addPhiPrefix(scopes, res, neededPhis);
}

static StateMachineState *
buildReplacement(SMScopes *scopes,
		 const StateMachineSideEffecting *sme,
		 std::vector<relocT> &relocs,
		 usedGenerationsT &usedGens,
		 const regSetsT &regSets,
		 const std::map<const StateMachineSideEffecting *, threadAndRegister> &rewrites)
{
	neededPhisT neededPhis;
	StateMachineSideEffect *newSe;
	if (sme->sideEffect) {
		auto it = rewrites.find(sme);
		newSe =	replaceRegs(
			scopes,
			sme->sideEffect,
			regSets,
			usedGens,
			neededPhis,
			it == rewrites.end() ? NULL : &it->second);
	} else {
		newSe = NULL;
	}
	StateMachineSideEffecting *res =
		new StateMachineSideEffecting(
			sme->dbg_origin,
			newSe,
			NULL);
	relocs.push_back(relocT(&res->target, sme->target));
	return addPhiPrefix(scopes, res, neededPhis);
}
	
static StateMachine *
convertToSSA(SMScopes *scopes, StateMachine *inp, std::map<threadAndRegister, threadAndRegister> &correspondence)
{
	std::map<const StateMachineState *, int> labels;
	if (debug_ssa_conversion) {
		printf("Convert to SSA, input machine:\n");
		printStateMachine(inp, stdout, labels);
	}

	std::map<const StateMachineSideEffecting *, threadAndRegister> replacements;
	usedGenerationsT usedGens;
	buildRegOutputReplacementTable(inp, usedGens, replacements);
	if (replacements.empty())
		return inp;

	if (debug_ssa_conversion) {
		printf("Replacement table:\n");
		for (auto it = replacements.begin(); it != replacements.end(); it++)
			printf("l%d -> %s\n", labels[it->first], it->second.name());
		printf("Gens table:\n");
		for (auto it = usedGens.begin(); it != usedGens.end(); it++) {
			printf("%s -> {", it->first.name());
			for (auto it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++) {
				if (it2 != it->second.begin())
					printf(", ");
				printf("%d", *it2);
			}
			printf("}\n");
		}
	}

	regSetsT subRegisters;
	for (auto it = replacements.begin(); it != replacements.end(); it++) {
		const StateMachineSideEffect *se = it->first->sideEffect;
		assert(se != NULL);
		threadAndRegister tr(threadAndRegister::invalid());
		if (se->definesRegister(tr)) {
			subRegisters[tr].insert(it->second);
			assert(!correspondence.count(it->second));
			correspondence[it->second] = tr;
		}
	}

	if (debug_ssa_conversion) {
		printf("Register families:\n");
		for (auto it = subRegisters.begin();
		     it != subRegisters.end();
		     it++) {
			printf("%s: {", it->first.name());
			for (auto it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++) {
				if (it2 != it->second.begin())
					printf(", ");
				printf("%s", it2->name());
			}
			printf("}\n");
		}
	}

	std::set<const StateMachineState *> allStates;
	enumStates(inp, &allStates);
	std::map<const StateMachineState *, StateMachineState *> rewrites;
	std::vector<std::pair<StateMachineState **, const StateMachineState *> > relocs;

	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		const StateMachineState *inpState = *it;
		StateMachineState *outState = (StateMachineState *)0xdead;
		switch (inpState->type) {
#define do_state_type(name)						\
			case StateMachineState::name:			\
				outState = buildReplacement(		\
					scopes,				\
					(const StateMachine ## name *)inpState,	\
					relocs,				\
					usedGens,			\
					subRegisters,			\
					replacements);			\
				break;
			all_state_types(do_state_type);
#undef do_state_type
		}
		rewrites[inpState] = outState;
		if (debug_ssa_conversion) {
			printf("Rewrite.  State l%d ->\n", labels[inpState]);
			printStateMachine(outState, stdout);
		}
	}
	if (TIMEOUT)
		return NULL;
	for (auto it = relocs.begin();
	     it != relocs.end();
	     it++) {
		assert(rewrites.count(it->second));
		*it->first = rewrites[it->second];
	}
	assert(rewrites.count(inp->root));
	if (debug_ssa_conversion) {
		printf("Result of SSA conversion:\n");
		printStateMachine(rewrites[inp->root], stdout);
	}
	return new StateMachine(inp, rewrites[inp->root]);
}

/* End of namespace SSA */
}

StateMachine *
convertToSSA(SMScopes *scopes, StateMachine *inp, std::map<threadAndRegister, threadAndRegister> &correspondence)
{
	return SSA::convertToSSA(scopes, inp, correspondence);
}

StateMachineSideEffect *
StateMachineSideEffectPhi::optimise(SMScopes *, const AllowableOptimisations &, bool *done_something)
{
	if (generations.size() == 0)
		return StateMachineSideEffectUnreached::get();

	exprbdd *v = generations[0].val;
	for (unsigned x = 1; x < generations.size(); x++) {
		if (generations[x].val != v)
			return this;
	}
	*done_something = true;
	return new StateMachineSideEffectCopy(reg, v);
}

