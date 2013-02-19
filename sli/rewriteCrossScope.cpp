#include "sli.h"
#include "state_machine.hpp"
#include "inferred_information.hpp"

namespace rewriteSummaryCrossScopeWorkers{

template <typename ctxtT>
struct reloc {
	void **ptr;
	const void *src;
	typedef void *(*doitT)(const void *src, std::vector<reloc> &pending, ctxtT &ctxt);
	doitT doit;
	reloc(void **_ptr, const void *_src, doitT _doit)
		: ptr(_ptr), src(_src), doit(_doit)
	{}
	template <typename t> static reloc<ctxtT> mk(
		t **_ptr,
		const t *_src,
		t *(*_doit)(const t *src, std::vector<reloc> &pending, ctxtT &ctxt))
	{
		return reloc<ctxtT>((void **)_ptr, (const void *)_src, (doitT)_doit);
	}
};

struct state {
	SMScopes *scopes;
	std::map<const bbdd *, bbdd *> bools;
	std::map<const smrbdd *, smrbdd *> smrs;
	std::map<const exprbdd *, exprbdd *> exprs;
};

typedef reloc<state> relocT;
template <typename t> static void r(
	std::vector<relocT> &pending,
	t **targ,
	const t *src);
static bbdd *doit(const bbdd *inp, std::vector<relocT> &relocs, state &state)
{
	auto it_did_insert = state.bools.insert(std::pair<const bbdd *, bbdd *>(inp, (bbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (inp->isLeaf()) {
			it->second = state.scopes->bools.cnst(inp->leaf());
		} else {
			it->second = bbdd::ifelse(
				&state.scopes->bools,
				bbdd::var(&state.scopes->bools, inp->internal().condition),
				doit(inp->internal().trueBranch,
				     relocs,
				     state),
				doit(inp->internal().falseBranch,
				     relocs,
				     state));
		}
	}
	assert(it->second);
	return it->second;
}
static smrbdd *doit(const smrbdd *inp, std::vector<relocT> &relocs, state &state)
{
	auto it_did_insert = state.smrs.insert(std::pair<const smrbdd *, smrbdd *>(inp, (smrbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (inp->isLeaf()) {
			it->second = state.scopes->smrs.cnst(inp->leaf());
		} else {
			it->second = smrbdd::ifelse(
				&state.scopes->smrs,
				bbdd::var(&state.scopes->bools, inp->internal().condition),
				doit(inp->internal().trueBranch,
				     relocs,
				     state),
				doit(inp->internal().falseBranch,
				     relocs,
				     state));
		}
	}
	assert(it->second);
	return it->second;
}
static exprbdd *doit(const exprbdd *inp, std::vector<relocT> &relocs, state &state)
{
	auto it_did_insert = state.exprs.insert(std::pair<const exprbdd *, exprbdd *>(inp, (exprbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (inp->isLeaf()) {
			it->second = exprbdd::var(&state.scopes->exprs,
						  &state.scopes->bools,
						  inp->leaf());
		} else {
			it->second = exprbdd::ifelse(
				&state.scopes->exprs,
				bbdd::var(&state.scopes->bools, inp->internal().condition),
				doit(inp->internal().trueBranch,
				     relocs,
				     state),
				doit(inp->internal().falseBranch,
				     relocs,
				     state));
		}
	}
	assert(it->second);
	return it->second;
}

/* It's arguably a bit silly to have a const side-effect,
   since all of the side-effect structures are immutable
   anyway, but put it in anyway as a hint about which pointers
   are in the old state machine and which are in the new
   one. */
static StateMachineSideEffectLoad *_doit(const StateMachineSideEffectLoad *inp,
					 std::vector<relocT> &pending,
					 state &state)
{
	return new StateMachineSideEffectLoad(inp, doit(inp->addr, pending, state));
}
static StateMachineSideEffectStore *_doit(const StateMachineSideEffectStore *inp,
					  std::vector<relocT> &pending,
					  state &state)
{
	return new StateMachineSideEffectStore(
		inp,
		doit(inp->addr, pending, state),
		doit(inp->data, pending, state));
}
static StateMachineSideEffectCopy *_doit(const StateMachineSideEffectCopy *inp,
					 std::vector<relocT> &pending,
					 state &state)
{
	return new StateMachineSideEffectCopy(inp, doit(inp->value, pending, state));
}
static StateMachineSideEffectAssertFalse *_doit(const StateMachineSideEffectAssertFalse *inp,
						std::vector<relocT> &pending,
						state &state)
{
	return new StateMachineSideEffectAssertFalse(inp, doit(inp->value, pending, state));
}
static StateMachineSideEffectStartAtomic *_doit(const StateMachineSideEffectStartAtomic *inp,
						std::vector<relocT> &,
						state &)
{
	return const_cast<StateMachineSideEffectStartAtomic *>(inp);
}
static StateMachineSideEffectEndAtomic *_doit(const StateMachineSideEffectEndAtomic *inp,
					      std::vector<relocT> &,
					      state &)
{
	return const_cast<StateMachineSideEffectEndAtomic *>(inp);
}
static StateMachineSideEffectUnreached *_doit(const StateMachineSideEffectUnreached *inp,
					      std::vector<relocT> &,
					      state &)
{
	return const_cast<StateMachineSideEffectUnreached *>(inp);
}
static StateMachineSideEffectPhi *_doit(const StateMachineSideEffectPhi *inp,
					std::vector<relocT> &relocs,
					state &state)
{
	std::vector<StateMachineSideEffectPhi::input> inputs(inp->generations);
	for (auto it = inputs.begin(); it != inputs.end(); it++) {
		it->val = doit(it->val, relocs, state);
	}
	return new StateMachineSideEffectPhi(inp, inputs);
}
#if !CONFIG_NO_STATIC_ALIASING
static StateMachineSideEffectStartFunction *_doit(const StateMachineSideEffectStartFunction *inp,
						  std::vector<relocT> &relocs,
						  state &state)
{
	return new StateMachineSideEffectStartFunction(inp, doit(inp->rsp, relocs, state));
}
static StateMachineSideEffectEndFunction *_doit(const StateMachineSideEffectEndFunction *inp,
						std::vector<relocT> &relocs,
						state &state)
{
	return new StateMachineSideEffectEndFunction(inp, doit(inp->rsp, relocs, state));
}
static StateMachineSideEffectStackLayout *_doit(const StateMachineSideEffectStackLayout *inp,
						std::vector<relocT> &,
						state &)
{
	return const_cast<StateMachineSideEffectStackLayout *>(inp);
}
#endif
static StateMachineSideEffectImportRegister *_doit(const StateMachineSideEffectImportRegister *inp,
						   std::vector<relocT> &,
						   state &)
{
	return const_cast<StateMachineSideEffectImportRegister *>(inp);
}

static StateMachineSideEffect *doit(const StateMachineSideEffect *inp,
				    std::vector<relocT> &pending,
				    state &state)
{
	switch (inp->type) {
#define do_type(name)							\
		case StateMachineSideEffect:: name :			\
			return _doit((const StateMachineSideEffect ## name *)inp, \
				     pending,				\
				     state);
		all_side_effect_types(do_type)
#undef do_type
			}
	abort();
}

static StateMachineState *doit(const StateMachineState *inp, std::vector<relocT> &pending, state &);
static StateMachineBifurcate *_doit(const StateMachineBifurcate *inp,
				    std::vector<relocT> &pending,
				    state &state)
{
	StateMachineBifurcate *res = new StateMachineBifurcate(inp->dbg_origin,
							       doit(inp->condition, pending, state),
							       NULL,
							       NULL);
	r(pending, &res->trueTarget, inp->trueTarget);
	r(pending, &res->falseTarget, inp->falseTarget);
	return res;
}
static StateMachineSideEffecting *_doit(const StateMachineSideEffecting *inp,
					std::vector<relocT> &pending,
					state &)
{
	StateMachineSideEffecting *res = new StateMachineSideEffecting(inp->dbg_origin,
								       NULL,
								       NULL);
	if (inp->sideEffect)
		r(pending, &res->sideEffect, inp->sideEffect);
	r(pending, &res->target, inp->target);
	return res;
}
static StateMachineTerminal *_doit(const StateMachineTerminal *inp,
				   std::vector<relocT> &relocs,
				   state &state)
{
	return new StateMachineTerminal(inp->dbg_origin,
					doit(inp->res, relocs, state));
}
static StateMachineState *doit(const StateMachineState *inp, std::vector<relocT> &pending, state &state)
{
	switch (inp->type) {
#define do_type(name)							\
		case StateMachineState:: name :				\
			return _doit( (StateMachine ## name *)inp,	\
				      pending, state);
		all_state_types(do_type)
#undef do_type
			}
	abort();
}
static StateMachine *doit(const StateMachine *inp, std::vector<relocT> &pending, state &)
{
	StateMachine *res = new StateMachine(NULL, inp->cfg_roots);
	r(pending, &res->root, inp->root);
	return res;
}
static CrashSummary *doit(const CrashSummary *inp, std::vector<relocT> &pending, state &state)
{
	CrashSummary *res = new CrashSummary(state.scopes,
					     NULL,
					     NULL,
					     NULL,
					     NULL,
					     inp->aliasing,
					     inp->mai);
	r(pending, &res->loadMachine, inp->loadMachine);
	r(pending, &res->storeMachine, inp->storeMachine);
	r(pending, &res->inferredAssumption, inp->inferredAssumption);
	r(pending, &res->crashCondition, inp->crashCondition);
	return res;
}
template <typename t>
static void r(std::vector<relocT> &pending,
	      t **targ,
	      const t *src)
{
	pending.push_back(
		relocT::mk<t>(
			targ,
			src,
			doit));
}

static void
processRelocs(state &stt, std::vector<reloc<state> > &relocs)
{
	std::map<const void *, void *> results;
	while (!relocs.empty()) {
		const reloc<rewriteSummaryCrossScopeWorkers::state> r(relocs.back());
		relocs.pop_back();
		auto it_did_insert = results.insert(std::pair<const void *, void *>(r.src, (void *)NULL));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (did_insert) {
			it->second = r.doit(r.src, relocs, stt);
		}
		*r.ptr = it->second;
	}
}

static CrashSummary *
rewriteSummaryCrossScope(const CrashSummary *oldSummary, SMScopes *newScopes)
{
	CrashSummary *res;

	/* Shut compiler up */
	res = (CrashSummary *)0xf001;

	std::vector<reloc<state> > relocs;
	state stt;
	stt.scopes = newScopes;
	r(relocs, &res, oldSummary);

	processRelocs(stt, relocs);

	assert(res != NULL);
	return res;
}

static StateMachine *
rewriteMachineCrossScope(const StateMachine *oldMachine, SMScopes *newScopes)
{
	StateMachine *res;

	/* Shut compiler up */
	res = (StateMachine *)0xf001;

	std::vector<reloc<state> > relocs;
	state stt;
	stt.scopes = newScopes;
	r(relocs, &res, oldMachine);
	std::map<const void *, void *> results;

	processRelocs(stt, relocs);

	assert(res != NULL);
	return res;
}

/* End of scope */
};

CrashSummary *
rewriteSummaryCrossScope(const CrashSummary *oldSummary, SMScopes *newScopes)
{
	return rewriteSummaryCrossScopeWorkers::rewriteSummaryCrossScope(oldSummary, newScopes);
}

StateMachine *
rewriteMachineCrossScope(const StateMachine *oldMachine, SMScopes *newScopes)
{
	return rewriteSummaryCrossScopeWorkers::rewriteMachineCrossScope(oldMachine, newScopes);
}

