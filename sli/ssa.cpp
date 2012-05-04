/* Conversion to static single assignment form */
#include "sli.h"
#include "state_machine.hpp"
#include "ssa.hpp"
#include "offline_analysis.hpp"

namespace SSA {

/* Unconfuse emacs indent */
#if 0
}
#endif

static bool
sideEffectDefinesReg(const StateMachineSideEffect *se, const threadAndRegister &reg,
		     bool acceptPartialDefinition)
{
	bool (*comparator)(const threadAndRegister &a, const threadAndRegister &b);
	if (acceptPartialDefinition)
		comparator = threadAndRegister::partialEq;
	else
		comparator = threadAndRegister::fullEq;
	switch (se->type) {
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *l = (StateMachineSideEffectLoad *)se;
		return comparator(l->target, reg);
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *l = (StateMachineSideEffectCopy *)se;
		return comparator(l->target, reg);
	}
	case StateMachineSideEffect::Phi: {
		StateMachineSideEffectPhi *l = (StateMachineSideEffectPhi *)se;
		return comparator(l->reg, reg);
	}
	case StateMachineSideEffect::AssertFalse:
	case StateMachineSideEffect::Unreached:
	case StateMachineSideEffect::Store:
		return false;
	}
	return true;
}

/* Most machines depend on the initial values of registers i.e. are
   free in some registers.  That confuses a naive conversion to SSA
   form, so, for each possible register, we generate a pseudo-Phi node
   which initialises it from nothing at all, and we pretend that those
   nodes run before the machine starts.  If at the end we find that
   we're dependent on one of those nodes then we code that as a
   dependency on the initial value (i.e. generation -1) */
class ImportRegTable {
public:
	std::set<StateMachineSideEffect *> content;
	ImportRegTable(StateMachine *inp);
};

ImportRegTable::ImportRegTable(StateMachine *inp)
{
	class _ : public StateMachineTransformer {
		std::set<threadAndRegister, threadAndRegister::partialCompare> done;
		std::set<StateMachineSideEffect *> &content;
		IRExpr *transformIex(IRExprGet *g) {
			if (!done.count(g->reg)) {
				std::set<unsigned> gen;
				content.insert(new StateMachineSideEffectPhi(g->reg.setGen(-1), gen));
			}
			return NULL;
		}
	public:
		_(std::set<StateMachineSideEffect *> &_content)
			: content(_content)
		{}
	} doit(content);
	doit.transform(inp);
}

/* Possibly reaching map.  This tells us, for each side effect in a
   state machine, the set of side effects which might conceivably
   reach it. */
template <bool acceptPartialDefinition>
class PossiblyReaching {
	void updateStateReaching(StateMachineState *state,
				 std::set<StateMachineState *> &needsUpdate);
	void buildSideEffectTable(StateMachineState *edge);
	std::map<StateMachineState *, std::set<StateMachineSideEffect *> > stateTable;
	std::map<StateMachineSideEffect *, std::set<StateMachineSideEffect *> > effectTable;
public:
	std::set<StateMachineSideEffect *> &effectsReachingState(StateMachineState *state) {
		return stateTable[state];
	}
	std::set<StateMachineSideEffect *> &effectsReachingSideEffect(StateMachineSideEffect *effect) {
		return effectTable[effect];
	}
	void findReachingGenerations(StateMachineState *e,
				     const threadAndRegister &r,
				     std::set<unsigned> &out);
	void findReachingGenerations(StateMachineSideEffect *e,
				     const threadAndRegister &r,
				     std::set<unsigned> &out);
	PossiblyReaching(StateMachine *inp, const ImportRegTable &imports);
};

static void
enumAllStates(StateMachine *sm, std::set<StateMachineState *> &out)
{
	enumStates(sm, &out);
}

template <bool acceptPartialDefinition>
PossiblyReaching<acceptPartialDefinition>::PossiblyReaching(StateMachine *inp, const ImportRegTable &r)
{
	std::set<StateMachineState *> statesNeedingUpdate;
	enumAllStates(inp, statesNeedingUpdate);

	/* Initial state's initial reaching set is just the import
	 * table.  Other states and edges start off with empty
	 * reaching set. */
	stateTable[inp->root] = r.content;

	/* Iterate to fixed point. */
	while (!statesNeedingUpdate.empty()) {
		if (TIMEOUT)
			return;
		while (!statesNeedingUpdate.empty()) {
			auto it = statesNeedingUpdate.begin();
			auto s = *it;
			statesNeedingUpdate.erase(it);
			updateStateReaching(s, statesNeedingUpdate);
		}
	}

	/* Now build the reaching-side-effect table */
	std::set<StateMachineState *> allStates;
	enumAllStates(inp, allStates);
	for (auto it = allStates.begin(); it != allStates.end(); it++)
		buildSideEffectTable(*it);
}

static void
updateReachingSetForSideEffect(StateMachineSideEffect *smse, std::set<StateMachineSideEffect *> *out,
			       bool acceptPartialDefinition)
{
	class _ {
	public:
		std::set<StateMachineSideEffect *> *out;
		bool acceptPartialDefinition;
		void operator()(threadAndRegister reg) {
			for (auto it = out->begin(); it != out->end(); ) {
				StateMachineSideEffect *o = *it;
				if (sideEffectDefinesReg(o, reg, acceptPartialDefinition))
					out->erase(it++);
				else
					it++;
			}
		}
		_(std::set<StateMachineSideEffect *> *_out,
		  bool _acceptPartialDefinition)
			: out(_out), acceptPartialDefinition(_acceptPartialDefinition)
		{}
	} defineReg(out, acceptPartialDefinition);
	switch (smse->type) {
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *smsel = (StateMachineSideEffectLoad *)smse;
		defineReg(smsel->target);
		out->insert(smse);
		return;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec = (StateMachineSideEffectCopy *)smse;
		defineReg(smsec->target);
		out->insert(smse);
		return;
	}
	case StateMachineSideEffect::Phi: {
		StateMachineSideEffectPhi *smsep = (StateMachineSideEffectPhi *)smse;
		defineReg(smsep->reg);
		out->insert(smse);
		return;
	}
	case StateMachineSideEffect::AssertFalse:
	case StateMachineSideEffect::Unreached:
	case StateMachineSideEffect::Store:
		return;
	}
	abort();
}

template <bool acceptPartialDefinition> void
PossiblyReaching<acceptPartialDefinition>::updateStateReaching(StateMachineState *state, std::set<StateMachineState *> &needsUpdate)
{
	std::set<StateMachineSideEffect *> &reachingThisState(effectsReachingState(state));
	std::set<StateMachineSideEffect *> *reachingEndOfState;
	std::set<StateMachineSideEffect *> _reachingEndOfState;
	if (state->type == StateMachineState::SideEffecting) {
		StateMachineSideEffecting *s = (StateMachineSideEffecting *)state;
		if (s->sideEffect) {
			_reachingEndOfState = reachingThisState;
			updateReachingSetForSideEffect(s->sideEffect, &_reachingEndOfState, acceptPartialDefinition);
			reachingEndOfState = &_reachingEndOfState;
		}
	} else {
		reachingEndOfState = &reachingThisState;
	}
	std::vector<StateMachineState *> targets;
	state->targets(targets);
	for (auto it = targets.begin(); it != targets.end(); it++) {
		std::set<StateMachineSideEffect *> &reachingThisTarget(effectsReachingState(*it));
		if (expandSet(reachingThisTarget, *reachingEndOfState))
			needsUpdate.insert(*it);
	}
}

static void
sideEffectSetToGenerationSet(const std::set<StateMachineSideEffect *> &effects,
			     const threadAndRegister &reg,
			     std::set<unsigned> &out)
{
	struct _ {
		std::set<unsigned> &out;
		_(std::set<unsigned> &_out)
			: out(_out)
		{}
		void operator()(unsigned r) {
			out.insert(r);
		}
	} addItem(out);
	for (auto it = effects.begin(); it != effects.end(); it++) {
		StateMachineSideEffect *se = *it;
		switch (se->type) {
		case StateMachineSideEffect::Load: {
			StateMachineSideEffectLoad *l = (StateMachineSideEffectLoad *)se;
			if (threadAndRegister::partialEq(l->target, reg))
				addItem(l->target.gen());
			break;
		}
		case StateMachineSideEffect::Copy: {
			StateMachineSideEffectCopy *l = (StateMachineSideEffectCopy *)se;
			if (threadAndRegister::partialEq(l->target, reg))
				addItem(l->target.gen());
			break;
		}
		case StateMachineSideEffect::Phi: {
			StateMachineSideEffectPhi *l = (StateMachineSideEffectPhi *)se;
			if (threadAndRegister::partialEq(l->reg, reg))
				addItem(l->reg.gen());
			break;
		}
		case StateMachineSideEffect::AssertFalse:
		case StateMachineSideEffect::Unreached:
		case StateMachineSideEffect::Store:
			break;
		}
	}
}

template <bool acceptPartialDefinition> void
PossiblyReaching<acceptPartialDefinition>::findReachingGenerations(StateMachineState *e,
								   const threadAndRegister &reg,
								   std::set<unsigned> &out)
{
	std::set<StateMachineSideEffect *> &effects(effectsReachingState(e));
	sideEffectSetToGenerationSet(effects, reg, out);
}

template <bool acceptPartialDefinition> void
PossiblyReaching<acceptPartialDefinition>::findReachingGenerations(StateMachineSideEffect *e,
								   const threadAndRegister &reg,
								   std::set<unsigned> &out)
{
	std::set<StateMachineSideEffect *> &effects(effectsReachingSideEffect(e));
	sideEffectSetToGenerationSet(effects, reg, out);
}

template <bool acceptPartialDefinition> void
PossiblyReaching<acceptPartialDefinition>::buildSideEffectTable(StateMachineState *e)
{
	if (e->type != StateMachineState::SideEffecting)
		return;
	StateMachineSideEffecting *se = (StateMachineSideEffecting *)e;
	if (se->sideEffect)
		expandSet(effectsReachingSideEffect(se->sideEffect),
			  effectsReachingState(e));
}

/* Assert that the machine does not currently reference and tAR
   structures with non-zero generation number. */
static void
assertNonSsa(StateMachine *inp)
{
#ifndef NDEBUG
	class : public StateMachineTransformer {
		IRExpr *transformIex(IRExprGet *g) {
			assert(g->reg.gen() == 0);
			return NULL;
		}
		StateMachineSideEffectLoad *transformOneSideEffect(StateMachineSideEffectLoad *l, bool *done_something) {
			assert(l->target.gen() == 0);
			return StateMachineTransformer::transformOneSideEffect(l, done_something);
		}
		StateMachineSideEffectCopy *transformOneSideEffect(StateMachineSideEffectCopy *l, bool *done_something) {
			assert(l->target.gen() == 0);
			return StateMachineTransformer::transformOneSideEffect(l, done_something);
		}
		StateMachineSideEffectPhi *transformOneSideEffect(StateMachineSideEffectPhi *, bool *) {
			abort();
		}
	} t;
	t.StateMachineTransformer::transform(inp);
#endif
}

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

static IRRegArray *rawDupe(duplication_context &ctxt, const IRRegArray *inp)
{
	IRRegArray *res = new IRRegArray();
	res->base = inp->base;
	res->elemTy = inp->elemTy;
	res->nElems = inp->nElems;
	return res;
}

static IRConst *rawDupe(duplication_context &ctxt, const IRConst *inp)
{
	IRConst *res = new IRConst();
	res->tag = inp->tag;
	res->Ico = inp->Ico;
	return res;
}

static IRCallee *rawDupe(duplication_context &ctxt, const IRCallee *inp)
{
	IRCallee *res = new IRCallee();
	res->regparms = inp->regparms;
	res->name = inp->name;
	res->addr = inp->addr;
	res->mcx_mask = inp->mcx_mask;
	return res;
}

static IRExpr *rawDupe(duplication_context &ctxt, const IRExpr *inp)
{
	switch (inp->tag) {
	case Iex_Get: {
		const IRExprGet *i = (const IRExprGet *)inp;
		return new IRExprGet(i->reg, i->ty);
	}
	case Iex_GetI: {
		const IRExprGetI *i = (const IRExprGetI *)inp;
		IRExprGetI *res = new IRExprGetI();
		ctxt(&res->descr, i->descr, rawDupe);
		ctxt(&res->ix, i->ix, rawDupe);
		res->bias = i->bias;
		res->tid = i->tid;
		return res;
	}
	case Iex_Qop: {
		const IRExprQop *i = (const IRExprQop *)inp;
		IRExprQop *res = new IRExprQop();
		res->op = i->op;
		ctxt(&res->arg1, i->arg1, rawDupe);
		ctxt(&res->arg2, i->arg2, rawDupe);
		ctxt(&res->arg3, i->arg3, rawDupe);
		ctxt(&res->arg4, i->arg4, rawDupe);
		return res;
	}
	case Iex_Triop: {
		const IRExprTriop *i = (const IRExprTriop *)inp;
		IRExprTriop *res = new IRExprTriop();
		res->op = i->op;
		ctxt(&res->arg1, i->arg1, rawDupe);
		ctxt(&res->arg2, i->arg2, rawDupe);
		ctxt(&res->arg3, i->arg3, rawDupe);
		return res;
	}
	case Iex_Binop: {
		const IRExprBinop *i = (const IRExprBinop *)inp;
		IRExprBinop *res = new IRExprBinop();
		res->op = i->op;
		ctxt(&res->arg1, i->arg1, rawDupe);
		ctxt(&res->arg2, i->arg2, rawDupe);
		return res;
	}
	case Iex_Unop: {
		const IRExprUnop *i = (const IRExprUnop *)inp;
		IRExprUnop *res = new IRExprUnop();
		res->op = i->op;
		ctxt(&res->arg, i->arg, rawDupe);
		return res;
	}
	case Iex_Load: {
		const IRExprLoad *i = (const IRExprLoad *)inp;
		IRExprLoad *res = new IRExprLoad(i->rip);
		res->ty = i->ty;
		ctxt(&res->addr, i->addr, rawDupe);
		return res;
	}
	case Iex_Const: {
		const IRExprConst *i = (const IRExprConst *)inp;
		IRExprConst *res = new IRExprConst();
		ctxt(&res->con, i->con, rawDupe);
		return res;
	}
	case Iex_CCall: {
		const IRExprCCall *i = (const IRExprCCall *)inp;
		IRExprCCall *res = new IRExprCCall();
		ctxt(&res->cee, i->cee, rawDupe);
		res->retty = i->retty;
		int nr_args;
		for (nr_args = 0; i->args[nr_args]; nr_args++)
			;
		res->args = alloc_irexpr_array(nr_args + 1);
		for (nr_args = 0; i->args[nr_args]; nr_args++)
			ctxt(&res->args[nr_args], i->args[nr_args], rawDupe);
		res->args[nr_args] = NULL;
		return res;
	}
	case Iex_Mux0X: {
		const IRExprMux0X *i = (const IRExprMux0X *)inp;
		IRExprMux0X *res = new IRExprMux0X();
		ctxt(&res->cond, i->cond, rawDupe);
		ctxt(&res->expr0, i->expr0, rawDupe);
		ctxt(&res->exprX, i->exprX, rawDupe);
		return res;
	}
	case Iex_Associative: {
		const IRExprAssociative *i = (const IRExprAssociative *)inp;
		IRExprAssociative *res = new IRExprAssociative();
		res->op = i->op;
		res->nr_arguments = i->nr_arguments;
		res->nr_arguments_allocated = i->nr_arguments;
		static libvex_allocation_site __las = {0, __FILE__, __LINE__};		
		res->contents =
			(IRExpr **)__LibVEX_Alloc_Bytes(&ir_heap,
							sizeof(res->contents[0]) * res->nr_arguments,
							&__las);
		for (int j = 0; j < res->nr_arguments; j++)
			ctxt(&res->contents[j], i->contents[j], rawDupe);
		return res;
	}
	case Iex_FreeVariable: {
		const IRExprFreeVariable *i = (const IRExprFreeVariable *)inp;
		IRExprFreeVariable *res = new IRExprFreeVariable();
		res->key = i->key;
		return res;
	}
	case Iex_ClientCall: {
		const IRExprClientCall *i = (const IRExprClientCall *)inp;
		IRExprClientCall *res = new IRExprClientCall();
		res->calledRip = i->calledRip;
		res->callSite = i->callSite;
		int nr_args;
		for (nr_args = 0; i->args[nr_args]; nr_args++)
			;
		res->args = alloc_irexpr_array(nr_args + 1);
		for (nr_args = 0; i->args[nr_args]; nr_args++)
			ctxt(&res->args[nr_args], i->args[nr_args], rawDupe);
		res->args[nr_args] = NULL;
		return res;
	}
	case Iex_ClientCallFailed: {
		const IRExprClientCallFailed *i = (const IRExprClientCallFailed *)inp;
		IRExprClientCallFailed *res = new IRExprClientCallFailed();
		ctxt(&res->target, i->target, rawDupe);
		return res;
	}
	case Iex_HappensBefore: {
		const IRExprHappensBefore *i = (const IRExprHappensBefore *)inp;
		return new IRExprHappensBefore(i->before, i->after);
	}
	case Iex_Phi: {
		const IRExprPhi *i = (const IRExprPhi *)inp;
		return new IRExprPhi(i->reg, i->generations, i->ty);
	}
	}
	abort();
}

static StateMachineSideEffectLoad *
rawDupe(duplication_context &ctxt, const StateMachineSideEffectLoad *l)
{
	StateMachineSideEffectLoad *res = new StateMachineSideEffectLoad(l->target,
									 NULL,
									 l->rip,
									 l->type);
	ctxt(&res->addr, l->addr, rawDupe);
	return res;
}

static StateMachineSideEffectStore *
rawDupe(duplication_context &ctxt, const StateMachineSideEffectStore *l)
{
	StateMachineSideEffectStore *res = new StateMachineSideEffectStore(NULL,
									   NULL,
									   l->rip);
	ctxt(&res->addr, l->addr, rawDupe);
	ctxt(&res->data, l->data, rawDupe);
	return res;
}

static StateMachineSideEffectUnreached *
rawDupe(duplication_context &ctxt, const StateMachineSideEffectUnreached *l)
{
	return StateMachineSideEffectUnreached::get();
}

static StateMachineSideEffectAssertFalse *
rawDupe(duplication_context &ctxt, const StateMachineSideEffectAssertFalse *l)
{
	StateMachineSideEffectAssertFalse *res = new StateMachineSideEffectAssertFalse(NULL);
	ctxt(&res->value, l->value, rawDupe);
	return res;
}

static StateMachineSideEffectCopy *
rawDupe(duplication_context &ctxt, const StateMachineSideEffectCopy *l)
{
	StateMachineSideEffectCopy *res = new StateMachineSideEffectCopy(l->target,
									 NULL);
	ctxt(&res->value, l->value, rawDupe);
	return res;
}

static StateMachineSideEffectPhi *
rawDupe(duplication_context &ctxt, const StateMachineSideEffectPhi *l)
{
	StateMachineSideEffectPhi *res = new StateMachineSideEffectPhi(l->reg, l->generations);
	for (unsigned x = 0; x < l->generations.size(); x++)
		ctxt(&res->generations[x].second, l->generations[x].second, rawDupe);
	return res;
}

static StateMachineSideEffect *
rawDupe(duplication_context &ctxt, const StateMachineSideEffect *smse)
{
	switch (smse->type) {
#define do_case(n)							\
		case StateMachineSideEffect::n:				\
			return rawDupe(ctxt,				\
				       (const StateMachineSideEffect ## n *)smse)
		do_case(Load);
		do_case(Store);
		do_case(Unreached);
		do_case(AssertFalse);
		do_case(Copy);
		do_case(Phi);
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
		StateMachineBifurcate *res = new StateMachineBifurcate(smb->origin, NULL, NULL, NULL);
		ctxt(&res->condition, smb->condition, rawDupe);
		ctxt(&res->trueTarget, smb->trueTarget, rawDupe);
		ctxt(&res->falseTarget, smb->falseTarget, rawDupe);
		return res;
	}
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *sme = (StateMachineSideEffecting *)inp;
		StateMachineSideEffecting *res = new StateMachineSideEffecting(sme->origin,
									       rawDupe(ctxt, sme->sideEffect),
									       NULL);
		ctxt(&res->target, sme->target, rawDupe);
		return res;
	}
	case StateMachineState::Unreached:
		return StateMachineUnreached::get();
	case StateMachineState::Crash:
		return StateMachineCrash::get();
	case StateMachineState::NoCrash:
		return StateMachineNoCrash::get();
	case StateMachineState::Stub: {
		StateMachineStub *sms = (StateMachineStub *)inp;
		return new StateMachineStub(sms->origin, sms->target);
	}
	}
	abort();
}

static StateMachine *
rawDupe(duplication_context &ctxt, const StateMachine *inp)
{
	assert(inp->freeVariables.empty());
	FreeVariableMap fv;
	StateMachine *res = new StateMachine(
		NULL,
		inp->origin,
		fv,
		inp->tid);
	ctxt(&res->root, inp->root, rawDupe);
	return res;
}

static StateMachine *
duplicateStateMachine(const StateMachine *inp)
{
	duplication_context ctxt;
	assert(inp->freeVariables.empty());
	StateMachine *res;
	ctxt(&res, inp, rawDupe);
	ctxt.doit();
	return res;
}

static StateMachine *
assignLabelsToDefinitions(StateMachine *sm,
			  std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &lastGeneration)
{
	struct _ : public StateMachineTransformer {
		std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &lastGeneration;
		StateMachineSideEffect *transformSideEffect(StateMachineSideEffect *se,
							    bool *done_something) {
			threadAndRegister tr(threadAndRegister::invalid());
			if (se->definesRegister(tr)) {
				/* Shouldn't be processing the same
				 * side effect multiple times. */
				assert(tr.gen() == 0);
				tr = tr.setGen(++lastGeneration[tr]);
				switch (se->type) {
				case StateMachineSideEffect::Load: {
					StateMachineSideEffectLoad *smsel =
						(StateMachineSideEffectLoad *)se;
					se = new StateMachineSideEffectLoad(
						tr,
						smsel->addr,
						smsel->rip,
						smsel->type);
					*done_something = true;
					break;
				}
				case StateMachineSideEffect::Copy: {
					StateMachineSideEffectCopy *smsec =
						(StateMachineSideEffectCopy *)se;
					se = new StateMachineSideEffectCopy(
						tr,
						smsec->value);
					*done_something = true;
					break;
				}
				case StateMachineSideEffect::Phi:
					/* Shouldn't be in SSA form yet */
					abort();
				case StateMachineSideEffect::Store:
				case StateMachineSideEffect::AssertFalse:
				case StateMachineSideEffect::Unreached:
					/* These shouldn't define registers */
					abort();
				}
			}
			return se;
		}
		_(std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &_lastGeneration)
			: lastGeneration(_lastGeneration)
		{}
	} doit(lastGeneration);
	return doit.transform(sm);
}

/* A map from registers to sets of generations, telling us precisely
   which generations can reach a particular state. */
class ReachingEntry : public std::map<threadAndRegister, std::set<unsigned>, threadAndRegister::partialCompare> {
public:
	bool merge(const ReachingEntry &other);
	const std::set<unsigned> &get(const threadAndRegister &tr) const {
		auto it = find(tr);
		assert(it != end());
		return it->second;
	}
};

bool
ReachingEntry::merge(const ReachingEntry &other)
{
	/* Could make this faster by taking advantage of the fact that
	   both maps are sorted in the same order, and the fact that
	   all the sets are sorted in the same order. */
	bool res = false;
	for (auto it = other.begin(); it != other.end(); it++) {
		auto localIt = find(it->first);
		if (localIt == end()) {
			insert(*it);
			res = true;
		} else {
			for (auto genIt = it->second.begin();
			     genIt != it->second.end();
			     genIt++)
				res |= localIt->second.insert(*genIt).second;
		}
	}
	return res;
}

class ReachingTable {
	std::map<const StateMachineState *, ReachingEntry> content;
	ReachingEntry initialReachingSet(const StateMachine *);
	ReachingEntry getExitReaching(const StateMachineState *);
public:
	const ReachingEntry &getEntryReaching(const StateMachineState *sm) const {
		auto it = content.find(sm);
		assert(it != content.end());
		return it->second;
	}
	ReachingTable(const StateMachine *);
};

ReachingTable::ReachingTable(const StateMachine *inp)
{
	/* Initial value of the root is the import of all of the
	   registers which might possibly be relevant.  Initial value
	   of everything else is empty. */
	content[inp->root] = initialReachingSet(inp);

	/* Iterate to a fixed point. */
	std::queue<const StateMachineState *> toProcess;
	toProcess.push(inp->root);
	while (!toProcess.empty()) {
		const StateMachineState *s = toProcess.front();
		toProcess.pop();
		ReachingEntry exitReaching(getExitReaching(s));
		std::vector<const StateMachineState *> exits;
		s->targets(exits);
		for (auto it = exits.begin(); it != exits.end(); it++) {
			if (content[*it].merge(exitReaching))
				toProcess.push(*it);
		}
	}
}

ReachingEntry
ReachingTable::initialReachingSet(const StateMachine *sm)
{
	struct : public StateMachineTransformer {
		ReachingEntry res;
		IRExpr *transformIex(IRExprGet *ieg) {
			if (ieg->reg.isReg())
				res[ieg->reg].insert((unsigned)-1);
			return IRExprTransformer::transformIex(ieg);
		}
	} doit;
	doit.transform(const_cast<StateMachine *>(sm));
	return doit.res;
}

ReachingEntry
ReachingTable::getExitReaching(const StateMachineState *s)
{
	const StateMachineSideEffect *se = s->getSideEffect();
	threadAndRegister definedHere(threadAndRegister::invalid());
	if (!se || !se->definesRegister(definedHere))
		return content[s];
	ReachingEntry res(content[s]);
	std::set<unsigned> &gens(res[definedHere]);
	gens.clear();
	gens.insert(definedHere.gen());
	return res;
}

static StateMachine *
resolveDependencies(StateMachine *sm,
		    ReachingTable &reachingTable,
		    std::set<StateMachineState *> &failedStates)
{
	struct _ : public StateMachineTransformer {
		const ReachingTable &reachingTable;
		std::set<StateMachineState *> &failedStates;

		const ReachingEntry *currentStateReaching;
		StateMachineState *currentState;

		IRExpr *transformIex(IRExprGet *ieg) {
			assert(currentStateReaching);
			assert(currentState);
			const std::set<unsigned> &gen(currentStateReaching->get(ieg->reg));
			assert(gen.size() != 0);
			if (gen.size() == 1) {
				return IRExpr_Get(
					ieg->reg.setGen(*gen.begin()),
					ieg->ty);
			} else {
				failedStates.insert(currentState);
				return NULL;
			}
		}
		StateMachineState *transformState(StateMachineState *sms,
						  bool *done_something)
		{
			assert(!currentState);
			assert(!currentStateReaching);
			if (sms->type == StateMachineState::Bifurcate ||
			    sms->type == StateMachineState::SideEffecting)
				currentStateReaching = &reachingTable.getEntryReaching(sms);
			currentState = sms;
			StateMachineState *res =
				StateMachineTransformer::transformState(sms, done_something);
			assert(currentState == sms);
			currentState = NULL;
			currentStateReaching = NULL;
			return res;
		}
		_(ReachingTable &_reachingTable,
		  std::set<StateMachineState *> &_failedStates)
			: reachingTable(_reachingTable),
			  failedStates(_failedStates),
			  currentStateReaching(NULL),
			  currentState(NULL)
		{}
	} doit(reachingTable, failedStates);
	return doit.transform(sm);
}

static void
findUnresolvedReferences(StateMachineState *s, std::set<threadAndRegister, threadAndRegister::partialCompare> &out)
{
	struct _ : public StateMachineTransformer {
		std::set<threadAndRegister, threadAndRegister::partialCompare> &out;
		IRExpr *transformIex(IRExprGet *ieg) {
			if (ieg->reg.gen() == 0)
				out.insert(ieg->reg);
			return NULL;
		}
		_(
			std::set<threadAndRegister, threadAndRegister::partialCompare> &_out)
			: out(_out)
		{}
	} t(out);
	bool d;
	t.transformState(s, &d);
}

static StateMachineSideEffecting *
findPredecessor(StateMachine *sm, StateMachineState *s)
{
	if (s->type == StateMachineState::SideEffecting)
		return (StateMachineSideEffecting *)s;
	std::set<StateMachineState *> allStates;
	enumStates(sm, &allStates);
	StateMachineState *found = NULL;
	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		std::vector<StateMachineState *> successors;
		(*it)->targets(successors);
		for (auto it2 = successors.begin(); it2 != successors.end(); it2++) {
			if (*it2 == s) {
				if (found == NULL) {
					found = *it;
				} else {
					goto insert_new_predecessor;
				}
			}
		}
	}
	if (found && found->type == StateMachineState::SideEffecting)
		return (StateMachineSideEffecting *)found;

insert_new_predecessor:
	StateMachineSideEffecting *res = new StateMachineSideEffecting(s->origin, NULL, s);
	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		StateMachineState *s = *it;
		switch (s->type) {
		case StateMachineState::SideEffecting: {
			StateMachineSideEffecting *se = (StateMachineSideEffecting *)s;
			if (se->target == s)
				se->target = res;
			break;
		}
		case StateMachineState::Bifurcate: {
			StateMachineBifurcate *se = (StateMachineBifurcate *)s;
			if (se->trueTarget == s)
				se->trueTarget = res;
			if (se->falseTarget == s)
				se->falseTarget = res;
			break;
		}
		case StateMachineState::Unreached:
		case StateMachineState::Crash:
		case StateMachineState::NoCrash:
		case StateMachineState::Stub:
			break;
		}
	}

	return res;
}

static StateMachine *
convertToSSA(StateMachine *inp)
{
	inp->sanityCheck();
	assertNonSsa(inp);

	inp = duplicateStateMachine(inp);

	std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> lastGeneration;
	inp = assignLabelsToDefinitions(inp, lastGeneration);

	std::set<StateMachineState *> pendingStates;
	enumStates(inp, &pendingStates);

	while (1) {
		if (TIMEOUT)
			return NULL;

		ReachingTable reaching(inp);
		std::set<StateMachineState *> newPendingStates;
		inp = resolveDependencies(inp, reaching, newPendingStates);
		if (newPendingStates.empty()) {
			/* We're done */
			break;
		}

		/* We can only introduce one phi node for each
		   register each time around, because every time we do
		   we invalidate the reaching map.  We simplify
		   further by just only resolving one state each
		   time around. */
		StateMachineState *s;
		{
			auto it = newPendingStates.begin();
			s = *it;
			it++;
			pendingStates.clear();
			pendingStates.insert(it, newPendingStates.end());
		}

		std::set<threadAndRegister, threadAndRegister::partialCompare> needed;
		StateMachineSideEffecting *insertAt;

		findUnresolvedReferences(s, needed);
		insertAt = findPredecessor(inp, s);
		for (auto it = needed.begin();
		     it != needed.end();
		     it++)
			insertAt->prependSideEffect(
					new StateMachineSideEffectPhi(
						it->setGen(++lastGeneration[*it]),
						reaching.getEntryReaching(s).get(*it)));
	}

	inp->assertSSA();
	inp->sanityCheck();

	return inp;
}

class optimiseSSATransformer : public StateMachineTransformer {
	PossiblyReaching<false> reaching;

	StateMachineSideEffectPhi *transformOneSideEffect(StateMachineSideEffectPhi *phi,
							  bool *done_something)
	{
		assert(phi->generations.size() != 0);
		std::set<unsigned> generations;
		reaching.findReachingGenerations(phi, phi->reg, generations);
		for (auto it = phi->generations.begin(); it != phi->generations.end(); ) {
			if (!generations.count(it->first)) {
				*done_something = true;
				it = phi->generations.erase(it);
			} else {
				it++;
			}
		}
		assert(phi->generations.size() != 0);
		return phi;
	}
	IRExpr *transformIRExpr(IRExpr *e, bool *b) { return NULL; }
public:
	optimiseSSATransformer(StateMachine *inp)
		: reaching(inp, ImportRegTable(inp))
	{}
};

/* Other optimisations can sometimes lead to the set of assignments
   which might reach a Phi node shrinking.  This pass goes through and
   fixes things up so that the reaching set in the Phi node
   accurately reflects this. */
static StateMachine *
optimiseSSA(StateMachine *inp, bool *done_something)
{
	optimiseSSATransformer t(inp);
	if (TIMEOUT)
		return inp;
	return t.transform(inp, done_something);
}

/* End of namespace SSA */
}

StateMachine *
convertToSSA(StateMachine *inp)
{
	return SSA::convertToSSA(inp);
}

StateMachine *
optimiseSSA(StateMachine *inp, bool *done_something)
{
	return SSA::optimiseSSA(inp, done_something);
}

StateMachineSideEffect *
StateMachineSideEffectPhi::optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something)
{
	if (generations.size() == 0 ||
	    generations[0].second == NULL)
		return this;
	IRExpr *v = generations[0].second;
	for (unsigned x = 1; x < generations.size(); x++) {
		if (generations[x].second != v)
			return this;
	}
	*done_something = true;
	return new StateMachineSideEffectCopy(reg, v);
}

