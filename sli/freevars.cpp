/* There are some memory locations which are effectively completely
 * unconstrained by anything which the machine does.  Replace those
 * with freshly allocated free variables.  The idea here is that we
 * can then propagate that through a bit and potentially simplify lots
 * of other bits of the machine by allocating yet more free
 * variables. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "libvex_prof.hpp"
#include "libvex_parse.h"

namespace _freevars {
/* Unconfuse emacs. */
#if 0
}
#endif

static void
nrAliasingLoads(StateMachineState *sm,
		StateMachineSideEffectLoad *smsel,
		const Oracle::RegisterAliasingConfiguration &alias,
		const AllowableOptimisations &opt,
		int *out,
		std::set<StateMachineState *> &visited,
		OracleInterface *oracle);
static void
nrAliasingLoads(StateMachineEdge *sme,
		StateMachineSideEffectLoad *smsel,
		const Oracle::RegisterAliasingConfiguration &alias,
		const AllowableOptimisations &opt,
		int *out,
		std::set<StateMachineState *> &visited,
		OracleInterface *oracle)
{
	for (unsigned x = 0; x < sme->sideEffects.size(); x++) {
		StateMachineSideEffectLoad *smsel2 =
			dynamic_cast<StateMachineSideEffectLoad *>(sme->sideEffects[x]);
		if (smsel2 &&
		    alias.ptrsMightAlias(smsel->addr, smsel2->addr, opt.freeVariablesMightAccessStack) &&
		    oracle->memoryAccessesMightAlias(smsel, smsel2) &&
		    definitelyEqual( smsel->addr,
				     smsel2->addr,
				     opt))
			(*out)++;
	}
	nrAliasingLoads(sme->target, smsel, alias, opt, out, visited, oracle);
}
static void
nrAliasingLoads(StateMachineState *sm,
		StateMachineSideEffectLoad *smsel,
		const Oracle::RegisterAliasingConfiguration &alias,
		const AllowableOptimisations &opt,
		int *out,
		std::set<StateMachineState *> &visited,
		OracleInterface *oracle)
{
	if (visited.count(sm))
		return;
	visited.insert(sm);
	if (sm->target0())
		nrAliasingLoads(sm->target0(),
				smsel,
				alias,
				opt,
				out,
				visited,
				oracle);
	if (sm->target1())
		nrAliasingLoads(sm->target1(),
				smsel,
				alias,
				opt,
				out,
				visited,
				oracle);
}
static int
nrAliasingLoads(StateMachine *sm,
		StateMachineSideEffectLoad *smsel,
		const Oracle::RegisterAliasingConfiguration &alias,
		const AllowableOptimisations &opt,
		OracleInterface *oracle)
{
	std::set<StateMachineState *> visited;
	int res = 0;
	nrAliasingLoads(sm->root, smsel, alias, opt, &res, visited, oracle);
	return res;
}

		   
static bool definitelyNoSatisfyingStores(StateMachineState *sm,
					 StateMachineSideEffectLoad *smsel,
					 const Oracle::RegisterAliasingConfiguration &alias,
					 const AllowableOptimisations &opt,
					 bool haveAliasingStore,
					 OracleInterface *oracle);
static bool
definitelyNoSatisfyingStores(StateMachineEdge *sme,
			     StateMachineSideEffectLoad *smsel,
			     const Oracle::RegisterAliasingConfiguration &alias,
			     const AllowableOptimisations &opt,
			     bool haveAliasingStore,
			     OracleInterface *oracle)
{
	for (unsigned x = 0; x < sme->sideEffects.size(); x++) {
		StateMachineSideEffect *smse = sme->sideEffects[x];
		if (smse == smsel) {
			if (haveAliasingStore) {
				return false;
			} else {
				/* The load can't appear twice in one
				   path, and we've not seen a
				   satisfying store yet, so we're
				   fine. */
				return true;
			}
		}
		if (haveAliasingStore)
			continue;
		StateMachineSideEffectStore *smses =
			dynamic_cast<StateMachineSideEffectStore *>(smse);
		if (smses &&
		    alias.ptrsMightAlias(smsel->addr, smses->addr, opt.freeVariablesMightAccessStack) &&
		    oracle->memoryAccessesMightAlias(smsel, smses) &&
		    !definitelyNotEqual( smsel->addr,
					 smses->addr,
					 opt)) {
			/* This store might alias with the load.  If
			   we encounter the load after this, then it
			   might be satisfied. */
			haveAliasingStore = true;
		}
	}
	return definitelyNoSatisfyingStores(sme->target,
					    smsel,
					    alias,
					    opt,
					    haveAliasingStore,
					    oracle);
}
static bool
definitelyNoSatisfyingStores(StateMachineState *sm,
			     StateMachineSideEffectLoad *smsel,
			     const Oracle::RegisterAliasingConfiguration &alias,
			     const AllowableOptimisations &opt,
			     bool haveAliasingStore,
			     OracleInterface *oracle)
{
	if (sm->target0() && !definitelyNoSatisfyingStores(sm->target0(),
							   smsel,
							   alias,
							   opt,
							   haveAliasingStore,
							   oracle))
		return false;
	if (sm->target1() && !definitelyNoSatisfyingStores(sm->target1(),
							   smsel,
							   alias,
							   opt,
							   haveAliasingStore,
							   oracle))
		return false;
	return true;
}
static bool definitelyNoSatisfyingStores(StateMachine *sm,
					 StateMachineSideEffectLoad *smsel,
					 const Oracle::RegisterAliasingConfiguration &alias,
					 const AllowableOptimisations &opt,
					 bool haveAliasingStore,
					 OracleInterface *oracle)
{
	return definitelyNoSatisfyingStores(sm->root, smsel, alias, opt, haveAliasingStore, oracle);
}

class BuildFreeVariableMapTransformer : public StateMachineTransformer {
public:
	std::set<threadAndRegister, threadAndRegister::fullCompare> accessedRegisters;
	std::set<threadAndRegister, threadAndRegister::fullCompare> puttedRegisters;
	FreeVariableMap &freeVariables;

	std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> map;

	StateMachineSideEffectCopy *transformOneSideEffect(StateMachineSideEffectCopy *c, bool *done_something)
	{
		puttedRegisters.insert(c->target);
		return StateMachineTransformer::transformOneSideEffect(c, done_something);
	}
	StateMachineSideEffectLoad *transformOneSideEffect(StateMachineSideEffectLoad *l, bool *done_something)
	{
		puttedRegisters.insert(l->target);
		return StateMachineTransformer::transformOneSideEffect(l, done_something);
	}
	StateMachineSideEffectPhi *transformOneSideEffect(StateMachineSideEffectPhi *p, bool *done_something)
	{
		/* Suppress free variable transformation for anything
		   involved in a Phi node, because it gets far too
		   confusing. */
		puttedRegisters.insert(p->reg);
		for (auto it = p->generations.begin();
		     it != p->generations.end();
		     it++)
			puttedRegisters.insert(p->reg.setGen(*it));
		return StateMachineTransformer::transformOneSideEffect(p, done_something);
	}
	IRExpr *transformIex(IRExprGet *what) {
		accessedRegisters.insert(what->reg);
		return StateMachineTransformer::transformIex(what);
	}
	BuildFreeVariableMapTransformer(FreeVariableMap &_freeVariables)
		: freeVariables(_freeVariables)
	{}
	/* It's not really a good idea to introduce more free
	   variables on behalf of an expression which is only used in
	   the free variable map. */
	void transformFreeVariables(FreeVariableMap *fvm, bool *done_something)
	{}
	void finalise()
	{
		for (auto it = accessedRegisters.begin();
		     it != accessedRegisters.end();
		     it++)
			if (!puttedRegisters.count(*it))
				map[*it] = IRExpr_FreeVariable();
	}
};

class IntroduceFreeVariablesRegisterTransformer : public StateMachineTransformer {
public:
	std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> &map;
	IntroduceFreeVariablesRegisterTransformer(
		std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> &_map)
		: map(_map)
	{}
	IRExpr *transformIex(IRExprGet *what) {
		if (map.count(what->reg)) {
			IRExprFreeVariable *res = (IRExprFreeVariable *)map[what->reg];
			assert(res->tag == Iex_FreeVariable);
			fvDelta.push_back(std::pair<FreeVariableKey, IRExpr *>(res->key, currentIRExpr()));
			return res;
		} else {
			return NULL;
		}
	}
};

static StateMachine *
introduceFreeVariablesForRegisters(StateMachine *sm, bool *done_something)
{
	__set_profiling(introduceFreeVariablesForRegisters);
	BuildFreeVariableMapTransformer t(sm->freeVariables);
	t.StateMachineTransformer::transform(sm);
	t.finalise();
	IntroduceFreeVariablesRegisterTransformer s(t.map);
	return s.transform(sm, done_something);
}

static StateMachineState *introduceFreeVariables(StateMachineState *sm,
						 StateMachine *root_sm,
						 const Oracle::RegisterAliasingConfiguration &alias,
						 const AllowableOptimisations &opt,
						 OracleInterface *oracle,
						 bool *done_something,
						 std::vector<std::pair<FreeVariableKey, IRExpr *> > &fresh);
static StateMachineEdge *
introduceFreeVariables(StateMachineEdge *sme,
		       StateMachine *root_sm,
		       const Oracle::RegisterAliasingConfiguration &alias,
		       const AllowableOptimisations &opt,
		       OracleInterface *oracle,
		       bool *done_something,
		       std::vector<std::pair<FreeVariableKey, IRExpr *> > &fresh)
{
	StateMachineEdge *out = new StateMachineEdge(NULL);
	bool doit = false;
	/* A load results in a free variable if it's local and no
	   stores could potentially alias with it and no other loads
	   could alias with it. */
	for (unsigned idx = 0; idx < sme->sideEffects.size(); idx++) {
		StateMachineSideEffect *smse = sme->sideEffects[idx];
		StateMachineSideEffectLoad *smsel = dynamic_cast<StateMachineSideEffectLoad *>(smse);
		if (!smsel ||
		    !oracle->loadIsThreadLocal(smsel) ||
		    !definitelyNoSatisfyingStores(root_sm, smsel, alias, opt, false, oracle) ||
		    nrAliasingLoads(root_sm, smsel, alias, opt, oracle) != 1) {
			out->sideEffects.push_back(smse);
			continue;
		}
		/* This is a local load from a location which is never
		 * stored.  Remove it. */
		StateMachineSideEffectCopy *smsec = new StateMachineSideEffectCopy(smsel->target, IRExpr_FreeVariable());
		out->sideEffects.push_back(smsec);
		fresh.push_back(std::pair<FreeVariableKey, IRExpr *>
				(((IRExprFreeVariable *)smsec->value)->key,
				 IRExpr_Load(Ity_I64, smsel->addr, smsel->rip)));
		doit = true;
	}
	out->target = introduceFreeVariables(sme->target, root_sm, alias, opt, oracle, &doit, fresh);

	if (doit) {
		*done_something = true;
		return out;
	} else {
		return sme;
	}
}
static StateMachineState *
introduceFreeVariables(StateMachineState *sm,
		       StateMachine *root_sm,
		       const Oracle::RegisterAliasingConfiguration &alias,
		       const AllowableOptimisations &opt,
		       OracleInterface *oracle,
		       bool *done_something,
		       std::vector<std::pair<FreeVariableKey, IRExpr *> > &fresh)
{
	bool doit = false;
	if (dynamic_cast<StateMachineTerminal *>(sm))
		return sm;
	if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm)) {
		StateMachineEdge *e = introduceFreeVariables(smp->target,
							     root_sm,
							     alias,
							     opt,
							     oracle,
							     &doit,
							     fresh);
		if (doit) {
			*done_something = true;
			return new StateMachineProxy(smp->origin, e);
		} else {
			return sm;
		}
	}
	StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(sm);
	assert(smb);
	StateMachineEdge *t = introduceFreeVariables(smb->trueTarget,
						     root_sm,
						     alias,
						     opt,
						     oracle,
						     &doit,
						     fresh);
	StateMachineEdge *f = introduceFreeVariables(smb->falseTarget,
						     root_sm,
						     alias,
						     opt,
						     oracle,
						     &doit,
						     fresh);
	if (doit) {
		*done_something = true;
		return new StateMachineBifurcate(smb->origin,
						 smb->condition,
						 t,
						 f);
	} else {
		return sm;
	}
}
static StateMachine *
introduceFreeVariables(StateMachine *sm,
		       const Oracle::RegisterAliasingConfiguration &alias,
		       const AllowableOptimisations &opt,
		       OracleInterface *oracle,
		       bool *done_something)
{
	bool b = false;
	std::vector<std::pair<FreeVariableKey, IRExpr *> > fresh;
	StateMachineState *new_root = introduceFreeVariables(sm->root, sm, alias, opt, oracle, &b, fresh);
	if (b) {
		*done_something = true;
		StateMachine *new_sm =  new StateMachine(sm, fresh);
		new_sm->root = new_root;
		return new_sm;
	} else {
		return sm;
	}
}

class countFreeVariablesVisitor : public StateMachineTransformer {
	IRExpr *transformIex(IRExprFreeVariable *e) {
		counts[e->key]++;
		return StateMachineTransformer::transformIex(e);
	}
public:
	std::map<FreeVariableKey, int> counts;
};
class simplifyFreeVariablesTransformer : public StateMachineTransformer {
public:
	std::map<FreeVariableKey, int> &counts;
	FreeVariableMap &freeVariables;
	IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
		switch (e->tag) {
		case Iex_Const:
		case Iex_Get:
		case Iex_GetI:
		case Iex_Load:
		case Iex_Mux0X:
		case Iex_CCall:
		case Iex_FreeVariable:
		case Iex_ClientCall:
		case Iex_ClientCallFailed:
		case Iex_HappensBefore:
			break;
		case Iex_Qop: {
			IRExprQop *exp = (IRExprQop *)e;
			if (exp->arg1->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg1)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg1)->key,
						IRExpr_Qop(
							exp->op,
							freeVariables.get(((IRExprFreeVariable *)exp->arg1)->key),
							exp->arg2,
							exp->arg3,
							exp->arg4)));
				return exp->arg1;
			}
			if (exp->arg2->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg2)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg2)->key,
						IRExpr_Qop(
							exp->op,
							exp->arg1,
							freeVariables.get(((IRExprFreeVariable *)exp->arg2)->key),
							exp->arg3,
							exp->arg4)));
				return exp->arg2;
			}
			if (exp->arg3->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg3)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg3)->key,
						IRExpr_Qop(
							exp->op,
							exp->arg1,
							exp->arg2,
							freeVariables.get(((IRExprFreeVariable *)exp->arg3)->key),
							exp->arg4)));
				return exp->arg3;
			}
			if (exp->arg4->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg4)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg4)->key,
						IRExpr_Qop(
							exp->op,
							exp->arg1,
							exp->arg2,
							exp->arg3,
							freeVariables.get(((IRExprFreeVariable *)exp->arg4)->key))));
				return exp->arg4;
			}
			break;
		}
		case Iex_Triop: {
			IRExprTriop *exp = (IRExprTriop *)e;
			if (exp->arg1->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg1)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg1)->key,
						IRExpr_Triop(
							exp->op,
							freeVariables.get(((IRExprFreeVariable *)exp->arg1)->key),
							exp->arg2,
							exp->arg3)));
				return exp->arg1;
			}
			if (exp->arg2->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg2)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg2)->key,
						IRExpr_Triop(
							exp->op,
							exp->arg1,
							freeVariables.get(((IRExprFreeVariable *)exp->arg2)->key),
							exp->arg3)));
				return exp->arg2;
			}
			if (exp->arg3->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg3)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg3)->key,
						IRExpr_Triop(
							exp->op,
							exp->arg1,
							exp->arg2,
							freeVariables.get(((IRExprFreeVariable *)exp->arg3)->key))));
				return exp->arg3;
			}
			break;
		}
		case Iex_Binop: {
			IRExprBinop *exp = (IRExprBinop *)e;
			if (exp->arg1->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg1)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg1)->key,
						IRExpr_Binop(
							exp->op,
							freeVariables.get(((IRExprFreeVariable *)exp->arg1)->key),
							exp->arg2)));
				return exp->arg1;
			}
			if (exp->arg2->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg2)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg2)->key,
						IRExpr_Binop(
							exp->op,
							exp->arg1,
							freeVariables.get(((IRExprFreeVariable *)exp->arg2)->key))));
				return exp->arg2;
			}
			break;
		}
		case Iex_Unop: {
			IRExprUnop *exp = (IRExprUnop *)e;
			if (exp->arg->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg)->key,
						IRExpr_Unop(
							exp->op,
							freeVariables.get(((IRExprFreeVariable *)exp->arg)->key))));
				return exp->arg;
			}
			break;
		}
		case Iex_Associative: {
			IRExprAssociative *exp = (IRExprAssociative *)e;
			for (int x = 0; x < exp->nr_arguments; x++) {
				IRExpr *_a = exp->contents[x];
				if (_a->tag != Iex_FreeVariable)
					continue;
				IRExprFreeVariable *a = (IRExprFreeVariable *)_a;
				if (counts[a->key] != 1)
					continue;
				*done_something = true;
				IRExprAssociative *b = (IRExprAssociative *)IRExpr_Associative(exp);
				assert(freeVariables.get(a->key));
				b->contents[x] = freeVariables.get(a->key);
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						a->key, b));
				return a;
			}
			break;
		}
		}
		return StateMachineTransformer::transformIRExpr(e, done_something);
	}
	simplifyFreeVariablesTransformer(std::map<FreeVariableKey, int> &_counts,
					 FreeVariableMap &fv)
		: counts(_counts), freeVariables(fv)
	{}
};

static void
findAllCopies(StateMachine *sm, std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> &out)
{
	class _ : public StateMachineTransformer {
		std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> &out;
		StateMachineSideEffectCopy *transformOneSideEffect(StateMachineSideEffectCopy *c, bool *)
		{
			out[c->target] = c->value;
			return c;
		}
		IRExpr *transformIRExpr(IRExpr *e, bool *)
		{
			return e;
		}
	public:
		_(std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> &_out)
			: out(_out)
		{}
	} t(out);
	t.transform(sm);
}

static void
applyCopiesToFreeVariables(FreeVariableMap &fv,
			   std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> &m,
			   bool *done_something)
{
	class _ : public IRExprTransformer {
		std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> &m;
		FreeVariableMap &fvm;
		IRExpr *transformIex(IRExprGet *g) {
			auto it = m.find(g->reg);
			if (it != m.end())
				return it->second;
			return IRExprTransformer::transformIex(g);
		}
		IRExpr *transformIex(IRExprFreeVariable *e) {
			return fvm.get(e->key);
		}
	public:
		_(std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> &_m,
		  FreeVariableMap &_fvm)
			: m(_m), fvm(_fvm)
		{}
	} t(m, fv);
	fv.applyTransformation(t, done_something);
}

static void
findUsedFreeVars(StateMachine *sm, std::set<FreeVariableKey> &out)
{
	class _ : public StateMachineTransformer {
		std::set<FreeVariableKey> &out;
		IRExpr *transformIex(IRExprFreeVariable *e) {
			out.insert(e->key);
			return NULL;
		}
	public:
		_(std::set<FreeVariableKey> &_out)
			: out(_out)
		{}
	} t(out);
	t.transform(sm);
}

static StateMachine *
optimiseFreeVariables(StateMachine *sm, bool *done_something)
{
	countFreeVariablesVisitor cfvv;
	bool ign;
	cfvv.transform(sm, &ign);
	simplifyFreeVariablesTransformer sfvt(cfvv.counts, sm->freeVariables);
	sm = sfvt.transform(sm, done_something);
	std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> copies;
	findAllCopies(sm, copies);
	applyCopiesToFreeVariables(sm->freeVariables, copies, done_something);
	std::set<FreeVariableKey> usedFreeVars;
	findUsedFreeVars(sm, usedFreeVars);
	for (auto it = sm->freeVariables.content->begin();
	     it != sm->freeVariables.content->end();
		) {
		if (!usedFreeVars.count(it.key())) {
			it = sm->freeVariables.content->erase(it);
			*done_something = true;
		} else {
			it++;
		}
	}
	return sm;
}

/* End of namespace */
}

StateMachine *
introduceFreeVariablesForRegisters(StateMachine *sm, bool *done_something)
{
	return _freevars::introduceFreeVariablesForRegisters(sm, done_something);
}

StateMachine *
introduceFreeVariables(StateMachine *sm,
		       const Oracle::RegisterAliasingConfiguration &alias,
		       const AllowableOptimisations &opt,
		       OracleInterface *oracle,
		       bool *done_something)
{
	return _freevars::introduceFreeVariables(sm, alias, opt, oracle, done_something);
}

StateMachine *
optimiseFreeVariables(StateMachine *sm, bool *done_something)
{
	return _freevars::optimiseFreeVariables(sm, done_something);
}

void
FreeVariableMap::optimise(const AllowableOptimisations &opt, bool *done_something)
{
	for (auto it = content->begin(); it != content->end(); it++)
		it.set_value(optimiseIRExprFP(it.value(), opt, done_something));
}

void
FreeVariableMap::print(FILE *f) const
{
	for (map_t::iterator it = content->begin();
	     it != content->end();
	     it++) {
		fprintf(f, "free%d -> ", it.key().val);
		ppIRExpr(it.value(), f);
		fprintf(f, "\n");
	}
}

bool
FreeVariableMap::parse(const char *str, const char **succ)
{
	content = new map_t();
	while (1) {
		FreeVariableKey k;
		IRExpr *val;
		if (!parseThisString("free", str, &str) ||
		    !parseDecimalInt(&k.val, str, &str) ||
		    !parseThisString(" -> ", str, &str) ||
		    !parseIRExpr(&val, str, &str) ||
		    !parseThisChar('\n', str, &str))
			break;
		content->set(FreeVariableKey(k), val);
	}
	*succ = str;
	return true;
}

void
FreeVariableMap::applyTransformation(IRExprTransformer &x, bool *done_something)
{
	for (map_t::iterator it = content->begin();
	     it != content->end();
	     it++)
		it.set_value(x.transformIRExpr(it.value(), done_something));
}
