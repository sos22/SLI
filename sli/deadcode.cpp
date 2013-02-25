/* Simple dead code elimination: find binders and registers which are
   never accessed after being set and eliminate them. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"
#include "visitor.hpp"
#include "stacked_cdf.hpp"

namespace _deadCode {

#ifdef NDEBUG
#define debug_deadcode 0
#else
static bool debug_deadcode = false;
#endif

class LivenessEntry {
	void killRegister(threadAndRegister r)
	{
		content.erase(r);
	}
	void useRegister(const threadAndRegister &r, IRType ty) {
		auto it_di = content.insert(r, ty);
		if (!it_di.second && it_di.first->second < ty) {
			it_di.first->second = ty;
		}
	}
	sane_map<threadAndRegister, IRType> content;
	bool anyLoads;
public:
	LivenessEntry()
		: anyLoads(false)
	{}
	void useExpression(const bbdd *e)
	{
		struct {
			static visit_result f(LivenessEntry *out, const IRExprGet *g) {
				out->useRegister(g->reg, g->type());
				return visit_continue;
			}
		} foo;
		static bdd_visitor<LivenessEntry> visitor;
		visitor.irexpr.Get = foo.f;
		visit_const_bdd(this, &visitor, e);
	}
	void useExpression(const smrbdd *e)
	{
		struct {
			static visit_result f(LivenessEntry *out, const IRExprGet *g) {
				out->useRegister(g->reg, g->type());
				return visit_continue;
			}
		} foo;
		static bdd_visitor<LivenessEntry> visitor;
		visitor.irexpr.Get = foo.f;
		visit_const_bdd(this, &visitor, e);
	}
	void useExpression(const exprbdd *e)
	{
		struct {
			static visit_result f(LivenessEntry *out, const IRExprGet *g) {
				out->useRegister(g->reg, g->type());
				return visit_continue;
			}
		} foo;
		static bdd_visitor<LivenessEntry> visitor;
		visitor.irexpr.Get = foo.f;
		visit_bdd(this, &visitor, visit_irexpr<LivenessEntry>, e);
	}
	void useExpression(const IRExpr *e)
	{
		struct {
			static visit_result f(LivenessEntry *out, const IRExprGet *g) {
				out->useRegister(g->reg, g->type());
				return visit_continue;
			}
		} foo;
		static irexpr_visitor<LivenessEntry> visitor;
		visitor.Get = foo.f;
		visit_irexpr(this, &visitor, e);
	}

	void useSideEffect(StateMachineSideEffect *smse)
	{
		threadAndRegister def(threadAndRegister::invalid());
		if (smse->definesRegister(def))
			killRegister(def);
		switch (smse->type) {
		case StateMachineSideEffect::Load:
			useExpression( ((StateMachineSideEffectLoad *)smse)->addr);
			anyLoads = true;
			break;
		case StateMachineSideEffect::Store:
			useExpression( ((StateMachineSideEffectStore *)smse)->addr);
			useExpression( ((StateMachineSideEffectStore *)smse)->data);
			break;
		case StateMachineSideEffect::Copy:
			useExpression( ((StateMachineSideEffectCopy *)smse)->value);
			break;
		case StateMachineSideEffect::Unreached:
		case StateMachineSideEffect::StartAtomic:
		case StateMachineSideEffect::EndAtomic:
#if TRACK_FRAMES
		case StateMachineSideEffect::StackLayout:
#endif
		case StateMachineSideEffect::ImportRegister:
			break;
		case StateMachineSideEffect::AssertFalse:
			useExpression( ((StateMachineSideEffectAssertFalse *)smse)->value );
			break;
#if TRACK_FRAMES
		case StateMachineSideEffect::StartFunction:
			useExpression( ((StateMachineSideEffectStartFunction *)smse)->rsp );
			break;
		case StateMachineSideEffect::EndFunction:
			useExpression( ((StateMachineSideEffectEndFunction *)smse)->rsp );
			break;
#endif
		case StateMachineSideEffect::Phi: {
			StateMachineSideEffectPhi *smsep =
				(StateMachineSideEffectPhi *)smse;
			for (auto it = smsep->generations.begin(); it != smsep->generations.end(); it++) {
				useExpression(it->val);
				useRegister(it->reg, smsep->ty);
			}
			break;
		}
		}
	}

	bool merge(const LivenessEntry &other) {
		bool res = false;
		for (auto it = other.content.begin(); it != other.content.end(); it++) {
			auto it2 = content.find(it->first);
			if (it2 == content.end()) {
				content.insert(it->first, it->second);
				res = true;
			} else if (it2->second < it->second) {
				it2->second = it->second;
				res = true;
			}
		}
		if (other.anyLoads && !anyLoads) {
			res = true;
			anyLoads = true;
		}
		return res;
	}

	bool registerLive(threadAndRegister reg, IRType *maxType) const {
		auto it = content.find(reg);
		if (it == content.end()) {
			return false;
		}
		*maxType = it->second;
		return true;
	}
	bool mightLoadAnything() const { return anyLoads; }

	void print() const {
		printf("content = {");
		for (auto it = content.begin(); it != content.end(); it++) {
			if (it != content.begin()) {
				printf(", ");
			}
			printf("%s:%s", it->first.name(), nameIRType(it->second));
		}
		printf("}, anyLoads = %s", anyLoads ? "true" : "false");
		
	}
};


static StateMachine *
ssaDeadCode(SMScopes *scopes, StateMachine *sm, bool *done_something)
{
	std::set<threadAndRegister> refed_regs;
	std::set<StateMachineState *> states;
	enumStates(sm, &states);
	struct {
		static visit_result Get(std::set<threadAndRegister> *refed_regs,
					const IRExprGet *ieg) {
			refed_regs->insert(ieg->reg);
			return visit_continue;
		}
		static visit_result Phi(std::set<threadAndRegister> *refed_regs,
					const StateMachineSideEffectPhi *phi) {
			for (auto it = phi->generations.begin();
			     it != phi->generations.end();
			     it++)
				refed_regs->insert(it->reg);
			return visit_continue;
		}
	} foo;
	static state_machine_visitor<std::set<threadAndRegister> > visitor;
	visitor.bdd.irexpr.Get = foo.Get;
	visitor.Phi = foo.Phi;
	for (auto it = states.begin(); !TIMEOUT && it != states.end(); it++)
		visit_one_state(&refed_regs, &visitor, *it);
	std::set<StateMachineSideEffecting *> ses;
	enumStates(sm, &ses);
	for (auto it = ses.begin(); !TIMEOUT && it != ses.end(); it++) {
		StateMachineSideEffect *effect = (*it)->sideEffect;
		if (!effect)
			continue;
		switch (effect->type) {
		case StateMachineSideEffect::Copy: {
			StateMachineSideEffectCopy *smsec =
				(StateMachineSideEffectCopy *)effect;
			if (!refed_regs.count(smsec->target)) {
				*done_something = true;
				(*it)->sideEffect = NULL;
			}
			break;
		}
		case StateMachineSideEffect::Load: {
			StateMachineSideEffectLoad *smsel =
				(StateMachineSideEffectLoad *)effect;
			if (!refed_regs.count(smsel->target)) {
				*done_something = true;
				if (smsel->tag.neverBadPtr()) {
					(*it)->sideEffect = NULL;
				} else {
					(*it)->sideEffect =
						new StateMachineSideEffectAssertFalse(
							exprbdd::to_bbdd(
								&scopes->bools,
								exprbdd::unop(
									&scopes->exprs,
									&scopes->bools,
									Iop_BadPtr,
									smsel->addr)),
							true);
				}
			}
			break;
		}
		case StateMachineSideEffect::Phi: {
			StateMachineSideEffectPhi *p =
				(StateMachineSideEffectPhi *)effect;
			if (!refed_regs.count(p->reg)) {
				*done_something = true;
				(*it)->sideEffect = NULL;
			}
			break;
		}
		case StateMachineSideEffect::ImportRegister: {
			auto *p = (StateMachineSideEffectImportRegister *)effect;
			if (!refed_regs.count(p->reg)) {
				*done_something = true;
				(*it)->sideEffect = NULL;
			}
			break;
		}
		default:
			break;
		}
	}
	return sm;
}

static void
stripNoops(StateMachineState *&what, bool *done_something)
{
	while (what->type == StateMachineState::SideEffecting &&
	       ((StateMachineSideEffecting *)what)->sideEffect == NULL) {
		*done_something = true;
		what = ((StateMachineSideEffecting *)what)->target;
	}
}

static StateMachine *
deadCodeElimination(SMScopes *scopes, StateMachine *sm, bool *done_something,
		    bool is_ssa, const AllowableOptimisations &opt)
{
	if (is_ssa) {
		return ssaDeadCode(scopes, sm, done_something);
	}

	std::map<const StateMachineState *, int> stateLabels;

	if (debug_deadcode) {
		printf("Input to deadCodeElimination:\n");
		printStateMachine(sm, stdout, stateLabels);
	}

	/* We want a consistent backwards advance here: arrange to
	   visit nodes in an order which means that the liveness set
	   of its successors have always been computed by the time we
	   get there. */
	std::map<StateMachineState *, std::set<StateMachineState *> > predecessors;
	std::map<StateMachineState *, int> nrPendingSuccessors;
	std::set<StateMachineState *> states;
	enumStates(sm, &states);
	predecessors[sm->root].clear();
	std::vector<StateMachineState *> pending;
	for (auto it = states.begin(); it != states.end(); it++) {
		StateMachineState *s = *it;
		std::vector<StateMachineState *> targ;
		s->targets(targ);
		nrPendingSuccessors[s] = targ.size();
		if (targ.size() == 0) {
			pending.push_back(s);
		}
		for (auto it2 = targ.begin(); it2 != targ.end(); it2++) {
			predecessors[*it2].insert(s);
		}
	}

	/* Map from states to the liveness state at that state */
	std::map<StateMachineState *, LivenessEntry> livenessMap;

	bool p = false;

	while (!TIMEOUT && !pending.empty()) {
		StateMachineState *s = pending.back();
		pending.pop_back();

		if (debug_deadcode) {
			printf("Consider state l%d\n", stateLabels[s]);
		}

		assert(nrPendingSuccessors.count(s));
		assert(nrPendingSuccessors[s] == 0);

		assert(!livenessMap.count(s));
		LivenessEntry &le(livenessMap[s]);

		switch (s->type) {
		case StateMachineState::Terminal:
			le.useExpression( ((StateMachineTerminal *)s)->res );
			if (debug_deadcode) {
				printf("Terminal; liveness = ");
				le.print();
				printf("\n");
			}
			break;
		case StateMachineState::Bifurcate: {
			auto smb = (StateMachineBifurcate *)s;
			stripNoops(smb->trueTarget, &p);
			stripNoops(smb->falseTarget, &p);

			auto it_t = livenessMap.find(smb->trueTarget);
			assert(it_t != livenessMap.end());
			le = it_t->second;

			auto it_f = livenessMap.find(smb->falseTarget);
			assert(it_f != livenessMap.end());
			le.merge(it_f->second);

			if (debug_deadcode) {
				printf("Bifurcate; exit liveness = ");
				le.print();
			}
			le.useExpression(smb->condition);
			if (debug_deadcode) {
				printf("; entry liveness = ");
				le.print();
				printf("\n");
			}
			break;
		}
		case StateMachineState::SideEffecting: {
			auto sme = (StateMachineSideEffecting *)s;
			stripNoops(sme->target, &p);

			auto it_t = livenessMap.find(sme->target);
			assert(it_t != livenessMap.end());
			le = it_t->second;

			if (debug_deadcode) {
				printf("SideEffecting; exit liveness = ");
				le.print();
				printf("\n");
			}

			if (!sme->sideEffect) {
				if (debug_deadcode) {
					printf("No-op\n");
				}
				break;
			}

			StateMachineSideEffect *newEffect = sme->sideEffect;
			switch (sme->sideEffect->type) {
			case StateMachineSideEffect::Load: {
				StateMachineSideEffectLoad *smsel =
					(StateMachineSideEffectLoad *)newEffect;
				IRType maxType;
				if (!le.registerLive(smsel->target, &maxType)) {
					if (smsel->tag.neverBadPtr()) {
						newEffect = NULL;
					} else {
						newEffect = new StateMachineSideEffectAssertFalse(
							exprbdd::to_bbdd(
								&scopes->bools,
								exprbdd::unop(
									&scopes->exprs,
									&scopes->bools,
									Iop_BadPtr,
									smsel->addr)),
							true);
					}
				} else if (maxType < smsel->type) {
					newEffect = new StateMachineSideEffectLoad(
						smsel,
						maxType);
				}
				break;
			}
			case StateMachineSideEffect::Store: {
				if (opt.ignoreSideEffects() &&
				    !le.mightLoadAnything()) {
					newEffect = NULL;
				}
				break;
			}

			case StateMachineSideEffect::Unreached:
			case StateMachineSideEffect::StartAtomic:
			case StateMachineSideEffect::EndAtomic:
#if TRACK_FRAMES
			case StateMachineSideEffect::StartFunction:
			case StateMachineSideEffect::EndFunction:
			case StateMachineSideEffect::StackLayout:
#endif
			case StateMachineSideEffect::AssertFalse: {
				break;
			}
			case StateMachineSideEffect::Copy: {
				StateMachineSideEffectCopy *smsec =
					(StateMachineSideEffectCopy *)newEffect;
				IRType maxType;
				if (smsec->value->isLeaf() &&
				    smsec->value->leaf()->tag == Iex_Get &&
				    ((IRExprGet *)smsec->value->leaf())->reg == smsec->target) {
					/* Copying a register or
					   temporary back to itself is
					   always dead, regardless of
					   what liveness analysis
					   proper might say. */
					newEffect = NULL;
				} else if (!le.registerLive(smsec->target, &maxType)) {
					newEffect = NULL;
				} else if (maxType < smsec->value->type()) {
					newEffect = new StateMachineSideEffectCopy(
						smsec,
						exprbdd::unop(
							&scopes->exprs,
							&scopes->bools,
							coerceTypesOp(
								smsec->value->type(),
								maxType),
							smsec->value));
				}
				break;
			}
			case StateMachineSideEffect::Phi: {
				StateMachineSideEffectPhi *p =
					(StateMachineSideEffectPhi *)newEffect;
				IRType maxType;
				if (!le.registerLive(p->reg, &maxType)) {
					newEffect = NULL;
				} else if (maxType < p->ty) {
					std::vector<StateMachineSideEffectPhi::input> gen(p->generations);
					IROp c = coerceTypesOp(p->ty, maxType);
					for (auto it = gen.begin();
					     it != gen.end();
					     it++) {
						it->val = exprbdd::unop(
							&scopes->exprs,
							&scopes->bools,
							c,
							it->val);
					}
					newEffect = new StateMachineSideEffectPhi(
						p->reg,
						maxType,
						gen);
				}
				break;
			}
			case StateMachineSideEffect::ImportRegister: {
				auto *p = (StateMachineSideEffectImportRegister *)newEffect;
				IRType maxT;
				if (!le.registerLive(p->reg, &maxT)) {
					newEffect = NULL;
				}
				break;
			}
			}

			if (newEffect != sme->sideEffect) {
				if (debug_deadcode) {
					printf("Rewrite side effect to ");
					if (newEffect) {
						newEffect->prettyPrint(stdout);
					} else {
						printf("<null>");
					}
					printf("\n");
				}
				sme->sideEffect = newEffect;
			}

			if (sme->sideEffect) {
				le.useSideEffect(sme->sideEffect);
				if (debug_deadcode) {
					printf("Side effect live; entry liveness ");
					le.print();
					printf("\n");
				}
			}
			break;
		}
		}

		assert(predecessors.count(s));
		const std::set<StateMachineState *> &pred(predecessors[s]);
		for (auto it = pred.begin(); it != pred.end(); it++) {
			assert(nrPendingSuccessors[*it] > 0);
			if (--nrPendingSuccessors[*it] == 0) {
				pending.push_back(*it);
			}
		}
	}

	if (p) {
		if (debug_deadcode) {
			printf("Final result:\n");
			printStateMachine(sm, stdout);
		}
		*done_something = true;
	} else {
		if (debug_deadcode) {
			printf("Achieved nothing\n");
		}
	}

	return sm;
}

/* end of namespace */
}

StateMachine *
deadCodeElimination(SMScopes *scopes, StateMachine *sm, bool *done_something, bool is_ssa,
		    const AllowableOptimisations &opt)
{
	stackedCdf::startDeadcode();
	auto res = _deadCode::deadCodeElimination(scopes, sm, done_something, is_ssa, opt);
	stackedCdf::stopDeadcode();
	return res;
}

