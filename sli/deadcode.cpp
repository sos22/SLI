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

template <typename content, int nr_inline> class small_set {
	unsigned long inline_mask;
	content inlined[nr_inline];
	std::set<content> *out_of_line;
public:
	small_set(const small_set &o)
		: inline_mask(o.inline_mask),
		  inlined(o.inlined),
		  out_of_line(o.out_of_line ? new std::set<content>(*o.out_of_line) : NULL)
	{
	}
	small_set()
		: inline_mask(0), out_of_line(NULL)
	{}
	void operator=(const small_set &o) {
		if (out_of_line) {
			if (o.out_of_line) {
				*out_of_line = *o.out_of_line;
			} else {
				delete out_of_line;
				out_of_line = NULL;
			}
		} else {
			if (o.out_of_line)
				out_of_line = new std::set<content>(*o.out_of_line);
		}
		inline_mask = o.inline_mask;
		std::copy(o.inlined, o.inlined + nr_inline, inlined);
	}
	~small_set()
	{
		if (out_of_line)
			delete out_of_line;
	}
	class iterator {
		small_set *owner;
		int inline_idx;
		typename std::set<content>::iterator it;
		bool _started;
	public:
		iterator(small_set *_owner)
			: owner(_owner),
			  inline_idx(-1)
		{
			advance();
			_started = false;
		}
		void advance() {
			_started = true;
			if (inline_idx == nr_inline) {
				it++;
				if (it == owner->out_of_line->end())
					inline_idx = nr_inline + 1;
				return;
			}
			do {
				inline_idx++;
			} while (inline_idx < nr_inline && !(owner->inline_mask & (1ul << inline_idx)));
			if (inline_idx == nr_inline) {
				if (owner->out_of_line) {
					it = owner->out_of_line->begin();
					if (it == owner->out_of_line->end())
						inline_idx = nr_inline + 1;
				} else {
					inline_idx = nr_inline + 1;
				}
			}
		}
		bool finished() const {
			return inline_idx == nr_inline + 1;
		}
		bool started() const {
			return _started;
		}
		const content &operator*() const {
			assert(inline_idx <= nr_inline);
			if (inline_idx == nr_inline)
				return *it;
			else
				return owner->inlined[inline_idx];
		}
		const content *operator->() const {
			assert(inline_idx <= nr_inline);
			if (inline_idx == nr_inline)
				return &*it;
			else
				return &owner->inlined[inline_idx];
		}
		void erase() {
			if (inline_idx == nr_inline) {
				owner->out_of_line->erase(it++);
			} else {
				owner->inline_mask &= (1ul << inline_idx);
				advance();
			}
		}
	};
	iterator begin() { return iterator(this); }
	class const_iterator {
		const small_set *owner;
		int inline_idx;
		typename std::set<content>::iterator it;
		bool _started;
	public:
		const_iterator(const small_set *_owner)
			: owner(_owner),
			  inline_idx(-1)
		{
			advance();
			_started = false;
		}
		void advance() {
			_started = true;
			if (inline_idx == nr_inline) {
				it++;
				if (it == owner->out_of_line->end())
					inline_idx = nr_inline + 1;
				return;
			}
			do {
				inline_idx++;
			} while (inline_idx < nr_inline && !(owner->inline_mask & (1ul << inline_idx)));
			if (inline_idx == nr_inline) {
				if (owner->out_of_line) {
					it = owner->out_of_line->begin();
					if (it == owner->out_of_line->end())
						inline_idx = nr_inline + 1;
				} else {
					inline_idx = nr_inline + 1;
				}
			}
		}
		bool finished() const {
			return inline_idx == nr_inline + 1;
		}
		bool started() const {
			return _started;
		}
		const content &operator*() const {
			assert(inline_idx <= nr_inline);
			if (inline_idx == nr_inline)
				return *it;
			else
				return owner->inlined[inline_idx];
		}
		const content *operator->() const {
			assert(inline_idx <= nr_inline);
			if (inline_idx == nr_inline)
				return &*it;
			else
				return &owner->inlined[inline_idx];
		}
	};
	const_iterator begin() const { return const_iterator(this); }
	bool insert(const content &k) {
		for (int i = 0; i < nr_inline; i++) {
			if (inline_mask & (1ul << i)) {
				if (inlined[i] == k)
					return false;
			}
		}
		if (out_of_line && out_of_line->count(k))
			return false;
		for (int i = 0; i < nr_inline; i++) {
			if (!(inline_mask & (1ul << i))) {
				inlined[i] = k;
				inline_mask |= 1ul << i;
				return true;
			}
		}
		if (!out_of_line)
			out_of_line = new std::set<content>();
		out_of_line->insert(k);
		return true;
	}
	void erase(const content &k) {
		for (int i = 0; i < nr_inline; i++) {
			if ( (inline_mask & (1ul << i)) &&
			     inlined[i] == k ) {
				inline_mask &= ~(1ul << i);
				return;
			}
		}
		if (out_of_line)
			out_of_line->erase(k);
	}
	bool contains(const content &k) const {
		for (int i = 0; i < nr_inline; i++) {
			if (inline_mask & (1ul << i)) {
				if (inlined[i] == k)
					return true;
			}
		}
		if (out_of_line)
			return out_of_line->count(k) != 0;
		return false;
	}
};

class LivenessEntry {
	void killRegister(threadAndRegister r)
	{
		liveDataOnly.erase(r);
		livePointer.erase(r);
	}
	/* We track two different kinds of liveness: live for data and
	 * live as a pointer.  The idea is that if something is never
	 * used as a pointer then we can kill off its aliasing
	 * information, even if it's still live as a data value. */
	/* A register is added to livePointer if it's used to compute
	 * a pointer.  It's added to liveDataOnly if it's used to
	 * compute something which isn't a pointer.  Anything where
	 * the value computed might be used as a pointer, but we're
	 * not sure, goes in livePointer. */
	small_set<threadAndRegister, 8> liveDataOnly;
	small_set<threadAndRegister, 8> livePointer;
	bool anyLoads;
public:
	LivenessEntry()
		: anyLoads(false)
	{}
	void useExpressionData(const bbdd *e)
	{
		struct {
			static visit_result f(LivenessEntry *out, const IRExprGet *g) {
				if (!out->livePointer.contains(g->reg))
					out->liveDataOnly.insert(g->reg);
				return visit_continue;
			}
		} foo;
		static bdd_visitor<LivenessEntry> visitor;
		visitor.irexpr.Get = foo.f;
		visit_const_bdd(this, &visitor, e);
	}
	void useExpressionData(const smrbdd *e)
	{
		struct {
			static visit_result f(LivenessEntry *out, const IRExprGet *g) {
				if (!out->livePointer.contains(g->reg))
					out->liveDataOnly.insert(g->reg);
				return visit_continue;
			}
		} foo;
		static bdd_visitor<LivenessEntry> visitor;
		visitor.irexpr.Get = foo.f;
		visit_const_bdd(this, &visitor, e);
	}
	void useExpressionData(const exprbdd *e)
	{
		struct {
			static visit_result f(LivenessEntry *out, const IRExprGet *g) {
				if (!out->livePointer.contains(g->reg))
					out->liveDataOnly.insert(g->reg);
				return visit_continue;
			}
		} foo;
		static bdd_visitor<LivenessEntry> visitor;
		visitor.irexpr.Get = foo.f;
		visit_bdd(this, &visitor, visit_irexpr<LivenessEntry>, e);
	}
	void useExpressionData(const IRExpr *e)
	{
		struct {
			static visit_result f(LivenessEntry *out, const IRExprGet *g) {
				if (!out->livePointer.contains(g->reg))
					out->liveDataOnly.insert(g->reg);
				return visit_continue;
			}
		} foo;
		static irexpr_visitor<LivenessEntry> visitor;
		visitor.Get = foo.f;
		visit_irexpr(this, &visitor, e);
	}
	void useExpressionPointer(IRExpr *e)
	{
		struct {
			static visit_result f(LivenessEntry *out, const IRExprGet *g) {
				out->livePointer.insert(g->reg);
				out->liveDataOnly.erase(g->reg);
				return visit_continue;
			}
		} foo;
		static irexpr_visitor<LivenessEntry> visitor;
		visitor.Get = foo.f;
		visit_irexpr(this, &visitor, e);
	}
	void useExpressionPointer(const exprbdd *e)
	{
		struct {
			static visit_result f(LivenessEntry *out, const IRExprGet *g) {
				out->livePointer.insert(g->reg);
				out->liveDataOnly.erase(g->reg);
				return visit_continue;
			}
		} foo;
		static bdd_visitor<LivenessEntry> visitor;
		visitor.irexpr.Get = foo.f;
		visit_bdd(this, &visitor, visit_irexpr<LivenessEntry>, e);
	}

	void useSideEffect(StateMachineSideEffect *smse)
	{
		threadAndRegister def(threadAndRegister::invalid());
		if (smse->definesRegister(def))
			killRegister(def);
		switch (smse->type) {
		case StateMachineSideEffect::Load:
			useExpressionPointer( ((StateMachineSideEffectLoad *)smse)->addr);
			anyLoads = true;
			break;
		case StateMachineSideEffect::Store:
			useExpressionPointer( ((StateMachineSideEffectStore *)smse)->addr);
			useExpressionPointer( ((StateMachineSideEffectStore *)smse)->data);
			break;
		case StateMachineSideEffect::Copy:
			useExpressionData( ((StateMachineSideEffectCopy *)smse)->value);
			break;
		case StateMachineSideEffect::Unreached:
		case StateMachineSideEffect::StartAtomic:
		case StateMachineSideEffect::EndAtomic:
#if !CONFIG_NO_STATIC_ALIASING
		case StateMachineSideEffect::StackLayout:
#endif
		case StateMachineSideEffect::ImportRegister:
			break;
		case StateMachineSideEffect::AssertFalse:
			useExpressionData( ((StateMachineSideEffectAssertFalse *)smse)->value );
			break;
#if !CONFIG_NO_STATIC_ALIASING
		case StateMachineSideEffect::StartFunction:
			useExpressionData( ((StateMachineSideEffectStartFunction *)smse)->rsp );
			break;
		case StateMachineSideEffect::EndFunction:
			useExpressionData( ((StateMachineSideEffectEndFunction *)smse)->rsp );
			break;
#endif
		case StateMachineSideEffect::Phi: {
			StateMachineSideEffectPhi *smsep =
				(StateMachineSideEffectPhi *)smse;
			for (auto it = smsep->generations.begin(); it != smsep->generations.end(); it++) {
				useExpressionData(it->val);
				livePointer.insert(it->reg);
			}
			break;
		}
		}
	}

	bool merge(const LivenessEntry &other) {
		bool res = false;
		for (auto it = other.livePointer.begin(); !it.finished(); it.advance()) {
			if (livePointer.insert(*it)) {
				liveDataOnly.erase(*it);
				res = true;
			}
		}
		for (auto it = other.liveDataOnly.begin(); !it.finished(); it.advance()) {
			if (!livePointer.contains(*it))
				res |= liveDataOnly.insert(*it);
		}
		if (other.anyLoads && !anyLoads) {
			res = true;
			anyLoads = true;
		}
		return res;
	}

	bool registerLiveData(threadAndRegister reg) const { return liveDataOnly.contains(reg) || livePointer.contains(reg); }
	bool registerLivePointer(threadAndRegister reg) const { return livePointer.contains(reg); }
	bool mightLoadAnything() const { return anyLoads; }

	void print() const {
		printf("dataOnly = {");
		for (auto it = liveDataOnly.begin(); !it.finished(); it.advance()) {
			if (it.started())
				printf(", ");
			printf("%s", it->name());
		}
		printf("}, pointer = {");
		for (auto it = livePointer.begin(); !it.finished(); it.advance()) {
			if (it.started())
				printf(", ");
			printf("%s", it->name());
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
			le.useExpressionData( ((StateMachineTerminal *)s)->res );
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
			le.useExpressionData(smb->condition);
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
				if (!le.registerLiveData(smsel->target)) {
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
#if !CONFIG_NO_STATIC_ALIASING
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
				if (smsec->value->isLeaf() &&
				    smsec->value->leaf()->tag == Iex_Get &&
				    ((IRExprGet *)smsec->value->leaf())->reg == smsec->target) {
					/* Copying a register or
					   temporary back to itself is
					   always dead, regardless of
					   what liveness analysis
					   proper might say. */
					newEffect = NULL;
				} else if (!le.registerLiveData(smsec->target)) {
					newEffect = NULL;
				}
				break;
			}
			case StateMachineSideEffect::Phi: {
				StateMachineSideEffectPhi *p =
					(StateMachineSideEffectPhi *)newEffect;
				if (!le.registerLiveData(p->reg)) {
					newEffect = NULL;
				}
				break;
			}
			case StateMachineSideEffect::ImportRegister: {
				auto *p = (StateMachineSideEffectImportRegister *)newEffect;
				if (!le.registerLiveData(p->reg)) {
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

