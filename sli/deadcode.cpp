/* Simple dead code elimination: find binders and registers which are
   never accessed after being set and eliminate them. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"
#include "visitor.hpp"

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
public:
	void useExpressionData(const bbdd *e)
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
		static irexpr_visitor<LivenessEntry> visitor;
		visitor.Get = foo.f;
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
		static irexpr_visitor<LivenessEntry> visitor;
		visitor.Get = foo.f;
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
		static irexpr_visitor<LivenessEntry> visitor;
		visitor.Get = foo.f;
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
		case StateMachineSideEffect::StackLayout:
		case StateMachineSideEffect::PointerAliasing:
			break;
		case StateMachineSideEffect::AssertFalse:
			useExpressionData( ((StateMachineSideEffectAssertFalse *)smse)->value );
			break;
		case StateMachineSideEffect::StartFunction:
			useExpressionData( ((StateMachineSideEffectStartFunction *)smse)->rsp );
			break;
		case StateMachineSideEffect::EndFunction:
			useExpressionData( ((StateMachineSideEffectEndFunction *)smse)->rsp );
			break;

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
		return res;
	}

	bool registerLiveData(threadAndRegister reg) const { return liveDataOnly.contains(reg) || livePointer.contains(reg); }
	bool registerLivePointer(threadAndRegister reg) const { return livePointer.contains(reg); }

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
		printf("}");
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
			res.useExpressionData(smb->condition);
			break;
		}
		case StateMachineState::Terminal: {
			StateMachineTerminal *smt = (StateMachineTerminal *)sm;
			res.useExpressionData(smt->res);
			break;
		}
		}
		if (content[sm].merge(res))
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
ssaDeadCode(bbdd::scope *scope, StateMachine *sm, bool *done_something)
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
	visitor.irexpr.Get = foo.Get;
	visitor.Phi = foo.Phi;
	for (auto it = states.begin(); it != states.end(); it++)
		visit_one_state(&refed_regs, &visitor, *it);
	std::set<StateMachineSideEffecting *> ses;
	enumStates(sm, &ses);
	for (auto it = ses.begin(); it != ses.end(); it++) {
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
				(*it)->sideEffect =
					new StateMachineSideEffectAssertFalse(
						bbdd::var(
							scope,
							IRExpr_Unop(Iop_BadPtr, exprbdd::to_irexpr(smsel->addr))),
						true);
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
		case StateMachineSideEffect::PointerAliasing: {
			auto *p = (StateMachineSideEffectPointerAliasing *)effect;
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

static StateMachine *
deadCodeElimination(bbdd::scope *scope, StateMachine *sm, bool *done_something, bool is_ssa)
{
	if (is_ssa)
		return ssaDeadCode(scope, sm, done_something);

	std::map<const StateMachineState *, int> stateLabels;

	if (debug_dump_liveness_map) {
		printf("Input to deadCodeElimination:\n");
		printStateMachine(sm, stdout, stateLabels);
	}

	std::set<StateMachineState *> allStates;
	enumStates(sm, &allStates);

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
		bbdd::scope *scope;

		StateMachineSideEffect *doit(StateMachineSideEffect *e,
					     const LivenessEntry &alive) {
			StateMachineSideEffect *newEffect = NULL;
			bool dead = false;
			switch (e->type) {
			case StateMachineSideEffect::Load: {
				StateMachineSideEffectLoad *smsel =
					(StateMachineSideEffectLoad *)e;
				if (!alive.registerLiveData(smsel->target))
					newEffect = new StateMachineSideEffectAssertFalse(
						bbdd::var(
							scope,
							IRExpr_Unop(Iop_BadPtr, exprbdd::to_irexpr(smsel->addr))),
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
			case StateMachineSideEffect::StackLayout:
				break;
			case StateMachineSideEffect::Copy: {
				StateMachineSideEffectCopy *smsec =
					(StateMachineSideEffectCopy *)e;
				if (smsec->value->isLeaf &&
				    smsec->value->leaf()->tag == Iex_Get &&
				    ((IRExprGet *)smsec->value->leaf())->reg == smsec->target) {
					/* Copying a register
					   or temporary back
					   to itself is always
					   dead, regardless of
					   what liveness
					   analysis proper
					   might say. */
					dead = true;
				} else {
					dead = !alive.registerLiveData(smsec->target);
				}
				break;
			}
			case StateMachineSideEffect::Phi: {
				StateMachineSideEffectPhi *p =
					(StateMachineSideEffectPhi *)e;
				if (!alive.registerLiveData(p->reg))
					dead = true;
				break;
			}
			case StateMachineSideEffect::PointerAliasing: {
				auto *p = (StateMachineSideEffectPointerAliasing *)e;
				if (!alive.registerLivePointer(p->reg))
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
			case StateMachineState::Terminal:
				/* Nothing needed */
				return;
			}
			abort();
		}

		_(LivenessMap &_livenessMap, bool *_done_something, bbdd::scope *_scope)
			: livenessMap(_livenessMap), done_something(_done_something),
			  scope(_scope)
		{}
	} eliminateDeadCode(livenessMap, done_something, scope);

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
deadCodeElimination(bbdd::scope *scope, StateMachine *sm, bool *done_something, bool is_ssa)
{
	return _deadCode::deadCodeElimination(scope, sm, done_something, is_ssa);
}

