/* Simple dead code elimination: find binders and registers which are
   never accessed after being set and eliminate them. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"

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

class LivenessEntry : public small_set<threadAndRegister, 8> {
	void killRegister(threadAndRegister r)
	{
		erase(r);
	}
public:
	void useExpression(IRExpr *e)
	{
		class _ : public IRExprTransformer {
			LivenessEntry &out;
			IRExpr *transformIex(IRExprGet *g) {
				out.insert(g->reg);
				return IRExprTransformer::transformIex(g);
			}
		public:
			_(LivenessEntry &_out) : out(_out) {}
		} t(*this);
		t.doit(e);
	}

	void useSideEffect(StateMachineSideEffect *smse)
	{
		threadAndRegister def(threadAndRegister::invalid());
		if (smse->definesRegister(def))
			killRegister(def);
		std::vector<IRExpr *> inp;
		smse->inputExpressions(inp);
		for (auto it = inp.begin(); it != inp.end(); it++)
			useExpression(*it);
		if (smse->type == StateMachineSideEffect::Phi) {
			StateMachineSideEffectPhi *smsep =
				(StateMachineSideEffectPhi *)smse;
			for (auto it = smsep->generations.begin();
			     it != smsep->generations.end();
			     it++)
				this->insert(it->first);
		}
	}

	bool merge(const LivenessEntry &other) {
		bool res = false;
		for (auto it = other.begin(); !it.finished(); it.advance())
			res |= insert(*it);
		return res;
	}

	bool registerLive(threadAndRegister reg) const { return contains(reg); }

	void print() const {
		for (auto it = begin(); !it.finished(); it.advance()) {
			if (it.started())
				printf(", ");
			printf("%s", it->name());
		}
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
			res.useExpression(smb->condition);
			break;
		}
		case StateMachineState::Unreached:
		case StateMachineState::Crash:
		case StateMachineState::NoCrash:
			/* Nothing needed */
			break;
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
deadCodeElimination(StateMachine *sm, bool *done_something, const AllowableOptimisations &opt)
{
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
		const AllowableOptimisations &opt;

		StateMachineSideEffect *doit(StateMachineSideEffect *e,
					     const LivenessEntry &alive) {
			StateMachineSideEffect *newEffect = NULL;
			bool dead = false;
			switch (e->type) {
			case StateMachineSideEffect::Load: {
				StateMachineSideEffectLoad *smsel =
					(StateMachineSideEffectLoad *)e;
				if (!alive.registerLive(smsel->target))
					newEffect = new StateMachineSideEffectAssertFalse(
						IRExpr_Unop(Iop_BadPtr, smsel->addr),
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
				if (smsec->value->tag == Iex_Get &&
				    ((IRExprGet *)smsec->value)->reg == smsec->target) {
					/* Copying a register
					   or temporary back
					   to itself is always
					   dead, regardless of
					   what liveness
					   analysis proper
					   might say. */
					dead = true;
				} else {
					dead = !alive.registerLive(smsec->target);
				}
				break;
			}
			case StateMachineSideEffect::Phi: {
				StateMachineSideEffectPhi *p =
					(StateMachineSideEffectPhi *)e;
				if (!alive.registerLive(p->reg))
					dead = true;
				break;
			}
			case StateMachineSideEffect::PointerAliasing: {
				auto *p = (StateMachineSideEffectPointerAliasing *)e;
				if (!alive.registerLive(p->reg))
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
			case StateMachineState::Crash:
			case StateMachineState::NoCrash:
			case StateMachineState::Unreached:
				/* Nothing needed */
				return;
			}
			abort();
		}

		_(LivenessMap &_livenessMap, bool *_done_something, const AllowableOptimisations &_opt)
			: livenessMap(_livenessMap), done_something(_done_something), opt(_opt)
		{}
	} eliminateDeadCode(livenessMap, done_something, opt);

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
deadCodeElimination(StateMachine *sm, bool *done_something, const AllowableOptimisations &opt)
{
	return _deadCode::deadCodeElimination(sm, done_something, opt);
}

