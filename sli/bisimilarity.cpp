/* Try to identify states which are bisimilar, and then go and merge
 * them.  This is in-place, so should really be part of ::optimise();
 * nevermind. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "libvex_prof.hpp"
#include "maybe.hpp"

namespace _bisimilarity {
/* Unconfuse emacs */
#if 0
}
#endif

class st_pair_t: public  std::pair<StateMachineState *, StateMachineState *> {
public:
	st_pair_t(StateMachineState *a, StateMachineState *b)
		: std::pair<StateMachineState *, StateMachineState *>(a, b)
	{}
	st_pair_t() {}
	unsigned long hash() const {
		return (unsigned long)first * 3 + (unsigned long)second * 5;
	}
};

template <typename member> class HashedSet {
	static const int nr_heads = 2053;
	static const int nr_per_elem = 4;
	struct elem {
		struct elem *next;
		unsigned long use_map;
		member content[nr_per_elem];
		elem()
			: next(NULL), use_map(0)
		{}
	};
	struct elem heads[nr_heads];
#ifndef NDEBUG
	std::set<member> std_set;
#endif
public:
	bool contains(const member &v) const {
		unsigned long h = v.hash() % nr_heads;
		const struct elem *c = &heads[h];
		while (c) {
			for (int i = 0; i < nr_per_elem; i++) {
				if ( (c->use_map & (1ul << i)) &&
				     c->content[i] == v ) {
#ifndef NDEBUG
					assert(std_set.count(v));
#endif
					return true;
				}
			}
			c = c->next;
		}
#ifndef NDEBUG
		assert(!std_set.count(v));
#endif
		return false;
	}
	bool insert(const member &v) {
		unsigned long h = v.hash() % nr_heads;
		struct elem *c = &heads[h];
		struct elem **last;
		member *slot = NULL;
		unsigned long *slot_use;
		unsigned long slot_use_mask;
		while (c) {
			for (int i = 0; i < nr_per_elem; i++) {
				if ( (c->use_map & (1ul << i)) ) {
					if (c->content[i] == v ) {
#ifndef NDEBUG
						assert(std_set.count(v));
#endif
						return true;
					}
				} else if (!slot) {
					slot = &c->content[i];
					slot_use = &c->use_map;
					slot_use_mask = 1ul << i;
				}
			}
			last = &c->next;
			c = c->next;
		}
#ifndef NDEBUG
		assert(!std_set.count(v));
		std_set.insert(v);
#endif
		if (slot) {
			*slot = v;
			*slot_use |= slot_use_mask;
			return false;
		}
		c = new elem();
		c->use_map = 1;
		c->content[0] = v;
		*last = c;
		return false;
	}
	class iterator {
		HashedSet *owner;
		elem *elm;
		int idx1;
		int idx2;
	public:
		iterator(HashedSet *_owner)
			: owner(_owner)
		{
			elm = NULL;
			idx1 = nr_per_elem;
			idx2 = -1;
			advance();
		}
		bool finished() const {
			return idx2 == nr_heads;
		}
		void advance() {
			idx1 = (idx1 + 1) % nr_per_elem;
			if (idx1 == 0) {
				if (elm) {
					elm = elm->next;
				} else {
					assert(idx2 < nr_heads);
					idx2++;
					elm = &owner->heads[idx2];
				}
			}
			while (idx2 < nr_heads) {
				while (elm != NULL) {
					for (; idx1 < nr_per_elem; idx1++) {
						if (elm->use_map & (1ul << idx1))
							return;
					}
					idx1 = 0;
					elm = elm->next;
				}
				idx2++;
				elm = &owner->heads[idx2];
			}
		}
		const member *operator->() const {
			assert(!finished());
			assert(elm);
			return &elm->content[idx1];
		}
		void erase() {
			elm->use_map &= ~(1ul << idx1);
#ifndef NDEBUG
			assert(owner->std_set.count(elm->content[idx1]));
			owner->std_set.erase(elm->content[idx1]);
#endif
			advance();
		}
	};
	iterator begin() { return iterator(this); }
	~HashedSet() {
		for (int x = 0; x < nr_heads; x++) {
			struct elem *n;
			for (struct elem *e = heads[x].next; e; e = n) {
				n = e->next;
				delete e;
			}
		}
	}
};

template <typename key, typename value> class HashedMap {
	static const int nr_heads = 2053;
	static const int nr_per_elem = 4;
	struct elem {
		struct elem *next;
		unsigned long use_map;
		std::pair<key, value> content[nr_per_elem];
		elem()
			: next(NULL), use_map(0)
		{}
	};
	struct elem heads[nr_heads];
#ifndef NDEBUG
	std::map<key, value> std_map;
#endif

public:
	Maybe<value> get(const key &k) const {
		unsigned long h = k.hash() % nr_heads;
		const struct elem *c = &heads[h];
		while (c) {
			for (int i = 0; i < nr_per_elem; i++) {
				if ( (c->use_map & (1ul << i)) &&
				     c->content[i].first == k ) {
#ifndef NDEBUG
					auto it = std_map.find(k);
					assert(it != std_map.end());
					assert(it->second == c->content[i].second);
#endif
					return Maybe<value>::just(c->content[i].second);
				}
			}
			c = c->next;
		}
#ifndef NDEBUG
		assert(!std_map.count(k));
#endif
		return Maybe<value>::nothing();
	}
	void set(const key &k, value &v) {
		unsigned long h = k.hash() % nr_heads;
		struct elem *c = &heads[h];
		struct elem **last;
		std::pair<key, value> *slot = NULL;
		unsigned long *slot_use;
		unsigned long slot_use_mask;
		while (c) {
			for (int i = 0; i < nr_per_elem; i++) {
				if ( (c->use_map & (1ul << i)) ) {
					if (c->content[i].first == k ) {
#ifndef NDEBUG
						assert(std_map[k] == c->content[i].second);
#endif
						c->content[i].second = v;
#ifndef NDEBUG
						std_map[k] = v;
#endif
						return;
					}
				} else if (!slot) {
					slot = &c->content[i];
					slot_use = &c->use_map;
					slot_use_mask = 1ul << i;
				}
			}
			last = &c->next;
			c = c->next;
		}
#ifndef NDEBUG
		assert(!std_map.count(k));
		std_map[k] = v;
#endif
		if (slot) {
			*slot = std::pair<key, value>(k, v);
			*slot_use |= slot_use_mask;
			return;
		}
		c = new elem();
		c->use_map = 1;
		c->content[0].first = k;
		c->content[0].second = v;
		*last = c;
	}
};

template <typename ptr> class HashedPtr {
	ptr *content;
public:
	operator ptr*() const { return content; }
	HashedPtr(ptr *_content)
		: content(_content)
	{}
	unsigned long hash() const {
		return (unsigned long)content;
	}
	HashedPtr() {}
};

static StateMachineState *
rewriteStateMachine(StateMachineState *sm,
		    HashedMap<HashedPtr<StateMachineState>, StateMachineState *> &rules,
		    HashedSet<HashedPtr<StateMachineState> > &memo);

static StateMachineState *
rewriteStateMachine(StateMachineState *sm,
		    HashedMap<HashedPtr<StateMachineState>, StateMachineState *> &rules,
		    HashedSet<HashedPtr<StateMachineState> > &memo)
{
	if (memo.contains(sm))
		return sm;

	Maybe<StateMachineState *> r = rules.get(sm);
	if (r.valid && r.content != sm) {
		memo.insert(r.content);
		return r.content;
	}
	memo.insert(sm);
	std::vector<StateMachineState **> targets;
	sm->targets(targets);
	for (auto it = targets.begin(); it != targets.end(); it++)
		**it = rewriteStateMachine(**it, rules, memo);
	return sm;
}

static StateMachineState *
rewriteStateMachine(StateMachineState *sm, HashedMap<HashedPtr<StateMachineState>, StateMachineState *> &rules)
{
	HashedSet<HashedPtr<StateMachineState> > memo;

	return rewriteStateMachine(sm, rules, memo);
}

static StateMachine *
rewriteStateMachine(StateMachine *sm, HashedMap<HashedPtr<StateMachineState>, StateMachineState *> &rules)
{
	sm->root = rewriteStateMachine(sm->root, rules);
	return sm;
}

static bool
statesLocallyBisimilar(StateMachineState *sm1,
		       StateMachineState *sm2,
		       const HashedSet<st_pair_t> &edges,
		       const AllowableOptimisations &opt)
{
	if (sm1 == sm2)
		return true;

	if (sm1->type != sm2->type)
		return false;

	std::vector<StateMachineState *> smTarg1;
	std::vector<StateMachineState *> smTarg2;
	sm1->targets(smTarg1);
	sm2->targets(smTarg2);
	if (smTarg1.size() != smTarg2.size())
		return false;
	for (unsigned x = 0; x < smTarg1.size(); x++) {
		if (!edges.contains(st_pair_t(smTarg1[x], smTarg2[x])))
			return false;
	}
	switch (sm1->type) {
		/* These have no data, so if they're the same type it's fine */
	case StateMachineState::Unreached:
	case StateMachineState::Crash:
	case StateMachineState::NoCrash:
		return true;

	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *sme1 = (StateMachineSideEffecting *)sm1;
		StateMachineSideEffecting *sme2 = (StateMachineSideEffecting *)sm2;
		return sideEffectsBisimilar(sme1->sideEffect, sme2->sideEffect, opt);
	}

	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb1 = (StateMachineBifurcate *)sm1;
		StateMachineBifurcate *smb2 = (StateMachineBifurcate *)sm2;
		return definitelyEqual(smb1->condition, smb2->condition, opt);
	}
	}
	abort();
}

static void
buildStateMachineBisimilarityMap(HashedSet<st_pair_t> &bisimilarStates,
				 const std::set<StateMachineState *> &allStates,
				 const AllowableOptimisations &opt)
{
	/* We start by assuming that all states are bisimilar to each
	   other, and then use Tarski iteration to eliminate the
	   contradictions.  That allows us to build up maximal sets of
	   states such that the states in the sets are bisimilar to
	   each other.  Once we've got that, we pick one of the states
	   as being representative of the set, and then use it in
	   place of the other states. */

	/* Initially, everything is bisimilar to everything else. */
	for (auto it = allStates.begin();
	     !TIMEOUT && it != allStates.end();
	     it++)
		for (auto it2 = allStates.begin();
		     !TIMEOUT && it2 != allStates.end();
		     it2++)
			bisimilarStates.insert(st_pair_t(*it, *it2));

	bool progress;
	do {
		progress = false;

		if (TIMEOUT)
			return;
		/* Iterate over every suspected bisimilarity pair and
		   check for ``local bisimilarity''.  Once we're
		   consistent with the local bisimilarity
		   relationship, we will also be consistent with
		   global bismilarity. */
		for (auto it = bisimilarStates.begin(); !it.finished(); ) {
			if (statesLocallyBisimilar(it->first, it->second, bisimilarStates, opt)) {
				it.advance();
			} else {
				it.erase();
				progress = true;
			}
		}
	} while (progress);
}

static StateMachine *
bisimilarityReduction(StateMachine *sm, const AllowableOptimisations &opt)
{
	__set_profiling(bisimilarityReduction);
	HashedSet<st_pair_t> bisimilarStates;
	std::set<StateMachineState *> allStates;

	findAllStates(sm, allStates);
	buildStateMachineBisimilarityMap(bisimilarStates, allStates, opt);

	if (TIMEOUT)
		return sm;

	HashedMap<HashedPtr<StateMachineState>, StateMachineState *> canonMap;

	/* Now build a mapping from states to canonical states, using
	   the bisimilarity information, such that two states map to
	   the same canonical state iff they are bisimilar. */
	/* The canonMap effectively forms an inverted forest.  Each
	   tree in the forest represents some set of bisimilar nodes,
	   and each node's entry points at its parent in the tree, if
	   it has one.  The canonical representation of each set is
	   the root of its corresponding tree.  We advance by merging
	   sets, by inserting one as a child of the root of the other,
	   in response to bisimilar state entries. */

	for (auto it = bisimilarStates.begin(); !it.finished(); it.advance()) {
		StateMachineState *s1 = it->first;
		StateMachineState *s2 = it->second;

		/* Map the two nodes to their canonicalisations, if
		 * they have them. */
		while (1) {
			Maybe<StateMachineState *> r = canonMap.get(s1);
			if (!r.valid)
				break;
			s1 = r.content;
		}
		while (1) {
			Maybe<StateMachineState *> r = canonMap.get(s2);
			if (!r.valid)
				break;
			s2 = r.content;
		}
		/* This is more subtle than it looks.  It might appear
		   that we should be able to pick pretty much
		   arbitrarily which way round we perform the mapping
		   (s2 -> s1 or s1 -> s2).  Not so: the mapping we
		   build has to respect a depth-first ordering of the
		   graph, or you risk introducing loops.  This way
		   around does respect that ordering, whereas the
		   other way around wouldn't. */
		/* XXX I'm not entirely convinced I believe that
		 * explanation. */
		if (s1 != s2)
			canonMap.set(s2, s1);
	}

	/* Perform the rewrite.  We do this in-place, because it's not
	   context-dependent. */
	return rewriteStateMachine(sm, canonMap);
}

/* end of namespace */
}

StateMachine *
bisimilarityReduction(StateMachine *sm, const AllowableOptimisations &opt)
{
	return _bisimilarity::bisimilarityReduction(sm, opt);
}

