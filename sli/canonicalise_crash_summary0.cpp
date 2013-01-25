#include "sli.h"
#include "offline_analysis.hpp"
#include "inferred_information.hpp"
#include "dummy_oracle.hpp"
#include "allowable_optimisations.hpp"
#include "state_machine.hpp"
#include "sat_checker.hpp"
#include "visitor.hpp"

#include "cfgnode_tmpl.cpp"

#ifndef NDEBUG
static bool debug_root_reduce = false;
#else
#define debug_root_reduce false
#endif

template <typename t>
class _saneIterator {
	t cursor;
	t end;
public:
	typedef typename t::value_type value_type;
	_saneIterator(const t &begin, const t &_end)
		: cursor(begin), end(_end)
	{}
	bool finished() const {
		return cursor == end;
	}
	void operator++(int) {
		cursor++;
	}
	typename t::value_type &operator *() {
		return *cursor;
	}
};
template <typename t> _saneIterator<t>
saneIterator(const t &begin, const t &end)
{
	return _saneIterator<t>(begin, end);
}
template <typename k, typename v> _saneIterator<typename std::map<k, v>::iterator>
saneIterator(std::map<k, v> &m)
{
	return saneIterator(m.begin(), m.end());
}
template <typename k> _saneIterator<typename std::vector<k>::iterator>
saneIterator(std::vector<k> &m)
{
	return saneIterator(m.begin(), m.end());
}

template <typename underlying_it1, typename underlying_it2>
class concatIterator {
	enum { ph_1, ph_2, ph_finished } phase;
	underlying_it1 cursor1;
	underlying_it2 cursor2;
public:
	concatIterator(const underlying_it1 &_begin1,
		       const underlying_it2 &_begin2)
		: phase(ph_1),
		  cursor1(_begin1),
		  cursor2(_begin2)
	{
		if (cursor1.finished()) {
			phase = ph_2;
			if (cursor2.finished())
				phase = ph_finished;
		}
	}
	bool finished() const {
		return phase == ph_finished;
	}
	void operator++(int) {
		switch (phase) {
		case ph_1:
			cursor1++;
			if (cursor1.finished()) {
				phase = ph_2;
				if (cursor2.finished())
					phase = ph_finished;
			}
			break;
		case ph_2:
			cursor2++;
			if (cursor2.finished())
				phase = ph_finished;
			break;
		case ph_finished:
			abort();
		}
	}
	const typename underlying_it1::value_type &operator*() {
		switch (phase) {
		case ph_1:
			return *cursor1;
		case ph_2:
			return *cursor2;
		case ph_finished:
			abort();
		}
		abort();
	}
	const typename underlying_it1::value_type *operator->() {
		switch (phase) {
		case ph_1:
			return &*cursor1;
		case ph_2:
			return &*cursor2;
		case ph_finished:
			abort();
		}
		abort();
	}
};
template <typename a, typename b> concatIterator<a, b>
concatIterators(const a &a1, const b &b1)
{
	return concatIterator<a, b>(a1, b1);
}

template <typename t>
class ptrIterator {
	int nr_ptrs;
	int cursor;
	t **content;
public:
	ptrIterator(t *a, ...)
		: cursor(0), content(NULL)
	{
		if (a == NULL) {
			nr_ptrs = 0;
			return;
		}
		nr_ptrs = 1;
		va_list args;
		va_start(args, a);
		while (1) {
			t *b = va_arg(args, t *);
			if (!b)
				break;
			nr_ptrs++;
		}
		va_end(args);

		content = (t **)malloc(sizeof(t *) * nr_ptrs);
		content[0] = a;
		va_start(args, a);
		int i = 1;
		while (1) {
			t *b = va_arg(args, t*);
			if (!b)
				break;
			content[i] = b;
			i++;
		}
		assert(i == nr_ptrs);
	}
	~ptrIterator()
	{
		free(content);
	}
	ptrIterator(const ptrIterator &other)
		: nr_ptrs(other.nr_ptrs),
		  cursor(other.cursor)
	{
		content = (t **)malloc(sizeof(t *) * nr_ptrs);
		memcpy(content, other.content, sizeof(t *) * nr_ptrs);
	}
	void operator=(const ptrIterator &other)
	{
		nr_ptrs = other.nr_ptrs;
		cursor = other.cursor;
		if (content)
			free(content);
		content = (t **)malloc(sizeof(t *) * nr_ptrs);
		memcpy(content, other.content, sizeof(t *) * nr_ptrs);
	}
	bool finished() const {
		return cursor == nr_ptrs;
	}
	void operator++(int) {
		assert(!finished());
		cursor++;
	}
	t *&operator *() {
		return content[cursor];
	}
};

template <typename t>
struct intersectSets {
	const std::set<t> &a;
	const std::set<t> &b;
	intersectSets(const std::set<t> &_a, const std::set<t> &_b)
		: a(_a), b(_b)
	{}
	struct iterator {
		typename std::set<t>::const_iterator a_iterator;
		typename std::set<t>::const_iterator a_iterator_end;
		typename std::set<t>::const_iterator b_iterator;
		typename std::set<t>::const_iterator b_iterator_end;
		iterator(const typename std::set<t>::const_iterator &_a_iterator,
			 const typename std::set<t>::const_iterator &_a_iterator_end,
			 const typename std::set<t>::const_iterator &_b_iterator,
			 const typename std::set<t>::const_iterator &_b_iterator_end)
			: a_iterator(_a_iterator),
			  a_iterator_end(_a_iterator_end),
			  b_iterator(_b_iterator),
			  b_iterator_end(_b_iterator_end)
		{
			advance();
		}
		bool finished() const {
			return a_iterator == a_iterator_end || b_iterator == b_iterator_end;
		}
		const t &operator *() {
			assert(*a_iterator == *b_iterator);
			return *a_iterator;
		}
		void operator++(int) {
			assert(!finished());
			a_iterator++;
			b_iterator++;
			advance();
		}
		void advance(void) {
			while (!finished()) {
				if (*a_iterator < *b_iterator)
					a_iterator++;
				else if (*b_iterator < *a_iterator)
					b_iterator++;
				else
					break;
			}
		}
	};
	iterator begin() const {
		return iterator(a.begin(), a.end(),
				b.begin(), b.end());
	}
};
template <typename t> intersectSets<t>
operator &(const std::set<t> &_a, const std::set<t> &_b)
{
	return intersectSets<t>(_a, _b);
}

template <typename t, typename s> void
operator |=(std::set<t> &dest, const s &other)
{
	for (auto it = other.begin();
	     !it.finished();
	     it++)
		dest.insert(*it);
}

static CrashSummary *
rewriteEntryPointExpressions(CrashSummary *cs, const std::map<std::pair<unsigned, CfgLabel>, std::pair<unsigned, CfgLabel> > &rules)
{
	struct : public StateMachineTransformer {
		const std::map<std::pair<unsigned, CfgLabel>, std::pair<unsigned, CfgLabel> > *rules;
		IRExpr *transformIex(IRExprEntryPoint *iep) {
			std::pair<unsigned, CfgLabel> key(iep->thread, iep->label);
			auto it = rules->find(key);
			if (it != rules->end())
				return IRExprEntryPoint::mk(it->second.first, it->second.second);
			return iep;
		}
		bool rewriteNewStates() const { return false; }
	} doit;
	doit.rules = &rules;
	return transformCrashSummary(cs, doit);
}

static void
findMinimalRoots(StateMachine *sm,
		 const std::set<const CFGNode *> &needed,
		 std::map<std::pair<unsigned, CfgLabel>, std::pair<unsigned, CfgLabel> > &rootRewrites)
{
	for (auto it = sm->cfg_roots.begin(); it != sm->cfg_roots.end(); it++) {
		CFGNode *n = const_cast<CFGNode *>(it->first.node);
		while (!needed.count(n)) {
			int nr_successors = 0;
			for (auto it2 = n->successors.begin(); it2 != n->successors.end(); it2++) {
				if (it2->instr)
					nr_successors++;
			}
			if (nr_successors != 1)
				break;
			for (auto it2 = n->successors.begin(); it2 != n->successors.end(); it2++) {
				if (it2->instr) {
					n = it2->instr;
					break;
				}
			}
		}
		if (debug_root_reduce) {
			printf("Root rewrite: %d:%s -> %d:%s\n",
			       it->first.thread, it->first.node->label.name(),
			       it->first.thread, n->label.name());
		}
		rootRewrites.insert(
			std::pair<std::pair<unsigned, CfgLabel>,
			          std::pair<unsigned, CfgLabel> >(
					  std::pair<unsigned, CfgLabel>(it->first.thread, it->first.node->label),
					  std::pair<unsigned, CfgLabel>(it->first.thread, n->label)));
		it->first.node = n;
	}
}

static CrashSummary *
optimise_crash_summary(VexPtr<CrashSummary, &ir_heap> cs,
		       const VexPtr<OracleInterface> &oracle,
		       GarbageCollectionToken token)
{
	VexPtr<MaiMap, &ir_heap> mai(cs->mai);
	cs->loadMachine = optimiseStateMachine(
		cs->scopes,
		mai,
		cs->loadMachine,
		AllowableOptimisations::defaultOptimisations.
			enableassumePrivateStack().
			enableignoreSideEffects().
			enablenoLocalSurvival(),
		oracle,
		true,
		token);
	cs->storeMachine = optimiseStateMachine(
		cs->scopes,
		mai,
		cs->storeMachine,
		AllowableOptimisations::defaultOptimisations.
			enableassumePrivateStack().
			enableassumeNoInterferingStores(),
		oracle,
		true,
		token);
	cs->mai = mai;

	/* The only reason we maintain the CFG is so that we can
	   resolve references into it from the machines and
	   verification condition.  There's not much point in hanging
	   on to nodes which are no longer referenced from anywhere.
	   The definition of ``referenced'' is slightly subtle:

	   -- Obviously, and explicit references from memory accesses
              count.
	   -- Registers implicitly reference all of the roots of the
              CFG.
	   -- Any node on a path between two nodes which are referenced
	      in one of the first two senses is also considered to
	      be referenced.
	*/
	std::set<const CFGNode *> needed;

	HashedSet<HashedPtr<CFGNode> > allNodes;
	for (auto it = concatIterators(saneIterator(cs->loadMachine->cfg_roots),
				       saneIterator(cs->storeMachine->cfg_roots));
	     !it.finished();
	     it++) {
		enumerateCFG(const_cast<CFGNode *>(it->first.node), allNodes);
	}

	/* Find references of the first sense */
	{
		std::set<MemoryAccessIdentifier> mais;
		cs->loadMachine->root->enumerateMentionedMemoryAccesses(mais);
		cs->storeMachine->root->enumerateMentionedMemoryAccesses(mais);
		for (auto it = mais.begin(); it != mais.end(); it++) {
			for (auto it2 = cs->mai->begin(*it); !it2.finished(); it2.advance()) {
				if (debug_root_reduce) {
					printf("Root %s is needed because of %s\n",
					       it2.node()->label.name(),
					       it->name());
				}
				needed.insert(it2.node());
			}
		}
	}

	/* Find references of the second sense */
	{
		struct {
			static visit_result Get(void *, const IRExprGet *ieg) {
				if (ieg->reg.isReg())
					return visit_abort;
				else
					return visit_continue;
			}
		} foo;
		static irexpr_visitor<void> visitor;
		visitor.Get = foo.Get;
		if (visit_crash_summary((void *)NULL, &visitor, cs) == visit_abort) {
			for (auto it = concatIterators(saneIterator(cs->loadMachine->cfg_roots),
						       saneIterator(cs->storeMachine->cfg_roots));
			     !it.finished();
			     it++) {
				if (debug_root_reduce) {
					printf("%s is needed because of register reference\n",
					       it->first.node->label.name());
				}
				needed.insert(it->first.node);
			}
		}
	}

	/* Find references in the third sense.  This is a three step
	   process:

	   1) find nodes which can reach a directly referenced node.
	   2) find nodes which are reachable from a directly referenced node.
	   3) Intersect those sets.
	*/
	{
		/* Find nodes which can reach a referenced node. */
		std::set<const CFGNode *> reachesReferencedNode(needed);
		bool progress = true;
		while (progress) {
			progress = false;
			for (auto it = allNodes.begin(); !it.finished(); it.advance()) {
				const CFGNode *n = *it;
				if (reachesReferencedNode.count(n))
					continue;
				for (auto it2 = n->successors.begin(); it2 != n->successors.end(); it2++) {
					if (it2->instr && reachesReferencedNode.count(it2->instr)) {
						reachesReferencedNode.insert(n);
						progress = true;
						break;
					}
				}
			}
		}
		/* And find nodes which are reachable from a referenced
		 * node. */
		std::set<const CFGNode *> reachableFromReferencedNode;
		std::queue<const CFGNode *> pending;
		for (auto it = needed.begin(); it != needed.end(); it++)
			pending.push(*it);
		while (!pending.empty()) {
			const CFGNode *n = pending.front();
			pending.pop();
			if (!reachableFromReferencedNode.insert(n).second)
				continue;
			for (auto it = n->successors.begin(); it != n->successors.end(); it++)
				if (it->instr)
					pending.push(it->instr);
		}

		/* We need anything in the intersection of those two
		 * sets. */
		needed |= reachableFromReferencedNode & reachesReferencedNode;
	}


	/* Now trim the CFG down a bit.  First step: any transition
	 * from a needed node to a not-needed one can be killed. */
	for (auto it = allNodes.begin(); !it.finished(); it.advance()) {
		CFGNode *n = *it;
		if (!needed.count(n))
			continue;
		for (auto it2 = n->successors.begin(); it2 != n->successors.end(); it2++) {
			if (it2->instr && !needed.count(it2->instr))
				it2->instr = NULL;
		}
	}

	/* Now try to rationalise the roots a little bit.  Ideally,
	   we'd like to trim the roots back a bit so as to remove
	   anything which isn't necessary.  Complication is that the
	   roots of the new graph have to correspond with the roots of
	   the old one, in a way which isn't entirely well defined.
	   Be conservative for now: if a root isn't needed and it has
	   a single successor, replace it with that successor. */
	std::map<std::pair<unsigned, CfgLabel>, std::pair<unsigned, CfgLabel> > rootRewrites;
	findMinimalRoots(cs->loadMachine, needed, rootRewrites);
	findMinimalRoots(cs->storeMachine, needed, rootRewrites);

	cs = rewriteEntryPointExpressions(cs, rootRewrites);

	/* Remove any roots which can't reach needed instructions. */
	for (auto it = cs->loadMachine->cfg_roots.begin();
	     it != cs->loadMachine->cfg_roots.end();
		) {
		bool reachesNeededInstr = false;
		std::queue<const CFGNode *> pending;
		std::set<const CFGNode *> visited;
		pending.push(it->first.node);
		while (!reachesNeededInstr && !pending.empty()) {
			const CFGNode *n = pending.front();
			pending.pop();
			if (!visited.insert(n).second)
				continue;
			if (needed.count(n))
				reachesNeededInstr = true;
			for (auto it = n->successors.begin(); it != n->successors.end(); it++)
				if (it->instr)
					pending.push(it->instr);
		}
		if (reachesNeededInstr)
			it++;
		else
			cs->loadMachine->cfg_roots.erase(it++);
	}
	for (auto it = cs->storeMachine->cfg_roots.begin();
	     it != cs->storeMachine->cfg_roots.end();
		) {
		bool reachesNeededInstr = false;
		std::queue<const CFGNode *> pending;
		std::set<const CFGNode *> visited;
		pending.push(it->first.node);
		while (!reachesNeededInstr && !pending.empty()) {
			const CFGNode *n = pending.front();
			pending.pop();
			if (!visited.insert(n).second)
				continue;
			if (needed.count(n))
				reachesNeededInstr = true;
			for (auto it = n->successors.begin(); it != n->successors.end(); it++)
				if (it->instr)
					pending.push(it->instr);
		}
		if (reachesNeededInstr)
			it++;
		else
			cs->storeMachine->cfg_roots.erase(it++);
	}

	rootRewrites.clear();

	/* Try a bit harder to rationalise the roots.  This version
	 * only works for single-rooted CFGs.  The idea is to replace
	 * the root with the least dominator of all of the needed
	 * instructions. */
	for (auto it0 = ptrIterator<StateMachine>(cs->loadMachine, cs->storeMachine, NULL);
	     !it0.finished();
	     it0++) {
		StateMachine *s = *it0;
		if (s->cfg_roots.size() != 1)
			continue;

		/* We want to find a dominator of all of the needed
		   instructions i.e. some instruction I such that
		   every path from the root to a needed instruction
		   passes through I.  We want to find the least such
		   dominator in the sense that if some other
		   instruction I' is also a dominator then every path
		   from I' to a needed instruction must pass through
		   I. */
		unsigned thread = s->cfg_roots.begin()->first.thread;
		CFGNode *root = const_cast<CFGNode *>(s->cfg_roots.begin()->first.node);
		HashedSet<HashedPtr<CFGNode> > nodes;
		enumerateCFG(root, nodes);
		std::set<CFGNode *> nodesSet;
		for (auto it = nodes.begin(); !it.finished(); it.advance())
			nodesSet.insert(it->get());

		/* First, calculate the dominators map for all
		 * instructions. */
		std::map<CFGNode *, std::set<CFGNode *> > dominators;
		for (auto it = nodes.begin(); !it.finished(); it.advance())
			if (*it == root)
				dominators[*it].insert(*it);
			else
				dominators[*it] = nodesSet;
		std::queue<CFGNode *> pending;
		for (auto it = nodes.begin(); !it.finished(); it.advance())
			pending.push(*it);
		while (!pending.empty()) {
			CFGNode *p = pending.front();
			pending.pop();
			const std::set<CFGNode *> &thisNode(dominators[p]);
			for (auto it = p->successors.begin(); it != p->successors.end(); it++) {
				if (it->instr) {
					std::set<CFGNode *> &otherNode(dominators[it->instr]);
					bool done_something = false;
					for (auto it2 = otherNode.begin();
					     it2 != otherNode.end();
						) {
						if (*it2 != it->instr && !thisNode.count(*it2)) {
							otherNode.erase(it2++);
							done_something = true;
						} else {
							it2++;
						}
					}
					if (done_something)
						pending.push(it->instr);
				}
			}
		}

		/* Initial candidates: everything which dominators
		 * every needed instruction. */
		auto it = needed.begin();
		while (it != needed.end() && !nodes.contains(const_cast<CFGNode *>(*it)))
			it++;
		if (it == needed.end()) {
			/* Weird... the whole cfg is redundant.  Kill
			 * it. */
			s->cfg_roots.clear();
			continue;
		}
		std::set<CFGNode *> candidates(dominators[const_cast<CFGNode *>(*it)]);
		it++;
		for (; it != needed.end(); it++) {
			if (!nodes.contains(const_cast<CFGNode *>(*it)))
				continue;
			std::set<CFGNode *> &dom(dominators[const_cast<CFGNode *>(*it)]);
			for (auto it2 = candidates.begin(); it2 != candidates.end(); ) 
				if (dom.count(*it2))
					it2++;
				else
					candidates.erase(it2++);
		}

		if (candidates.empty())
			continue;

		/* The final result is a candidate which is not
		   dominated by anything else in the candidate set. */
		CFGNode *result;
		auto it2 = candidates.begin();
		result = *it2;
		it2++;
		for ( ; it2 != candidates.end(); it2++) {
			if (dominators[*it2].count(result))
				result = *it2;
		}
		rootRewrites.insert(
			std::pair<std::pair<unsigned, CfgLabel>,
			          std::pair<unsigned, CfgLabel> >(
					  std::pair<unsigned, CfgLabel>(thread, root->label),
					  std::pair<unsigned, CfgLabel>(thread, result->label)));
		std::map<StateMachine::entry_point, StateMachine::entry_point_ctxt> newRoots;
		s->cfg_roots.begin()->first.node = result;
	}

	cs = rewriteEntryPointExpressions(cs, rootRewrites);

	/* Now walk the MAI map and remove anything which has become
	 * redundant. */
	HashedSet<HashedPtr<CFGNode> > remainingNodes;
	for (auto it = concatIterators(saneIterator(cs->loadMachine->cfg_roots),
				       saneIterator(cs->storeMachine->cfg_roots));
	     !it.finished();
	     it++) {
		enumerateCFG(const_cast<CFGNode *>(it->first.node), remainingNodes);
	}
	for (auto it = mai->begin(); !it.finished(); ) {
		for (auto it2 = it.begin(); !it2.finished(); ) {
			if (remainingNodes.contains(const_cast<CFGNode *>(it2.node())))
				it2.advance();
			else
				it2.erase();
		}
		if (it.empty())
			it.erase();
		else
			it.advance();
	}
	return cs;
}

int
main(int argc, char *argv[])
{
	if (argc != 3)
		errx(1, "need two arguments: input and output summaries");

	init_sli();

	CrashSummary *summary;
	char *first_line;

	SMScopes scopes;
	summary = readBugReport(&scopes, argv[1], &first_line);

	summary = optimise_crash_summary(summary, new DummyOracle(summary), ALLOW_GC);

	FILE *f = fopen(argv[2], "w");
	fprintf(f, "%s\n", first_line);
	printCrashSummary(summary, f);
	fclose(f);

	return 0;
}
