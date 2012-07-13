#include "sli.h"
#include "offline_analysis.hpp"
#include "inferred_information.hpp"
#include "dummy_oracle.hpp"
#include "allowable_optimisations.hpp"
#include "state_machine.hpp"
#include "sat_checker.hpp"

#include "cfgnode_tmpl.cpp"

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
template <typename t> _saneIterator<typename std::vector<t>::iterator>
saneIterator(std::vector<t> &v)
{
	return saneIterator(v.begin(), v.end());
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
	typename underlying_it1::value_type &operator*() {
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
optimise_crash_summary(VexPtr<CrashSummary, &ir_heap> cs,
		       const VexPtr<OracleInterface> &oracle,
		       GarbageCollectionToken token)
{
	cs->loadMachine = optimiseStateMachine(
		cs->loadMachine,
		AllowableOptimisations::defaultOptimisations.
			enableassumePrivateStack().
			enableignoreSideEffects().
			enablenoLocalSurvival(),
		oracle,
		true,
		token);
	cs->storeMachine = optimiseStateMachine(
		cs->storeMachine,
		AllowableOptimisations::defaultOptimisations.
			enableassumePrivateStack().
			enableassumeNoInterferingStores(),
		oracle,
		true,
		token);
	cs->verificationCondition = simplifyIRExpr(
		cs->verificationCondition,
		AllowableOptimisations::defaultOptimisations);
	cs->verificationCondition = simplify_via_anf(
		cs->verificationCondition);
	cs->verificationCondition = simplifyIRExpr(
		cs->verificationCondition,
		AllowableOptimisations::defaultOptimisations);

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
	CfgDecode decode;
	decode.addMachine(cs->loadMachine);
	decode.addMachine(cs->storeMachine);

	std::set<CFGNode *> allNodes;
	for (auto it = concatIterators(saneIterator(cs->loadMachine->cfg_roots),
				       saneIterator(cs->storeMachine->cfg_roots));
	     !it.finished();
	     it++)
		enumerateCFG(const_cast<CFGNode *>(*it), allNodes);

	/* Find references of the first sense */
	{
		std::set<MemoryAccessIdentifier> mais;
		cs->loadMachine->root->enumerateMentionedMemoryAccesses(mais);
		cs->storeMachine->root->enumerateMentionedMemoryAccesses(mais);
		for (auto it = mais.begin(); it != mais.end(); it++)
			needed.insert(decode(it->where));
	}

	/* Find references of the second sense */
	{
		struct : public StateMachineTransformer {
			bool res;
			IRExpr *transformIex(IRExprGet *ieg) {
				if (ieg->reg.isReg())
					res = true;
				return ieg;
			}
			bool rewriteNewStates() const { return false; }
		} checkForRegisterReferences;
		checkForRegisterReferences.res = false;
		transformCrashSummary(cs, checkForRegisterReferences);
		if (checkForRegisterReferences.res) {
			for (auto it = concatIterators(saneIterator(cs->loadMachine->cfg_roots),
						       saneIterator(cs->storeMachine->cfg_roots));
			     !it.finished();
			     it++)
				needed.insert(*it);
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
			for (auto it = allNodes.begin(); it != allNodes.end(); it++) {
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
	for (auto it = allNodes.begin(); it != allNodes.end(); it++) {
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
	   anything which isn't necesarry.  Complication is that the
	   roots of the new graph have to correspond with the roots of
	   the old one, in a way which isn't entirely well defined.
	   Be conservative for now: if a root isn't needed and it has
	   a single successor, replace it with that successor. */
	for (auto it = concatIterators(saneIterator(cs->loadMachine->cfg_roots),
				       saneIterator(cs->storeMachine->cfg_roots));
	     !it.finished();
	     it++) {
		CFGNode *n = const_cast<CFGNode *>(*it);
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
		*it = n;
	}

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
		CFGNode *root = const_cast<CFGNode *>(s->cfg_roots[0]);
		std::set<CFGNode *> nodes;
		enumerateCFG(root, nodes);

		/* First, calculate the dominators map for all
		 * instructions. */
		std::map<CFGNode *, std::set<CFGNode *> > dominators;
		for (auto it = nodes.begin(); it != nodes.end(); it++)
			if (*it == root)
				dominators[*it].insert(*it);
			else
				dominators[*it] = nodes;
		std::queue<CFGNode *> pending;
		for (auto it = nodes.begin(); it != nodes.end(); it++)
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
		while (it != needed.end() && !nodes.count(const_cast<CFGNode *>(*it)))
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
			if (!nodes.count(const_cast<CFGNode *>(*it)))
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
		s->cfg_roots[0] = result;
	}

	return cs;
}

int
main(int argc, char *argv[])
{
	init_sli();

	CrashSummary *summary;
	char *first_line;

	summary = readBugReport(argv[1], &first_line);

	CfgDecode decode;
	decode.addMachine(summary->loadMachine);
	decode.addMachine(summary->storeMachine);
	summary = optimise_crash_summary(summary, new DummyOracle(summary, &decode), ALLOW_GC);

	FILE *f = fopen(argv[2], "w");
	fprintf(f, "%s\n", first_line);
	printCrashSummary(summary, f);
	fclose(f);

	return 0;
}
