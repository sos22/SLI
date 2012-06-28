#include "sli.h"
#include "state_machine.hpp"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"

namespace _realias {

typedef std::map<const StateMachineState *, int> stateLabelT;

#ifndef NDEBUG
static bool debug_build_stack_layout = false;
static bool debug_build_points_to_table = false;
static bool debug_refine_points_to_table = false;
static bool debug_build_alias_table = false;
static bool debug_refine_alias_table = false;
static bool debug_use_alias_table = false;
static void enable_debug() __attribute__((unused, used));
static void enable_debug() {
	debug_build_stack_layout = true;
	debug_build_points_to_table = true;
	debug_refine_points_to_table = true;
	debug_build_alias_table = true;
	debug_refine_alias_table = true;
	debug_use_alias_table = true;
}
#else
#define debug_build_stack_layout false
#define debug_build_points_to_table false
#define debug_refine_points_to_table false
#define debug_build_alias_table false
#define debug_refine_alias_table false
#define debug_use_alias_table false
#endif
#define any_debug (debug_build_stack_layout || debug_build_points_to_table || debug_refine_points_to_table || debug_build_alias_table || debug_refine_alias_table || debug_use_alias_table)

class AliasTable;

static char *
flattenStringFragmentsMalloc(const std::vector<const char *> &fragments)
{
	size_t s = 0;
	for (auto it = fragments.begin();
	     it != fragments.end();
	     it++)
		s += strlen(*it);
	char *res = (char *)malloc(s + 1);
	s = 0;
	for (auto it = fragments.begin();
	     it != fragments.end();
	     it++) {
		size_t s2 = strlen(*it);
		memcpy(res + s, *it, s2);
		s += s2;
	}
	res[s] = 0;
	return res;
}

/* set dest to dest \union src.  Returns true if we had to do
   anything, or false otherwise. */
template <typename t> static bool
setUnion(std::set<t> &dest, const std::set<t> &src)
{
	bool res = false;
	for (auto it = src.begin(); it != src.end(); it++) {
		auto it_did_insert = dest.insert(*it);
		res |= it_did_insert.second;
	}
	return res;
}

class PointsToSet : public Named {
	char *mkName() const {
		std::vector<const char *> fragments;
		fragments.push_back("PTS(");
		bool m = false;
		if (mightPointOutsideStack) {
			fragments.push_back("!stack");
			m = true;
		}
		for (auto it = targets.begin(); it != targets.end(); it++) {
			if (m)
				fragments.push_back(", ");
			m = true;
			fragments.push_back(vex_asprintf("%d", (*it)->frameId));
		}
		fragments.push_back(")");
		return flattenStringFragmentsMalloc(fragments);
	}
public:
	PointsToSet(bool _mightPointOutsideStack,
		    const std::set<StateMachineSideEffectStartFunction *> &_targets)
		: mightPointOutsideStack(_mightPointOutsideStack),
		  targets(_targets)
	{}
	PointsToSet()
		: mightPointOutsideStack(false)
	{}
	bool mightPointOutsideStack;
	std::set<StateMachineSideEffectStartFunction *> targets;
	void sanity_check() const {
		assert(mightPointOutsideStack == true ||
		       mightPointOutsideStack == false);
	}
	bool operator!=(const PointsToSet &o) const {
		return mightPointOutsideStack != o.mightPointOutsideStack ||
			targets != o.targets;
	}
	void operator|=(const PointsToSet &o) {
		mightPointOutsideStack |= o.mightPointOutsideStack;
		setUnion(targets, o.targets);
	}
	bool operator &(const PointsToSet &o) const {
		if (mightPointOutsideStack && o.mightPointOutsideStack)
			return true;
		for (auto it = targets.begin(); it != targets.end(); it++)
			if (o.targets.count(*it))
				return true;
		return false;
	}
};

class StackLayout : public Named {
	char *mkName() const {
		std::vector<const char *> fragments;
		auto it1 = rsps.rbegin();
		auto it2 = functions.rbegin();
		while (it1 != rsps.rend()) {
			fragments.push_back(vex_asprintf("%d <%s> ",
							 (*it2)->frameId,
							 nameIRExpr(*it1)));
			it1++;
			it2++;
		}
		fragments.push_back(vex_asprintf("%d", (*it2)->frameId));
		return flattenStringFragmentsMalloc(fragments);
	}
	/* A stack layout looks like this:

	   func1 <rsp1> func2 <rsp2> func3

	   which indicates that everything below rsp1 is the frame for
	   function 1, the stuff between rsp1 and rsp2 is the frame
	   for function 2, and everything above rsp2 is for function
	   3.

	   Note that the functions and rsps vectors are both reversed
	   from what you might expect (i.e. func1 is the last thing in
	   the function vector and rsp1 is the last thing in the rsps
	   vector).
	*/
	std::vector<StateMachineSideEffectStartFunction *> functions;
	std::vector<IRExpr *> rsps;
public:

	void sanity_check() const {
		assert(functions.size() == rsps.size() + 1);
		/* No dupes */
		for (auto it1 = functions.begin();
		     it1 != functions.end();
		     it1++) {
			assert(*it1);
			for (auto it2 = it1 + 1;
			     it2 != functions.end();
			     it2++)
				assert(*it1 != *it2);
		}
		for (auto it = rsps.begin(); it != rsps.end(); it++)
			assert(*it);
	}

	explicit StackLayout(StateMachineSideEffectStartFunction *s)
	{
		functions.push_back(s);
	}

	bool operator==(const StackLayout &o)
	{
		return o.functions == functions && o.rsps == rsps;
	}

	void startFunction(StateMachineSideEffectStartFunction *se)
	{
		functions.push_back(se);
		rsps.push_back(se->rsp);
	}
	void endFunction()
	{
		functions.pop_back();
		rsps.pop_back();
	}
	void enumFrames(std::set<StateMachineSideEffectStartFunction *> &out)
	{
		out.insert(functions.begin(), functions.end());
	}
	StateMachineSideEffectStartFunction *identifyFrameFromPtr(IRExpr *ptr);
};

enum compare_expressions_res {
	compare_expressions_lt,
	compare_expressions_eq,
	compare_expressions_gt,
	compare_expressions_unknown
};

static compare_expressions_res
compare_expressions(IRExpr *a, IRExpr *b)
{
	assert(a->type() == Ity_I64);
	assert(b->type() == Ity_I64);
	struct reg_plus_offset {
		threadAndRegister tr;
		long offset;
		reg_plus_offset(IRExpr *ex)
			: tr(threadAndRegister::invalid()),
			  offset(0)
		{
			if (ex->tag == Iex_Get) {
				tr = ((IRExprGet *)ex)->reg;
			} else if (ex->tag == Iex_Associative) {
				IRExprAssociative *a = (IRExprAssociative *)ex;
				if (a->nr_arguments == 2 &&
				    a->op == Iop_Add64 &&
				    a->contents[0]->tag == Iex_Const &&
				    a->contents[1]->tag == Iex_Get) {
					tr = ((IRExprGet *)a->contents[1])->reg;
					offset = ((IRExprConst *)a->contents[0])->con->Ico.U64;
				}
			}
		}
	} as(a), bs(b);
	if (!as.tr.isValid() ||
	    !bs.tr.isValid() ||
	    !threadAndRegister::fullEq(as.tr, bs.tr))
		return compare_expressions_unknown;
	if (as.offset < bs.offset)
		return compare_expressions_lt;
	else if (as.offset == bs.offset)
		return compare_expressions_eq;
	else
		return compare_expressions_gt;
}


StateMachineSideEffectStartFunction *
StackLayout::identifyFrameFromPtr(IRExpr *ptr)
{
	assert(ptr->type() == Ity_I64);
	auto it2 = functions.rbegin();
	for (auto it = rsps.rbegin(); it != rsps.rend(); it++) {
		IRExpr *rsp = *it;
		switch (compare_expressions(ptr, rsp)) {
		case compare_expressions_lt:
		case compare_expressions_eq:
			return *it2;
		case compare_expressions_gt:
			continue;
		case compare_expressions_unknown:
			return NULL;
		}
		it2++;
	}
	return NULL;
}

class StackLayoutTable {
	std::map<StateMachineState *, StackLayout> content;
public:
	StateMachineSideEffectStartFunction *rootFunction;
	StackLayoutTable()
		: rootFunction(NULL)
	{}
	bool build(StateMachine *inp);
	void prettyPrint(FILE *f, const stateLabelT &labels) const {
		for (auto it = content.begin(); it != content.end(); it++) {
			auto i = labels.find(it->first);
			assert(i != labels.end());
			fprintf(f, "%d: %s\n", i->second, it->second.name());
		}
	}
	void sanity_check() const {
		for (auto it = content.begin();
		     it != content.end();
		     it++) {
			assert(it->first);
			it->second.sanity_check();
		}
	}
	PointsToSet pointsToAnything();
	StackLayout &forState(StateMachineState *s)
	{
		auto it = content.find(s);
		assert(it != content.end());
		return it->second;
	}
};

bool
StackLayoutTable::build(StateMachine *inp)
{
	assert(!rootFunction);
	rootFunction = new StateMachineSideEffectStartFunction(NULL, -1);
	typedef std::pair<StateMachineState *, StackLayout> q_entry;

	/* This does actually need to be BFS, for correctness. */
	std::queue<q_entry> pending;
	pending.push(q_entry(inp->root, StackLayout(rootFunction)));
	while (!pending.empty()) {
		q_entry q(pending.front());
		pending.pop();
		auto it_did_insert = content.insert(q);
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (!did_insert) {
			assert(it->second == q.second);
			continue;
		}
		std::vector<StateMachineState *> targets;
		q.first->targets(targets);
		StackLayout exitLayout(q.second);
		if (q.first->getSideEffect()) {
			if (q.first->getSideEffect()->type == StateMachineSideEffect::StartFunction)
				exitLayout.startFunction((StateMachineSideEffectStartFunction *)
							 q.first->getSideEffect());
			else if (q.first->getSideEffect()->type == StateMachineSideEffect::EndFunction)
				exitLayout.endFunction();
		}
		for (auto it = targets.begin(); it != targets.end(); it++)
			pending.push(q_entry(*it, exitLayout));
	}
	sanity_check();
	return true;
}

PointsToSet
StackLayoutTable::pointsToAnything()
{
	std::set<StateMachineSideEffectStartFunction *> allFunctions;
	for (auto it = content.begin(); it != content.end(); it++)
		it->second.enumFrames(allFunctions);
	return PointsToSet(true, allFunctions);
}

class PointsToTable {
	std::map<threadAndRegister, PointsToSet, threadAndRegister::fullCompare> content;
public:
	PointsToSet pointsToSetForExpr(IRExpr *e,
				       StackLayout &sl,
				       StackLayoutTable &slt);
	bool build(StateMachine *sm, StackLayoutTable &slt);
	void prettyPrint(FILE *f);
	void sanity_check() const {
		for (auto it = content.begin(); it != content.end(); it++) {
			assert(it->first.isValid());
			assert(it->first.isTemp());
			it->second.sanity_check();
		}
	}
	PointsToTable refine(AliasTable &at, StateMachine *sm, StackLayoutTable &slt, bool *done_something);
};

PointsToSet
PointsToTable::pointsToSetForExpr(IRExpr *e,
				  StackLayout &sl,
				  StackLayoutTable &slt)
{
	if (e->type() != Ity_I64)
		return PointsToSet();
	switch (e->tag) {
	case Iex_Get: {
		IRExprGet *iex = (IRExprGet *)e;
		if (iex->reg.isTemp()) {
			assert(content.count(iex->reg));
			return content[iex->reg];
		}
		if (iex->reg.isReg() &&
		    iex->reg.asReg() == OFFSET_amd64_RSP) {
			StateMachineSideEffectStartFunction *f;
			f = sl.identifyFrameFromPtr(iex);
			if (f) {
				PointsToSet p;
				p.mightPointOutsideStack = false;
				p.targets.insert(f);
				return p;
			} else {
				break;
			}
		}
	}
		/* Fall through */
	case Iex_Load: {
		PointsToSet p;
		p.mightPointOutsideStack = true;
		p.targets.insert(slt.rootFunction);
		return p;
	}
	case Iex_Const: {
		PointsToSet p;
		p.mightPointOutsideStack = true;
		return p;
	}
	case Iex_Associative: {
		IRExprAssociative *iex = (IRExprAssociative *)e;
		if (iex->op == Iop_Add64 &&
		    iex->nr_arguments == 2 &&
		    iex->contents[0]->tag == Iex_Const &&
		    iex->contents[1]->tag == Iex_Get &&
		    ((IRExprGet *)iex->contents[1])->reg.isReg() &&
		    ((IRExprGet *)iex->contents[1])->reg.asReg() == OFFSET_amd64_RSP) {
			StateMachineSideEffectStartFunction *f;
			f = sl.identifyFrameFromPtr(iex);
			if (f) {
				PointsToSet p;
				p.mightPointOutsideStack = false;
				p.targets.insert(f);
				return p;
			}
		}
		if (iex->op == Iop_Add64) {
			PointsToSet res;
			for (int i = 0; i < iex->nr_arguments; i++)
				res |= pointsToSetForExpr(iex->contents[i], sl, slt);
			return res;
		}

		break;
	}
	default:
		break;
	}
	return slt.pointsToAnything();
}

bool
PointsToTable::build(StateMachine *sm, StackLayoutTable &slt)
{
	PointsToSet defaultTmpPointsTo(slt.pointsToAnything());
	struct : public StateMachineTransformer {
		PointsToSet *pts;
		PointsToTable *ptt;
		IRExpr *transformIex(IRExprGet *ieg) {
			if (ieg->reg.isTemp())
				ptt->content.insert(std::pair<threadAndRegister, PointsToSet>(ieg->reg, *pts));
			return ieg;
		}
		bool rewriteNewStates() const { return false; }
	} doit;
	doit.pts = &defaultTmpPointsTo;
	doit.ptt = this;
	doit.transform(sm);
	if (TIMEOUT)
		return false;
	sanity_check();
	return true;
}

void
PointsToTable::prettyPrint(FILE *f)
{
	for (auto it = content.begin(); it != content.end(); it++)
		fprintf(f, "\t%s\t%s\n", it->first.name(), it->second.name());
}

class AliasTableEntry {
public:
	std::set<StateMachineSideEffecting *> stores;
	bool mightHaveExternalStores;
	bool mightLoadInitial;
	void sanity_check() const {
		assert(mightHaveExternalStores == true ||
		       mightHaveExternalStores == false);
		assert(mightLoadInitial == true ||
		       mightLoadInitial == false);
		for (auto it = stores.begin();
		     it != stores.end();
		     it++) {
			assert(*it);
			assert((*it)->getSideEffect());
			assert((*it)->getSideEffect()->type == StateMachineSideEffect::Store);
		}
	}
	AliasTableEntry(const std::set<StateMachineSideEffecting *> &_stores,
			bool _mightHaveExternalStores,
			bool _mightLoadInitial)
		: stores(_stores),
		  mightHaveExternalStores(_mightHaveExternalStores),
		  mightLoadInitial(_mightLoadInitial)
	{
		sanity_check();
	}
	void prettyPrint(FILE *f, stateLabelT &labels) const {
		bool m = false;
		if (mightHaveExternalStores) {
			fprintf(f, "<external>");
			m = true;
		}
		if (mightLoadInitial) {
			if (m)
				fprintf(f, ", ");
			fprintf(f, "<initial>");
			m = true;
		}
		for (auto it = stores.begin(); it != stores.end(); it++) {
			if (m)
				fprintf(f, ", ");
			fprintf(f, "%d", labels[*it]);
			m = true;
		}
	}
	struct store_iterator {
		std::set<StateMachineSideEffecting *>::const_iterator it;
		explicit store_iterator(const std::set<StateMachineSideEffecting *>::const_iterator &_it)
			: it(_it)
		{}
		StateMachineSideEffectStore *operator->() {
			assert(*it);
			assert((*it)->getSideEffect());
			assert((*it)->getSideEffect()->type == StateMachineSideEffect::Store);
			return (StateMachineSideEffectStore *)(*it)->getSideEffect();
		}
		void operator++(int) { it++; }
		bool operator!=(const store_iterator &o)
		{
			return it != o.it;
		}
	};
	store_iterator beginStores() const { return store_iterator(stores.begin()); }
	store_iterator endStores() const { return store_iterator(stores.end()); }	
};

class AliasTable {
public:
	std::map<StateMachineSideEffecting *, AliasTableEntry> content;
	bool build(StateMachine *sm,
		   stateLabelT &labels,
		   const AllowableOptimisations &opt,
		   OracleInterface *oracle);
	void prettyPrint(FILE *f, stateLabelT &labels) const;
	void sanity_check() const {
		for (auto it = content.begin(); it != content.end(); it++) {
			assert(it->first);
			assert(it->first->getSideEffect());
			assert(it->first->getSideEffect()->type == StateMachineSideEffect::Load);
			it->second.sanity_check();
		}
	}
	StateMachineSideEffecting *loadDefiningRegister(const threadAndRegister &tr)
	{
		for (auto it = content.begin();
		     it != content.end();
		     it++)
			if ( threadAndRegister::fullEq(((StateMachineSideEffectLoad *)it->first->getSideEffect())->target,
						       tr) )
				return it->first;
		abort();
	}
	const AliasTableEntry &storesForLoad(StateMachineSideEffecting *smse) const
	{
		assert(smse->getSideEffect());
		assert(smse->getSideEffect()->type == StateMachineSideEffect::Load);
		auto it = content.find(smse);
		assert(it != content.end());
		return it->second;
	}
	void refine(PointsToTable &ptt, StackLayoutTable &slt, bool *done_something,
		    stateLabelT &labels);
};

static bool
mightLoadInitialValue(StateMachineSideEffecting *smse, StateMachine *sm,
		      const AllowableOptimisations &opt)
{
	assert(smse->getSideEffect());
	assert(smse->getSideEffect()->type == StateMachineSideEffect::Load);
	StateMachineSideEffectLoad *load = (StateMachineSideEffectLoad *)smse->getSideEffect();
	std::queue<StateMachineState *> q;
	q.push(sm->root);
	while (!q.empty()) {
		StateMachineState *s = q.front();
		q.pop();
		if (s == smse)
			return true;
		if (s->getSideEffect() &&
		    s->getSideEffect()->type == StateMachineSideEffect::Store) {
			StateMachineSideEffectStore *store = (StateMachineSideEffectStore *)s->getSideEffect();
			if (store->data->type() == load->type &&
			    definitelyEqual(store->addr, load->addr, opt)) {
				/* This store will satisfy the load,
				   so we don't need to explore this
				   path any further. */
				continue;
			}
		}
		s->targets(q);
	}
	/* No paths load from the root to smse without first passing
	   through a satisfying store. */
	return false;
}

bool
AliasTable::build(StateMachine *sm,
		  stateLabelT &labels,
		  const AllowableOptimisations &opt,
		  OracleInterface *oracle)
{
	/* First figure out where the stores might reach from a
	 * simple control-flow perspective. */
	/* Map from states to all of the store side effect states
	 * which might happen before that state. */
	typedef std::pair<StateMachineState *, std::set<StateMachineSideEffecting *> > reachingEntryT;
	std::map<StateMachineState *, std::set<StateMachineSideEffecting *> > reaching;
	std::queue<StateMachineState *> pending;
	pending.push(sm->root);
	reaching.insert(reachingEntryT(sm->root, std::set<StateMachineSideEffecting *>()));
	while (!pending.empty()) {
		StateMachineState *s = pending.front();
		pending.pop();
		auto this_it = reaching.find(s);
		assert(this_it != reaching.end());
		std::set<StateMachineSideEffecting *> exitReaching(this_it->second);
		if (s->getSideEffect() &&
		    s->getSideEffect()->type == StateMachineSideEffect::Store) {
			StateMachineSideEffectStore *store = (StateMachineSideEffectStore *)s->getSideEffect();
			/* Kill off anything which we definitely clobber */
			for (auto it = exitReaching.begin();
			     it != exitReaching.end();
				) {
				assert((*it)->getSideEffect());
				assert((*it)->getSideEffect()->type == StateMachineSideEffect::Store);
				StateMachineSideEffectStore *other =
					(StateMachineSideEffectStore *)(*it)->getSideEffect();
				if (other->data->type() == store->data->type() &&
				    definitelyEqual(store->addr, other->addr, opt)) {
					exitReaching.erase(it++);
				} else {
					it++;
				}
			}
			/* And insert ourselves into the set */
			exitReaching.insert((StateMachineSideEffecting *)s);
		}
		std::vector<StateMachineState *> targets;
		s->targets(targets);
		for (auto it = targets.begin(); it != targets.end(); it++) {
			auto it2_did_insert = reaching.insert(reachingEntryT(*it, exitReaching));
			auto it2 = it2_did_insert.first;
			auto did_insert = it2_did_insert.second;
			if (!did_insert && !setUnion(it2->second, exitReaching))
				continue;
			pending.push(*it);
		}
	}

	if (debug_build_alias_table) {
		printf("Initial reaching table:\n");
		for (auto it = reaching.begin(); it != reaching.end(); it++) {
			printf("l%d: ", labels[it->first]);
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				if (it2 != it->second.begin())
					printf(", ");
				printf("%d", labels[*it2]);
			}
			printf("\n");
		}
	}

	/* Now restrict that to only contain loads, and only those
	 * which are compatible with the oracle. */
	for (auto it = reaching.begin();
	     it != reaching.end();
		) {
		StateMachineState *s = it->first;
		if (s->type != StateMachineState::SideEffecting ||
		    s->getSideEffect() == NULL ||
		    s->getSideEffect()->type != StateMachineSideEffect::Load) {
			reaching.erase(it++);
			continue;
		}
		StateMachineSideEffectLoad *smsel = (StateMachineSideEffectLoad *)s->getSideEffect();
		for (auto it2 = it->second.begin(); it2 != it->second.end(); ) {
			StateMachineSideEffecting *o = *it2;
			assert(o->getSideEffect());
			assert(o->getSideEffect()->type == StateMachineSideEffect::Store);
			StateMachineSideEffectStore *smses =
				(StateMachineSideEffectStore *)o->getSideEffect();
			if (oracle->memoryAccessesMightAlias(opt, smsel, smses)) {
				it2++;
			} else {
				it->second.erase(it2++);
			}
		}
		it++;
	}

	if (debug_build_alias_table) {
		printf("Oracle-restricted reaching table:\n");
		for (auto it = reaching.begin(); it != reaching.end(); it++) {
			printf("l%d: ", labels[it->first]);
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				if (it2 != it->second.begin())
					printf(", ");
				printf("%d", labels[*it2]);
			}
			printf("\n");
		}
	}

	/* Now convert that into an actual aliasing table. */
	for (auto it = reaching.begin(); it != reaching.end(); it++) {
		assert(it->first->type == StateMachineState::SideEffecting);
		StateMachineSideEffecting *smse = (StateMachineSideEffecting *)it->first;
		StateMachineSideEffect *se = smse->getSideEffect();
		assert(se);
		assert(se->type == StateMachineSideEffect::Load);
		StateMachineSideEffectLoad *l = (StateMachineSideEffectLoad *)se;
		bool mightHaveExternalStores =
			!opt.assumeNoInterferingStores() &&
			oracle->hasConflictingRemoteStores(opt, l);
		content.insert(std::pair<StateMachineSideEffecting *, AliasTableEntry>(
				       smse,
				       AliasTableEntry(it->second,
						       mightHaveExternalStores,
						       mightLoadInitialValue(smse, sm, opt))));
	}

	sanity_check();

	return true;
}

void
AliasTable::prettyPrint(FILE *f, stateLabelT &labels) const
{
	for (auto it = content.begin(); it != content.end(); it++) {
		fprintf(f, "l%d: ", labels[it->first]);
		it->second.prettyPrint(f, labels);
		fprintf(f, "\n");
	}
}

static StateMachineSideEffecting *
sideEffectDefiningRegister(StateMachine *sm, const threadAndRegister &tr)
{
	std::vector<StateMachineSideEffecting *> sideEffects;
	enumStates(sm, &sideEffects);
	threadAndRegister tr2(threadAndRegister::invalid());
	for (auto it = sideEffects.begin(); it != sideEffects.end(); it++) {
		if ((*it)->getSideEffect() &&
		    (*it)->getSideEffect()->definesRegister(tr2) &&
		    threadAndRegister::fullEq(tr, tr2))
			return *it;
	}
	abort();
}

PointsToTable
PointsToTable::refine(AliasTable &at,
		      StateMachine *sm,
		      StackLayoutTable &slt,
		      bool *done_something)
{
	PointsToTable res;
	for (auto it = content.begin();
	     it != content.end();
	     it++) {
		StateMachineSideEffecting *smse = sideEffectDefiningRegister(sm, it->first);
		StateMachineSideEffect *effect = smse->getSideEffect();
		assert(effect);
		PointsToSet newPts;
		StackLayout &sl(slt.forState(smse));
		switch (effect->type) {
		case StateMachineSideEffect::Load: {
			const AliasTableEntry &e(at.storesForLoad(smse));
			if (e.mightLoadInitial || e.mightHaveExternalStores) {
				newPts.mightPointOutsideStack = true;
				newPts.targets.insert(slt.rootFunction);
			}
			for (auto it2 = e.beginStores(); it2 != e.endStores(); it2++)
				newPts |= pointsToSetForExpr(it2->data, sl, slt);
			break;
		}
		case StateMachineSideEffect::Copy: {
			StateMachineSideEffectCopy *c = (StateMachineSideEffectCopy *)effect;
			newPts = pointsToSetForExpr(c->value, sl, slt);
			break;
		}
		case StateMachineSideEffect::Phi: {
			StateMachineSideEffectPhi *p = (StateMachineSideEffectPhi *)effect;
			for (auto it = p->generations.begin();
			     it != p->generations.end();
			     it++) {
				auto i = content.find(p->reg.setGen(it->first));
				assert(i != content.end());
				newPts |= i->second;
			}
			break;
		}
		case StateMachineSideEffect::Store:
		case StateMachineSideEffect::Unreached:
		case StateMachineSideEffect::AssertFalse:
		case StateMachineSideEffect::StartAtomic:
		case StateMachineSideEffect::EndAtomic:
		case StateMachineSideEffect::StartFunction:
		case StateMachineSideEffect::EndFunction:
			/* These aren't supposed to define registers */
			abort();
		}
		if (newPts != it->second)
			*done_something = true;
		res.content.insert(std::pair<threadAndRegister, PointsToSet>(it->first, newPts));
	}
	return res;
}

void
AliasTable::refine(PointsToTable &ptt, StackLayoutTable &slt, bool *done_something,
		   stateLabelT &labels)
{
	for (auto it = content.begin();
	     it != content.end();
	     it++) {
		StateMachineSideEffectLoad *l = (StateMachineSideEffectLoad *)it->first->getSideEffect();
		StackLayout loadSl(slt.forState(it->first));
		PointsToSet loadPts(ptt.pointsToSetForExpr(l->addr, loadSl, slt));
		if (debug_refine_alias_table)
			printf("Examining alias table for state %d\n",
			       labels[it->first]);
		for (auto it2 = it->second.stores.begin();
		     it2 != it->second.stores.end();
			) {
			StackLayout storeSl(slt.forState(*it2));
			PointsToSet storePts(ptt.pointsToSetForExpr( ((StateMachineSideEffectStore *)(*it2)->getSideEffect())->addr,
								     storeSl,
								     slt));
			if (storePts & loadPts) {
				if (debug_refine_alias_table)
					printf("\tPreserve l%d: %s vs %s\n",
					       labels[*it2], storePts.name(),
					       loadPts.name());
				it2++;
			} else {
				if (debug_refine_alias_table)
					printf("\tKill l%d: %s vs %s\n",
					       labels[*it2], storePts.name(),
					       loadPts.name());
				*done_something = true;
				it->second.stores.erase(it2++);
			}
		}
	}
}

static StateMachine *
functionAliasAnalysis(StateMachine *sm, const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something)
{
	StackLayoutTable stackLayout;
	stateLabelT stateLabels;
	if (any_debug) {
		printf("%s, input:\n", __func__);
		printStateMachine(sm, stdout, stateLabels);
	}
	if (!stackLayout.build(sm)) {
		if (any_debug)
			printf("Failed to build stack layout!\n");
		return sm;
	}
	if (debug_build_stack_layout) {
		printf("Stack layout table:\n");
		stackLayout.prettyPrint(stdout, stateLabels);
	}

	PointsToTable ptt;
	if (!ptt.build(sm, stackLayout)) {
		if (any_debug)
			printf("Failed to build points-to table!\n");
		return sm;
	}
	if (debug_build_points_to_table) {
		printf("Points-to table:\n");
		ptt.prettyPrint(stdout);
	}

	AliasTable at;
	if (!at.build(sm, stateLabels, opt, oracle)) {
		if (any_debug)
			printf("Failed to build alias table!\n");
		return sm;
	}
	if (debug_build_alias_table) {
		printf("Alias table:\n");
		at.prettyPrint(stdout, stateLabels);
	}

	while (1) {
		bool p = false;
		PointsToTable ptt2 = ptt.refine(at, sm, stackLayout, &p);
		if (!p)
			break;
		if (debug_refine_points_to_table) {
			printf("Refined points-to table:\n");
			ptt2.prettyPrint(stdout);
		}
		ptt = ptt2;

		p = false;
		at.refine(ptt, stackLayout, &p, stateLabels);
		if (!p)
			break;
		if (debug_refine_alias_table) {
			printf("Refined alias table:\n");
			at.prettyPrint(stdout, stateLabels);
		}
	}
	if (any_debug) {
		printf("Final points-to table:\n");
		ptt.prettyPrint(stdout);
		printf("Final alias table:\n");
		at.prettyPrint(stdout, stateLabels);
	}

	bool progress = false;

	/* Use the aliasing table to resolve loads wherever possible. */
	for (auto it = at.content.begin(); it != at.content.end(); it++) {
		StateMachineSideEffectLoad *l = (StateMachineSideEffectLoad *)it->first->getSideEffect();
		if (it->second.mightHaveExternalStores)
			continue;
		if (it->second.stores.size() == 0) {
			assert(it->second.mightLoadInitial);
			if (debug_use_alias_table)
				printf("Replace l%d with initial load\n",
				       stateLabels[it->first]);
			progress = true;
			it->first->sideEffect =
				new StateMachineSideEffectCopy(
					l->target,
					IRExpr_Load(
						l->type,
						l->addr,
						MemoryAccessIdentifier::initial_value()));
		} else if (it->second.stores.size() == 1 &&
			   !it->second.mightLoadInitial) {
			StateMachineSideEffecting *s_state = *it->second.stores.begin();
			if (debug_use_alias_table)
				printf("Replace l%d with forward from l%d\n",
				       stateLabels[it->first], stateLabels[s_state]);
			assert(s_state->getSideEffect());
			assert(s_state->getSideEffect()->type == StateMachineSideEffect::Store);
			progress = true;
			it->first->sideEffect =
				new StateMachineSideEffectCopy(
					l->target,
					((StateMachineSideEffectStore *)s_state->getSideEffect())->data);
		} else {
			if (debug_use_alias_table)
				printf("Can't do anything with load l%d\n",
				       stateLabels[it->first]);
		}
	}

	/* Let's also have a go at ripping out redundant stores. */
	std::set<StateMachineSideEffecting *> sideEffects;
	enumStates(sm, &sideEffects);
	for (auto it = sideEffects.begin(); it != sideEffects.end(); it++) {
		if (!(*it)->getSideEffect() ||
		    (*it)->getSideEffect()->type != StateMachineSideEffect::Store)
			continue;
		StateMachineSideEffectStore *s = (StateMachineSideEffectStore *)(*it)->getSideEffect();
		if (!opt.ignoreSideEffects() &&
		    oracle->hasConflictingRemoteStores(opt, s))
			continue;
		bool noConflictingLoads = true;
		for (auto it2 = at.content.begin(); noConflictingLoads && it2 != at.content.end(); it2++) {
			if (it2->second.stores.count(*it)) {
				if (debug_use_alias_table)
					printf("Can't remove store l%d because of load l%d\n",
					       stateLabels[*it], stateLabels[it2->first]);
				noConflictingLoads = false;
			}
		}
		if (noConflictingLoads) {
			if (debug_use_alias_table)
				printf("Remove store l%d\n",
				       stateLabels[*it]);
			(*it)->sideEffect = NULL;
			progress = true;
		}
	}
	*done_something |= progress;
	if (debug_use_alias_table) {
		if (progress) {
			printf("Final machine:\n");
			printStateMachine(sm, stdout);
		} else {
			printf("Achieved nothing\n");
		}
	}

	return sm;
}

/* End of namespace */
}

StateMachine *
functionAliasAnalysis(StateMachine *machine, const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something)
{
	return _realias::functionAliasAnalysis(machine, opt, oracle, done_something);
}
