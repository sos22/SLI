#include "sli.h"
#include "state_machine.hpp"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"
#include "maybe.hpp"
#include "control_dependence_graph.hpp"
#include "alloc_mai.hpp"
#include "predecessor_map.hpp"
#include "stacked_cdf.hpp"

namespace _realias {

typedef std::map<const StateMachineState *, int> stateLabelT;

#ifndef NDEBUG
static bool debug_build_stack_layout = false;
static bool debug_build_points_to_table = false;
static bool debug_refine_points_to_table = false;
static bool debug_build_alias_table = false;
static bool debug_refine_alias_table = false;
static bool debug_use_alias_table = false;
static bool debug_gc_frames = false;
static bool debug_enum_backwards = false;
static void enable_debug() __attribute__((unused, used));
static void enable_debug() {
	debug_build_stack_layout = true;
	debug_build_points_to_table = true;
	debug_refine_points_to_table = true;
	debug_build_alias_table = true;
	debug_refine_alias_table = true;
	debug_use_alias_table = true;
	debug_gc_frames = true;
	/* This one is loud enough that if you want it you have to
	 * enable it explicitly: */
	/*debug_enum_backwards = true;*/
}
#else
#define debug_build_stack_layout false
#define debug_build_points_to_table false
#define debug_refine_points_to_table false
#define debug_build_alias_table false
#define debug_refine_alias_table false
#define debug_use_alias_table false
#define debug_gc_frames false
#define debug_enum_backwards false
#endif
#define any_debug (debug_build_stack_layout || debug_build_points_to_table || debug_refine_points_to_table || debug_build_alias_table || debug_refine_alias_table || debug_use_alias_table || debug_enum_backwards || debug_gc_frames)

class AliasTable;

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

#warning Fuck, this is incorrect for multi-threaded machines.  Need to have one StackLayout for each thread.
#if !CONFIG_NO_STATIC_ALIASING
class StackLayout {
public:
	std::vector<FrameId> functions;
	std::vector<exprbdd *> rsps;

	void prettyPrint(FILE *f) const {
		std::vector<const char *> fragments;
		auto it1 = rsps.begin();
		auto it2 = functions.begin();
		while (it1 != rsps.end()) {
			fprintf(f, "%s --- ", it2->name());
			(*it1)->prettyPrint(f);
			it1++;
			it2++;
		}
		fprintf(f, "%s\n", it2->name());
	}

	void sanity_check() const {
#ifndef NDEBUG
		assert(functions.size() == rsps.size() + 1);
		/* No dupes */
		for (auto it1 = functions.begin();
		     it1 != functions.end();
		     it1++) {
			for (auto it2 = it1 + 1;
			     it2 != functions.end();
			     it2++)
				assert(*it1 != *it2);
		}
		for (auto it = rsps.begin(); it != rsps.end(); it++)
			assert(*it);
#endif
	}

	StackLayout()
	{}

	bool operator==(const StackLayout &o) const
	{
		return o.functions == functions && o.rsps == rsps;
	}
	bool operator!=(const StackLayout &o) const
	{
		return !(*this == o);
	}
	
	bool identifyFrameFromPtr(IRExpr *ptr, FrameId *out);
	size_t size() { return rsps.size(); }
};

enum compare_expressions_res {
	compare_expressions_lt,
	compare_expressions_eq,
	compare_expressions_gt,
	compare_expressions_unknown
};

/* This has to be non-static because it's invoked from a template.
   Why do template parameters have to be non-static?  Nobody seems to
   know. */
static compare_expressions_res
compare_expressions(IRExpr *a, IRExpr *b)
{
	assert(a->type() == Ity_I64);
	assert(b->type() == Ity_I64);
	struct reg_plus_offset {
		threadAndRegister tr;
		long offset;
		reg_plus_offset(const IRExpr *ex)
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
					offset = ((IRExprConst *)a->contents[0])->Ico.content.U64;
				}
			}
		}
	} as(a), bs(b);
	if (!as.tr.isValid() ||
	    !bs.tr.isValid() ||
	    as.tr != bs.tr)
		return compare_expressions_unknown;
	if (as.offset < bs.offset)
		return compare_expressions_lt;
	else if (as.offset == bs.offset)
		return compare_expressions_eq;
	else
		return compare_expressions_gt;
}

static compare_expressions_res
compare_expressions(IRExpr *a, const exprbdd *b)
{
	compare_expressions_res r = compare_expressions_unknown;
	std::set<const exprbdd *> visited;
	std::vector<const exprbdd *> q;
	q.push_back(b);
	while (!q.empty()) {
		const exprbdd *n = q.back();
		q.pop_back();
		if (!visited.insert(n).second) {
			continue;
		}
		if (n->isLeaf()) {
			compare_expressions_res r2 = compare_expressions(a, n->leaf());
			if (r != compare_expressions_unknown) {
				r = r2;
			} else if (r != r2) {
				return compare_expressions_unknown;
			}
		} else {
			q.push_back(n->internal().trueBranch);
			q.push_back(n->internal().falseBranch);
		}
	}
	return r;
}

bool
StackLayout::identifyFrameFromPtr(IRExpr *ptr, FrameId *out)
{
	if (TIMEOUT)
		return false;
	*out = FrameId();
	bool definitelyStack = false;
	assert(ptr->type() == Ity_I64);
	auto it2 = functions.begin();
	for (auto it = rsps.begin(); it != rsps.end(); it++) {
		exprbdd *rsp = *it;
		switch (compare_expressions(ptr, rsp)) {
		case compare_expressions_gt:
		case compare_expressions_eq:
			*out = *it2;
			return true;
		case compare_expressions_lt:
			definitelyStack = true;
			break;
		case compare_expressions_unknown:
			return false;
		}
		it2++;
	}
	if (rsps.size() == 0 || definitelyStack) {
		/* It's definitely on the stack, and it doesn't fit
		   into any of the delimited frames -> it must be the
		   root frame. */
		*out = functions.back();
		return true;
	}

	return false;
}

class StackLayoutTable {
	std::map<StateMachineState *, Maybe<StackLayout> > content;
	bool updateLayout(StateMachineState *s, const Maybe<StackLayout> &newLayout);
public:
	std::map<Maybe<FrameId>, PointerAliasingSet> initialLoadAliasing;
	StackLayoutTable()
	{}
	bool build(StateMachine *inp);
	void prettyPrint(FILE *f, const stateLabelT &labels) const {
		for (auto it = content.begin(); it != content.end(); it++) {
			auto i = labels.find(it->first);
			assert(i != labels.end());
			fprintf(f, "%d: ", i->second);
			if (it->second.valid)
				it->second.content.prettyPrint(f);
			else
				fprintf(f, "<none>");
		}
	}
	void sanity_check() const {
#ifndef NDEBUG
		for (auto it = content.begin();
		     it != content.end();
		     it++) {
			assert(it->first);
			if (it->second.valid)
				it->second.content.sanity_check();
		}
#endif
	}
	Maybe<StackLayout> *forState(StateMachineState *s)
	{
		auto it = content.find(s);
		if (it == content.end())
			return NULL;
		else
			return &it->second;
	}
	Maybe<StackLayout> *initialStackLayout(StateMachine *sm)
	{
		/* XXX could do better than this.  We can often derive
		   the initial stack layout for a state even when the
		   layout for the root is indeterminate. */
		return forState(sm->root);
	}
};

bool
StackLayoutTable::updateLayout(StateMachineState *s, const Maybe<StackLayout> &newLayout)
{
	auto it_did_insert = content.insert(std::pair<StateMachineState *, Maybe<StackLayout> >(s, newLayout));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		return true;
	if (!it->second.valid)
		return false;
	if (!newLayout.valid) {
		it->second = newLayout;
		return true;
	}
	if (it->second.content == newLayout.content)
		return false;
	it->second = Maybe<StackLayout>::nothing();
	return true;
}

bool
StackLayoutTable::build(StateMachine *inp)
{
	std::map<FrameId, exprbdd *> frameBoundaries;
	{
		std::set<StateMachineSideEffectStartFunction *> startFunctions;
		std::set<StateMachineSideEffectEndFunction *> endFunctions;
		enumSideEffects(inp, startFunctions);
		enumSideEffects(inp, endFunctions);
		for (auto it = startFunctions.begin(); it != startFunctions.end(); it++) {
			auto it2_did_insert = frameBoundaries.insert(
				std::pair<FrameId, exprbdd*>
				( (*it)->frame, (*it)->rsp ));
			auto it2 = it2_did_insert.first;
			auto did_insert = it2_did_insert.second;
			if (!did_insert &&
			    it2->second != (*it)->rsp) {
				if (debug_build_stack_layout) {
					printf("Cannot build stack layout because %p != %p\n",
					       it2->second,
					       (*it)->rsp);
					printf("arg1 = ");
					it2->second->prettyPrint(stdout);
					printf("arg2 = ");
					(*it)->rsp->prettyPrint(stdout);
				}
				return false;
			}
		}
		for (auto it = endFunctions.begin(); it != endFunctions.end(); it++) {
			auto it2_did_insert = frameBoundaries.insert(
				std::pair<FrameId, exprbdd*>
				( (*it)->frame, (*it)->rsp ));
			auto it2 = it2_did_insert.first;
			auto did_insert = it2_did_insert.second;
			if (!did_insert &&
			    it2->second != (*it)->rsp) {
				if (debug_build_stack_layout) {
					printf("Cannot build stack layout because %p != %p (EndFunction)\n",
					       it2->second,
					       (*it)->rsp);
					printf("arg1 = ");
					it2->second->prettyPrint(stdout);
					printf("arg2 = ");
					(*it)->rsp->prettyPrint(stdout);
				}
				return false;
			}
		}
	}
	if (debug_build_stack_layout) {
		printf("Frame -> RSP correspondence:\n");
		for (auto it = frameBoundaries.begin();
		     it != frameBoundaries.end();
		     it++) {
			printf("\t%s -> ", it->first.name());
			it->second->prettyPrint(stdout);
		}
	}
	std::queue<StateMachineState *> needingUpdate;
	enumStates(inp, &needingUpdate);
	while (!needingUpdate.empty()) {
		StateMachineState *s = needingUpdate.front();
		needingUpdate.pop();
		StateMachineSideEffect *se = s->getSideEffect();
		bool haveExitLayout;
		Maybe<StackLayout> exitLayout(Maybe<StackLayout>::nothing());
		if (se && se->type == StateMachineSideEffect::StackLayout) {
			auto l = (StateMachineSideEffectStackLayout *)se;
			bool failed = false;
			haveExitLayout = true;
			exitLayout.valid = true;
			exitLayout.content = StackLayout();
			exitLayout.content.functions.resize(l->functions.size(), FrameId());
			exitLayout.content.rsps.resize(l->functions.size() - 1);
			for (unsigned x = 1; x < l->functions.size(); x++) {
				if (frameBoundaries.count(l->functions[x].frame) == 0) {
					failed = true;
					break;
				}
				exitLayout.content.functions[x] = l->functions[x].frame;
				exitLayout.content.rsps[x-1] = frameBoundaries[l->functions[x].frame];
			}
			if (failed) {
				exitLayout.valid = false;
			} else {
				exitLayout.content.functions[0] = l->functions.front().frame;
			}
		} else {
			auto it = content.find(s);
			if (it == content.end()) {
				haveExitLayout = false;
			} else {
				haveExitLayout = true;
				exitLayout = it->second;
				if (exitLayout.valid) {
					if (se && se->type == StateMachineSideEffect::StartFunction) {
						auto sf = (StateMachineSideEffectStartFunction *)se;
						exitLayout.content.functions.push_back(sf->frame);
						exitLayout.content.rsps.push_back(sf->rsp);
						assert(frameBoundaries.count(exitLayout.content.functions.back()));
						assert(exitLayout.content.rsps.back() ==
						       frameBoundaries[exitLayout.content.functions.back()]);
					} else if (se && se->type == StateMachineSideEffect::EndFunction) {
						if (exitLayout.content.rsps.empty()) {
							exitLayout.valid = false;
						} else {
							auto sf = (StateMachineSideEffectStartFunction *)se;
							assert(exitLayout.content.functions.back() == sf->frame);
							assert(exitLayout.content.rsps.back() == sf->rsp);
							exitLayout.content.functions.pop_back();
							exitLayout.content.rsps.pop_back();
						}
					}
				}
			}
		}

		if (haveExitLayout) {
			std::vector<StateMachineState *> succ;
			s->targets(succ);
			for (auto it = succ.begin(); it != succ.end(); it++) {
				if (updateLayout(*it, exitLayout))
					needingUpdate.push(*it);
			}
		}
	}

	PointerAliasingSet baseInitialLoadAliasing = PointerAliasingSet::nonStackPointer | PointerAliasingSet::notAPointer;
	std::set<StateMachineSideEffectStackLayout *> layouts;
	enumSideEffects(inp, layouts);
	for (auto it = layouts.begin(); it != layouts.end(); it++) {
		for (auto it2 = (*it)->functions.begin(); it2 != (*it)->functions.end(); it2++)
			if (it2->pointedAtByOthers)
				baseInitialLoadAliasing |= PointerAliasingSet::frame(it2->frame);
	}
	initialLoadAliasing[Maybe<FrameId>::nothing()] = baseInitialLoadAliasing;

	for (auto it = layouts.begin(); it != layouts.end(); it++) {
		for (auto it2 = (*it)->functions.begin(); it2 != (*it)->functions.end(); it2++) {
			auto it3_did_insert = initialLoadAliasing.insert(
				std::pair<Maybe<FrameId>, PointerAliasingSet>(
					Maybe<FrameId>::just(it2->frame),
					baseInitialLoadAliasing));
			auto it3 = it3_did_insert.first;
			if (it2->pointsAtSelf)
				initialLoadAliasing[Maybe<FrameId>::just(it2->frame)] |=
					PointerAliasingSet::frame(it2->frame);
		}
	}

	sanity_check();
	return true;
}

class PointsToTable {
	std::map<threadAndRegister, PointerAliasingSet> content;
	PointerAliasingSet getInitialLoadAliasing(IRExpr *addr,
						  StackLayoutTable &slt,
						  StateMachine *machine);
	PointerAliasingSet getInitialLoadAliasing(exprbdd *addr,
						  StackLayoutTable &slt,
						  StateMachine *machine);

	PointerAliasingSet pointsToSetForExpr(IRExpr *e,
					      Maybe<StackLayout> *sl,
					      StackLayoutTable &slt,
					      StateMachine *machine);
public:
	PointerAliasingSet pointsToSetForExpr(exprbdd *e,
					      Maybe<StackLayout> *sl,
					      StackLayoutTable &slt,
					      StateMachine *machine);
	bool build(StateMachine *sm);
	void prettyPrint(FILE *f);
	void sanity_check() const {
		for (auto it = content.begin(); it != content.end(); it++)
			assert(it->first.isValid());
	}
	PointsToTable refine(AliasTable &at,
			     StateMachine *sm,
			     StackLayoutTable &slt,
			     bool *done_something);
};

PointerAliasingSet
PointsToTable::getInitialLoadAliasing(IRExpr *addr,
				      StackLayoutTable &slt,
				      StateMachine *machine)
{
	Maybe<StackLayout> *sl = slt.initialStackLayout(machine);
	PointerAliasingSet addrPts(pointsToSetForExpr(addr,
						      sl,
						      slt,
						      machine));
	PointerAliasingSet res = PointerAliasingSet::nonStackPointer | PointerAliasingSet::notAPointer;
	if (!addrPts.valid || addrPts.otherStackPointer) {
		for (auto it = slt.initialLoadAliasing.begin();
		     it != slt.initialLoadAliasing.end();
		     it++) {
			if (it->first.valid)
				res |= it->second;
		}
	} else {
		for (auto it = addrPts.stackPointers.begin();
		     it != addrPts.stackPointers.end();
		     it++) {
			if (slt.initialLoadAliasing.count(Maybe<FrameId>::just(*it)))
				res |= slt.initialLoadAliasing[Maybe<FrameId>::just(*it)];
			else
				return PointerAliasingSet::anything;
		}
	}
	if (addrPts.mightPointAtNonStack())
		res |= slt.initialLoadAliasing[Maybe<FrameId>::nothing()];
	return res;
}

PointerAliasingSet
PointsToTable::pointsToSetForExpr(IRExpr *e,
				  Maybe<StackLayout> *sl,
				  StackLayoutTable &slt,
				  StateMachine *machine)
{
	if (e->type() != Ity_I64)
		return PointerAliasingSet();
	switch (e->tag) {
	case Iex_Get: {
		IRExprGet *iex = (IRExprGet *)e;
		if (!content.count(iex->reg)) {
			/* This can actually happen sometimes during
			   optimisation if, for instance, we determine
			   that a load is definitely going to
			   dereference a bad pointer and is replaced
			   by an <unreached> side effect.  The
			   temporary targeted by the load is then left
			   uninitialised.  The optimiser will later
			   remove all references to it, so it's not
			   actually a problem, but we can sometimes
			   see the intermediate state due to phase
			   ordering problems.  Just do something
			   vaguely sensible. */
			return PointerAliasingSet::nothing;
		} else {
			return content[iex->reg];
		}
	}

	case Iex_Load: {
		IRExprLoad *iel = (IRExprLoad *)e;
		return getInitialLoadAliasing(iel->addr, slt, machine);
	}
	case Iex_Const:
		return PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer;
	case Iex_Associative: {
		IRExprAssociative *iex = (IRExprAssociative *)e;
		if (sl &&
		    sl->valid &&
		    iex->op == Iop_Add64 &&
		    iex->nr_arguments == 2 &&
		    iex->contents[0]->tag == Iex_Const &&
		    iex->contents[1]->tag == Iex_Get &&
		    ((IRExprGet *)iex->contents[1])->reg.isReg() &&
		    ((IRExprGet *)iex->contents[1])->reg.asReg() == OFFSET_amd64_RSP) {
			FrameId f;
			if (sl->content.identifyFrameFromPtr(iex, &f))
				return PointerAliasingSet::frame(f);
		}
		if (iex->op == Iop_Add64) {
			PointerAliasingSet res(PointerAliasingSet::nothing);
			for (int i = 0; i < iex->nr_arguments; i++)
				res |= pointsToSetForExpr(iex->contents[i], sl, slt, machine);
			return res;
		}

		break;
	}
	default:
		break;
	}
	return PointerAliasingSet::anything;
}

PointerAliasingSet
PointsToTable::getInitialLoadAliasing(exprbdd *addr,
				      StackLayoutTable &slt,
				      StateMachine *machine)
{
	PointerAliasingSet acc(PointerAliasingSet::nothing);
	std::set<exprbdd *> visited;
	std::vector<exprbdd *> q;
	q.push_back(addr);
	while (!q.empty()) {
		exprbdd *ee = q.back();
		q.pop_back();
		if (!visited.insert(ee).second)
			continue;
		if (ee->isLeaf()) {
			acc |= getInitialLoadAliasing(ee->leaf(), slt, machine);
		} else {
			q.push_back(ee->internal().trueBranch);
			q.push_back(ee->internal().falseBranch);
		}
	}
	return acc;
}

PointerAliasingSet
PointsToTable::pointsToSetForExpr(exprbdd *e,
				  Maybe<StackLayout> *sl,
				  StackLayoutTable &slt,
				  StateMachine *machine)
{
	PointerAliasingSet acc(PointerAliasingSet::nothing);
	std::set<exprbdd *> visited;
	std::vector<exprbdd *> q;
	q.push_back(e);
	while (!q.empty()) {
		exprbdd *ee = q.back();
		q.pop_back();
		if (!visited.insert(ee).second)
			continue;
		if (ee->isLeaf()) {
			acc |= pointsToSetForExpr(ee->leaf(), sl, slt, machine);
		} else {
			q.push_back(ee->internal().trueBranch);
			q.push_back(ee->internal().falseBranch);
		}
	}
	return acc;
}

bool
PointsToTable::build(StateMachine *sm)
{
	PointerAliasingSet defaultTmpPointsTo(PointerAliasingSet::anything);
	std::set<StateMachineSideEffect *> sideEffects;
	enumSideEffects(sm, sideEffects);
	if (TIMEOUT)
		return false;
	for (auto it = sideEffects.begin(); it != sideEffects.end(); it++) {
		threadAndRegister tr(threadAndRegister::invalid());
		if ( (*it)->definesRegister(tr) )
			content.insert(std::pair<threadAndRegister, PointerAliasingSet>(tr, defaultTmpPointsTo));
	}
	sanity_check();
	return true;
}

void
PointsToTable::prettyPrint(FILE *f)
{
	for (auto it = content.begin(); it != content.end(); it++)
		fprintf(f, "\t%s\t%s\n", it->first.name(), it->second.name());
}
#endif

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
};

class AliasTable {
public:
	std::map<StateMachineSideEffecting *, AliasTableEntry> content;
	bool build(const MaiMap &decode,
		   StateMachine *sm,
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
			if ( ((StateMachineSideEffectLoad *)it->first->getSideEffect())->target == tr )
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
#if !CONFIG_NO_STATIC_ALIASING
	void refine(PointsToTable &ptt,
		    StackLayoutTable &slt,
		    StateMachine *sm,
		    bool *done_something,
		    stateLabelT &labels);
#endif
};

static bool
mightLoadInitialValue(StateMachineSideEffecting *smse,
		      StateMachine *sm,
		      OracleInterface *oracle,
		      const MaiMap &decode,
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
			StateMachineSideEffectMemoryAccess *store = (StateMachineSideEffectMemoryAccess *)s->getSideEffect();
			/* Note that checking the oracle is
			   *mandatory* here.  Otherwise, when the
			   oracle is incomplete we end up with an
			   inconsistency between here and the alias
			   table, and that leads to lots of bad things
			   happening. */
			if (store->_type() == load->_type() &&
			    oracle->memoryAccessesMightAlias(decode, opt, load, store) &&
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
AliasTable::build(const MaiMap &decode,
		  StateMachine *sm,
		  stateLabelT &labels,
		  const AllowableOptimisations &opt,
		  OracleInterface *oracle)
{
	/* First figure out where the accesses might reach from a
	 * simple control-flow perspective. */
	/* Map from states to all of the memory access side effect
	 * states which might happen before that state. */
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
			StateMachineSideEffectStore *acc = (StateMachineSideEffectStore *)s->getSideEffect();
			/* Kill off anything which we definitely clobber */
			for (auto it = exitReaching.begin();
			     it != exitReaching.end();
				) {
				assert((*it)->getSideEffect());
				StateMachineSideEffectMemoryAccess *other =
					dynamic_cast<StateMachineSideEffectMemoryAccess *>((*it)->getSideEffect());
				assert(other);
				if (other->_type() == acc->_type() &&
				    definitelyEqual(acc->addr, other->addr, opt)) {
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
			/* The condition on types is unsound, but it's
			   what eval_state_machine does. */
#warning unsound
			if (oracle->memoryAccessesMightAlias(decode, opt, smsel, smses) &&
			    smsel->type <= smses->_type()) {
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
		if (TIMEOUT) {
			return false;
		}
		assert(it->first->type == StateMachineState::SideEffecting);
		StateMachineSideEffecting *smse = (StateMachineSideEffecting *)it->first;
		StateMachineSideEffect *se = smse->getSideEffect();
		assert(se);
		assert(se->type == StateMachineSideEffect::Load);
		StateMachineSideEffectLoad *l = (StateMachineSideEffectLoad *)se;
		bool mightHaveExternalStores =
			!opt.assumeNoInterferingStores() &&
			oracle->hasConflictingRemoteStores(decode, opt, l);
		content.insert(std::pair<StateMachineSideEffecting *, AliasTableEntry>(
				       smse,
				       AliasTableEntry(it->second,
						       mightHaveExternalStores,
						       mightLoadInitialValue(smse, sm, oracle, decode, opt))));
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

#if !CONFIG_NO_STATIC_ALIASING
static StateMachineSideEffecting *
sideEffectDefiningRegister(StateMachine *sm, const threadAndRegister &tr)
{
	std::vector<StateMachineSideEffecting *> sideEffects;
	enumStates(sm, &sideEffects);
	threadAndRegister tr2(threadAndRegister::invalid());
	for (auto it = sideEffects.begin(); it != sideEffects.end(); it++) {
		if ((*it)->getSideEffect() &&
		    (*it)->getSideEffect()->definesRegister(tr2) &&
		    tr == tr2)
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
#ifndef NDEBUG
		{
			threadAndRegister tr(threadAndRegister::invalid());
			assert(effect->definesRegister(tr));
			assert(tr == it->first);
		}
#endif
		PointerAliasingSet newPts(PointerAliasingSet::nothing);
		Maybe<StackLayout> *sl = slt.forState(smse);
		switch (effect->type) {
		case StateMachineSideEffect::Load: {
			const AliasTableEntry &e(at.storesForLoad(smse));
			if (e.mightHaveExternalStores)
				newPts |= PointerAliasingSet::nonStackPointer;
			if (e.mightLoadInitial)
				newPts |= getInitialLoadAliasing( ((StateMachineSideEffectLoad *)effect)->addr,
								  slt, sm);
			for (auto it2 = e.stores.begin(); it2 != e.stores.end(); it2++) {
				StateMachineSideEffecting *satisfierState = *it2;
				StateMachineSideEffect *satisfier = satisfierState->sideEffect;
				assert(satisfier);
				assert(satisfier->type == StateMachineSideEffect::Store);
				newPts |=
					pointsToSetForExpr(
						((StateMachineSideEffectStore *)satisfier)->data,
						sl,
						slt,
						sm);
			}

			/* A load can only load from a frame if the
			   frame is actually live at the time of the
			   load. */
			if (newPts.valid &&
			    !newPts.otherStackPointer &&
			    sl &&
			    sl->valid) {
				for (auto it = newPts.stackPointers.begin();
				     it != newPts.stackPointers.end();
					) {
					bool present = false;
					for (auto it2 = sl->content.functions.begin();
					     !present && it2 != sl->content.functions.end();
					     it2++) {
						if (*it2 == *it)
							present = true;
					}
					if (present) {
						it++;
					} else {
						it = newPts.stackPointers.erase(it);
					}
				}
			}
			break;
		}
		case StateMachineSideEffect::Copy: {
			StateMachineSideEffectCopy *c = (StateMachineSideEffectCopy *)effect;
			newPts = pointsToSetForExpr(c->value, sl, slt, sm);
			break;
		}
		case StateMachineSideEffect::Phi: {
			StateMachineSideEffectPhi *p = (StateMachineSideEffectPhi *)effect;
			for (auto it = p->generations.begin();
			     it != p->generations.end();
			     it++)
				newPts |= pointsToSetForExpr(it->val, sl, slt, sm);
			break;
		}
		case StateMachineSideEffect::ImportRegister: {
			StateMachineSideEffectImportRegister *r =
				(StateMachineSideEffectImportRegister *)effect;
			newPts = r->set;
			break;
		}

		case StateMachineSideEffect::Store:
		case StateMachineSideEffect::Unreached:
		case StateMachineSideEffect::AssertFalse:
		case StateMachineSideEffect::StartAtomic:
		case StateMachineSideEffect::EndAtomic:
		case StateMachineSideEffect::StartFunction:
		case StateMachineSideEffect::EndFunction:
		case StateMachineSideEffect::StackLayout:
			/* These aren't supposed to define registers */
			abort();
		}
		newPts = newPts & it->second;
		if (newPts != it->second)
			*done_something = true;
		assert(!res.content.count(it->first));
		res.content.insert(std::pair<threadAndRegister, PointerAliasingSet>(it->first, newPts));
	}
	return res;
}

void
AliasTable::refine(PointsToTable &ptt,
		   StackLayoutTable &slt,
		   StateMachine *sm,
		   bool *done_something,
		   stateLabelT &labels)
{
	for (auto it = content.begin();
	     it != content.end();
	     it++) {
		StateMachineSideEffectLoad *l = (StateMachineSideEffectLoad *)it->first->getSideEffect();
		Maybe<StackLayout> *sl = slt.forState(it->first);
		PointerAliasingSet loadPts(
			ptt.pointsToSetForExpr(
				l->addr,
				sl,
				slt,
				sm));
		if (debug_refine_alias_table)
			printf("Examining alias table for state %d (currently %s)\n",
			       labels[it->first], loadPts.name());
		for (auto it2 = it->second.stores.begin();
		     it2 != it->second.stores.end();
			) {
			assert( (*it2)->getSideEffect() );
			assert( (*it2)->getSideEffect()->type == StateMachineSideEffect::Store );
			Maybe<StackLayout> *sl2 = slt.forState(*it2);
			PointerAliasingSet storePts(
				ptt.pointsToSetForExpr( ((StateMachineSideEffectStore *)(*it2)->getSideEffect())->addr,
							sl2,
							slt,
							sm));
			if (storePts.overlaps(loadPts)) {
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
#endif

/* Enumerate all of the states which can reach @startFrom, starting
   from the root, such that by the time state T is enumerated all of
   the predecessors of T have already been enumerated.  That's a bit
   like a breadth-first enumeration, in the sense that all of the
   nodes at depth N will be enumerated before we start enumerating
   things at depth N+1, if you define the depth of a node to be the
   length of the longest path from the root to that node. */
static void
breadthFirstEnumBackwards(const predecessor_map &pm,
			  StateMachineState *startFrom,
			  StateMachineState *root,
			  std::vector<StateMachineState *> &out,
			  std::map<const StateMachineState *, int> &labels)
{
	if (debug_enum_backwards) {
		printf("Enum backwards from l%d to l%d\n", labels[startFrom],
		       labels[root]);
	}

	/* Map from states to the number of predecessors of that node
	   which have not yet been enumerated.  Only contains entries
	   for states which can reach @startFrom. */
	std::map<StateMachineState *, int> neededPredecessors;
	std::vector<StateMachineState *> pending;
	pending.push_back(startFrom);
	while (!pending.empty()) {
		StateMachineState *s = pending.back();
		pending.pop_back();
		auto it_did_insert = neededPredecessors.insert(std::pair<StateMachineState *, int>(s, -99));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (!did_insert) {
			/* Already did this one. */
			continue;
		}
		std::vector<StateMachineState *> pred;
		pm.getPredecessors(s, pred);
		it->second = pred.size();
		if (pred.size() == 0) {
			assert(s == root);
		}
		if (debug_enum_backwards) {
			printf("l%d has %zd predecessors\n", 
			       labels[s], pred.size());
		}

		for (auto it = pred.begin(); it != pred.end(); it++)
			pending.push_back(*it);
	}

	/* Now do the actual enumeration, starting from the root. */
	out.reserve(neededPredecessors.size());
	assert(neededPredecessors.count(root));
	assert(neededPredecessors[root] == 0);
	pending.push_back(root);
#ifndef NDEBUG
	std::set<StateMachineState *> emitted;
#endif
	while (!pending.empty()) {
		StateMachineState *s = pending.back();
		pending.pop_back();
		assert(neededPredecessors.count(s));
		assert(neededPredecessors[s] == 0);
#ifndef NDEBUG
		assert(!emitted.count(s));
		emitted.insert(s);
#endif
		out.push_back(s);

		if (debug_enum_backwards) {
			printf("Emit l%d\n", labels[s]);
		}

		std::vector<StateMachineState *> targs;
		s->targets(targs);
		for (auto it = targs.begin(); it != targs.end(); it++) {
			StateMachineState *target = *it;
			auto it2 = neededPredecessors.find(target);
			if (it2 == neededPredecessors.end()) {
				/* This successor can never reach
				 * @startFrom -> ignore it */
				continue;
			}
			assert(it2->second > 0);
			it2->second--;
			if (debug_enum_backwards) {
				printf("Dismiss l%d -> l%d; l%d has %d predecessors left\n",
				       labels[s], labels[target],
				       labels[target],
				       it2->second);
			}
			if (it2->second == 0) {
				/* All predecessors of this target
				   emitted -> emit the target. */
				pending.push_back(target);
			}
		}
	}

#ifndef NDEBUG
	if (emitted.size() != neededPredecessors.size()) {
		printf("Whoops, failed to emit all needed states\n");
		printf("Emitted extras: ");
		for (auto it = emitted.begin(); it != emitted.end(); it++) {
			if (!neededPredecessors.count(*it)) {
				printf("l%d ", labels[*it]);
			}
		}
		printf("\nFailed to emit: ");
		for (auto it = neededPredecessors.begin(); it != neededPredecessors.end(); it++) {
			if (!emitted.count(it->first)) {
				printf("l%d ", labels[it->first]);
			}
		}
		printf("\nLeft-over predecessors: ");
		for (auto it = neededPredecessors.begin(); it != neededPredecessors.end(); it++) {
			if (it->second != 0) {
				printf("l%d(%d) ", labels[it->first], it->second);
			}
		}
		printf("\n");
		abort();
	}
#endif
}

static exprbdd *
dataOfSideEffect(SMScopes *scopes, const StateMachineSideEffect *s_effect, IRType ty)
{
	exprbdd *res;
	if (s_effect->type == StateMachineSideEffect::Store) {
		res = ((StateMachineSideEffectStore *)s_effect)->data;
	} else if (s_effect->type == StateMachineSideEffect::Load) {
		res = exprbdd::var(
			&scopes->exprs,
			&scopes->bools,
			IRExpr_Get(
				((StateMachineSideEffectLoad *)s_effect)->target,
				((StateMachineSideEffectLoad *)s_effect)->type));
	} else if (s_effect->type == StateMachineSideEffect::Copy) {
		res = ((StateMachineSideEffectCopy *)s_effect)->value;
	} else {
		abort();
	}
	return exprbdd::coerceTypes(&scopes->exprs, &scopes->bools, ty, res);
}

static StateMachine *
functionAliasAnalysis(SMScopes *scopes, const MaiMap &decode, StateMachine *sm,
		      const AllowableOptimisations &opt, OracleInterface *oracle,
		      control_dependence_graph &cdg,
		      predecessor_map &predMap,
		      bool *done_something)
{
	stateLabelT stateLabels;
	if (any_debug) {
		printf("%s, input:\n", __func__);
		printStateMachine(sm, stdout, stateLabels);
	}
#if !CONFIG_NO_STATIC_ALIASING
	StackLayoutTable stackLayout;
	if (!stackLayout.build(sm)) {
		warning("Failed to build stack layout!\n");
		return sm;
	}
	if (debug_build_stack_layout) {
		printf("Stack layout table:\n");
		stackLayout.prettyPrint(stdout, stateLabels);
	}

	PointsToTable ptt;
	if (!ptt.build(sm)) {
		warning("Failed to build points-to table!\n");
		return sm;
	}
	if (debug_build_points_to_table) {
		printf("Points-to table:\n");
		ptt.prettyPrint(stdout);
	}
#endif

	AliasTable at;
	if (!at.build(decode, sm, stateLabels, opt, oracle)) {
		warning("Failed to build alias table!\n");
		return sm;
	}
	if (debug_build_alias_table) {
		printf("Alias table:\n");
		at.prettyPrint(stdout, stateLabels);
	}

#if !CONFIG_NO_STATIC_ALIASING
	while (1) {
		bool p = false;
		PointsToTable ptt2 = ptt.refine(at, sm, stackLayout, &p);

		if (p && debug_refine_points_to_table) {
			printf("Refined points-to table:\n");
			ptt2.prettyPrint(stdout);
		}
		ptt = ptt2;

		bool p2 = false;
		at.refine(ptt, stackLayout, sm, &p2, stateLabels);
		p |= p2;

		if (p2 && debug_refine_alias_table) {
			printf("Refined alias table:\n");
			at.prettyPrint(stdout, stateLabels);
		}

		if (!p)
			break;
	}
	if (any_debug) {
		printf("Final points-to table:\n");
		ptt.prettyPrint(stdout);
		printf("Final alias table:\n");
		at.prettyPrint(stdout, stateLabels);
	}
#endif

	bool progress = false;
	bool killedAllLoads = true;

	/* Use the aliasing table to resolve loads wherever possible. */
	for (auto it = at.content.begin(); it != at.content.end(); it++) {
		assert(it->first->getSideEffect());
		assert(it->first->getSideEffect()->type == StateMachineSideEffect::Load);
		StateMachineSideEffectLoad *l = (StateMachineSideEffectLoad *)it->first->getSideEffect();
		if (it->second.mightHaveExternalStores) {
			killedAllLoads = false;
			continue;
		}

		if (debug_use_alias_table) {
			printf("Trying to remove load at l%d\n",
			       stateLabels[it->first]);
		}

		/* A couple of easy special cases: */
		if (it->second.stores.size() == 0) {
			/* Load always loads initial memory value. */
			assert(it->second.mightLoadInitial);
			if (debug_use_alias_table)
				printf("Replace l%d with initial load\n",
                                      stateLabels[it->first]);
			progress = true;
			it->first->sideEffect =
				new StateMachineSideEffectCopy(
					l->target,
					exprbdd::load(
						&scopes->exprs,
						&scopes->bools,
						l->type,
						l->addr));
			StateMachineState *t =
				new StateMachineSideEffecting(
					it->first->dbg_origin,
					new StateMachineSideEffectAssertFalse(
						exprbdd::to_bbdd(
							&scopes->bools,
							exprbdd::unop(
								&scopes->exprs,
								&scopes->bools,
								Iop_BadPtr,
								l->addr)),
						true),
					it->first->target);
			predMap.removePredecessor(it->first->target, it->first);
			predMap.addPredecessor(t, it->first);
			predMap.addPredecessor(it->first->target, t);
			cdg.introduceState(t, cdg.domOf(it->first));
			it->first->target = t;
			continue;
		} else if (it->second.stores.size() == 1 &&
			   !it->second.mightLoadInitial) {
			/* Load always loads from one specific store. */
			StateMachineSideEffecting *s_state = *it->second.stores.begin();
			StateMachineSideEffect *s_effect = s_state->getSideEffect();
			if (debug_use_alias_table)
				printf("Replace l%d with forward from l%d\n",
				       stateLabels[it->first], stateLabels[s_state]);
			assert(s_effect);
			progress = true;
			exprbdd *d = dataOfSideEffect(scopes, s_effect, l->type);
			it->first->sideEffect =
				new StateMachineSideEffectCopy(
					l->target, d);
			continue;
		} else if (!it->second.mightLoadInitial) {
			/* Maybe the CDG can show that only one store
			   is ever present on any path from the root
			   to the load?  In that case, we don't need
			   to do the more complicated path-dependent
			   algorithm. */
			exprbdd::enablingTableT possibleInputs;
			bool failed = false;
			exprbdd *defaultVal = NULL;
			bbdd *stateDominator = cdg.domOf(it->first);

			/* CDG optimiseation should have eliminated
			   all unreachable states already. */
			assert(stateDominator != scopes->bools.cnst(false));
			for (auto it2 = it->second.stores.begin();
			     !failed && it2 != it->second.stores.end();
			     it2++) {
				bbdd *gate = bbdd::assume(&scopes->bools, cdg.domOf(*it2), stateDominator);
				if (!gate)
					continue;
				exprbdd *val = dataOfSideEffect(scopes, (*it2)->sideEffect, l->type);
				defaultVal = val;
				exprbdd **slot = possibleInputs.getSlot(gate, val);
				if (*slot != val) {
					if (debug_use_alias_table) {
						printf("Can't do quick load resolution because of conflict detected at l%d\n",
						       stateLabels[*it2]);
					}
					failed = true;
				}
			}
			assert(defaultVal != NULL);
			if (!failed) {
				exprbdd *res = exprbdd::from_enabling(
					&scopes->exprs,
					possibleInputs,
					defaultVal);
				if (res) {
					if (debug_use_alias_table) {
						printf("Replace l%d with simple mux:\n",
						       stateLabels[it->first]);
						res->prettyPrint(stdout);
					}
					it->first->sideEffect =
						new StateMachineSideEffectCopy(
							l->target, res);
					progress = true;
					continue;
				}
			}
		}

		if (CONFIG_REALIAS_SIMPLE_ONLY) {
			if (debug_use_alias_table) {
				printf("Simple rules failed, giving up.\n");
			}
			killedAllLoads = false;
			continue;
		}

		if (debug_use_alias_table) {
			printf("All simple rules failed, applying full load elimination rule.\n");
		}

		/* Map from states to what we'd load if we issued the
		   load immediately after that state. */
		std::map<StateMachineState *, exprbdd *> replacements;

		/* Bit of a hack: treat NULL as a special initial
		   state which executes immediately before the machine
		   starts. */
		replacements[NULL] =
			exprbdd::load(
				&scopes->exprs,
				&scopes->bools,
				l->type,
				l->addr);

		/* Figure out what order to visit states in so as to
		 * avoid revisiting any states. */
		std::vector<StateMachineState *> statesToVisit;
		breadthFirstEnumBackwards(predMap, it->first, sm->root, statesToVisit, stateLabels);

		if (debug_use_alias_table) {
			printf("State visit order: ");
			for (auto it = statesToVisit.begin();
			     it != statesToVisit.end();
			     it++)
				printf("l%d ", stateLabels[*it]);
			printf("\n");
		}
		for (auto it2 = statesToVisit.begin();
		     it2 != statesToVisit.end();
		     it2++) {
			StateMachineState *state = *it2;
			assert(!replacements.count(state));

			if (debug_use_alias_table) {
				printf("Consider state l%d\n", stateLabels[state]);
			}

			std::vector<StateMachineState *> predecessors;
			predMap.getPredecessors(state, predecessors);
#ifndef NDEBUG
			for (auto it3 = predecessors.begin();
			     it3 != predecessors.end();
			     it3++) {
				assert(replacements.count(*it3));
			}
#endif
			bbdd *assumption = cdg.domOf(state);
			if (assumption == scopes->bools.cnst(false)) {
				/* This state is completely
				   unreachable.  Hmm.  That should
				   have been dealt with by the CDG
				   optimisation already. */
				if (debug_use_alias_table) {
					printf("Failed because state l%d is unreachable?\n",
					       stateLabels[state]);
				}
				if (!TIMEOUT)
					abort();
				return sm;
			}
			if (state == sm->root) {
				predecessors.push_back(NULL);
			}
			exprbdd::enablingTableT tabAtStartOfState;
			for (auto it3 = predecessors.begin();
			     it3 != predecessors.end();
			     it3++) {
				StateMachineState *predState = *it3;
				bbdd *condition, *c;
				if (predState) {
					condition = cdg.edgeCondition(scopes, predState, state);
				} else {
					condition = scopes->bools.cnst(true);
				}
				c = condition;
				/* Should have already applied CDG
				 * optimisation to remove these
				 * edges. */
				assert(condition != scopes->bools.cnst(false));
				condition = bbdd::assume(&scopes->bools, condition, assumption);
				if (!condition) {
					/* Can't actually take this edge. */
					continue;
				}
				/* If there's a path from A to B then
				   knowing that B is reached shouldn't
				   imply that A is unreachable. */
				assert(condition != scopes->bools.cnst(false));

				assert(replacements.count(predState));
				exprbdd **slot = tabAtStartOfState.getSlot(
					condition,
					replacements[predState]);
				if (debug_use_alias_table) {
					printf("Consider edge l%d -> l%d\n",
					       stateLabels[predState],
					       stateLabels[state]);
					printf("Edge condition ");
					condition->prettyPrint(stdout);
					printf("Value ");
					replacements[predState]->prettyPrint(stdout);
				}
				assert(*slot == replacements[predState]);
			}
			if (TIMEOUT) {
				return sm;
			}
			/* What would be loaded at the start of this state? */
			exprbdd *startOfState = exprbdd::from_enabling(&scopes->exprs,
								       tabAtStartOfState,
								       NULL);
			if (!startOfState) {
				warning("Failed to flatten start-of-state enabling table for state l%d\n",
					stateLabels[state]);
				break;
			}

			if (debug_use_alias_table) {
				printf("startOfState for l%d: ",
				       stateLabels[state]);
				startOfState->prettyPrint(stdout);
			}

			/* Figure out what we'd load at the end of the
			 * state. */
			exprbdd *endOfState = startOfState;
			if (state->type == StateMachineState::SideEffecting &&
			    ((StateMachineSideEffecting *)state)->sideEffect &&
			    ((StateMachineSideEffecting *)state)->sideEffect->type == StateMachineSideEffect::Store &&
			    it->second.stores.count((StateMachineSideEffecting *)state)) {
				StateMachineSideEffectStore *st =
					(StateMachineSideEffectStore *)state->getSideEffect();
				assert(st);
				assert(st->type == StateMachineSideEffect::Store);
				endOfState = exprbdd::ifelse(
					&scopes->exprs,
					exprbdd::to_bbdd(
						&scopes->bools,
						exprbdd::binop(
							&scopes->exprs,
							&scopes->bools,
							Iop_CmpEQ64,
							st->addr,
							l->addr)),
					st->data,
					startOfState);
				if (debug_use_alias_table && !TIMEOUT) {
					printf("endOfState for l%d:\n",
					       stateLabels[state]);
					endOfState->prettyPrint(stdout);
				}
			}

			replacements[state] = endOfState;
		}
		
		if (!replacements.count(it->first)) {
			warning("No replacement for load in l%d?\n",
				stateLabels[it->first]);
			continue;
		}
		exprbdd *repl = replacements[it->first];
		if (!repl) {
			if (!TIMEOUT)
				abort();
		} else {
			if (debug_use_alias_table) {
				printf("Mux for l%d is:\n", stateLabels[it->first]);
				repl->prettyPrint(stdout);
			}
			it->first->sideEffect = new StateMachineSideEffectCopy(
				l->target,
				repl);
			StateMachineState *t = new StateMachineSideEffecting(
				it->first->dbg_origin,
				new StateMachineSideEffectAssertFalse(
					exprbdd::to_bbdd(
						&scopes->bools,
						exprbdd::unop(
							&scopes->exprs,
							&scopes->bools,
							Iop_BadPtr,
							l->addr)),
					true),
				it->first->target);
			predMap.removePredecessor(it->first->target, it->first);
			predMap.addPredecessor(t, it->first);
			predMap.addPredecessor(it->first->target, t);
			cdg.introduceState(t, cdg.domOf(it->first));
			it->first->target = t;
			progress = true;
		}
	}

#if !CONFIG_NO_STATIC_ALIASING
	/* Figure out which frames might actually be accessed by the
	   machine.  There's not much point in keeping any of the
	   other ones hanging around. */
	std::set<FrameId> liveFrames;
	bool allFramesLive = false;
	for (auto it = at.content.begin(); !allFramesLive && it != at.content.end(); it++) {
		/* This load might already have been eliminated. */
		if (!it->first->getSideEffect() ||
		    it->first->getSideEffect()->type != StateMachineSideEffect::Load)
			continue;
		StateMachineSideEffectLoad *l = (StateMachineSideEffectLoad *)it->first->getSideEffect();
		if (debug_gc_frames) {
			printf("Check l%d for effects on frame GC\n",
			       stateLabels[it->first]);
		}
		PointerAliasingSet pas(ptt.pointsToSetForExpr(
					       l->addr,
					       stackLayout.forState(it->first),
					       stackLayout,
					       sm));
		if (debug_gc_frames) {
			printf("PAS for l%d is %s\n",
			       stateLabels[it->first],
			       pas.name());
		}
		if (pas.otherStackPointer || !pas.valid) {
			Maybe<StackLayout> *sl = stackLayout.forState(it->first);
			if (!sl || !sl->valid) {
				allFramesLive = true;
				if (any_debug) {
					printf("l%d forces all stack frames to be live\n",
					       stateLabels[it->first]);
				}
			} else {
				for (auto it = sl->content.functions.begin();
				     it != sl->content.functions.end();
				     it++) {
					liveFrames.insert(*it);
				}
			}
		} else {
			Maybe<StackLayout> *sl = stackLayout.forState(it->first);
			if (sl && sl->valid) {
				for (auto it = pas.stackPointers.begin();
				     it != pas.stackPointers.end();
				     it++) {
					bool live = false;
					for (auto it2 = sl->content.functions.begin();
					     !live && it2 != sl->content.functions.end();
					     it2++)
						if (*it2 == *it)
							live = true;
					if (live)
						liveFrames.insert(*it);
				}
			} else {
				liveFrames.insert(pas.stackPointers.begin(), pas.stackPointers.end());
			}
		}
	}
	if (debug_gc_frames) {
		if (allFramesLive) {
			printf("All frames are live!\n");
		} else {
			printf("Live frames: {");
			for (auto it = liveFrames.begin(); it != liveFrames.end(); it++) {
				if (it != liveFrames.begin())
					printf(", ");
				printf("%s", it->name());
			}
			printf("}\n");
		}
	}
#endif

	/* Let's also have a go at ripping out redundant stores and
	   stack annotations. */
	std::set<StateMachineSideEffecting *> sideEffects;
	enumStates(sm, &sideEffects);
	for (auto it = sideEffects.begin(); it != sideEffects.end(); it++) {
		StateMachineSideEffect *sideEffect = (*it)->getSideEffect();
		if (!sideEffect)
			continue;
		switch (sideEffect->type) {
		case StateMachineSideEffect::Store: {
			StateMachineSideEffectStore *s = (StateMachineSideEffectStore *)sideEffect;
			bool ignore = true;
			for (auto it2 = decode.begin(s->rip); ignore && !it2.finished(); it2.advance())
				ignore &= opt.ignoreStore(it2.node()->rip);
			if (!ignore)
				break;
			bool noConflictingLoads = true;
			for (auto it2 = at.content.begin();
			     !killedAllLoads && noConflictingLoads && it2 != at.content.end();
			     it2++) {
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
				(*it)->sideEffect = 
					new StateMachineSideEffectAssertFalse(
						exprbdd::to_bbdd(
							&scopes->bools,
							exprbdd::unop(
								&scopes->exprs,
								&scopes->bools,
								Iop_BadPtr,
								s->addr)),
						true);
				progress = true;
			}
			break;
		}
#if !CONFIG_NO_STATIC_ALIASING
		case StateMachineSideEffect::StartFunction: {
			StateMachineSideEffectStartFunction *s = (StateMachineSideEffectStartFunction *)sideEffect;
			if (!allFramesLive && !liveFrames.count(s->frame)) {
				if (debug_gc_frames) {
					printf("Remove start function l%d\n",
					       stateLabels[*it]);
				}
				(*it)->sideEffect = NULL;
				progress = true;
			}
			break;
		}
		case StateMachineSideEffect::EndFunction: {
			StateMachineSideEffectEndFunction *s = (StateMachineSideEffectEndFunction *)sideEffect;
			if (!allFramesLive && !liveFrames.count(s->frame)) {
				if (debug_gc_frames) {
					printf("Remove end function l%d\n",
					       stateLabels[*it]);
				}
				(*it)->sideEffect = NULL;
				progress = true;
			}
			break;
		}
		case StateMachineSideEffect::StackLayout: {
			StateMachineSideEffectStackLayout *s = (StateMachineSideEffectStackLayout *)sideEffect;
			if (allFramesLive)
				break;
			bool repl = false;
			for (auto it2 = s->functions.begin(); !repl && it2 != s->functions.end(); it2++)
				if (!liveFrames.count(it2->frame))
					repl = true;
			if (repl) {
				std::vector<StateMachineSideEffectStackLayout::entry> newFunctions;
				for (auto it2 = s->functions.begin(); it2 != s->functions.end(); it2++) {
					if (liveFrames.count(it2->frame))
						newFunctions.push_back(*it2);
				}
				if (newFunctions.empty()) {
					if (debug_gc_frames) {
						printf("Stack layout l%d is dead\n",
						       stateLabels[*it]);
					}
					(*it)->sideEffect = NULL;
				} else {
					(*it)->sideEffect =
						new StateMachineSideEffectStackLayout(
							newFunctions);
					if (debug_gc_frames) {
						printf("Shrink stack layout l%d to ", stateLabels[*it]);
						(*it)->sideEffect->prettyPrint(stdout);
						printf("\n");
					}
				}

				progress = true;
			}
			break;
		}
#endif
			/* Don't do anything with these. */
		case StateMachineSideEffect::ImportRegister:
		case StateMachineSideEffect::Load:
		case StateMachineSideEffect::Copy:
		case StateMachineSideEffect::Unreached:
		case StateMachineSideEffect::Phi:
		case StateMachineSideEffect::AssertFalse:
		case StateMachineSideEffect::StartAtomic:
		case StateMachineSideEffect::EndAtomic:
			break;
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

#if !CONFIG_NO_STATIC_ALIASING

class partial_import {
	int tid;
	int vex_offset;
	bool mightBePointer;
	bool mightBeNonPointer;
public:
	partial_import(StateMachineSideEffectImportRegister *smi)
		: tid(smi->tid),
		  vex_offset(smi->vex_offset),
		  mightBePointer(smi->set.mightPoint()),
		  mightBeNonPointer(smi->set.mightBeNonPointer())
	{
	}
	PointerAliasingSet to_pas() const {
		if (mightBePointer && mightBeNonPointer) {
			return PointerAliasingSet::anything;
		} else if (mightBePointer && !mightBeNonPointer) {
			return PointerAliasingSet::stackPointer |
				PointerAliasingSet::nonStackPointer;
		} else if (!mightBePointer && mightBeNonPointer) {
			return PointerAliasingSet::notAPointer;
		} else {
			/* !mightBePointer && !mightBeNonPointer */
			return PointerAliasingSet::nothing;
		}
	}
	bool operator <(const partial_import &o) const {
		if (tid < o.tid)
			return true;
		if (tid > o.tid)
			return false;
		if (vex_offset < o.vex_offset)
			return true;
		if (vex_offset > o.vex_offset)
			return false;
		if (mightBePointer < o.mightBePointer)
			return true;
		if (mightBePointer > o.mightBePointer)
			return true;
		return mightBeNonPointer < o.mightBeNonPointer;
	}
};

/* We've pushed realias as far as it can go.  Remove the annotations. */
static StateMachine *
zapRealiasInfo(SMScopes *scopes, StateMachine *sm, bool *done_something)
{
	std::map<partial_import, threadAndRegister> preservedImports;
	std::map<StateMachineState *, int> pendingPredecessors;
	std::vector<StateMachineState *> states;
	enumStates(sm, &states);
	pendingPredecessors[sm->root] = 0;
	for (auto it = states.begin(); it != states.end(); it++) {
		std::vector<StateMachineState *> targ;
		(*it)->targets(targ);
		for (auto it2 = targ.begin(); it2 != targ.end(); it2++) {
			pendingPredecessors[*it2]++;
		}
	}
	states.clear();
	states.push_back(sm->root);
	while (!states.empty()) {
		StateMachineState *s = states.back();
		states.pop_back();
		assert(pendingPredecessors.count(s));
		assert(pendingPredecessors[s] == 0);
		switch (s->type) {
		case StateMachineState::Bifurcate: {
			auto smb = (StateMachineBifurcate *)s;
			if (--pendingPredecessors[smb->trueTarget] == 0) {
				states.push_back(smb->trueTarget);
			}
			if (--pendingPredecessors[smb->falseTarget] == 0) {
				states.push_back(smb->falseTarget);
			}
			break;
		}
		case StateMachineState::Terminal:
			break;
		case StateMachineState::SideEffecting: {
			auto sme = (StateMachineSideEffecting *)s;
			if (--pendingPredecessors[sme->target] == 0) {
				states.push_back(sme->target);
			}
			if (sme->sideEffect) {
				switch (sme->sideEffect->type) {
					/* These ones are pure
					 * annotations, so can just be
					 * killed off. */
				case StateMachineSideEffect::StartFunction:
				case StateMachineSideEffect::EndFunction:
				case StateMachineSideEffect::StackLayout:
					sme->sideEffect = NULL;
					*done_something = true;
					break;

					/* Imports are more tricky,
					   because they contain both
					   annotation-like and
					   side-effect-like behaviour,
					   and we need to preserve the
					   side effect while killing
					   the annotation.  The
					   approach is fairly simple:
					   the first import of a
					   particular
					   (thread,vex_offset) pair
					   remains an import, with a
					   references-anything PAS,
					   and everything else turns
					   into copies of that one.
					   The order in which we
					   process states is chosen so
					   that we process states in
					   the order in which they'll
					   execute, so figuring out
					   which one to keep is
					   trivial. */
				case StateMachineSideEffect::ImportRegister: {
					auto smi = (StateMachineSideEffectImportRegister *)sme->sideEffect;
					auto it_did_insert =
						preservedImports.insert(
							std::pair<partial_import, threadAndRegister>(
								partial_import(smi),
								smi->reg));
					auto it = it_did_insert.first;
					auto did_insert = it_did_insert.second;
					if (did_insert) {
						if (smi->set != PointerAliasingSet::anything) {
							sme->sideEffect = new StateMachineSideEffectImportRegister(
								smi->reg,
								smi->tid,
								smi->vex_offset,
								it->first.to_pas());
							*done_something = true;
						}
					} else {
						sme->sideEffect = new StateMachineSideEffectCopy(
							smi->reg,
							exprbdd::var(
								&scopes->exprs,
								&scopes->bools,
								IRExpr_Get(it->second, Ity_I64)));
						*done_something = true;
					}
					break;
				}
				default:
					break;
				}
			}
		}
		}
	}
	return sm;
}
#endif

/* End of namespace */
}

StateMachine *
functionAliasAnalysis(SMScopes *scopes, const MaiMap &decode, StateMachine *machine,
		      const AllowableOptimisations &opt, OracleInterface *oracle,
		      control_dependence_graph &cdg, predecessor_map &pm,
		      bool *done_something)
{
	stackedCdf::startLoadElimination();
	auto res = _realias::functionAliasAnalysis(scopes, decode, machine, opt, oracle, cdg, pm, done_something);
	stackedCdf::stopLoadElimination();
	return res;
}

#if !CONFIG_NO_STATIC_ALIASING
StateMachine *
zapRealiasInfo(SMScopes *scopes, StateMachine *sm, bool *done_something)
{
	return _realias::zapRealiasInfo(scopes, sm, done_something);
}
#endif
