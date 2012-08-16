#include "sli.h"
#include "state_machine.hpp"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"
#include "maybe.hpp"
#include "MachineAliasingTable.hpp"

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

class StackLayout : public Named {
	char *mkName() const {
		std::vector<const char *> fragments;
		auto it1 = rsps.begin();
		auto it2 = functions.begin();
		while (it1 != rsps.end()) {
			fragments.push_back(vex_asprintf("%s <%s> ",
							 it2->name(),
							 nameIRExpr(*it1)));
			it1++;
			it2++;
		}
		fragments.push_back(it2->name());
		return flattenStringFragmentsMalloc(fragments);
	}
public:
	std::vector<FrameId> functions;
	std::vector<IRExpr *> rsps;
	void sanity_check() const {
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


bool
StackLayout::identifyFrameFromPtr(IRExpr *ptr, FrameId *out)
{
	*out = FrameId::invalid();
	bool definitelyStack = false;
	assert(ptr->type() == Ity_I64);
	auto it2 = functions.begin();
	for (auto it = rsps.begin(); it != rsps.end(); it++) {
		IRExpr *rsp = *it;
		switch (compare_expressions(ptr, rsp)) {
		case compare_expressions_lt:
		case compare_expressions_eq:
			*out = *it2;
			return true;
		case compare_expressions_gt:
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
	PointerAliasingSet initialLoadAliasing;
	StackLayoutTable()
	{}
	bool build(StateMachine *inp);
	void prettyPrint(FILE *f, const stateLabelT &labels) const {
		for (auto it = content.begin(); it != content.end(); it++) {
			auto i = labels.find(it->first);
			assert(i != labels.end());
			fprintf(f, "%d: %s\n", i->second,
				it->second.valid ? it->second.content.name() : "<none>");
		}
	}
	void sanity_check() const {
		for (auto it = content.begin();
		     it != content.end();
		     it++) {
			assert(it->first);
			if (it->second.valid)
				it->second.content.sanity_check();
		}
	}
	Maybe<StackLayout> &forState(StateMachineState *s)
	{
		auto it = content.find(s);
		assert(it != content.end());
		return it->second;
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
	std::map<FrameId, IRExpr *> frameBoundaries;
	{
		std::set<StateMachineSideEffectStartFunction *> startFunctions;
		std::set<StateMachineSideEffectEndFunction *> endFunctions;
		enumSideEffects(inp, startFunctions);
		enumSideEffects(inp, endFunctions);
		for (auto it = startFunctions.begin(); it != startFunctions.end(); it++) {
			auto it2_did_insert = frameBoundaries.insert(
				std::pair<FrameId, IRExpr*>
				( (*it)->frame, (*it)->rsp ));
			auto it2 = it2_did_insert.first;
			auto did_insert = it2_did_insert.second;
			if (!did_insert)
				assert(it2->second == (*it)->rsp);
		}
		for (auto it = endFunctions.begin(); it != endFunctions.end(); it++) {
			auto it2_did_insert = frameBoundaries.insert(
				std::pair<FrameId, IRExpr*>
				( (*it)->frame, (*it)->rsp ));
			auto it2 = it2_did_insert.first;
			auto did_insert = it2_did_insert.second;
			if (!did_insert &&
			    it2->second != (*it)->rsp) {
				if (debug_build_stack_layout)
					printf("Cannot build stack layout because %s(%p) != %s(%p)\n",
					       nameIRExpr(it2->second),
					       it2->second,
					       nameIRExpr( (*it)->rsp),
					       (*it)->rsp);
				return false;
			}
		}
	}
	if (debug_build_stack_layout) {
		printf("Frame -> RSP correspondence:\n");
		for (auto it = frameBoundaries.begin();
		     it != frameBoundaries.end();
		     it++)
			printf("\t%s -> %s\n", it->first.name(), nameIRExpr(it->second));
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
			haveExitLayout = true;
			exitLayout.valid = true;
			exitLayout.content = StackLayout();
			exitLayout.content.functions.resize(l->functions.size(), FrameId::invalid());
			exitLayout.content.rsps.resize(l->functions.size() - 1);
			for (unsigned x = 1; x < l->functions.size(); x++) {
				assert(frameBoundaries.count(l->functions[x].first));
				exitLayout.content.functions[x] = l->functions[x].first;
				exitLayout.content.rsps[x-1] = frameBoundaries[l->functions[x].first];
			}
			exitLayout.content.functions[0] = l->functions.front().first;
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
						auto sf = (StateMachineSideEffectStartFunction *)se;
						assert(exitLayout.content.functions.back() == sf->frame);
						assert(exitLayout.content.rsps.back() == sf->rsp);
						exitLayout.content.functions.pop_back();
						exitLayout.content.rsps.pop_back();
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

	initialLoadAliasing = PointerAliasingSet::nonStackPointer | PointerAliasingSet::notAPointer;
	std::set<StateMachineSideEffectStackLayout *> layouts;
	enumSideEffects(inp, layouts);
	for (auto it = layouts.begin(); it != layouts.end(); it++) {
		for (auto it2 = (*it)->functions.begin(); it2 != (*it)->functions.end(); it2++)
			if (it2->second)
				initialLoadAliasing |= PointerAliasingSet::frame(it2->first);
	}

	sanity_check();
	return true;
}

class PointsToTable {
	std::map<threadAndRegister, PointerAliasingSet, threadAndRegister::fullCompare> content;
public:
	PointerAliasingSet pointsToSetForExpr(IRExpr *e,
					      StateMachineState *sm,
					      Maybe<StackLayout> &sl,
					      MachineAliasingTable &mat,
					      StackLayoutTable &slt);
	bool build(StateMachine *sm);
	void prettyPrint(FILE *f);
	void sanity_check() const {
		for (auto it = content.begin(); it != content.end(); it++) {
			assert(it->first.isValid());
			assert(it->first.isTemp());
		}
	}
	PointsToTable refine(AliasTable &at,
			     StateMachine *sm,
			     MachineAliasingTable &mat,
			     StackLayoutTable &slt,
			     bool *done_something);
};

static bool
aliasConfigForState(StateMachineState *sm,
		    unsigned thread,
		    MachineAliasingTable &mat,
		    Oracle::ThreadRegisterAliasingConfiguration *config)
{
	Oracle::RegisterAliasingConfiguration config2;

	if (!mat.findConfig(sm, &config2))
		return false;
	for (auto it = config2.content.begin(); it != config2.content.end(); it++) {
		if (it->first == thread) {
			*config = it->second;
			return true;
		}
	}
	return false;
}

static bool
aliasConfigForReg(StateMachineState *sm,
		  const threadAndRegister &reg,
		  MachineAliasingTable &mat,
		  PointerAliasingSet *alias)
{
	assert(reg.isReg());
	assert(reg.gen() == (unsigned)-1);
	if (reg.asReg() >= Oracle::NR_REGS * 8)
		return false;
	assert(reg.asReg() % 8 == 0);

	Oracle::ThreadRegisterAliasingConfiguration config;
	if (!aliasConfigForState(sm, reg.tid(), mat, &config))
		return false;
	*alias = config.v[reg.asReg() / 8];
	return true;
}

PointerAliasingSet
PointsToTable::pointsToSetForExpr(IRExpr *e,
				  StateMachineState *sm,
				  Maybe<StackLayout> &sl,
				  MachineAliasingTable &mat,
				  StackLayoutTable &slt)
{
	if (e->type() != Ity_I64)
		return PointerAliasingSet();
	switch (e->tag) {
	case Iex_Get: {
		IRExprGet *iex = (IRExprGet *)e;
		if (iex->reg.isTemp()) {
			assert(content.count(iex->reg));
			return content[iex->reg];
		}
		if (iex->reg.isReg() &&
		    iex->reg.asReg() == OFFSET_amd64_RSP) {
			if (sl.valid) {
				FrameId f(FrameId::invalid());
				if (sl.content.identifyFrameFromPtr(iex, &f)) {
					return PointerAliasingSet::frame(f);
				} else {
					break;
				}
			} else {
				return PointerAliasingSet::stackPointer;
			}
		}

		if (iex->reg.gen() != (unsigned)-1) {
			/* Non-initial registers might point anywhere,
			   including into any stack frame, and we
			   can't say anything interesting about
			   them. */
			break;
		}

		PointerAliasingSet alias;
		if (!aliasConfigForReg(sm, iex->reg, mat, &alias))
			alias = PointerAliasingSet::anything;
		return alias;
	}

	case Iex_Load:
		return slt.initialLoadAliasing;
	case Iex_Const:
		return PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer;
	case Iex_Associative: {
		IRExprAssociative *iex = (IRExprAssociative *)e;
		if (sl.valid &&
		    iex->op == Iop_Add64 &&
		    iex->nr_arguments == 2 &&
		    iex->contents[0]->tag == Iex_Const &&
		    iex->contents[1]->tag == Iex_Get &&
		    ((IRExprGet *)iex->contents[1])->reg.isReg() &&
		    ((IRExprGet *)iex->contents[1])->reg.asReg() == OFFSET_amd64_RSP) {
			FrameId f(FrameId::invalid());
			if (sl.content.identifyFrameFromPtr(iex, &f))
				return PointerAliasingSet::frame(f);
		}
		if (iex->op == Iop_Add64) {
			PointerAliasingSet res(PointerAliasingSet::nothing);
			for (int i = 0; i < iex->nr_arguments; i++)
				res |= pointsToSetForExpr(iex->contents[i], sm, sl, mat, slt);
			return res;
		}

		break;
	}
	default:
		break;
	}
	return PointerAliasingSet::anything;
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
		if ( (*it)->definesRegister(tr) &&
		     tr.isTemp() )
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
	bool build(CfgDecode &decode,
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
	void refine(PointsToTable &ptt,
		    MachineAliasingTable &mat,
		    StackLayoutTable &slt,
		    bool *done_something,
		    stateLabelT &labels);
};

static bool
mightLoadInitialValue(StateMachineSideEffecting *smse,
		      StateMachine *sm,
		      OracleInterface *oracle,
		      CfgDecode &decode,
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
			/* Note that checking the oracle is
			   *mandatory* here.  Otherwise, when the
			   oracle is incomplete we end up with an
			   inconsistency between here and the alias
			   table, and that leads to lots of bad things
			   happening. */
			if (store->data->type() == load->type &&
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
AliasTable::build(CfgDecode &decode,
		  StateMachine *sm,
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
			if (oracle->memoryAccessesMightAlias(decode, opt, smsel, smses)) {
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
		      MachineAliasingTable &mat,
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
		PointerAliasingSet newPts(PointerAliasingSet::nothing);
		Maybe<StackLayout> &sl(slt.forState(smse));
		switch (effect->type) {
		case StateMachineSideEffect::Load: {
			const AliasTableEntry &e(at.storesForLoad(smse));
			if (e.mightHaveExternalStores)
				newPts |= PointerAliasingSet::nonStackPointer;
			if (e.mightLoadInitial)
				newPts |= slt.initialLoadAliasing;
			for (auto it2 = e.beginStores(); it2 != e.endStores(); it2++)
				newPts |= pointsToSetForExpr(it2->data, smse, sl, mat, slt);
			break;
		}
		case StateMachineSideEffect::Copy: {
			StateMachineSideEffectCopy *c = (StateMachineSideEffectCopy *)effect;
			newPts = pointsToSetForExpr(c->value, smse, sl, mat, slt);
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
		case StateMachineSideEffect::PointerAliasing:
		case StateMachineSideEffect::Store:
		case StateMachineSideEffect::Unreached:
		case StateMachineSideEffect::AssertFalse:
		case StateMachineSideEffect::StartAtomic:
		case StateMachineSideEffect::EndAtomic:
		case StateMachineSideEffect::StartFunction:
		case StateMachineSideEffect::EndFunction:
		case StateMachineSideEffect::StackUnescaped:
		case StateMachineSideEffect::StackLayout:
			/* These aren't supposed to define registers */
			abort();
		}
		if (newPts != it->second)
			*done_something = true;
		res.content.insert(std::pair<threadAndRegister, PointerAliasingSet>(it->first, newPts));
	}
	return res;
}

void
AliasTable::refine(PointsToTable &ptt,
		   MachineAliasingTable &mat,
		   StackLayoutTable &slt,
		   bool *done_something,
		   stateLabelT &labels)
{
	for (auto it = content.begin();
	     it != content.end();
	     it++) {
		StateMachineSideEffectLoad *l = (StateMachineSideEffectLoad *)it->first->getSideEffect();
		PointerAliasingSet loadPts(
			ptt.pointsToSetForExpr(
				l->addr,
				it->first,
				slt.forState(it->first),
				mat,
				slt));
		if (debug_refine_alias_table)
			printf("Examining alias table for state %d\n",
			       labels[it->first]);
		for (auto it2 = it->second.stores.begin();
		     it2 != it->second.stores.end();
			) {
			PointerAliasingSet storePts(
				ptt.pointsToSetForExpr( ((StateMachineSideEffectStore *)(*it2)->getSideEffect())->addr,
							it->first,
							slt.forState(*it2),
							mat,
							slt));
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

static StateMachine *
functionAliasAnalysis(StateMachine *sm, const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something)
{
	/* This analysis relies on identifying when accesses are part
	   of particular stack frames, but it's not good at
	   distinguishing between the stacks of different threads.
	   Easy fix: only appply it to single-threaded machines. */
	if (sm->bad_origin.size() != 1)
		return sm;

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
	if (!ptt.build(sm)) {
		if (any_debug)
			printf("Failed to build points-to table!\n");
		return sm;
	}
	if (debug_build_points_to_table) {
		printf("Points-to table:\n");
		ptt.prettyPrint(stdout);
	}

	MachineAliasingTable mat;
	mat.initialise(sm);

	CfgDecode decode;
	decode.addMachine(sm);
	AliasTable at;
	if (!at.build(decode, sm, stateLabels, opt, oracle)) {
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
		PointsToTable ptt2 = ptt.refine(at, sm, mat, stackLayout, &p);
		if (p && debug_refine_points_to_table) {
			printf("Refined points-to table:\n");
			ptt2.prettyPrint(stdout);
		}
		ptt = ptt2;

		at.refine(ptt, mat, stackLayout, &p, stateLabels);
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
						l->addr));
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
		if (!opt.ignoreStore(decode(s->rip.where)->rip))
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
			(*it)->sideEffect = 
				new StateMachineSideEffectAssertFalse(
					IRExpr_Unop(
						Iop_BadPtr,
						s->addr),
					true);
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
