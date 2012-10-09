#include <sys/time.h>
#include <err.h>
#include <stdlib.h>

#include <map>
#include <queue>

#include <sqlite3.h>

#include "sli.h"
#include "oracle.hpp"
#include "simplify_irexpr.hpp"
#include "offline_analysis.hpp"
#include "typesdb.hpp"
#include "query_cache.hpp"
#include "allowable_optimisations.hpp"
#include "alloc_mai.hpp"

#include "libvex_prof.hpp"
#include "libvex_parse.h"

#ifndef NDEBUG
static bool debug_static_alias = false;
static bool debug_static_rbp_offsets = false;
#else
#define debug_static_alias false
#define debug_static_rbp_offsets false
#endif

void dbg_database_query(const char *query);
void dbg_database_queryf(const char *query, ...) __attribute__((__format__(__printf__, 1, 2)));

static bool
operator<(const InstructionSet &a, const InstructionSet &b)
{
	return a.rips < b.rips;
}

template <typename t> void
make_unique(std::vector<t> &v)
{
	std::sort(v.begin(), v.end());
	typename std::vector<t>::iterator it = std::unique(v.begin(), v.end());
	v.resize(it - v.begin());
}


unsigned long
hash_ulong_pair(const std::pair<unsigned long, unsigned long> &p)
{
	return p.first + p.second * 59;
}

template<typename t> void
operator |=(std::set<t> &x, const std::set<t> &y)
{
	for (typename std::set<t>::iterator it = y.begin();
	     it != y.end();
	     it++)
		x.insert(*it);
}

Oracle::LivenessSet Oracle::LivenessSet::everything(~0ul);
Oracle::LivenessSet Oracle::LivenessSet::argRegisters(
	0x01 | /* rax -- not strictly an arg register, but treated
	       as one for variadic functions. */
	0x02 | /* rcx */
	0x04 | /* rdx */
     /* 0x08 |    rbx */
	0x10 | /* rsp -- not an argument register, but almost certainly
		truly live on function entry */
     /* 0x20 |    rbp */
	0x40 | /* rsi */
	0x80 | /* rdi */
       0x100 | /* r8 */
       0x200 | /* r9 */
       0x400   /* r10 -- technically static chain rather than a true
		  argument, but they're the same thing for our
		  purposes. */
    /* 0x800 |   r11 */
	);

IRSB *
Oracle::getIRSBForRip(AddressSpace *as, const StaticRip &sr, bool singleInstr)
{
	return getIRSBForRip(as, VexRip::invent_vex_rip(sr.rip), singleInstr);
}

IRSB *
Oracle::getIRSBForRip(AddressSpace *as, const VexRip &sr, bool singleInstr)
{
	try {
		return as->getIRSBForAddress(ThreadRip::mk(STATIC_THREAD, sr), singleInstr);
	} catch (BadMemoryException e) {
		return NULL;
	}
}

IRSB *
Oracle::getIRSBForRip(const VexRip &vr, bool singleInstr)
{
	return getIRSBForRip(ms->addressSpace, vr, singleInstr);
}

Oracle::LivenessSet
Oracle::LivenessSet::use(Int offset)
{
	if (offset >= 8 * NR_REGS)
		return *this;
	else
		return LivenessSet(mask | (1ul << (offset / 8)));
}

Oracle::LivenessSet
Oracle::LivenessSet::define(threadAndRegister r)
{
	if (r.isTemp())
		return *this;
	if (r.asReg() >= 8 * NR_REGS)
		return *this;
	else
		return LivenessSet(mask & ~(1ul << (r.asReg() / 8)));
}

bool
Oracle::LivenessSet::isLive(Int offset) const
{
	if (offset >= 8 * NR_REGS)
		return true;
	else
		return !!(mask & (1ul << (offset / 8)));
}

const PointerAliasingSet PointerAliasingSet::nothing(0);
const PointerAliasingSet PointerAliasingSet::notAPointer(1);
const PointerAliasingSet PointerAliasingSet::stackPointer(2);
const PointerAliasingSet PointerAliasingSet::nonStackPointer(3);
const PointerAliasingSet PointerAliasingSet::anything(4);

Oracle::ThreadRegisterAliasingConfiguration Oracle::ThreadRegisterAliasingConfiguration::functionEntryConfiguration(5.3f);
Oracle::ThreadRegisterAliasingConfiguration::ThreadRegisterAliasingConfiguration(float)
{
	/* On function entry, the only pointer to the current stack
	   frame should be in RSP.  Anythign else indicates that the
	   guest program is doing something non-C-like. */
	stackInStack = false;
	stackInMemory = false;
	for (int i = 0; i < NR_REGS; i++)
		v[i] = PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer;
	v[4] = PointerAliasingSet::stackPointer; /* rsp */
}

Oracle::ThreadRegisterAliasingConfiguration Oracle::ThreadRegisterAliasingConfiguration::unknown(5.3f, 12);
Oracle::ThreadRegisterAliasingConfiguration::ThreadRegisterAliasingConfiguration(float, int)
{
	stackInStack = true;
	stackInMemory = true;
	for (int i = 0; i < NR_REGS; i++)
		v[i] = PointerAliasingSet::anything;
}

void
Oracle::ThreadRegisterAliasingConfiguration::prettyPrint(FILE *f) const
{
       for (int i = 0; i < NR_REGS; i++)
               fprintf(f, "\t%8d: %s\n", i, v[i].name());
       if (stackInMemory && stackInStack)
	       fprintf(f, "\tStack in memory and stack\n");
       else if (stackInMemory)
	       fprintf(f, "\tStack in memory\n");
       else if (stackInStack)
	       fprintf(f, "\tStack in stack\n");
       else
	       fprintf(f, "\tStack not escaped\n");
}

void
Oracle::RegisterAliasingConfiguration::prettyPrint(FILE *f) const
{
	for (auto it = content.begin(); it != content.end(); it++) {
		fprintf(f, "thread %d:\n", it->first);
		it->second.prettyPrint(f);
	}
}

void
Oracle::findPreviousInstructions(std::vector<VexRip> &out)
{
	std::vector<VexRip> fheads;
	getDominators(crashedThread, ms, out, fheads);
}

unsigned
getInstructionSize(AddressSpace *as, const StaticRip &rip)
{
	IRSB *irsb = Oracle::getIRSBForRip(as, rip, true);
	if (!irsb)
		return 0;
	assert(irsb->stmts[0]->tag == Ist_IMark);
	return ((IRStmtIMark *)irsb->stmts[0])->len;
}
unsigned
getInstructionSize(AddressSpace *as, const VexRip &rip)
{
	return getInstructionSize(as, StaticRip(rip));
}

bool
Oracle::functionCanReturn(const VexRip &rip)
{
#warning Horrible, horrible hack
	if (rip.unwrap_vexrip() == 0x768440 /* ut_dbg_assertion_failed */ ||
	    rip.unwrap_vexrip() == 0x7683e0 /* ut_dbg_stop_thread */)
		return false;
	else
		return true;
}

/* Try to find the RIPs of some stores which might conceivably have
   interfered with the observed load.  Stack accesses are not tracked
   by this mechanism. */
/* We do this using a profiling-based scheme.  There's some initial
   training phase during which we log, for every memory location, the
   set of loads and stores which access it, and we then just return
   the union of the store sets for all the locations whose load set
   includes the observed address. */
void
Oracle::findConflictingStores(const MaiMap &mai,
			      StateMachineSideEffectLoad *smsel,
			      std::set<DynAnalysisRip> &out)
{
	for (auto it = mai.begin(smsel->rip); !it.finished(); it.advance()) {

		std::vector<TypesDb::types_entry> loads;
		std::vector<TypesDb::types_entry> stores;
		if (!type_db->lookupEntry(it.dr(), loads, stores))
			continue;
		bool shared_loads = false;
		for (auto it2 = loads.begin(); !shared_loads && it2 != loads.end(); it2++)
			if (!it2->is_private && it2->rip == it.dr())
				shared_loads = true;
		if (!shared_loads)
			continue;
		for (auto it = stores.begin(); it != stores.end(); it++)
			if (!it->is_private)
				out.insert(it->rip);
	}
}

bool
Oracle::notInTagTable(const DynAnalysisRip &dr)
{
	__set_profiling(notInTagTable);
	return !type_db->ripPresent(dr);
}

bool
Oracle::hasConflictingRemoteStores(const DynAnalysisRip &dr)
{
	__set_profiling(hasConflictingRemoteStores);
	std::vector<TypesDb::types_entry> loads;
	std::vector<TypesDb::types_entry> stores;
	if (!type_db->lookupEntry(dr, loads, stores))
		return false;
	bool shared_load = false;
	for (auto it = loads.begin(); !shared_load && it != loads.end(); it++)
		if (!it->is_private && it->rip == dr)
			shared_load = true;
	if (!shared_load)
		return false;
	for (auto it = stores.begin(); it != stores.end(); it++)
		if (!it->is_private)
			return true;
	return false;
}

bool
Oracle::hasConflictingRemoteStores(const MaiMap &mai, const AllowableOptimisations &opt, StateMachineSideEffectMemoryAccess *access)
{
	if (opt.assumeNoInterferingStores())
		return false;
	for (auto it = mai.begin(access->rip); !it.finished(); it.advance()) {
		if (access->type == StateMachineSideEffect::Load &&
		    opt.nonLocalLoads() &&
		    !opt.nonLocalLoads()->count(it.dr()))
			continue;
		if (hasConflictingRemoteStores(it.dr()))
			return true;
	}
	return false;
}

Oracle::mam_result
Oracle::alias_query(const DynAnalysisRip &dr1,
		    const std::vector<TypesDb::types_entry> &alias1,
		    const DynAnalysisRip &dr2,
		    const std::vector<TypesDb::types_entry> &alias2)
{
	bool shared_1 = false;
	bool private_1 = false;
	for (auto it = alias1.begin();
	     (!shared_1 || !private_1) && it != alias1.end();
	     it++) {
		if (it->rip == dr1) {
			if (it->is_private)
				private_1 = true;
			else
				shared_1 = true;
		}
	}
	bool shared_2 = false;
	bool private_2 = false;
	for (auto it = alias2.begin();
	     (!shared_2 || !private_2) && it != alias2.end();
	     it++) {
		if (it->rip == dr2) {
			if (it->is_private)
				private_2 = true;
			else
				shared_2 = true;
		}
	}
	if (!private_1 && !shared_1) {
		if (!private_2 && !shared_2)
			return mam_private;
		return mam_no_alias;
	}
	if (!private_2 && !shared_2)
		return mam_no_alias;

	if (!private_1 && !shared_2)
		return mam_no_alias;
	if (!shared_1 && !private_2)
		return mam_no_alias;

	bool have_private_alias = false;
	for (auto it = alias1.begin(); it != alias1.end(); it++)
		if (it->rip == dr2) {
			if (it->is_private)
				have_private_alias = true;
			else
				return mam_might_alias;
		}
	if (have_private_alias)
		return mam_private;
	return mam_no_alias;
}

Oracle::mam_result
Oracle::memoryAccessesMightAliasLS(const DynAnalysisRip &smsel_dr, const DynAnalysisRip &smses_dr)
{
	__set_profiling(might_alias_load_store);
	std::vector<TypesDb::types_entry> load_loads;
	std::vector<TypesDb::types_entry> load_stores;
	std::vector<TypesDb::types_entry> store_loads;
	std::vector<TypesDb::types_entry> store_stores;
	if (!type_db->lookupEntry(smsel_dr, load_loads, load_stores)) {
		/* Load is private.  What about store? */
		if (!type_db->ripPresent(smses_dr)) {
			/* Both private  */
			return mam_private;
		}
		/* Load private, store shared -> no alias */
		return mam_no_alias;
	}
	if (!type_db->lookupEntry(smses_dr, store_loads, store_stores)) {
		/* Store is private, load is shared -> no alias */
		return mam_no_alias;
	}

	bool shared_load = false;
	bool private_load = false;
	for (auto it = load_loads.begin();
	     (!shared_load || !private_load) && it != load_loads.end();
	     it++) {
		if (it->rip == smsel_dr) {
			if (it->is_private)
				private_load = true;
			else
				shared_load = true;
		}
	}
	bool shared_store = false;
	bool private_store = false;
	for (auto it = store_stores.begin();
	     (!shared_store || !private_store) && it != store_stores.end();
	     it++) {
		if (it->rip == smses_dr) {
			if (it->is_private)
				private_store = true;
			else
				shared_store = true;
		}
	}

	if (!private_load && !shared_load) {
		/* Load is from the stack */
		if (!private_store && !shared_store) {
			/* So is store */
			return mam_private;
		}
		return mam_no_alias;
	}
	if (!private_store && !shared_store)
		return mam_no_alias;

	/* If the load is definitely shared and the store is
	   definitely private then they can't alias, and
	   vice-versa. */
	if (!private_load && !shared_store)
		return mam_no_alias;
	if (!shared_load && !private_store)
		return mam_no_alias;

	bool have_private_alias = false;
	for (auto it = load_stores.begin(); it != load_stores.end(); it++)
		if (it->rip == smses_dr) {
			if (it->is_private)
				have_private_alias = true;
			else
				return mam_might_alias;
		}
	if (have_private_alias)
		return mam_private;
	return mam_no_alias;
}
bool
Oracle::memoryAccessesMightAlias(const MaiMap &mai,
				 const AllowableOptimisations &opt,
				 StateMachineSideEffectLoad *smsel,
				 StateMachineSideEffectStore *smses)
{
	if (smsel->tag != smses->tag)
		return false;

	if (definitelyNotEqual(smsel->addr, smses->addr, opt))
		return false;

	static QueryCache<StateMachineSideEffectLoad, StateMachineSideEffectStore, bool> cache(__func__);
	int idx = cache.hash(smsel, smses);
	bool res;
	if (cache.query(smsel, smses, idx, &res))
		return res;

	for (auto it = mai.begin(smsel->rip); !it.finished(); it.advance()) {
		for (auto it2 = mai.begin(smses->rip); !it2.finished(); it2.advance()) {
			switch (memoryAccessesMightAliasLS(it.dr(), it2.dr())) {
			case mam_might_alias:
				cache.set(smsel, smses, idx, true);
				return true;
			case mam_no_alias:
				continue;
			case mam_private:
				if (smsel->rip.tid != smses->rip.tid)
					continue;
				cache.set(smsel, smses, idx, true);
				return true;
			}
		}
	}
	cache.set(smsel, smses, idx, false);
	return false;
}

bool
Oracle::memoryAccessesMightAliasCrossThread(const DynAnalysisRip &smsel_dr, const DynAnalysisRip &smses_dr)
{
	__set_profiling(might_alias_cross_thread);
	return memoryAccessesMightAliasLS(smsel_dr, smses_dr) == mam_might_alias;
}

Oracle::mam_result
Oracle::memoryAccessesMightAliasLL(const DynAnalysisRip &dr1, const DynAnalysisRip &dr2)
{
	__set_profiling(might_alias_load_load);
	std::vector<TypesDb::types_entry> l1_loads;
	std::vector<TypesDb::types_entry> l1_stores;
	std::vector<TypesDb::types_entry> l2_loads;
	std::vector<TypesDb::types_entry> l2_stores;
	if (!type_db->lookupEntry(dr1, l1_loads, l1_stores)) {
		if (!type_db->ripPresent(dr2))
			return mam_private;
		return mam_no_alias;
	}
	if (!type_db->lookupEntry(dr2, l2_loads, l2_stores))
		return mam_no_alias;

	return alias_query(dr1, l1_loads, dr2, l2_loads);
}

bool
Oracle::memoryAccessesMightAlias(const MaiMap &mai,
				 const AllowableOptimisations &opt,
				 StateMachineSideEffectLoad *smsel1,
				 StateMachineSideEffectLoad *smsel2)
{
	if (smsel1->tag != smsel2->tag)
		return false;

	if (definitelyNotEqual(smsel1->addr, smsel2->addr, opt))
		return false;

	for (auto it = mai.begin(smsel1->rip); !it.finished(); it.advance()) {
		for (auto it2 = mai.begin(smsel2->rip); !it2.finished(); it2.advance()) {
			switch (memoryAccessesMightAliasLL(it.dr(), it2.dr())) {
			case mam_might_alias:
				return true;
			case mam_no_alias:
				continue;
			case mam_private:
				if (smsel1->rip.tid != smsel2->rip.tid)
					continue;
				return true;
			}
		}
	}
	return false;
}

Oracle::mam_result
Oracle::memoryAccessesMightAliasSS(const DynAnalysisRip &dr1, const DynAnalysisRip &dr2)
{
	__set_profiling(might_alias_load_load);
	std::vector<TypesDb::types_entry> s1_loads;
	std::vector<TypesDb::types_entry> s1_stores;
	std::vector<TypesDb::types_entry> s2_loads;
	std::vector<TypesDb::types_entry> s2_stores;
	if (!type_db->lookupEntry(dr1, s1_loads, s1_stores)) {
		if (!type_db->ripPresent(dr2))
			return mam_private;
		return mam_no_alias;
	}
	if (!type_db->lookupEntry(dr2, s2_loads, s2_stores))
		return mam_no_alias;

	return alias_query(dr1, s1_stores, dr2, s2_stores);
}

bool
Oracle::memoryAccessesMightAlias(const MaiMap &mai,
				 const AllowableOptimisations &opt,
				 StateMachineSideEffectStore *smses1,
				 StateMachineSideEffectStore *smses2)
{
	if (smses1->tag != smses2->tag)
		return false;

	if (definitelyNotEqual(smses1->addr, smses2->addr, opt))
		return false;

	for (auto it = mai.begin(smses1->rip); !it.finished(); it.advance()) {
		for (auto it2 = mai.begin(smses2->rip); !it2.finished(); it2.advance()) {
			switch (memoryAccessesMightAliasSS(it.dr(), it2.dr())) {
			case mam_might_alias:
				return true;
			case mam_no_alias:
				continue;
			case mam_private:
				if (smses1->rip.tid != smses2->rip.tid)
					continue;
				return true;
			}
		}
	}
	return false;
}

void
Oracle::findRacingRips(const MaiMap &mai, StateMachineSideEffectLoad *smsel, std::set<DynAnalysisRip> &out)
{
	findConflictingStores(mai, smsel, out);
}

void
Oracle::findRacingRips(const MaiMap &mai, StateMachineSideEffectStore *smses, std::set<DynAnalysisRip> &out)
{
	__set_profiling(findRacingRips__store);
	std::vector<TypesDb::types_entry> loads, stores;
	for (auto it = mai.begin(smses->rip); !it.finished(); it.advance()) {
		if (!type_db->lookupEntry(it.dr(), loads, stores))
			continue;
		for (auto it = loads.begin(); it != loads.end(); it++)
			if (!it->is_private)
				out.insert(it->rip);
	}
}

template <typename t>
class union_find {
public:
	struct entry {
		entry(const t &_parent, unsigned _d)
			: parent(_parent), depth(_d)
		{}
		entry() { abort(); /* shouldn't happen */ }
		t parent;
		unsigned depth;
	};
	std::map<t, entry> content;

	/* Check whether we know anything at all about x */
	bool present(t x) { return content.count(x) != 0; }

	/* Insert x into the structure as a singleton, if it's not
	   already present. */
	void insert(t x) { if (!present(x)) content.insert(std::pair<t, entry>(x, entry(x, 0))); }

	/* Insert x and y into the structure, if they're not present,
	   and then merge their containing sets. */
	void insert(t x, t y) {
		t xr = representative(x);
		t yr = representative(y);
		if (xr != yr) {
			entry &xe(content[xr]);
			entry &ye(content[yr]);
			if (xe.depth < ye.depth)
				xe.parent = yr;
			else
				ye.parent = xr;
		}
		assert(representative(x) == representative(y));
	}

	/* Find the representative for the set to which a given item
	   belongs.  Create the item as a singleton if it isn't
	   already present. */
	t representative(t x) {
		if (!present(x)) {
			insert(x);
			return x;
		}
		while (1) {
			assert(content.count(x) != 0);
			entry *e = &content[x];
			if (e->parent == x)
				return x;
			assert(content.count(e->parent) != 0);
			entry *pe = &content[e->parent];
			if (pe->parent.isValid())
				e->parent = pe->parent;
			x = e->parent;
		}
	}
};

void
findInstrSuccessorsAndCallees(Oracle *oracle,
			      AddressSpace *as,
			      const VexRip &rip,
			      std::vector<VexRip> &directExits,
			      gc_pair_VexRip_set_t *callees)
{
	__set_profiling(findInstrSuccessorsAndCallees);
	IRSB *irsb = Oracle::getIRSBForRip(as, rip, true);
	if (!irsb)
		return;
	int i;

	for (i = 1; i < irsb->stmts_used; i++) {
		if (irsb->stmts[i]->tag == Ist_IMark) {
			/* That's the end of this instruction */
			directExits.push_back(((IRStmtIMark *)irsb->stmts[i])->addr.rip);
			return;
		}
		if (irsb->stmts[i]->tag == Ist_Exit)
			directExits.push_back(((IRStmtExit *)irsb->stmts[i])->dst.rip);
	}

	/* If we get here then there are no other marks in the IRSB,
	   so we need to look at the fall through addresses. */
	if (irsb->jumpkind == Ijk_Call) {
		if (!irsb->next_is_const ||
		    !oracle->functionNeverReturns(StaticRip(irsb->next_const.rip)))
			directExits.push_back(extract_call_follower(irsb));
		/* Emit the target as well, if possible. */
		if (irsb->next_is_const)
			callees->set(std::pair<VexRip, VexRip>(rip, irsb->next_const.rip),
				     true);
		return;
	}

	if (irsb->jumpkind != Ijk_NoDecode &&
	    irsb->next_is_const) {
		directExits.push_back(irsb->next_const.rip);
	} else {
		/* Should really do something more clever here,
		   possibly based on dynamic analysis. */
	}
}

static void
findSuccessors(Oracle *oracle, AddressSpace *as, VexRip rip, std::vector<VexRip> &out)
{
	gc_pair_VexRip_set_t *callees = new gc_pair_VexRip_set_t();
	findInstrSuccessorsAndCallees(oracle, as, rip, out, callees);
	for (auto it = callees->begin();
	     it != callees->end();
	     it++)
		out.push_back(it.key().second);
}

/* Try to group the RIPs into clusters which are likely to execute
 * together.  We'll eventually build state machines for each cluster,
 * rather than for individual RIPs. */
/* The mechanism used is a bit stupid: pick a RIP pretty much at
 * random out of the input set and create a new output set for it.  We
 * then explore the machine code from that address, and if we find any
 * other input RIPs we add them to the current output set.  If we find
 * a RIP which has already been assigned an output set then we merge
 * the relevant output sets. */
void
Oracle::clusterRips(const std::set<VexRip> &inputRips,
		    std::set<InstructionSet > &outputClusters)
{
	__set_profiling(clusterRips);
	union_find<VexRip> results;
#if 0
	std::set<unsigned long> explored;

	for (std::set<unsigned long>::const_iterator it = inputRips.begin();
	     it != inputRips.end();
	     it++) {
		unsigned long r = *it;
		assert(r);
		if (results.present(r))
			continue;

		results.insert(r);
		std::vector<VexRip> discoveredInstructions;
		discoveredInstructions.push_back(r);
		while (!discoveredInstructions.empty()) {
			unsigned long r2 = discoveredInstructions.back();
			discoveredInstructions.pop_back();
			if (!explored.count(r2))
				findSuccessors(ms->addressSpace, r2, discoveredInstructions);
			results.insert(r, r2);
			explored.insert(r2);
		}
	}
#else
	for (auto it = inputRips.begin();
	     it != inputRips.end();
	     it++) {
		VexRip item = *it;
		
		results.insert(item);

		/* Map from rips to the ``best'' depth we've visited
		 * with so far. */
		std::map<VexRip, int> visited;
		std::vector<std::pair<VexRip, int> > pending;
		pending.push_back(std::pair<VexRip, int>(item, 20));
		while (!pending.empty()) {
			std::pair<VexRip, int> next = pending.back();
			pending.pop_back();
			if (next.second == 0)
				continue;
			if (visited[next.first] >= next.second) {
				/* Okay, we've already been to this
				   instruction starting from this
				   root, so don't need to do anything
				   more. */
				continue;
			}
			visited.insert(next);
			if (inputRips.count(next.first) && next.first != item) {
				/* This root can reach another one of
				   the input instructions.  That means
				   that they need to be clustered.  Do
				   so. */
				results.insert(item, next.first);

				/* That's all we need to do: the bits
				   which are reachable from the
				   successor of this instruction will
				   be handled naturally when we take
				   it out of unprocessedRips.  That
				   might have already happened, in
				   which case we'll have already
				   handled everything.  Either way, we
				   don't need to do any more now. */
				continue;
			}

			/* Not already visited from this root, not
			 * another root -> have to do it the hard
			 * way. */
			std::vector<VexRip> s;
			findSuccessors(this, ms->addressSpace, next.first, s);
			for (auto it2 = s.begin();
			     it2 != s.end();
			     it2++)
				pending.push_back(std::pair<VexRip, int>(*it2, next.second - 1));
		}
	}
#endif

	/* Now explode the union-find structure into a set of sets. */
	std::set<VexRip> unprocessedInput(inputRips);
	while (!unprocessedInput.empty()) {
		VexRip r = *unprocessedInput.begin();

		InstructionSet thisSet;
		VexRip representative = results.representative(r);
		for (auto it = unprocessedInput.begin();
		     it != unprocessedInput.end();
			) {
			if (results.representative(*it) == representative) {
				thisSet.rips.insert(*it);
				unprocessedInput.erase(it++);
			} else {
				it++;
			}
		}
		outputClusters.insert(thisSet);
	}
}

void
Oracle::loadTagTable(const char *path)
{
	__set_profiling(loadTagTable);

	type_db = new TypesDb(path);
}

void
Oracle::calculateRegisterLiveness(VexPtr<Oracle> &ths,
				  GarbageCollectionToken token)
{
	bool done_something;
	unsigned long changed;
	unsigned long unchanged;
	std::vector<StaticRip> functions;

	do {
		changed = 0;
		unchanged = 0;
		done_something = false;
		ths->getFunctions(functions);
		for (auto it = functions.begin();
		     it != functions.end();
		     it++) {
			LibVEX_maybe_gc(token);
			bool this_did_something = false;
			Function f(*it);
			f.calculateRegisterLiveness(ths, ths->ms->addressSpace, &this_did_something);
			if (this_did_something)
				changed++;
			else
				unchanged++;
			done_something |= this_did_something;
		}
		printf("Register liveness progress: %ld/%ld\n", changed, changed+unchanged);
	} while (done_something);
}

void
Oracle::calculateRbpToRspOffsets(VexPtr<Oracle> &ths, GarbageCollectionToken token)
{
	std::vector<StaticRip> functions;
	ths->getFunctions(functions);
	for (auto it = functions.begin();
	     it != functions.end();
	     it++) {
		LibVEX_maybe_gc(token);
		Function f(*it);
		f.calculateRbpToRspOffsets(ths->ms->addressSpace, ths);
	}
}

void
Oracle::calculateAliasing(VexPtr<Oracle> &ths, GarbageCollectionToken token)
{
	bool done_something;
	std::vector<StaticRip> functions;

	ths->getFunctions(functions);
	for (auto it = functions.begin();
	     it != functions.end();
	     it++) {
		LibVEX_maybe_gc(token);
		Function f(*it);
		if (!f.aliasingConfigCorrect()) {
			do {
				done_something = false;
				f.calculateAliasing(ths->ms->addressSpace, &done_something);
			} while (done_something);
			f.setAliasingConfigCorrect(true);
		}
	}
}

static Oracle::LivenessSet
irexprUsedValues(Oracle::LivenessSet old, IRExpr *w)
{
	if (!w)
		return old;
	class _ : public IRExprTransformer {
	public:
		Oracle::LivenessSet old;
		IRExpr *transformIex(IRExprGet *e) {
			if (!e->reg.isTemp())
				old = old.use(e->reg.asReg());
			return IRExprTransformer::transformIex(e);
		}
		_(Oracle::LivenessSet &_old)
			: old(_old)
		{}
	} t(old);
	t.doit(w);
	return t.old;
}

static PointerAliasingSet
irexprAliasingClass(IRExpr *expr,
		    const Oracle::RegisterAliasingConfiguration &config,
		    std::map<threadAndRegister, PointerAliasingSet> *temps,
		    const AllowableOptimisations &opt,
		    bool buildingAliasTable)
{
	if (expr->type() != Ity_I64)
		/* Not a 64 bit value -> not a pointer */
		return PointerAliasingSet::notAPointer;

	switch (expr->tag) {
	case Iex_Get: {
		IRExprGet *e = (IRExprGet *)expr;
		if (e->reg.isTemp()) {
			if (!temps)
				return PointerAliasingSet::anything;
			auto it = temps->find(e->reg);
			assert(it != temps->end());
			return it->second;
		} else {
			return config.lookupRegister(e->reg, buildingAliasTable);
		}
	}
	case Iex_Const: {
		IRConst *con = ((IRExprConst *)expr)->con;
		if (con->Ico.U64 < 4096)
			return PointerAliasingSet::notAPointer;
		bool t;
		if (opt.addressAccessible(((IRExprConst *)expr)->con->Ico.U64, &t) && !t)
			return PointerAliasingSet::notAPointer;
		else
			return PointerAliasingSet::nonStackPointer | PointerAliasingSet::notAPointer;
	}
	case Iex_Unop:
		switch (((IRExprUnop *)expr)->op) {
		case Iop_1Uto8:
		case Iop_8Uto64:
		case Iop_8Sto64:
		case Iop_16Uto64:
		case Iop_16Sto64:
		case Iop_32Uto64:
		case Iop_32Sto64:
		case Iop_64to32:
		case Iop_128to64:
		case Iop_128HIto64:
		case Iop_V128to64:
		case Iop_V128HIto64:
		case Iop_Not64:
		case Iop_Neg64:
			return PointerAliasingSet::notAPointer;
		default:
			break;
		}
		break;
	case Iex_Binop: {
		IRExprBinop *e = (IRExprBinop *)expr;
		PointerAliasingSet a1 = irexprAliasingClass(
			e->arg1,
			config,
			temps,
			opt,
			buildingAliasTable);
		PointerAliasingSet a2 = irexprAliasingClass(
			e->arg2,
			config,
			temps,
			opt,
			buildingAliasTable);
		switch (e->op) {
		case Iop_Sub64:
			/* x - y is a pointer to zone A if x is a
			 * pointer to zone A and y is not a pointer of
			 * any sort.  Otherwise, it's just not a
			 * pointer. */ {
			if (a2.mightBeNonPointer()) {
				PointerAliasingSet res = a1;
				if (a2.mightPoint())
					res = res | PointerAliasingSet::notAPointer;
				return res;
			} else {
				return PointerAliasingSet::notAPointer;
			}
		}
		case Iop_Add64:
		case Iop_And64:
		case Iop_Xor64:
		case Iop_Or64:
			return a1 | a2;
		case Iop_Shl64:
		case Iop_Shr64:
		case Iop_Sar64:
		case Iop_Mul64:
		case Iop_MullU32:
		case Iop_MullS32:
		case Iop_F64toI64:
		case Iop_32HLto64:
		case Iop_DivModU64to32:
		case Iop_DivModS64to32:
			return PointerAliasingSet::notAPointer;
		default:
			break;
		}
		break;
	}
	case Iex_Mux0X: {
		IRExprMux0X *e = (IRExprMux0X *)expr;
		return irexprAliasingClass(e->expr0,
					   config,
					   temps,
					   opt,
					   buildingAliasTable) |
			irexprAliasingClass(e->exprX,
					    config,
					    temps,
					    opt,
					    buildingAliasTable);
	}
	case Iex_Associative: {
		IRExprAssociative *e = (IRExprAssociative *)expr;
		if (e->nr_arguments == 0)
			return PointerAliasingSet::notAPointer;
		switch (e->op) {
		case Iop_Add64:
			if (e->nr_arguments == 2 &&
			    e->contents[0]->tag == Iex_Const) {
				/* Special case: if X points at space
				   Y then X + k points at Y as well,
				   if k is a small constant. */
				long k = ((IRExprConst *)e->contents[0])->con->Ico.U64;
				if (k >= -4096 && k < 4096) {
					return irexprAliasingClass(e->contents[1],
								   config,
								   temps,
								   opt,
								   buildingAliasTable);
				}
			}
			/* Otherwise, fall through to normal assoc
			 * handling. */
		case Iop_And64:
		case Iop_Or64:
		case Iop_Xor64:
		{
			PointerAliasingSet res = 
				irexprAliasingClass(e->contents[0],
						    config,
						    temps,
						    opt,
						    buildingAliasTable);
			for (int i = 1; i < e->nr_arguments; i++)
				res = res | irexprAliasingClass(e->contents[i],
								config,
								temps,
								opt,
								buildingAliasTable);
			return res;
		}
		default:
			break;
		}
		break;
	}

	case Iex_CCall: {
		IRExprCCall *e = (IRExprCCall *)expr;
		if (!strcmp(e->cee->name, "amd64g_calculate_rflags_c") ||
		    !strcmp(e->cee->name, "amd64g_calculate_rflags_all"))
			return PointerAliasingSet::notAPointer;
		break;
	}

	case Iex_Load: {
		IRExprLoad *iel = (IRExprLoad *)expr;
		bool anyStackInStack = false;
		bool anyStackInMemory = false;
		for (auto it = config.content.begin();
		     (!anyStackInStack || !anyStackInMemory) && it != config.content.end();
		     it++) {
			anyStackInStack |= it->second.stackInStack;
			anyStackInMemory |= it->second.stackInMemory;
		}
		if (anyStackInStack && anyStackInMemory)
			return PointerAliasingSet::anything;
		PointerAliasingSet addrType =
			irexprAliasingClass(iel->addr, config, temps, opt, buildingAliasTable);
		if ( (anyStackInStack && addrType.mightPointAtStack()) ||
		     (anyStackInMemory && addrType.mightPointAtNonStack()) )
			return PointerAliasingSet::anything;
		else
			return PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer;
	}

	default:
		break;
	}
	warning("Don't know how to compute aliasing sets for %s\n", nameIRExpr(expr));
	return PointerAliasingSet::anything;
}

bool
Oracle::RegisterAliasingConfiguration::mightPointOutsideStack(IRExpr *a, const AllowableOptimisations &opt) const
{
	PointerAliasingSet as = irexprAliasingClass(a, *this, NULL, opt, false);
	if (as.mightPointAtNonStack())
		return true;
	else
		return false;
}

bool
Oracle::RegisterAliasingConfiguration::ptrsMightAlias(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt) const
{
	return (irexprAliasingClass(a, *this, NULL, opt, false) &
		irexprAliasingClass(b, *this, NULL, opt, false)).mightPoint();
}

void
Oracle::RegisterAliasingConfiguration::operator |=(const RegisterAliasingConfiguration &config)
{
	for (auto it = config.content.begin(); it != config.content.end(); it++)
		addConfig(it->first, it->second);
}

Oracle::ThreadRegisterAliasingConfiguration
Oracle::getAliasingConfigurationForRip(const StaticRip &rip)
{
	Function f(rip);
	return f.aliasConfigOnEntryToInstruction(rip);
}
Oracle::ThreadRegisterAliasingConfiguration
Oracle::getAliasingConfigurationForRip(const VexRip &rip)
{
	return getAliasingConfigurationForRip(StaticRip(rip));
}

struct cg_header {
	unsigned long rip;
	unsigned long nr;
};

enum read_cg_vexrip_res {
	read_cg_vexrip_error,
	read_cg_vexrip_take,
	read_cg_vexrip_skip
};

static read_cg_vexrip_res
read_cg_vexrip(FILE *f, DynAnalysisRip *out, AddressSpace *as, bool *is_private)
{
	unsigned long rip;
	unsigned nr_entries;
	std::vector<unsigned long> stack;

	if (fread(&rip, sizeof(rip), 1, f) != 1 ||
	    fread(&nr_entries, sizeof(nr_entries), 1, f) != 1)
		return read_cg_vexrip_error;
	stack.reserve(nr_entries);
	for (unsigned x = 0; x < nr_entries; x++) {
		unsigned long a;
		if (fread(&a, sizeof(a), 1, f) != 1)
			return read_cg_vexrip_error;
		if (as->isReadable(a, 1))
			stack.push_back(a);
	}
	if (rip & (1ul << 63)) {
		*is_private = true;
		rip &= ~(1ul << 63);
	} else {
		*is_private = false;
	}
	read_cg_vexrip_res res;
	if (as->isReadable(rip, 1)) {
		stack.push_back(rip);
		res = read_cg_vexrip_take;
	} else {
		res = read_cg_vexrip_skip;
	}
	
	out->nr_rips = stack.size();
	if (out->nr_rips > DynAnalysisRip::DATABASE_RIP_DEPTH)
		out->nr_rips = DynAnalysisRip::DATABASE_RIP_DEPTH;
	for (int x = 0; x < out->nr_rips; x++)
		out->rips[out->nr_rips - x - 1] = stack[stack.size() - x - 1];
	return res;
}

void
Oracle::loadCallGraph(VexPtr<Oracle> &ths, const char *fname, GarbageCollectionToken token)
{
	__set_profiling(oracle_load_call_graph);

	callgraph_t callgraph; 
	std::vector<StaticRip> roots;
	FILE *f = fopen(fname, "r");
	while (!feof(f)) {
		callgraph_entry ce;
		bool is_call;
		DynAnalysisRip branch_rip;
		auto res = read_cg_vexrip(f, &branch_rip, ths->ms->addressSpace, &is_call);
		if (res == read_cg_vexrip_error) {
			if (feof(f))
				break;
			err(1, "reading rip from %s", fname);
		}
		unsigned nr_callees;
		if (fread(&nr_callees, sizeof(nr_callees), 1, f) != 1)
			err(1, "reading number of callees from %s\n", fname);
		bool is_first = true;
		is_call = false;
		for (unsigned x = 0; x < nr_callees; x++) {
			unsigned long callee;
			bool ic;
			if (fread(&callee, sizeof(callee), 1, f) != 1)
				err(1, "reading callee rip from %s", fname);
			if (callee & (1ul << 63)) {
				ic = true;
				callee &= ~(1ul << 63);
			} else {
				ic = false;
			}
			if (is_first) {
				is_call = ic;
				is_first = false;
			} else {
				assert(is_call == ic);
			}
			ce.targets.insert(callee);
		}

		ce.is_call = is_call;
		if (branch_rip.isValid())
			callgraph[StaticRip(branch_rip)] = ce;

		if (ce.is_call) {
			for (auto it = ce.targets.begin(); it != ce.targets.end(); it++)
				roots.push_back(StaticRip(*it));
		}
	}

	fclose(f);

	make_unique(roots);
	Oracle::discoverFunctionHeads(ths, roots, callgraph, token);
}

void
Oracle::findPossibleJumpTargets(const StaticRip &rip,
				const callgraph_t &callgraph_table,
				std::vector<StaticRip> &output)
{
	auto it = callgraph_table.find(rip);
	if (it == callgraph_table.end())
		return;

	output.reserve(it->second.targets.size());
	for (auto it2 = it->second.targets.begin(); it2 != it->second.targets.end(); it2++)
		output.push_back(StaticRip(*it2));
}

void
Oracle::findPreviousInstructions(std::vector<VexRip> &output,
				 const VexRip &rip)
{
	StaticRip sr(functionHeadForInstruction(StaticRip(rip)));
	if (!sr.rip) {
		warning("No function for %s\n", rip.name());
		return;
	}
	Function f(sr);

	/* Build the shortest path from the start of the function to
	   the desired rip using Dijkstra's algorithm.  */
	/* Distance from start of function to key.  Non-present keys
	 * should be assumed to have an infinite length. */
	std::map<StaticRip, unsigned> pathLengths;
	/* Predecessor on best path from start to key. */
	std::map<StaticRip, StaticRip> predecessors; 
	/* We push stuff in here when we discover a new shortest path
	   to that node. */
	std::priority_queue<std::pair<unsigned, StaticRip> > grey;

	pathLengths[f.rip] = 0;
	grey.push(std::pair<unsigned, StaticRip>(0, f.rip));
	while (!grey.empty()) {
		std::pair<unsigned, StaticRip> e(grey.top());
		grey.pop();

		assert(pathLengths.count(e.second));
		unsigned p = pathLengths[e.second] + 1;
		std::vector<StaticRip> successors;
		f.getSuccessors(e.second, successors);
		for (auto it = successors.begin();
		     it != successors.end();
		     it++) {
			if (!pathLengths.count(*it) || pathLengths[*it] >= p) {
				pathLengths[*it] = p;
				predecessors[*it] = e.second;
				grey.push(std::pair<unsigned, StaticRip>(p, *it));
			}
		}
	}
	
	if (!predecessors.count(StaticRip(rip))) {
		/* This can happen if the information from the oracle
		   is inconsistent. */
		warning("Dijkstra failed in %s\n", __func__);
		return;
	}

	for (auto i = predecessors[StaticRip(rip)]; i.rip != 0; i = predecessors[i])
		output.push_back(i.makeVexRip(rip));
}

static sqlite3 *_database;

static void
create_index(const char *name, const char *table, const char *field)
{
	char *s = my_asprintf("CREATE INDEX %s ON %s (%s)", name, table, field);
	sqlite3_exec(_database, s, NULL, NULL, NULL);
	free(s);
}

static sqlite3 *
database(void)
{
	int rc;

	if (_database)
		return _database;
	
	rc = sqlite3_open_v2("static.db", &_database, SQLITE_OPEN_READONLY, NULL);
	if (rc == SQLITE_OK) {
		/* Return existing database */
		goto disable_journalling;
	}

	/* Create new database */
	rc = sqlite3_open_v2("static.db", &_database, SQLITE_OPEN_READWRITE|SQLITE_OPEN_CREATE, NULL);
	assert(rc == SQLITE_OK);

	rc = sqlite3_exec(_database,
			  "CREATE TABLE instructionAttributes (rip INTEGER UNIQUE NOT NULL, liveOnEntry INTEGER,"
			  "alias0 INTEGER,"
			  "alias1 INTEGER,"
			  "alias2 INTEGER,"
			  "alias3 INTEGER,"
			  "alias4 INTEGER,"
			  "alias5 INTEGER,"
			  "alias6 INTEGER,"
			  "alias7 INTEGER,"
			  "alias8 INTEGER,"
			  "alias9 INTEGER,"
			  "alias10 INTEGER,"
			  "alias11 INTEGER,"
			  "alias12 INTEGER,"
			  "alias13 INTEGER,"
			  "alias14 INTEGER,"
			  "alias15 INTEGER,"
			  "stackEscape INTEGER," /* 0 or NULL -> false, 1 -> true */
			  "rbpToRspDeltaState INTEGER NOT NULL DEFAULT 0,"  /* 0 -> unknown, 1 -> known, 2 -> incalculable */
			  "rbpToRspDelta INTEGER NOT NULL DEFAULT 0,"
			  "functionHead INTEGER NOT NULL)",
			  NULL,
			  NULL,
			  NULL);
	assert(rc == SQLITE_OK);
	rc = sqlite3_exec(_database, "CREATE TABLE fallThroughRips (rip INTEGER, dest INTEGER)", NULL, NULL, NULL);
	assert(rc == SQLITE_OK);
	rc = sqlite3_exec(_database, "CREATE TABLE callSuccRips (rip INTEGER, dest INTEGER)", NULL, NULL, NULL);
	assert(rc == SQLITE_OK);
	rc = sqlite3_exec(_database, "CREATE TABLE branchRips (rip INTEGER, dest INTEGER)", NULL, NULL, NULL);
	assert(rc == SQLITE_OK);
	rc = sqlite3_exec(_database, "CREATE TABLE callRips (rip INTEGER, dest INTEGER)", NULL, NULL, NULL);
	assert(rc == SQLITE_OK);
	rc = sqlite3_exec(_database, "CREATE TABLE returnRips (rip INTEGER, dest INTEGER)", NULL, NULL, NULL);
	assert(rc == SQLITE_OK);
	rc = sqlite3_exec(_database, "CREATE TABLE functionAttribs (functionHead INTEGER PRIMARY KEY, registerLivenessCorrect INTEGER NOT NULL, rbpOffsetCorrect INTEGER NOT NULL, aliasingCorrect INTEGER NOT NULL)",
			  NULL, NULL, NULL);
	assert(rc == SQLITE_OK);

	/* Bit of a hack: use this to stash a flag saying whether we
	   believe we've found all function heads already. */
	rc = sqlite3_exec(_database, "CREATE TABLE doneFindFunctionHeads (doneit INTEGER)",
			  NULL, NULL, NULL);
	assert(rc == SQLITE_OK);

disable_journalling:
	/* All of the information in the database can be regenerated
	   by just blowing it away and starting over, so there's not
	   much point in doing lots of journaling and fsync()
	   operations. */
	rc = sqlite3_exec(_database, "PRAGMA journal_mode = OFF", NULL, NULL, NULL);
	assert(rc == SQLITE_OK);
	rc = sqlite3_exec(_database, "PRAGMA synchronous = OFF", NULL, NULL, NULL);
	assert(rc == SQLITE_OK);

	return _database;
}

static sqlite3_stmt *
prepare_statement(const char *stmt)
{
	int rc;
	sqlite3_stmt *res;
	rc = sqlite3_prepare_v2(
		database(),
		stmt,
		-1,
		&res,
		NULL);
	assert(rc == SQLITE_OK);
	return res;
}

static void
extract_int64_column(sqlite3_stmt *stmt, int column, std::vector<unsigned long> &out)
{
	int rc;
	while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
		assert(sqlite3_column_type(stmt, column) == SQLITE_INTEGER);
		out.push_back(sqlite3_column_int64(stmt, column));
	}
	assert(rc == SQLITE_DONE);
	sqlite3_reset(stmt);
}

static void
extract_oraclerip_column(sqlite3_stmt *stmt, int column, std::vector<StaticRip> &out)
{
	int rc;
	while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
		assert(sqlite3_column_type(stmt, column) == SQLITE_INTEGER);
		out.push_back(StaticRip(sqlite3_column_int(stmt, column)));
	}
	assert(rc == SQLITE_DONE);
	sqlite3_reset(stmt);
}

static void
bind_int64(sqlite3_stmt *stmt, int idx, unsigned long val)
{
	int rc;
	rc = sqlite3_bind_int64(stmt, idx, val);
	assert(rc == SQLITE_OK);
}

static void
bind_oraclerip(sqlite3_stmt *stmt, int idx, const StaticRip &rip)
{
	bind_int64(stmt, idx, rip.rip);
}

static void
drop_index(const char *name)
{
	char *s = my_asprintf("DROP INDEX %s", name);
	sqlite3_exec(database(), s, NULL, NULL, NULL);
	free(s);
}

static int
_functionHeadsCorrect(void *_ctxt, int, char **, char **)
{
	bool *flag = (bool *)_ctxt;
	*flag = true;
	return 0;
}
static bool
functionHeadsCorrect(void)
{
	bool flag = false;
	int rc;

	rc = sqlite3_exec(database(), "SELECT * FROM doneFindFunctionHeads",
			  _functionHeadsCorrect, &flag, NULL);
	assert(rc == SQLITE_OK);
	return flag;
}

static void
setFunctionHeadsCorrect(void)
{
	int rc;
	rc = sqlite3_exec(database(), "INSERT INTO doneFindFunctionHeads VALUES (1)",
			  NULL, NULL, NULL);
	assert(rc == SQLITE_OK);
}

void
Oracle::discoverFunctionHeads(VexPtr<Oracle> &ths, std::vector<StaticRip> &heads, const callgraph_t &callgraph, GarbageCollectionToken token)
{
	if (!functionHeadsCorrect()) {
		drop_index("branchDest");
		drop_index("callDest");
		drop_index("fallThroughDest");
		drop_index("callSuccDest");
		drop_index("returnDest");
		drop_index("branchRip");
		drop_index("callRip");
		drop_index("fallThroughRip");
		drop_index("callSuccRip");
		drop_index("instructionAttributesFunctionHead");
		drop_index("instructionAttributesRip");

		struct timeval start;
		gettimeofday(&start, NULL);
		std::set<StaticRip> visited;
		int cntr = 0;
		printf("Discovering function heads...\n");
		sqlite3_exec(database(), "BEGIN TRANSACTION", NULL, NULL, NULL);
		while (!heads.empty()) {
			StaticRip head(heads.back());
			heads.pop_back();
			if (visited.count(head))
				continue;
			visited.insert(head);
			ths->discoverFunctionHead(head, heads, visited, callgraph);
			if (cntr++ % 100 == 0) {
				struct timeval now;
				gettimeofday(&now, NULL);
				now.tv_sec -= start.tv_sec;
				now.tv_usec -= start.tv_usec;
				if (now.tv_usec < 0) {
					now.tv_usec += 1e6;
					now.tv_sec--;
				}
				printf("%zd heads left; %d discovered in %ld.%06ld.\r", heads.size(), cntr,
				       now.tv_sec, now.tv_usec);
				fflush(stdout);
				sqlite3_exec(database(), "END TRANSACTION", NULL, NULL, NULL);
				sqlite3_exec(database(), "BEGIN TRANSACTION", NULL, NULL, NULL);
			}
			LibVEX_maybe_gc(token);
		}
		sqlite3_exec(database(), "END TRANSACTION", NULL, NULL, NULL);
		printf("Done discovering function heads\n");
		setFunctionHeadsCorrect();

		create_index("branchDest", "branchRips", "dest");
		create_index("callDest", "callRips", "dest");
		create_index("fallThroughDest", "fallThroughRips", "dest");
		create_index("callSuccDest", "callSuccRips", "dest");
		create_index("branchRip", "branchRips", "rip");
		create_index("callRip", "callRips", "rip");
		create_index("fallThroughRip", "fallThroughRips", "rip");
		create_index("callSuccRip", "callSuccRips", "rip");
		create_index("instructionAttributesFunctionHead", "instructionAttributes", "functionHead");
		create_index("instructionAttributesRip", "instructionAttributes", "rip");

		ths->buildReturnAddressTable();
		create_index("returnDest", "returnRips", "dest");
	}

	printf("Calculate register liveness...\n");
	calculateRegisterLiveness(ths, token);
	printf("Calculate aliasing map...\n");
	calculateAliasing(ths, token);
	printf("Calculate RBP map...\n");
	calculateRbpToRspOffsets(ths, token);
	printf("Done static analysis phase\n");
}

void
Oracle::buildReturnAddressTable()
{
	static sqlite3_stmt *stmt1, *stmt2, *stmt3;
	std::vector<StaticRip> returnInstructions;
	int rc;

	if (!stmt1)
		stmt1 = prepare_statement("SELECT rip FROM returnRips WHERE dest = 0");
	extract_oraclerip_column(stmt1, 0, returnInstructions);

	if (!stmt2)
		stmt2 = prepare_statement("DELETE FROM returnRips");
	rc = sqlite3_step(stmt2);
	assert(rc == SQLITE_DONE);
	sqlite3_reset(stmt2);

	printf("Building return address table\n");
	if (!stmt3)
		stmt3 = prepare_statement("INSERT INTO returnRips (rip, dest) VALUES (?, ?)");

	for (auto it = returnInstructions.begin();
	     it != returnInstructions.end();
	     it++) {
		std::set<StaticRip> headsProcessed;
		std::vector<StaticRip> toProcess;
		toProcess.push_back(*it);
		while (!toProcess.empty()) {
			StaticRip head(functionHeadForInstruction(toProcess.back()));
			toProcess.pop_back();
			if (headsProcessed.count(head))
				continue;
			headsProcessed.insert(head);
			std::vector<StaticRip> callers;
			Function(head).addPredecessorsCall(head, callers);
			for (auto it2 = callers.begin(); it2 != callers.end(); it2++) {
				/* *it2 is the address of a call
				   instruction which we might be
				   returning from.  The return address
				   is the end of that call
				   instruction. */
				StaticRip returnAddress(
					it2->rip + getInstructionSize(ms->addressSpace, *it2));
				bind_oraclerip(stmt3, 1, *it);
				bind_oraclerip(stmt3, 2, returnAddress);
				rc = sqlite3_step(stmt3);
				assert(rc == SQLITE_DONE);
				sqlite3_reset(stmt3);
			}

			/* Non-call predecessors of a function head
			   might be tail calls.  Add them to the queue
			   so that we process them later. */
			Function(head).addPredecessorsNonCall(head, toProcess);
		}
	}
	printf("Finished building return address table\n");
}

Oracle::LivenessSet
Oracle::Function::liveOnEntry(const StaticRip &rip, bool isHead)
{
	static sqlite3_stmt *stmt;
	int rc;

	if (!stmt)
		stmt = prepare_statement("SELECT liveOnEntry FROM instructionAttributes WHERE rip = ?");
	bind_oraclerip(stmt, 1, rip);
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE || rc == SQLITE_ROW);
	if (rc == SQLITE_DONE || sqlite3_column_type(stmt, 0) == SQLITE_NULL) {
		/* Still using default live set for this isntruction. */
		sqlite3_reset(stmt);
		if (isHead)
			return Oracle::LivenessSet::argRegisters;
		else
			return Oracle::LivenessSet();
	}
	unsigned long r;
	r = sqlite3_column_int64(stmt, 0);
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE);
	sqlite3_reset(stmt);
	return LivenessSet(r);
}

static PointerAliasingSet
PointerAliasingSet_from_int(int r)
{
	switch (r) {
	case 0:
		return PointerAliasingSet::nothing;
	case 1:
		return PointerAliasingSet::notAPointer;
	case 2:
		return PointerAliasingSet::stackPointer;
	case 3:
		return PointerAliasingSet::stackPointer | PointerAliasingSet::notAPointer;
	case 4:
		return PointerAliasingSet::nonStackPointer;
	case 5:
		return PointerAliasingSet::nonStackPointer | PointerAliasingSet::notAPointer;
	case 6:
		return PointerAliasingSet::nonStackPointer | PointerAliasingSet::stackPointer;
	case 7:
		return PointerAliasingSet::anything;
	default:
		abort();
	}
}

static int
int_from_PointerAliasingSet(const PointerAliasingSet &r)
{
	int acc;
	assert(!r.pointsAtFrames());
	acc = 0;
	if (r.mightBeNonPointer())
		acc |= 1;
	if (r.mightPointAtStack())
		acc |= 2;
	if (r.mightPointAtNonStack())
		acc |= 4;
	return acc;
}

Oracle::ThreadRegisterAliasingConfiguration
Oracle::Function::aliasConfigOnEntryToInstruction(const StaticRip &rip, bool *b)
{
	static sqlite3_stmt *stmt;
	int rc;

	if (!stmt)
		stmt = prepare_statement(
			"SELECT alias0, alias1, alias2, alias3, alias4, alias5, alias6, alias7, alias8, alias9, alias10, alias11, alias12, alias13, alias14, alias15, stackEscape FROM instructionAttributes WHERE rip = ?");
	bind_oraclerip(stmt, 1, rip);
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE || rc == SQLITE_ROW);
	if (rc == SQLITE_DONE) {
		sqlite3_reset(stmt);
		*b = false;
		return ThreadRegisterAliasingConfiguration::unknown;
	}
	int i;
	ThreadRegisterAliasingConfiguration res;
	for (i = 0; i < NR_REGS; i++) {
		unsigned long r;
		if (sqlite3_column_type(stmt, i) == SQLITE_NULL) {
			r = 0;
		} else {
			assert(sqlite3_column_type(stmt, i) == SQLITE_INTEGER);
			r = sqlite3_column_int64(stmt, i);
		}
		res.v[i] = PointerAliasingSet_from_int(r);
	}
	if (sqlite3_column_type(stmt, i) == SQLITE_NULL) {
		res.stackInMemory = false;
		res.stackInStack = false;
	} else {
		assert(sqlite3_column_type(stmt, i) == SQLITE_INTEGER);
		unsigned long r = sqlite3_column_int64(stmt, i);
		assert(!(r & ~3));
		res.stackInMemory = !!(r & 1);
		res.stackInStack  = !!(r & 2);
	}
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE);
	sqlite3_reset(stmt);
	*b = true;
	return res;
}

bool
Oracle::Function::aliasConfigOnEntryToInstruction(const StaticRip &rip, Oracle::ThreadRegisterAliasingConfiguration *out)
{
	bool res;
	*out = aliasConfigOnEntryToInstruction(rip, &res);
	return res;
}

Oracle::ThreadRegisterAliasingConfiguration
Oracle::Function::aliasConfigOnEntryToInstruction(const StaticRip &rip)
{
	bool ign;
	return aliasConfigOnEntryToInstruction(rip, &ign);
}

bool
Oracle::functionNeverReturns(const StaticRip &sr)
{
	for (auto it = terminalFunctions.begin(); it != terminalFunctions.end(); it++)
		if (sr == *it)
			return true;
	return false;
}

void
Oracle::findNoReturnFunctions()
{
	/* Some library functions which never return */
	static const char *const terminals[] =
		{ "pthread_exit", "abort", "exit", "__stack_chk_fail",
		  "__assert_fail", "__assert_perror_fail", "__assert",
		  "err", "errx", "verr", "verrx", "__pthread_unwind_next",
		  "longjmp", "_longjmp", "siglongjmp",
		  "quick_exit", "_exit", "_Exit", "__error_noreturn",
		  "__error_at_line_noreturn",

		  "SLang_exit_error",

		  "png_error", "png_chunk_error", "png_err",

		  "g_assertion_message", "g_assertion_message_expr",
		  "g_assertion_message_cmpstr", "g_assertion_message_cmpnum",
		  "g_assertion_message_error", "g_assert_warning",

		  "_ZSt9terminatev", "_ZSt10unexpectedv",
		  NULL };
	for (int i = 0; terminals[i]; i++) {
		unsigned long r;
		r = ms->elfData->getPltAddress(ms->addressSpace, terminals[i]);
		if (r)
			terminalFunctions.push_back(StaticRip(r));
	}
}

void
Oracle::discoverFunctionHead(const StaticRip &x, std::vector<StaticRip> &heads,
			     std::set<StaticRip> &visited,
			     const callgraph_t &callgraph_table)
{
	Function work(x);

	/* Start by building a CFG of the function's instructions. */
	std::vector<StaticRip> unexplored;
	std::set<StaticRip> explored;
	unexplored.push_back(x);
	while (!unexplored.empty()) {
		StaticRip rip = unexplored.back();
		unexplored.pop_back();

		if (explored.count(rip))
			continue;

		if (rip != x && visited.count(rip))
			continue;

		IRSB *irsb = getIRSBForRip(ms->addressSpace, rip, false);
		if (!irsb)
			continue;

		int end_of_instruction;
		int start_of_instruction = 0;
		while (start_of_instruction < irsb->stmts_used) {
			IRStmt *stmt = irsb->stmts[start_of_instruction];
			assert(stmt->tag == Ist_IMark);
			StaticRip r(((IRStmtIMark *)stmt)->addr.rip);
			if (explored.count(r))
				break;
			if (r != x && visited.count(r))
				break;

			std::vector<StaticRip> branch;
			std::vector<StaticRip> fallThrough;
			std::vector<StaticRip> callSucc;
			std::vector<StaticRip> callees;
			for (end_of_instruction = start_of_instruction + 1;
			     end_of_instruction < irsb->stmts_used && irsb->stmts[end_of_instruction]->tag != Ist_IMark;
			     end_of_instruction++) {
				stmt = irsb->stmts[end_of_instruction];
				if (stmt->tag == Ist_Exit)
					branch.push_back(StaticRip(((IRStmtExit *)stmt)->dst.rip));
			}

			rip = StaticRip( ((IRStmtIMark *)irsb->stmts[start_of_instruction])->addr.rip );
			if (end_of_instruction == irsb->stmts_used) {
				if (irsb->jumpkind == Ijk_Call) {
					if (!irsb->next_is_const ||
					    !functionNeverReturns(StaticRip(irsb->next_const.rip)))
						callSucc.push_back(StaticRip(extract_call_follower(irsb)));
					if (irsb->next_is_const)
						callees.push_back(StaticRip(irsb->next_const.rip));
					else
						findPossibleJumpTargets(rip, callgraph_table, callees);
				} else {
					if (irsb->next_is_const)
						fallThrough.push_back(StaticRip(irsb->next_const.rip));
					else if (irsb->jumpkind != Ijk_Ret)
						findPossibleJumpTargets(rip, callgraph_table, fallThrough);
				}
			} else {
				stmt = irsb->stmts[end_of_instruction];
				assert(dynamic_cast<IRStmtIMark *>(stmt));
				fallThrough.push_back(StaticRip( ((IRStmtIMark *)stmt)->addr.rip ));
			}

			heads.insert(heads.end(), callees.begin(), callees.end());
			unexplored.insert(unexplored.end(), fallThrough.begin(), fallThrough.end());
			unexplored.insert(unexplored.end(), callSucc.begin(), callSucc.end());
			unexplored.insert(unexplored.end(), branch.begin(), branch.end());

			/* This can sometimes contain duplicates if
			   you're looking at e.g. a rep cmps
			   instruction, which looks like this:

			   l1:
			   if (ecx == 0) goto next;
			   t1 = *rdi
			   t2 = *rsi;
			   ecx--;
			   if (t1 != t2) goto next;
			   goto l1;
			   next:

			   i.e. two branches to next. */
			make_unique(branch);

			explored.insert(r);
			bool isReturn = end_of_instruction == irsb->stmts_used &&
				irsb->jumpkind == Ijk_Ret;
			if (!work.addInstruction(r, isReturn, callees, fallThrough, callSucc, branch)) {
				/* Already explored this instruction
				 * as part of some other function.
				 * That means we have some kind of
				 * tail call going on. */

				/* This is a bit messy.  We need to
				 * purge everything we've done so far,
				 * plus whatever instruction
				 * previously discovered r, introduce
				 * a new head for r, and then make
				 * sure that we re-process this
				 * function and whatever previously
				 * discovered r. */
				purgeFunction(x);
				StaticRip old_head(functionHeadForInstruction(r));
				purgeFunction(old_head);
				/* Processed in stack order, so push
				 * in the inverse of the order we want
				 * the dealt with. */
				heads.push_back(x);
				heads.push_back(old_head);
				heads.push_back(r);
				visited.erase(x);
				visited.erase(old_head);
				return;
			}

			start_of_instruction = end_of_instruction;
		}
	}
}

void
Oracle::Function::calculateRbpToRspOffsets(AddressSpace *as, Oracle *oracle)
{
	if (rbpToRspOffsetsCorrect())
		return;

	if (debug_static_rbp_offsets)
		printf("Calculate RBP->RSP offsets for %s\n", rip.name());

	/* The correct answer for the function head instruction is
	   always ``impossible'' */
	oracle->setRbpToRspOffset(rip, RbpToRspOffsetStateImpossible, 0);

	std::vector<StaticRip> instrsToRecalculate1;
	std::vector<StaticRip> instrsToRecalculate2;

	getInstructionsInFunction(instrsToRecalculate1);

	while (1) {
		for (auto it = instrsToRecalculate1.begin();
		     it != instrsToRecalculate1.end();
		     it++) {
			bool t = false;
			updateRbpToRspOffset(*it, as, &t, oracle);
			if (t)
				getSuccessors(*it, instrsToRecalculate2);
		}
		instrsToRecalculate1.clear();
		if (instrsToRecalculate2.empty())
			break;

		for (auto it = instrsToRecalculate2.begin();
		     it != instrsToRecalculate2.end();
		     it++) {
			bool t = false;
			updateRbpToRspOffset(*it, as, &t, oracle);
			if (t)
				getSuccessors(*it, instrsToRecalculate1);
		}

		instrsToRecalculate2.clear();
		if (instrsToRecalculate1.empty())
			break;
	}

	setRbpToRspOffsetsCorrect(true);
}

void
Oracle::Function::calculateRegisterLiveness(Oracle *oracle, AddressSpace *as, bool *done_something)
{
	bool changed;

	if (registerLivenessCorrect())
		return;

	std::vector<StaticRip> instrsToRecalculate1;
	std::vector<StaticRip> instrsToRecalculate2;

	getInstructionsInFunction(instrsToRecalculate1);

	std::reverse(instrsToRecalculate1.begin(),
		     instrsToRecalculate1.end());

	changed = false;
	while (1) {
		for (auto it = instrsToRecalculate1.begin();
		     it != instrsToRecalculate1.end();
		     it++) {
			bool t = false;
			updateLiveOnEntry(oracle, *it, as, &t);
			if (t)
				addPredecessorsNonCall(*it, instrsToRecalculate2);
		}
		instrsToRecalculate1.clear();
		if (instrsToRecalculate2.empty())
			break;
		changed = true;

		for (auto it = instrsToRecalculate2.begin();
		     it != instrsToRecalculate2.end();
		     it++) {
			bool t = false;
			updateLiveOnEntry(oracle, *it, as, &t);
			if (t)
				addPredecessorsNonCall(*it, instrsToRecalculate1);
		}

		instrsToRecalculate2.clear();
		if (instrsToRecalculate1.empty())
			break;
	}

	setRegisterLivenessCorrect(true);

	if (changed) {
		*done_something = true;
		std::vector<StaticRip> callers;
		getFunctionCallers(callers);
		for (auto it = callers.begin();
		     it != callers.end();
		     it++)
			(Function(*it)).setRegisterLivenessCorrect(false);
	}
}

void
Oracle::Function::calculateAliasing(AddressSpace *as, bool *done_something)
{
	{
		bool aValid;
		ThreadRegisterAliasingConfiguration a(aliasConfigOnEntryToInstruction(rip, &aValid));
		if (aValid) {
			ThreadRegisterAliasingConfiguration b(a);
			b |= ThreadRegisterAliasingConfiguration::functionEntryConfiguration;
			if (a != b) {
				*done_something = true;
				setAliasConfigOnEntryToInstruction(rip, b);
			}
		} else {
			*done_something = true;
			setAliasConfigOnEntryToInstruction(rip, ThreadRegisterAliasingConfiguration::functionEntryConfiguration);
		}
	}

	if (debug_static_alias) {
		printf("Calculate aliasing for function head %s\n", rip.name());
		printf("Entry configuration:\n");
		dbg_database_queryf("SELECT rip, alias0, alias1, alias2, alias3, alias4, alias5, alias6, alias7, alias8, alias9, alias10, alias11, alias12, alias13, alias14, alias15, stackEscape FROM instructionAttributes WHERE functionHead = %ld ORDER BY rip",
				   rip.rip);
	}

	std::vector<StaticRip> needsUpdating;
	needsUpdating.push_back(rip);
	while (!needsUpdating.empty()) {
		StaticRip rip(needsUpdating.back());
		needsUpdating.pop_back();
		updateSuccessorInstructionsAliasing(rip, as, &needsUpdating, done_something);
	}

	if (debug_static_alias) {
		printf("Finished recomputing aliasing for function head %s\n", rip.name());
		printf("Exit configuration:\n");
		dbg_database_queryf("SELECT rip, alias0, alias1, alias2, alias3, alias4, alias5, alias6, alias7, alias8, alias9, alias10, alias11, alias12, alias13, alias14, alias15, stackEscape FROM instructionAttributes WHERE functionHead = %ld ORDER BY rip",
				    rip.rip);
	}
}

void
Oracle::Function::updateLiveOnEntry(Oracle *oracle, const StaticRip &rip, AddressSpace *as, bool *changed)
{
	LivenessSet res;

	IRSB *irsb = getIRSBForRip(as, rip, true);
	IRStmt **statements = irsb->stmts;
	int nr_statements;
	for (nr_statements = 1;
	     nr_statements < irsb->stmts_used && statements[nr_statements]->tag != Ist_IMark;
	     nr_statements++)
		;

	std::vector<StaticRip> fallThroughRips;
	std::vector<StaticRip> callees;

	if (nr_statements == irsb->stmts_used) {
		if (irsb->jumpkind == Ijk_Call) {
			if (!irsb->next_is_const ||
			    !oracle->functionNeverReturns(StaticRip(irsb->next_const.rip)))
				fallThroughRips.push_back(StaticRip(extract_call_follower(irsb)));
			if (irsb->next_is_const)
				callees.push_back(StaticRip(irsb->next_const.rip));
			else
				getInstructionCallees(rip, callees);
		} else {
			if (irsb->next_is_const)
				fallThroughRips.push_back(StaticRip(irsb->next_const.rip));
			else {
				getInstructionFallThroughs(rip, fallThroughRips);
				if (irsb->jumpkind == Ijk_Ret)
					assert(fallThroughRips.size() == 0);
			}
		}
	} else {
		assert(dynamic_cast<IRStmtIMark *>(statements[nr_statements]));
		fallThroughRips.push_back(StaticRip( ((IRStmtIMark *)statements[nr_statements])->addr.rip ));
	}

	for (auto it = fallThroughRips.begin();
	     it != fallThroughRips.end();
	     it++)
		res |= liveOnEntry(*it, false);
	for (auto it = callees.begin();
	     it != callees.end();
	     it++) {
		Function f(*it);
		res |= f.liveOnEntry(*it, true) & LivenessSet::argRegisters;
	}

	for (int i = nr_statements - 1; i >= 1; i--) {
		IRStmt *stmt = statements[i];
		switch (stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			abort();
		case Ist_AbiHint:
			break;
		case Ist_Put:
			res = res.define(((IRStmtPut *)stmt)->target);
			res = irexprUsedValues(res, ((IRStmtPut *)stmt)->data);
			break;
		case Ist_PutI:
			res = irexprUsedValues(res, ((IRStmtPutI *)stmt)->data);
			res = irexprUsedValues(res, ((IRStmtPutI *)stmt)->ix);
			break;
		case Ist_Store:
			res = irexprUsedValues(res, ((IRStmtStore *)stmt)->data);
			res = irexprUsedValues(res, ((IRStmtStore *)stmt)->addr);
			break;
		case Ist_CAS:
			res = irexprUsedValues(res, ((IRStmtCAS *)stmt)->details->addr);
			res = irexprUsedValues(res, ((IRStmtCAS *)stmt)->details->expdHi);
			res = irexprUsedValues(res, ((IRStmtCAS *)stmt)->details->expdLo);
			res = irexprUsedValues(res, ((IRStmtCAS *)stmt)->details->dataHi);
			res = irexprUsedValues(res, ((IRStmtCAS *)stmt)->details->dataLo);
			break;
		case Ist_Dirty:
			res = irexprUsedValues(res, ((IRStmtDirty *)stmt)->details->guard);
			for (int j = 0; ((IRStmtDirty *)stmt)->details->args[j]; j++)
				res = irexprUsedValues(res, ((IRStmtDirty *)stmt)->details->args[j]);
			res = irexprUsedValues(res, ((IRStmtDirty *)stmt)->details->mAddr);
			break;
		case Ist_MBE:
			abort();
		case Ist_Exit: {
			VexRip _branchRip = ((IRStmtExit *)stmt)->dst.rip;
			res |= liveOnEntry(StaticRip(_branchRip), false);
			res = irexprUsedValues(res, ((IRStmtExit *)stmt)->guard);
			break;
		}
		case Ist_StartAtomic:
			break;
		case Ist_EndAtomic:
			break;
		}
	}

	LivenessSet current = liveOnEntry(rip, rip == this->rip);
	res |= current;
	if (res != current) {
		*changed = true;
		static sqlite3_stmt *stmt;
		int rc;
		if (!stmt)
			stmt = prepare_statement(
				"UPDATE instructionAttributes SET liveOnEntry = ? WHERE rip = ?");
		bind_int64(stmt, 1, res.mask);
		bind_oraclerip(stmt, 2, rip);
		rc = sqlite3_step(stmt);
		assert(rc == SQLITE_DONE);
		sqlite3_reset(stmt);
	}
}

class RewriteRegisterExpr : public IRExprTransformer {
	threadAndRegister idx;
	IRExpr *to;
protected:
	IRExpr *transformIex(IRExprGet *what) {
		if (what->reg == idx)
			return to;
		else
			return NULL;
	}
public:
	RewriteRegisterExpr(threadAndRegister _idx, IRExpr *_to)
		: idx(_idx), to(_to)
	{
	}
};
static IRExpr *
rewriteRegister(IRExpr *expr, threadAndRegister offset, IRExpr *to)
{
	RewriteRegisterExpr rre(offset, to);
	return rre.doit(expr);
}

void
Oracle::Function::updateRbpToRspOffset(const StaticRip &rip, AddressSpace *as, bool *changed, Oracle *oracle)
{
	RbpToRspOffsetState current_state;
	unsigned long current_offset;
	RbpToRspOffsetState state;
	unsigned long offset = -99999999; /* Shut the compiler up. */

	oracle->getRbpToRspOffset(rip, &current_state, &current_offset);
	if (debug_static_rbp_offsets)
		printf("updateRbpToRspOffset(%s); current state %d, %ld\n",
		       rip.name(),
		       current_state,
		       current_offset);

	if (current_state == RbpToRspOffsetStateImpossible) {
		/* By monotonicity, the result will be
		   RbpToRspOffsetStateImpossible, so bypass and get
		   out early. */
		return;
	}

	/* Try to figure out what this instruction actually does. */
	IRSB *irsb = getIRSBForRip(as, rip, true);
	if (!irsb)
		return;
	IRStmt **statements = irsb->stmts;
	int nr_statements;
	for (nr_statements = 1;
	     nr_statements < irsb->stmts_used && statements[nr_statements]->tag != Ist_IMark;
	     nr_statements++)
		;

	if (debug_static_rbp_offsets)
		ppIRSB(irsb, stdout);

	long delta_offset = 0;
	IRExpr *rbp = NULL;
	IRExpr *rsp = NULL;
	int j;

	/* We assume called functions never change rsp or rbp, so
	 * treat calls as nops. */
	if (nr_statements == irsb->stmts_used &&
	    irsb->jumpkind == Ijk_Call) {
		if (debug_static_rbp_offsets)
			printf("Call; treat as nop\n");
		goto join_predecessors;
	}
	/* Scan backwards through the instruction for any writes to
	   either of the registers of interest. */
	for (j = nr_statements - 1; j >= 0; j--) {
		IRStmt *stmt = statements[j];
		if (stmt->tag == Ist_Put) {
			IRStmtPut *p = (IRStmtPut *)stmt;
			if (p->target.isReg()) {
				if (p->target.asReg() == OFFSET_amd64_RSP && !rsp)
					rsp = IRExpr_Get(OFFSET_amd64_RSP, Ity_I64, STATIC_THREAD, 0);
				if (p->target.asReg() == OFFSET_amd64_RBP && !rbp)
					rbp = IRExpr_Get(OFFSET_amd64_RBP, Ity_I64, STATIC_THREAD, 0);
			}
			if (rsp)
				rsp = rewriteRegister(rsp,
						      p->target,
						      p->data);
			if (rbp)
				rbp = rewriteRegister(rbp,
						      p->target,
						      p->data);
		} else if (stmt->tag == Ist_CAS) {
			if (((IRStmtCAS *)stmt)->details->oldLo.isReg() &&
			    (((IRStmtCAS *)stmt)->details->oldLo.asReg() == OFFSET_amd64_RSP ||
			     ((IRStmtCAS *)stmt)->details->oldLo.asReg() == OFFSET_amd64_RBP))
				goto impossible;
		} else if (stmt->tag == Ist_Dirty) {
			threadAndRegister tmp(((IRStmtDirty *)stmt)->details->tmp);
			IRType t = Ity_I1;
			if (!strcmp(((IRStmtDirty *)stmt)->details->cee->name,
				    "helper_load_128"))
				t = Ity_I128;
			else if (!strcmp(((IRStmtDirty *)stmt)->details->cee->name,
				    "helper_load_64"))
				t = Ity_I64;
			else if (!strcmp(((IRStmtDirty *)stmt)->details->cee->name,
					 "helper_load_32"))
				t = Ity_I32;
			else if (!strcmp(((IRStmtDirty *)stmt)->details->cee->name,
					 "helper_load_16"))
				t = Ity_I16;
			else if (!strcmp(((IRStmtDirty *)stmt)->details->cee->name,
					 "helper_load_8"))
				t = Ity_I8;
			else if (!strcmp(((IRStmtDirty *)stmt)->details->cee->name,
					 "amd64g_dirtyhelper_RDTSC")) {
				if (debug_static_rbp_offsets)
					printf("Can't handle RDTSC\n");
				goto impossible_clean;
			} else
				goto impossible;
			IRExpr *v = IRExpr_Load(t,
						((IRStmtDirty *)stmt)->details->args[0]);
			if (rsp)
				rsp = rewriteRegister(rsp, tmp, v);
			if (rbp)
				rbp = rewriteRegister(rbp, tmp, v);
		}
	}

	if (rsp)
		rsp = simplifyIRExpr(rsp, AllowableOptimisations::defaultOptimisations);
	if (rbp)
		rbp = simplifyIRExpr(rbp, AllowableOptimisations::defaultOptimisations);
	if (rsp && rsp->tag == Iex_Get && ((IRExprGet *)rsp)->reg.asReg() == OFFSET_amd64_RSP)
		rsp = NULL;
	if (rbp && rbp->tag == Iex_Get && ((IRExprGet *)rbp)->reg.asReg() == OFFSET_amd64_RBP)
		rbp = NULL;
	if (debug_static_rbp_offsets)
		printf("RBP = %s, RSP = %s\n",
		       rbp ? nameIRExpr(rbp) : "<null>",
		       rsp ? nameIRExpr(rsp) : "<null>");
	if (!rsp && !rbp) {
		if (debug_static_rbp_offsets)
			printf("No modifications to RBP or RSP -> join predecessors\n");
		goto join_predecessors;
	}
	if (rsp && rbp) {
		if (debug_static_rbp_offsets)
			printf("Disallowed odifications to both RBP and RSP -> impossible\n");
		goto impossible_clean;
	}
	
	if (rsp) {
		if (rsp->tag == Iex_Get) {
			IRExprGet *g = (IRExprGet *)rsp;
			if (g->reg.asReg() == OFFSET_amd64_RSP) {
				abort();
			} else if (g->reg.asReg() == OFFSET_amd64_RBP) {
				offset = 0;
				state = RbpToRspOffsetStateValid;
				if (debug_static_rbp_offsets)
					printf("Set RSP = RBP\n");
				goto done;
			}
		} else if (rsp->tag == Iex_Associative) {
			IRExprAssociative *a = (IRExprAssociative *)rsp;
			if (a->op == Iop_Add64 &&
			    a->nr_arguments >= 2 &&
			    a->contents[0]->tag == Iex_Const &&
			    a->contents[1]->tag == Iex_Get) {
				IRExprGet *base = (IRExprGet *)a->contents[1];
				if (base->reg.asReg() == OFFSET_amd64_RSP) {
					delta_offset = ((IRExprConst *)a->contents[0])->con->Ico.U64;
					if (debug_static_rbp_offsets)
						printf("Set RSP = RSP+%ld\n", delta_offset);
					goto join_predecessors;
				} else if (base->reg.asReg() == OFFSET_amd64_RBP) {
					offset = ((IRExprConst *)a->contents[0])->con->Ico.U64;
					state = RbpToRspOffsetStateValid;
					if (debug_static_rbp_offsets)
						printf("Set RSP = RBP+%ld\n", offset);
					goto done;
				}
			}
		}

		if (debug_static_rbp_offsets)
			printf("Unhandleable update to rsp\n");
		goto impossible_clean;
	} else {
		assert(rbp);

		if (rbp->tag == Iex_Get) {
			IRExprGet *g = (IRExprGet *)rbp;
			if (g->reg.asReg() == OFFSET_amd64_RBP) {
				abort();
			} else if (g->reg.asReg() == OFFSET_amd64_RSP) {
				offset = 0;
				state = RbpToRspOffsetStateValid;
				if (debug_static_rbp_offsets)
					printf("Set RBP = RSP\n");
				goto done;
			}
		} else if (rbp->tag == Iex_Associative) {
			IRExprAssociative *a = (IRExprAssociative *)rbp;
			if (a->op == Iop_Add64 &&
			    a->nr_arguments >= 2 &&
			    a->contents[0]->tag == Iex_Const &&
			    a->contents[1]->tag == Iex_Get) {
				IRExprGet *base = (IRExprGet *)a->contents[1];
				IRConst *o = ((IRExprConst *)a->contents[0])->con;
				if (base->reg.asReg() == OFFSET_amd64_RBP) {
					delta_offset = -o->Ico.U64;
					if (debug_static_rbp_offsets)
						printf("Set RBP + RBP+%ld\n", -delta_offset);
					goto join_predecessors;
				} else if (base->reg.asReg() == OFFSET_amd64_RSP) {
					offset = -o->Ico.U64;
					state = RbpToRspOffsetStateValid;
					if (debug_static_rbp_offsets)
						printf("Set RBP = RSP+%ld\n", -offset);
					goto done;
				}
			}
		}

		if (debug_static_rbp_offsets)
			printf("Unhandleable update to rbp\n");

		/* If the compiler's done base pointer elimination
		   then RBP can contain almost anything and it's not
		   worth trying to warn about it. */
		goto impossible_clean;
	}

join_predecessors:
	state = RbpToRspOffsetStateUnknown;
	{
		std::vector<StaticRip> predecessors;
		addPredecessorsNonCall(rip, predecessors);

		for (auto it = predecessors.begin();
		     it != predecessors.end();
		     it++) {
			enum RbpToRspOffsetState pred_state;
			unsigned long pred_offset;
			oracle->getRbpToRspOffset(*it, &pred_state, &pred_offset);
			if (pred_state == RbpToRspOffsetStateImpossible) {
				if (debug_static_rbp_offsets)
					printf("Predecessor %s -> impossible, give up\n", it->name());
				goto impossible_clean;
			}
			if (pred_state == RbpToRspOffsetStateUnknown) {
				if (debug_static_rbp_offsets)
					printf("Predecessor %s -> unknown, continue\n", it->name());
				continue;
			}
			assert(pred_state == RbpToRspOffsetStateValid);
			if (state == RbpToRspOffsetStateUnknown) {
				state = RbpToRspOffsetStateValid;
				offset = pred_offset;
				if (debug_static_rbp_offsets)
					printf("Predecesor %s valid at %ld, current unknown, take predecessor\n",
					       it->name(), offset);
				continue;
			}
			assert(state == RbpToRspOffsetStateValid);
			if (offset != pred_offset) {
				if (debug_static_rbp_offsets)
					printf("Predecessor %s has incompatible offset %ld\n",
					       it->name(), pred_offset);
				goto impossible_clean;
			}
			if (debug_static_rbp_offsets)
				printf("Predecessor %s has compatible offset %ld\n",
				       it->name(), pred_offset);
		}
	}
	if (state == RbpToRspOffsetStateUnknown) {
		/* Predecessor state is still unknown, nothing
		 * we can do. */
		if (debug_static_rbp_offsets)
			printf("Ultimate state is unknown\n");
		return;
	}

	offset += delta_offset;

done:
	if (current_state == state && current_offset == offset) {
		/* Already correct, nothing to do */
		if (debug_static_rbp_offsets)
			printf("Achieved nothing; state %d, offset %ld\n",
			       state, offset);
		return;
	}

	if (debug_static_rbp_offsets)
		printf("Update state\n");
	*changed = true;
	oracle->setRbpToRspOffset(rip, state, offset);
	return;

impossible:
	printf("Cannot do stack offset calculations in first instruction of: ");
	ppIRSB(irsb, stdout);

	warning("Whoops, screwed up stack offset calculation in %s\n", rip.name());

	dbg_break("badness");

impossible_clean:
	if (debug_static_rbp_offsets)
		printf("Ended in an impossible state\n");
	state = RbpToRspOffsetStateImpossible;
	offset = 0;
	goto done;
}

void
Oracle::Function::updateSuccessorInstructionsAliasing(const StaticRip &rip,
						      AddressSpace *as,
						      std::vector<StaticRip> *changed,
						      bool *done_something)
{
	const AllowableOptimisations opt(AllowableOptimisations::defaultOptimisations.setAddressSpace(as));
	RegisterAliasingConfiguration config;
	config.addConfig(STATIC_THREAD, aliasConfigOnEntryToInstruction(rip));
	ThreadRegisterAliasingConfiguration &tconfig(config.content[0].second);
	std::map<threadAndRegister, PointerAliasingSet> temporaryAliases;
	IRStmt *st;

	if (debug_static_alias) {
		printf("Update successor aliasing for %s\n", rip.name());
		printf("Config at start of instr:\n");
		config.prettyPrint(stdout);
	}

	int nr_statements;
	IRSB *irsb = getIRSBForRip(as, rip, true);
	if (!irsb)
		return;
	IRStmt **statements = irsb->stmts;
	for (nr_statements = 1;
	     nr_statements < irsb->stmts_used && statements[nr_statements]->tag != Ist_IMark;
	     nr_statements++)
		;
	if (debug_static_alias)
		ppIRSB(irsb, stdout);

	for (int i = 1; i < nr_statements; i++) {
		st = statements[i];
		switch (st->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			abort();
		case Ist_AbiHint:
			break;
		case Ist_Put: {
			IRStmtPut *p = (IRStmtPut *)st;
			if (p->target.isReg()) {
				config.set(p->target,
					   irexprAliasingClass(p->data,
							       config,
							       &temporaryAliases,
							       opt,
							       true));
			} else {
				temporaryAliases.insert(
					std::pair<threadAndRegister, PointerAliasingSet>(p->target,
											 irexprAliasingClass(p->data,
													     config,
													     &temporaryAliases,
													     opt,
													     true)));
			}
			break;
		}
		case Ist_PutI:
			/* Assume that PutIs never target the NR_REGS registers */
			break;
		case Ist_Store:
			if (!tconfig.stackInMemory || !tconfig.stackInStack) {
				PointerAliasingSet data = irexprAliasingClass(((IRStmtStore *)st)->data,
									      config,
									      &temporaryAliases,
									      opt,
									      true);
				if (!data.mightPointAtStack())
					break;
				PointerAliasingSet addr = irexprAliasingClass(((IRStmtStore *)st)->addr,
									      config,
									      &temporaryAliases,
									      opt,
									      true);
				tconfig.stackInMemory |= addr.mightPointAtNonStack();
				tconfig.stackInStack  |= addr.mightPointAtStack();
			}
			break;
		case Ist_CAS: {
			IRStmtCAS *s = (IRStmtCAS *)st;
			if (s->details->oldLo.isTemp()) {
				temporaryAliases.insert(
					std::pair<threadAndRegister, PointerAliasingSet>(
						s->details->oldLo,
						PointerAliasingSet::anything));
			} else {
				config.set(s->details->oldLo, PointerAliasingSet::anything);
			}
			break;
		}
		case Ist_Dirty:
			if (((IRStmtDirty *)st)->details->tmp.isValid()) {
				PointerAliasingSet res;
				if ((tconfig.stackInStack && tconfig.stackInMemory) ||
				    strcmp(((IRStmtDirty *)st)->details->cee->name, "helper_load_64")) {
					res = PointerAliasingSet::anything;
				} else {
					PointerAliasingSet addr(
						irexprAliasingClass(((IRStmtDirty *)st)->details->args[0],
								    config,
								    &temporaryAliases,
								    opt,
								    true));
					if ( (addr.mightPointAtStack() && tconfig.stackInStack) ||
					     (addr.mightPointAtNonStack() && tconfig.stackInMemory) )
						res = PointerAliasingSet::anything;
					else
						res = PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer;
				}
				temporaryAliases.insert(
					std::pair<threadAndRegister, PointerAliasingSet>(
						((IRStmtDirty *)st)->details->tmp,
						res));
			}
			break;
		case Ist_MBE:
			abort();
		case Ist_Exit: {
			StaticRip _branchRip(((IRStmtExit *)st)->dst.rip);
			ThreadRegisterAliasingConfiguration bConfig(aliasConfigOnEntryToInstruction(_branchRip));
			ThreadRegisterAliasingConfiguration newExitConfig(bConfig);
			newExitConfig |= tconfig;
			if (newExitConfig != bConfig) {
#warning This isn't even slightly right in the case where _branchRip hasn't been visited yet.
				changed->push_back(_branchRip);
				setAliasConfigOnEntryToInstruction(_branchRip, newExitConfig);
			}
			break;
		}
		case Ist_StartAtomic:
			break;
		case Ist_EndAtomic:
			break;
		}
	}

	if (debug_static_alias) {
		printf("Config at end of instr:\n");
		config.prettyPrint(stdout);
	}
	std::vector<StaticRip> callees;
	getInstructionCallees(rip, callees);
	if (!callees.empty())
		tconfig.v[0] = PointerAliasingSet::notAPointer;
	for (auto it = callees.begin();
	     tconfig.v[0] != PointerAliasingSet::anything && it != callees.end();
	     it++) {
		LivenessSet ls = (Function(*it)).liveOnEntry(*it, true);
		/* If any of the argument registers contain stack
		   pointers on entry, the return value can potentially
		   also contain stack pointers. */
		/* This isn't perfectly accurate, but it's a pretty
		   close approximation. */
		bool stackEscapes = false;
		/* rcx = 2, rdx = 4, rsi = 0x40, rdi = 0x80,
		 * r8 = 0x100, r9 = 0x200 */
#define ARG_REGISTERS 0x3c6
		for (int i = 0; !stackEscapes && i < NR_REGS; i++) {
			if (!(ARG_REGISTERS & (1 << i)))
				continue;
			if (!(ls.mask & (1 << i)))
				continue;
			if (tconfig.v[i].mightPointAtStack())
				stackEscapes = true;
		}
#undef ARG_REGISTERS
		if (stackEscapes)
			tconfig.v[0] = tconfig.v[0] | PointerAliasingSet::stackPointer;
		tconfig.v[0] = tconfig.v[0] | PointerAliasingSet::nonStackPointer;
#warning What about clearing the state of call-clobbered registers?
#warning Should allow the stack pointer to taint the return address if the stack has leaked in config!
#warning Should really say the stack has leaked in config if it escapes here!
	}
	
	std::vector<StaticRip> _fallThroughRips;
	if (nr_statements == irsb->stmts_used) {
		if (irsb->jumpkind != Ijk_Call) {
			if (irsb->next_is_const)
				_fallThroughRips.push_back(StaticRip(irsb->next_const.rip));
			else
				getInstructionFallThroughs(rip, _fallThroughRips);
		} else {
			_fallThroughRips.push_back(StaticRip(extract_call_follower(irsb)));
		}
	} else {
		assert(statements[nr_statements]->tag == Ist_IMark);
		IRStmtIMark *im = (IRStmtIMark *)statements[nr_statements];
		_fallThroughRips.push_back(StaticRip(im->addr.rip));
	}

	for (auto it = _fallThroughRips.begin();
	     it != _fallThroughRips.end();
	     it++) {
		bool b;
		ThreadRegisterAliasingConfiguration succ_config =
			aliasConfigOnEntryToInstruction(*it, &b);
		if (b) {
			ThreadRegisterAliasingConfiguration new_config = succ_config;
			new_config |= tconfig;
			if (new_config != succ_config) {
				if (debug_static_alias)
					printf("Change successor config %s\n",
					       it->name());
				*done_something = true;
				changed->push_back(*it);
				setAliasConfigOnEntryToInstruction(*it, new_config);
			}
		} else {
			warning("No instruction %s?\n", it->name());
		}
	}
}

void
Oracle::Function::addPredecessorsDirect(const StaticRip &rip, std::vector<StaticRip> &out)
{
	static sqlite3_stmt *stmt1, *stmt2;

	if (!stmt1 || !stmt2) {
		assert(!stmt1 && !stmt2);
		stmt1 = prepare_statement("SELECT rip FROM fallThroughRips WHERE dest = ?");
		stmt2 = prepare_statement("SELECT rip FROM branchRips WHERE dest = ?");
	}
	bind_oraclerip(stmt1, 1, rip);
	bind_oraclerip(stmt2, 1, rip);
	extract_oraclerip_column(stmt1, 0, out);
	extract_oraclerip_column(stmt2, 0, out);
}

void
Oracle::Function::addPredecessorsNonCall(const StaticRip &rip, std::vector<StaticRip> &out)
{
	static sqlite3_stmt *stmt;

	addPredecessorsDirect(rip, out);
	if (!stmt)
		stmt = prepare_statement("SELECT rip FROM callSuccRips WHERE dest = ?");
	bind_oraclerip(stmt, 1, rip);
	extract_oraclerip_column(stmt, 0, out);
}

void
Oracle::Function::addPredecessorsCall(const StaticRip &rip, std::vector<StaticRip> &out)
{
	static sqlite3_stmt *stmt;

	if (!stmt)
		stmt = prepare_statement("SELECT rip FROM callRips WHERE dest = ?");
	bind_oraclerip(stmt, 1, rip);
	extract_oraclerip_column(stmt, 0, out);
}

void
Oracle::Function::addPredecessorsReturn(const StaticRip &rip, std::vector<StaticRip> &out)
{
	static sqlite3_stmt *stmt;

	if (!stmt)
		stmt = prepare_statement("SELECT rip FROM returnRips WHERE dest = ?");
	bind_oraclerip(stmt, 1, rip);
	extract_oraclerip_column(stmt, 0, out);
}

void
Oracle::Function::getInstructionFallThroughs(const StaticRip &rip, std::vector<StaticRip> &succ)
{
	static sqlite3_stmt *stmt1, *stmt2;

	if (!stmt1)
		stmt1 = prepare_statement("SELECT dest FROM fallThroughRips WHERE rip = ?");
	if (!stmt2)
		stmt2 = prepare_statement("SELECT dest FROM callSuccRips WHERE rip = ?");
	bind_oraclerip(stmt1, 1, rip);
	bind_oraclerip(stmt2, 1, rip);

	succ.clear();
	extract_oraclerip_column(stmt1, 0, succ);
	extract_oraclerip_column(stmt2, 0, succ);
}

void
Oracle::Function::getInstructionsInFunction(std::vector<StaticRip> &succ) const
{
	static sqlite3_stmt *stmt1;

	if (!stmt1)
		stmt1 = prepare_statement("SELECT rip FROM instructionAttributes WHERE functionHead = ?");
	bind_oraclerip(stmt1, 1, rip);

	succ.clear();
	extract_oraclerip_column(stmt1, 0, succ);	
}

void
Oracle::Function::getSuccessors(const StaticRip &rip, std::vector<StaticRip> &succ)
{
	static sqlite3_stmt *stmt1, *stmt2, *stmt3;

	if (!stmt1 || !stmt2) {
		assert(!stmt1 && !stmt2);
		stmt1 = prepare_statement("SELECT dest FROM fallThroughRips WHERE rip = ?");
		stmt2 = prepare_statement("SELECT dest FROM callSuccRips WHERE rip = ?");
		stmt3 = prepare_statement("SELECT dest FROM branchRips WHERE rip = ?");
	}
	bind_oraclerip(stmt1, 1, rip);
	bind_oraclerip(stmt2, 1, rip);
	bind_oraclerip(stmt3, 1, rip);

	extract_oraclerip_column(stmt1, 0, succ);
	extract_oraclerip_column(stmt2, 0, succ);
	extract_oraclerip_column(stmt3, 0, succ);
}

void
Oracle::Function::setAliasConfigOnEntryToInstruction(const StaticRip &r,
						     const ThreadRegisterAliasingConfiguration &config)
{
	static sqlite3_stmt *stmt;
	int i;
	int rc;
	unsigned long stackEscape;

	if (!stmt)
		stmt = prepare_statement(
			"UPDATE instructionAttributes SET alias0 = ?, alias1 = ?, alias2 = ?, alias3 = ?, alias4 = ?, alias5 = ?, alias6 = ?, alias7 = ?, alias8 = ?, alias9 = ?, alias10 = ?, alias11 = ?, alias12 = ?, alias13 = ?, alias14 = ?, alias15 = ?, stackEscape = ? WHERE rip = ?"
			);
	for (i = 0; i < NR_REGS; i++)
		bind_int64(stmt, i + 1, int_from_PointerAliasingSet(config.v[i]));
	stackEscape = 0;
	if (config.stackInMemory)
		stackEscape |= 1;
	if (config.stackInStack)
		stackEscape |= 2;
	bind_int64(stmt, NR_REGS + 1, stackEscape);
	bind_oraclerip(stmt, NR_REGS + 2, r);
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE);
	sqlite3_reset(stmt);
}

bool
Oracle::Function::addInstruction(const StaticRip &rip,
				 bool isReturn,
				 const std::vector<StaticRip> &callees,
				 const std::vector<StaticRip> &fallThrough,
				 const std::vector<StaticRip> &callSucc,
				 const std::vector<StaticRip> &branch)
{
	static sqlite3_stmt *stmt1;
	static sqlite3_stmt *stmt2;
	static sqlite3_stmt *stmt3;
	static sqlite3_stmt *stmt4;
	static sqlite3_stmt *stmt5;
	static sqlite3_stmt *stmt6;
	int rc;

	if (!stmt1)
		stmt1 = prepare_statement("INSERT INTO instructionAttributes (rip, functionHead) VALUES (?, ?)");
	bind_oraclerip(stmt1, 1, rip);
	bind_oraclerip(stmt1, 2, this->rip);
	rc = sqlite3_step(stmt1);
	sqlite3_reset(stmt1);
	if (rc == SQLITE_CONSTRAINT) {
		/* We have a duplicte of this instruction.  Fail the insert. */
		return false;
	}
	assert(rc == SQLITE_DONE);

	if (!stmt2)
		stmt2 = prepare_statement("INSERT INTO fallThroughRips (rip, dest) VALUES (?, ?)");
	for (auto it = fallThrough.begin();
	     it != fallThrough.end();
	     it++) {
		bind_oraclerip(stmt2, 1, rip);
		bind_oraclerip(stmt2, 2, *it);
		rc = sqlite3_step(stmt2);
		assert(rc == SQLITE_DONE);
		rc = sqlite3_reset(stmt2);
		assert(rc == SQLITE_OK);
	}

	if (!stmt6)
		stmt6 = prepare_statement("INSERT INTO callSuccRips (rip, dest) VALUES (?, ?)");
	for (auto it = callSucc.begin();
	     it != callSucc.end();
	     it++) {
		bind_oraclerip(stmt6, 1, rip);
		bind_oraclerip(stmt6, 2, *it);
		rc = sqlite3_step(stmt6);
		assert(rc == SQLITE_DONE);
		rc = sqlite3_reset(stmt6);
		assert(rc == SQLITE_OK);
	}

	if (!stmt3)
		stmt3 = prepare_statement("INSERT INTO branchRips (rip, dest) VALUES (?, ?)");
	for (auto it = branch.begin();
	     it != branch.end();
	     it++) {
		bind_oraclerip(stmt3, 1, rip);
		bind_oraclerip(stmt3, 2, *it);
		rc = sqlite3_step(stmt3);
		assert(rc == SQLITE_DONE);
		rc = sqlite3_reset(stmt3);
		assert(rc == SQLITE_OK);
	}

	if (!stmt4)
		stmt4 = prepare_statement("INSERT INTO callRips (rip, dest) VALUES (?, ?)");
	for (auto it = callees.begin();
	     it != callees.end();
	     it++) {
		bind_oraclerip(stmt4, 1, rip);
		bind_oraclerip(stmt4, 2, *it);
		rc = sqlite3_step(stmt4);
		assert(rc == SQLITE_DONE);
		rc = sqlite3_reset(stmt4);
		assert(rc == SQLITE_OK);
	}

	if (isReturn) {
		if (!stmt5)
			stmt5 = prepare_statement("INSERT INTO returnRips (rip, dest) VALUES (?, 0)");
		bind_oraclerip(stmt5, 1, rip);
		rc = sqlite3_step(stmt5);
		assert(rc == SQLITE_DONE);
		rc = sqlite3_reset(stmt5);
		assert(rc == SQLITE_OK);
	}

	return true;
}

class prepared_stmt {
public:
	sqlite3_stmt *stmt;
	prepared_stmt(const char *content) {
		stmt = prepare_statement(content);
	}
	~prepared_stmt() {
		sqlite3_finalize(stmt);
	}
	void bindOracleRip(int idx, const StaticRip &sr) {
		bind_oraclerip(stmt, idx, sr);
	}
	void run() {
		int r;
		do {
			r = sqlite3_step(stmt);
		} while (r == SQLITE_ROW);
		assert(r == SQLITE_DONE);
		sqlite3_reset(stmt);
	}
};

void
Oracle::purgeFunction(const StaticRip &functionHead)
{
	Function f(functionHead);
	std::vector<StaticRip> rips;

	f.getInstructionsInFunction(rips);

	static prepared_stmt purgeInstrAttributes("DELETE FROM instructionAttributes WHERE functionHead = ?");
	purgeInstrAttributes.bindOracleRip(1, functionHead);
	purgeInstrAttributes.run();

	struct {
		void operator()(const char *tableName, std::vector<StaticRip> &rips) {
			char *p = my_asprintf("DELETE FROM %sRips WHERE rip = ? OR dest = ?", tableName);
			prepared_stmt stmt(p);
			for (auto it = rips.begin(); it != rips.end(); it++) {
				stmt.bindOracleRip(1, *it);
				stmt.bindOracleRip(2, *it);
				stmt.run();
			}
			free(p);
		}
	} doit;
	doit("fallThrough", rips);
	doit("callSucc", rips);
	doit("branch", rips);
	doit("call", rips);
	doit("return", rips);
	static prepared_stmt purge_function_attribs("DELETE FROM functionAttribs WHERE functionHead = ?");
	purge_function_attribs.bindOracleRip(1, functionHead);
	purge_function_attribs.run();
}

void
Oracle::Function::getInstructionCallees(const StaticRip &rip, std::vector<StaticRip> &out)
{
	static sqlite3_stmt *stmt;

	if (!stmt)
		stmt = prepare_statement("SELECT dest FROM callRips WHERE rip = ?");
	bind_oraclerip(stmt, 1, rip);
	extract_oraclerip_column(stmt, 0, out);
}

void
Oracle::Function::getFunctionCallers(std::vector<StaticRip> &out)
{
	static sqlite3_stmt *stmt;

	if (!stmt)
		stmt = prepare_statement("SELECT rip FROM callRips WHERE dest = ?");
	bind_oraclerip(stmt, 1, rip);
	extract_oraclerip_column(stmt, 0, out);
}

void
Oracle::getFunctions(std::vector<StaticRip> &out)
{
	static sqlite3_stmt *stmt;

	if (!stmt)
		stmt = prepare_statement("SELECT DISTINCT functionHead FROM instructionAttributes");
	extract_oraclerip_column(stmt, 0, out);
}

bool
Oracle::Function::registerLivenessCorrect() const
{
	static sqlite3_stmt *stmt;
	if (!stmt)
		stmt = prepare_statement("SELECT registerLivenessCorrect FROM functionAttribs WHERE functionHead = ?");
	bind_oraclerip(stmt, 1, rip);
	std::vector<unsigned long> a;
	extract_int64_column(stmt, 0, a);
	if (a.size() == 0)
		return false;
	assert(a.size() == 1);
	return !!a[0];
}

bool
Oracle::Function::rbpToRspOffsetsCorrect() const
{
	static sqlite3_stmt *stmt;
	if (!stmt)
		stmt = prepare_statement("SELECT rbpOffsetCorrect FROM functionAttribs WHERE functionHead = ?");
	bind_oraclerip(stmt, 1, rip);
	std::vector<unsigned long> a;
	extract_int64_column(stmt, 0, a);
	if (a.size() == 0)
		return false;
	assert(a.size() == 1);
	return !!a[0];
}

bool
Oracle::Function::aliasingConfigCorrect() const
{
	static sqlite3_stmt *stmt;
	if (!stmt)
		stmt = prepare_statement("SELECT aliasingCorrect FROM functionAttribs WHERE functionHead = ?");
	bind_oraclerip(stmt, 1, rip);
	std::vector<unsigned long> a;
	extract_int64_column(stmt, 0, a);
	if (a.size() == 0)
		return false;
	assert(a.size() == 1);
	return !!a[0];
}

void
Oracle::Function::setRegisterLivenessCorrect(bool x)
{
	static sqlite3_stmt *stmt;
	if (!stmt)
		stmt = prepare_statement("INSERT OR REPLACE INTO functionAttribs (functionHead, registerLivenessCorrect, rbpOffsetCorrect, aliasingCorrect) VALUES (?, ?, 0, 0)");
	bind_oraclerip(stmt, 1, rip);
	bind_int64(stmt, 2, x);

	int rc;
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE);
	rc = sqlite3_reset(stmt);
	assert(rc == SQLITE_OK);
}

void
Oracle::Function::setRbpToRspOffsetsCorrect(bool x)
{
	static sqlite3_stmt *stmt;
	if (!stmt)
		stmt = prepare_statement("UPDATE functionAttribs SET rbpOffsetCorrect = ? WHERE functionHead = ?");
	bind_oraclerip(stmt, 2, rip);
	bind_int64(stmt, 1, x);

	int rc;
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE);
	rc = sqlite3_reset(stmt);
	assert(rc == SQLITE_OK);
}

void
Oracle::getRbpToRspOffset(const StaticRip &rip, enum RbpToRspOffsetState *state, unsigned long *offset)
{
	static sqlite3_stmt *stmt;
	if (!stmt)
		stmt = prepare_statement("SELECT rbpToRspDeltaState,rbpToRspDelta FROM instructionAttributes WHERE rip = ?");
	bind_oraclerip(stmt, 1, rip);
	int rc = sqlite3_step(stmt);
	if (rc == SQLITE_DONE) {
		/* Not entered in database yet */
		*state = RbpToRspOffsetStateUnknown;
		*offset = 0;
	} else {
		assert(rc == SQLITE_ROW);
		assert(sqlite3_column_type(stmt, 0) == SQLITE_INTEGER);
		assert(sqlite3_column_type(stmt, 1) == SQLITE_INTEGER);
		switch (sqlite3_column_int64(stmt, 0)) {
		case 0:
			*state = RbpToRspOffsetStateUnknown;
			break;
		case 1:
			*state = RbpToRspOffsetStateValid;
			break;
		case 2:
			*state = RbpToRspOffsetStateImpossible;
			break;
		default:
			abort();
		}
		*offset = sqlite3_column_int64(stmt, 1);
		rc = sqlite3_step(stmt);
		assert(rc == SQLITE_DONE);
	}
	sqlite3_reset(stmt);
}

void
Oracle::setRbpToRspOffset(const StaticRip &r,
			  RbpToRspOffsetState state,
			  unsigned long offset)
{
	static sqlite3_stmt *stmt;
	int rc;

	if (!stmt)
		stmt = prepare_statement(
			"UPDATE instructionAttributes SET rbpToRspDeltaState = ?, rbpToRspDelta = ? WHERE rip = ?");
	switch (state) {
	case RbpToRspOffsetStateUnknown:
		bind_int64(stmt, 1, 0);
		break;
	case RbpToRspOffsetStateValid:
		bind_int64(stmt, 1, 1);
		break;
	case RbpToRspOffsetStateImpossible:
		bind_int64(stmt, 1, 2);
		break;
	default:
		abort();
	}
	bind_int64(stmt, 2, offset);
	bind_oraclerip(stmt, 3, r);
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE);
	sqlite3_reset(stmt);
}


void
Oracle::Function::setAliasingConfigCorrect(bool x)
{
	static sqlite3_stmt *stmt;
	if (!stmt)
		stmt = prepare_statement("UPDATE functionAttribs SET aliasingCorrect = ? WHERE functionHead = ?");
	bind_oraclerip(stmt, 2, rip);
	bind_int64(stmt, 1, x);

	int rc;
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE);
	rc = sqlite3_reset(stmt);
	assert(rc == SQLITE_OK);
}

StaticRip
Oracle::functionHeadForInstruction(const StaticRip &rip)
{
	__set_profiling(functionHeadForInstruction);
	static sqlite3_stmt *stmt;
	if (!stmt)
		stmt = prepare_statement("SELECT functionHead FROM instructionAttributes WHERE rip = ?");
	bind_oraclerip(stmt, 1, rip);
	std::vector<StaticRip> x;
	extract_oraclerip_column(stmt, 0, x);
	if (x.size() == 0)
		return StaticRip(0);
	assert(x.size() == 1);
	return x[0];
}

/* Hackety hackety hack: getRbpToRspDelta() returns the RBP->RSP delta
   at the *start* of an instruction, whereas getRbpToRspOffset()
   returns it at the end. */
bool
Oracle::getRbpToRspDelta(const StaticRip &rip, long *out)
{
	std::vector<StaticRip> pred;
	Function(StaticRip(rip)).addPredecessorsNonCall(rip, pred);
	if (pred.size() == 0) {
		/* Can't do anything if we don't have any
		 * predecessors. */
		return false;
	}
	RbpToRspOffsetState state;
	unsigned long o;
	getRbpToRspOffset(pred[0], &state, &o);
	if (state != RbpToRspOffsetStateValid)
		return false;
	for (unsigned x = 1; x < pred.size(); x++) {
		unsigned long o2;
		getRbpToRspOffset(pred[x], &state, &o2);
		if (state != RbpToRspOffsetStateValid ||
		    o2 != o)
			return false;
	}
	*out = o;
	return true;
}
bool
Oracle::getRbpToRspDelta(const VexRip &rip, long *out)
{
	if (getRbpToRspDelta(StaticRip(rip), out))
		return true;

	/* Bit of a hack, but not really.  If we're at the start of a
	   function, and the enclosing function has a known delta, we
	   can quite easily calculate the delta for this function from
	   the delta for the enclosing one. */
	if (rip.stack.size() > 1 && isFunctionHead(StaticRip(rip))) {
		long d2;
		VexRip parentVr(rip);
		parentVr.rtrn();
		if (!getRbpToRspDelta(StaticRip(parentVr), &d2))
			return false;
		*out = d2 - 8;
		return true;
	}
	/* Another hack: if we're right at the end of a function
	   (i.e. right on the ret instruction) then we can also grab
	   the caller's delta. */
	if (rip.stack.size() > 1) {
		IRSB *irsb = getIRSBForRip(rip, false);
		assert(irsb);
		int nr_marks = 0;
		for (int i = 0; i < irsb->stmts_used && nr_marks < 2; i++)
			if (irsb->stmts[i]->tag == Ist_IMark)
				nr_marks++;
		if (irsb->jumpkind == Ijk_Ret && nr_marks == 1) {
			VexRip parentVr(rip);
			long d2;
			parentVr.rtrn();
			if (!getRbpToRspDelta(StaticRip(parentVr), &d2))
				return false;
			*out = d2 - 8;
			return true;
		}
	}
	/* One more hack: try to do something sensible for the initial
	 * ``push rbp'' instruction. */
	StaticRip head(functionHeadForInstruction(StaticRip(rip)));
	if (rip.unwrap_vexrip() == head.rip + 1 &&
	    ms->addressSpace->fetch<unsigned char>(head.rip, NULL) == 0x55) {
		/* The first instruction in the function is push rbp,
		   and we're the second instruction -> can calculate
		   our delta from the parent function's delta. */
		VexRip parentVr(rip);
		long d2;
		parentVr.rtrn();
		if (!getRbpToRspDelta(StaticRip(parentVr), &d2))
			return false;
		*out = d2 - 16;
		return true;
	}

	/* Give up */
	return false;
}

void
Oracle::getInstrCallees(const VexRip &vr, std::vector<VexRip> &out)
{
	StaticRip sr(vr);
	std::vector<StaticRip> outSr;
	Function(sr).getInstructionCallees(sr, outSr);
	VexRip vrEnd = vr + getInstructionSize(ms->addressSpace, sr);
	for (auto it = outSr.begin(); it != outSr.end(); it++) {
		VexRip newVr(vrEnd);
		newVr.call(it->rip);
		out.push_back(newVr);
	}
}

void
Oracle::getInstrFallThroughs(const VexRip &vr, std::vector<VexRip> &out)
{
	StaticRip sr(vr);
	std::vector<StaticRip> outSr;
	Function(sr).getInstructionFallThroughs(sr, outSr);
	VexRip vrEnd = vr + getInstructionSize(ms->addressSpace, sr);
	for (auto it = outSr.begin(); it != outSr.end(); it++) {
		VexRip newVr(vrEnd);
		newVr.jump(it->rip);
		out.push_back(newVr);
	}
}

VexRip
StaticRip::makeVexRip(const VexRip &from)
{
	VexRip r(from);
	r.jump(rip);
	return r;
}

void
dbg_database_query(const char *query)
{
	if (!_database) {
		printf("Database not open yet!\n");
		return;
	}

	int rc;

	sqlite3_stmt *stmt;
	const char *tail;
	rc = sqlite3_prepare_v2(
		_database,
		(char *)query,
		-1,
		&stmt,
		&tail);
	if (rc != SQLITE_OK) {
		printf("Error compiling %s: %d\n", query, rc);
		return;
	}
	if (tail != NULL && *tail != '\0')
		printf("WARNING: Ignoring garbage after SQL statement: %s\n", tail);
	if (!stmt) {
		printf("No SQL statement\n");
		return;
	}


	int nr_columns = sqlite3_column_count(stmt);
	if (nr_columns == 0) {
		printf("No data returned\n");
		rc = sqlite3_step(stmt);
		if (rc != SQLITE_DONE)
			printf("Error return %d from sqlite3_step\n", rc);
	} else {
		int cwidth = 225 / nr_columns;
		int wide_columns = 225 % nr_columns;
		if (cwidth > 20) {
			cwidth = 20;
			wide_columns = 0;
		}
		for (int i = 0; i < nr_columns; i++)
			printf("%*.*s",
			       cwidth + (i < wide_columns),
			       cwidth + (i < wide_columns) - 1,
			       sqlite3_column_origin_name(stmt, i));
		printf("\n-----------------------------------------------------------\n");

		while (1) {
			rc = sqlite3_step(stmt);
			if (rc == SQLITE_DONE) {
				printf("End of data\n");
				break;
			}
			if (rc != SQLITE_ROW) {
				printf("Unexpected return code %d from sqlite3_step\n", rc);
				break;
			}
			for (int i = 0; i < nr_columns; i++) {
				int w = cwidth + (i < wide_columns);
				switch (sqlite3_column_type(stmt, i)) {
				case SQLITE_INTEGER:
					printf("%*llx", w, sqlite3_column_int64(stmt, i));
					break;
				case SQLITE_FLOAT:
					printf("%*f", w, sqlite3_column_double(stmt, i));
					break;
				case SQLITE_TEXT: {
					const unsigned char *s = sqlite3_column_text(stmt, i);
					if (strlen((const char *)s) >= (size_t)w)
						printf("%*.*s... ",
						       w - 4,
						       w - 4,
						       s);
					else
						printf("%*s", w, s);
					break;
				}
				case SQLITE_BLOB: {
					const unsigned char *s = (const unsigned char *)sqlite3_column_blob(stmt, i);
					int sz = sqlite3_column_bytes(stmt, i);
					bool trunc;
					if (sz * 2 >= w) {
						trunc = true;
						sz = w - 2;
					} else {
						trunc = false;
					}
					for (int j = 0; j < sz; j++)
						printf("%02x", s[j]);
					if (trunc)
						printf("...");
					break;
				}
				case SQLITE_NULL:
					printf("%*s", w, "NULL");
					break;
				default:
					abort();
				}
			}
			printf("\n");
		}
	}
	sqlite3_finalize(stmt);
}

void
dbg_database_queryf(const char *query, ...)
{
	va_list args;
	char *q;
	va_start(args, query);
	if (vasprintf(&q, query, args) < 0)
		errx(1, "vasprintf(%s)", query);
	va_end(args);
	dbg_database_query(q);
	free(q);
}

bool
parseThreadVexRip(ThreadVexRip *tr, const char *str, const char **suffix)
{
	if (!parseDecimalUInt(&tr->thread, str, &str) ||
	    !parseThisChar(':', str, &str) ||
	    !parseVexRip(&tr->rip, str, suffix))
		return false;
	return true;
}

/* Returns true if @vr is believed to be the first instruction in a
 * function. */
bool
Oracle::isFunctionHead(const StaticRip &sr)
{
	static sqlite3_stmt *stmt;

	if (!stmt)
		stmt = prepare_statement("SELECT COUNT(*) FROM instructionAttributes WHERE functionHead = ?");
	bind_oraclerip(stmt, 1, sr);
	std::vector<unsigned long> a;
	extract_int64_column(stmt, 0, a);
	assert(a.size() == 1);
	return a[0];
}
bool
Oracle::isFunctionHead(const VexRip &vr)
{
	return isFunctionHead(StaticRip(vr));
}

/* The call stack for @vr is possibly truncated.  Examine our
   databases and try to figure out what might possibly be supposed to
   be at the top of it. */
void
Oracle::getPossibleStackTruncations(const VexRip &vr,
				    std::vector<unsigned long> &callers)
{
	/* Find the thing on the bottom of the stack, then find which
	   function it's in, and then find all callers of that
	   function. */
	StaticRip baseRip(vr.stack[0]);
	StaticRip functionHead = functionHeadForInstruction(baseRip);
	std::vector<StaticRip> predecessors;
	Function(functionHead).addPredecessorsCall(functionHead, predecessors);
	/* That tells us the address of the start of the call
	   instruction, but we really want the end of the
	   instruction. */
	for (auto it = predecessors.begin(); it != predecessors.end(); it++) {
		callers.push_back(it->rip + getInstructionSize(ms->addressSpace, *it));
	}
}

/* Find all of the instructions which might have executed immediately
 * before @vr. */
void
Oracle::findPredecessors(const VexRip &vr, bool includeCallPredecessors,
			 std::vector<VexRip> &out)
{
	StaticRip sr(vr);
	Function f(sr);

	std::vector<StaticRip> nonCall;
	f.addPredecessorsDirect(sr, nonCall);
	for (auto it = nonCall.begin(); it != nonCall.end(); it++)
		out.push_back(it->makeVexRip(vr));
	if (includeCallPredecessors) {
		std::vector<StaticRip> call;
		f.addPredecessorsCall(sr, call);
		if (call.size() != 0) {
			VexRip parentVr(vr);
			parentVr.rtrn();
			for (auto it = call.begin(); it != call.end(); it++) {
				unsigned long expectedReturn =
					it->rip + getInstructionSize(
						ms->addressSpace,
						*it);
				if (expectedReturn == parentVr.unwrap_vexrip())
					out.push_back(it->makeVexRip(parentVr));
			}
		}
	}
	std::vector<StaticRip> rtrn;
	f.addPredecessorsReturn(sr, rtrn);
	for (auto it = rtrn.begin(); it != rtrn.end(); it++) {
		VexRip r(vr);
		r.call(it->rip);
		out.push_back(r);
	}

	if (rtrn.empty() && nonCall.empty()) {
		std::vector<StaticRip> callSucc;
		static sqlite3_stmt *stmt;
		if (!stmt)
			stmt = prepare_statement("SELECT rip FROM callSuccRips WHERE dest = ?");
		bind_oraclerip(stmt, 1, sr);
		extract_oraclerip_column(stmt, 0, callSucc);

		for (auto it = callSucc.begin(); it != callSucc.end(); it++)
			out.push_back(it->makeVexRip(vr));
	}
}

void
Oracle::findPredecessors(unsigned long rip, std::set<unsigned long> &out)
{
	StaticRip sr(rip);
	Function f(sr);

	std::vector<StaticRip> nonCall;
	f.addPredecessorsDirect(sr, nonCall);
	for (auto it = nonCall.begin(); it != nonCall.end(); it++)
		out.insert(it->rip);
}

bool
Oracle::isPltCall(const VexRip &vr)
{
	unsigned long r = vr.unwrap_vexrip();
	if (!ms->elfData ||
	    r < ms->elfData->plt_start ||
	    r >= ms->elfData->plt_end)
		return false;
	return true;
}

LibraryFunctionType
Oracle::identifyLibraryCall(const VexRip &vr)
{
	/* Bit of a hack: we know what a PLT entry looks like, so we
	 * can do the symbol lookup. */
	unsigned long r = vr.unwrap_vexrip();
	unsigned idx = ms->addressSpace->fetch<unsigned>(r + 7, NULL);
	const char *name;

	name = ms->elfData->lookupPltSymbol(idx);
	if (!name) {
		warning("Warning: don't know what library function to call at %s\n",
			vr.name());
		return LibraryFunctionTemplate::none;
	}
	LibraryFunctionType res = LibraryFunctionTemplate::parse(name);
	if (res == LibraryFunctionTemplate::none)
		warning("Warning: Ignoring call to %s at %s\n",
			name, vr.name());
	return res;
}

PointerAliasingSet
Oracle::RegisterAliasingConfiguration::lookupRegister(const threadAndRegister &r, bool buildingAliasTable) const
{
	/* This is only safe for SSA-form machines */
	if (buildingAliasTable)
		assert(r.gen() == 0);
	else
		assert(r.gen() != 0);

	/* Assume that anything which isn't a GPR isn't a pointer.
	   True for x86. */
	if (r.asReg() >= Oracle::NR_REGS * 8)
		return PointerAliasingSet::notAPointer;
	/* Can't say anything about non-default generations. */
	if (!buildingAliasTable && r.gen() != (unsigned)-1)
		return PointerAliasingSet::anything;
	for (auto it = content.begin(); it != content.end(); it++) {
		if (it->first == r.tid())
			return it->second.v[r.asReg() / 8];
	}

	/* Don't have an aliasing configuration for this thread ->
	   could go anywhere. */
	return PointerAliasingSet::anything;
}

void
Oracle::RegisterAliasingConfiguration::set(const threadAndRegister &r, const PointerAliasingSet &v)
{
	if (r.asReg() >= NR_REGS * 8)
		return;
	/* The class of RSP is always hard-wired to be just a stack
	 * pointer. */
	if (r.asReg() == OFFSET_amd64_RSP)
		return;
	for (auto it = content.begin(); it != content.end(); it++) {
		if (it->first == r.tid()) {
			it->second.v[r.asReg() / 8] = v;
			return;
		}
	}
	abort();
}

void
Oracle::RegisterAliasingConfiguration::addConfig(unsigned tid, const ThreadRegisterAliasingConfiguration &config)
{
	for (auto it = content.begin(); it != content.end(); it++)
		assert(tid != it->first);
	content.push_back(std::pair<unsigned, ThreadRegisterAliasingConfiguration>(tid, config));
}

Oracle::RegisterAliasingConfiguration
Oracle::getAliasingConfiguration(const std::vector<std::pair<unsigned, VexRip> > &origins)
{
	RegisterAliasingConfiguration rac;
	for (auto it = origins.begin(); it != origins.end(); it++)
		rac.addConfig(it->first,
			      getAliasingConfigurationForRip(it->second));
	return rac;
}

PointerAliasingSet
PointerAliasingSet::operator |(const PointerAliasingSet &o) const
{
	PointerAliasingSet res;
	if (!valid)
		return *this;
	if (!o.valid)
		return o;
	res.nonPointer = nonPointer | o.nonPointer;
	res.nonStckPointer = nonStckPointer | o.nonStckPointer;
	res.otherStackPointer = otherStackPointer | o.otherStackPointer;
	if (!res.otherStackPointer) {
		res.stackPointers.insert(res.stackPointers.end(), stackPointers.begin(), stackPointers.end());
		res.stackPointers.insert(res.stackPointers.end(), o.stackPointers.begin(), o.stackPointers.end());
		std::sort(res.stackPointers.begin(), res.stackPointers.end());
		auto i = std::unique(res.stackPointers.begin(), res.stackPointers.end());
		res.stackPointers.erase(i, res.stackPointers.end());
	}
	res.valid = true;
	return res;
}

PointerAliasingSet
PointerAliasingSet::operator &(const PointerAliasingSet &o) const
{
	PointerAliasingSet res;
	if (!valid)
		return o;
	if (!o.valid)
		return *this;
	res.nonPointer = nonPointer & o.nonPointer;
	res.nonStckPointer = nonStckPointer & o.nonStckPointer;
	res.otherStackPointer = otherStackPointer & o.otherStackPointer;
	if (!res.otherStackPointer) {
		if (!otherStackPointer) {
			for (auto it = stackPointers.begin(); it != stackPointers.end(); it++)
				if (o.mightPointAt(*it))
					res.stackPointers.push_back(*it);
		} else {
			res.stackPointers = o.stackPointers;
		}
	}
	res.valid = true;
	return res;
}

bool
PointerAliasingSet::operator == (const PointerAliasingSet &o) const
{
	if (!valid)
		return !o.valid;
	if (!o.valid)
		return false;
	if (nonPointer != o.nonPointer ||
	    nonStckPointer != o.nonStckPointer ||
	    otherStackPointer != o.otherStackPointer)
		return false;
	if (!otherStackPointer &&
	    stackPointers != o.stackPointers)
		return false;
	return true;
}

bool
PointerAliasingSet::overlaps(const PointerAliasingSet &o) const
{
	if (!valid || !o.valid)
		return true;
	if ( (nonPointer && o.nonPointer) ||
	     (nonStckPointer && o.nonStckPointer) )
		return true;
	if (otherStackPointer && o.otherStackPointer)
		return true;
	if (otherStackPointer && !o.stackPointers.empty())
		return true;
	if (o.otherStackPointer && !stackPointers.empty())
		return true;
	for (auto it = stackPointers.begin(); it != stackPointers.end(); it++)
		if (o.mightPointAt(*it))
			return true;
	return false;
}

/* Returns true if anything changes. */
bool
PointerAliasingSet::operator|=(const PointerAliasingSet &o)
{
	bool res = false;
	if (!valid)
		return false;
	if (!o.valid) {
		*this = o;
		return true;
	}

	//nonPointer |= o.nonPointer;
	if (o.nonPointer && !nonPointer) {
		res = true;
		nonPointer = true;
	}

	//nonStckPointer |= o.nonStckPointer;
	if (o.nonStckPointer && !nonStckPointer) {
		res = true;
		nonStckPointer = true;
	}

	//otherStackPointer |= o.otherStackPointer;
	if (o.otherStackPointer && !otherStackPointer) {
		res = true;
		otherStackPointer = true;
	}

	if (otherStackPointer) {
		/* stackPointers should be empty if otherStackPointers
		   is set, so this must be a no-op unless res is
		   already set. */
		assert(res || stackPointers.empty());
		stackPointers.clear();
	} else {
		for (auto it = o.stackPointers.begin();
		     it != o.stackPointers.end();
		     it++)
			stackPointers.push_back(*it);
		std::sort(stackPointers.begin(), stackPointers.end());
		auto it = std::unique(stackPointers.begin(), stackPointers.end());
		stackPointers.erase(it, stackPointers.end());
	}

	if (res)
		clearName();
	return res;
}

PointerAliasingSet
PointerAliasingSet::frames(const std::set<FrameId> &inp)
{
	PointerAliasingSet res(PointerAliasingSet::nothing);
	res.stackPointers.reserve(inp.size());
	for (auto it = inp.begin(); it != inp.end(); it++)
		res.stackPointers.push_back(*it);
	return res;
}

/* Compute the offset from RSP to the function's return address. */
unsigned
stack_offset(Oracle *oracle, unsigned long rip)
{
	StaticRip sr(rip);
	StaticRip head(oracle->functionHeadForInstruction(sr));
	typedef std::pair<StaticRip, unsigned> q_entry_t;
	std::map<StaticRip, unsigned> offsets;
	std::queue<q_entry_t> queue;
	queue.push(q_entry_t(head, 0));

	while (!queue.empty() && !offsets.count(sr)) {
		q_entry_t q(queue.front());
		queue.pop();
		auto it_did_insert = offsets.insert(q);
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (!did_insert) {
			assert(it->second == q.second);
			continue;
		}
		IRSB *irsb = Oracle::getIRSBForRip(oracle->ms->addressSpace, q.first, false);
		if (!irsb)
			continue;
		bool overlap = false;
		bool failed = false;
		for (int i = 1; !overlap && i < irsb->stmts_used; i++) {
			IRStmt *stmt = irsb->stmts[i];
			switch (stmt->tag) {
			case Ist_IMark: {
				IRStmtIMark *i = (IRStmtIMark *)stmt;
				q.first = StaticRip(i->addr.rip.unwrap_vexrip());
				it_did_insert = offsets.insert(q);
				it = it_did_insert.first;
				did_insert = it_did_insert.second;
				if (!did_insert) {
					assert(it->second == q.second);
					overlap = true;
				}
				break;
			}
			case Ist_Put: {
				IRStmtPut *p = (IRStmtPut *)stmt;
				/* 32 == RSP */
				if (!p->target.isReg() || p->target.asReg() != 32)
					break;
				switch (p->data->tag) {
				case Iex_Associative: {
					IRExprAssociative *iea = (IRExprAssociative *)p->data;
					if (iea->op != Iop_Add64 ||
					    iea->nr_arguments != 2 ||
					    iea->contents[0]->tag != Iex_Const ||
					    iea->contents[1]->tag != Iex_Get ||
					    ((IRExprGet *)iea->contents[1])->reg != p->target) {
						failed = true;
					} else {
						q.second -= ((IRExprConst *)iea->contents[0])->con->Ico.U64;
					}
					break;
				}
				default:
					failed = true;
					break;
				}
				break;
			}
			case Ist_Exit: {
				IRStmtExit *e = (IRStmtExit *)stmt;
				queue.push(q_entry_t(StaticRip(e->dst.rip.unwrap_vexrip()), q.second));
				break;
			}
			default:
				break;
			}
		}
		if (!failed && !overlap) {
			if (irsb->next_is_const) {
				q.first = StaticRip(irsb->next_const.rip.unwrap_vexrip());
				queue.push(q);
			} else if (irsb->jumpkind != Ijk_Ret) {
				/* XXX write me: should query the
				 * oracle for branch targets. */
				abort();
			}
		}
	}

	if (!offsets.count(sr))
		return 0;
	return offsets[sr];
}

unsigned long
Oracle::findCallPredecessor(unsigned long rip)
{
	StaticRip sr(rip);
	std::vector<StaticRip> pred;
	Function(sr).addPredecessorsCall(sr, pred);
	if (pred.empty())
		return 0;
	assert(pred.size() == 1);
	return pred[0].rip;
}


