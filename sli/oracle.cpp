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
#include "visitor.hpp"

#include "libvex_prof.hpp"
#include "libvex_parse.h"

#ifndef NDEBUG
static bool debug_static_alias = false;
#else
#define debug_static_alias false
#endif

void dbg_database_query(const char *query);
void dbg_database_queryf(const char *query, ...) __attribute__((__format__(__printf__, 1, 2)));

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

#if !CONFIG_NO_STATIC_ALIASING
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
	/* At the start of a function, no registers point at the
	   stack.  Anything which is an arg register might contain a
	   pointer; anything else is assumed to not contain one. */
	/* (The idea is that if it's not arg register then it must be
	   dead at the function head, so even if it is a pointer it's
	   guaranteed to never be dereferenced, so it might as well
	   not be.  This is helpful because it means that spilling
	   call clobbered registers doesn't instantly mean that the
	   stack frame contains non-stack pointers, which can make
	   later bits of analysis a little more accurate). */
	v[0] = PointerAliasingSet::notAPointer; /* rax */
	v[1] = PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer; /* rcx */
	v[2] = PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer; /* rdx */
	v[3] = PointerAliasingSet::notAPointer; /* rbx */
	v[4] = PointerAliasingSet::stackPointer; /* rsp */
	v[5] = PointerAliasingSet::notAPointer; /* rbx */
	v[6] = PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer; /* rsi */
	v[7] = PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer; /* rdi */
	v[8] = PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer; /* r8 */
	v[9] = PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer; /* r9 */
	v[10] = PointerAliasingSet::notAPointer; /* r10 */
	v[11] = PointerAliasingSet::notAPointer; /* r11 */
	v[12] = PointerAliasingSet::notAPointer; /* r12 */
	v[13] = PointerAliasingSet::notAPointer; /* r13 */
	v[14] = PointerAliasingSet::notAPointer; /* r14 */
	v[15] = PointerAliasingSet::notAPointer; /* r15 */
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
#endif

unsigned
getInstructionSize(AddressSpace *as, const StaticRip &rip)
{
	IRSB *irsb = Oracle::getIRSBForRip(as, rip, true);
	if (!irsb)
		return 0;
	assert(irsb->stmts[0]->tag == Ist_IMark);
	return ((IRStmtIMark *)irsb->stmts[0])->len;
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

	if (smsel->tag == MemoryTag::last_free()) {
		std::vector<DynAnalysisRip> frees;
		findFrees(frees);
		for (auto it = frees.begin(); it != frees.end(); it++)
			out.insert(*it);
	}
}

void
Oracle::findConflictingLoads(const MaiMap &mai,
			     StateMachineSideEffectStore *smses,
			     std::set<DynAnalysisRip> &out)
{
	for (auto it = mai.begin(smses->rip); !it.finished(); it.advance()) {
		std::vector<TypesDb::types_entry> loads;
		std::vector<TypesDb::types_entry> stores;
		if (!type_db->lookupEntry(it.dr(), loads, stores)) {
			continue;
		}
		bool shared_stores = false;
		for (auto it2 = stores.begin(); !shared_stores && it2 != stores.end(); it2++) {
			if (!it2->is_private && it2->rip == it.dr()) {
				shared_stores = true;
			}
		}
		if (!shared_stores) {
			continue;
		}
		for (auto it = loads.begin(); it != loads.end(); it++) {
			if (!it->is_private) {
				out.insert(it->rip);
			}
		}
	}
}

bool
Oracle::hasConflictingRemoteStores(const DynAnalysisRip &dr)
{
	__set_profiling(hasConflictingRemoteStores);
	if (CONFIG_NO_DYNAMIC_ALIASING)
		return true;
	std::vector<TypesDb::types_entry> loads;
	std::vector<TypesDb::types_entry> stores;
	if (!type_db->lookupEntry(dr, loads, stores))
		return false;
	bool shared_load = false;
	bool shared_store = false;
	for (auto it = loads.begin(); !shared_load && it != loads.end(); it++) {
		if (it->rip == dr && !it->is_private)
			shared_load = true;
	}
	for (auto it = stores.begin(); !shared_store && it != stores.end(); it++) {
		if (it->rip == dr && !it->is_private)
			shared_store = true;
	}

	if (shared_store)
		return true;

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
	if (access->tag == MemoryTag::last_free() && opt.freeMightRace())
		return true;
	if (access->tag == MemoryTag::mutex()) {
		return true;
	}
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
	if (CONFIG_NO_DYNAMIC_ALIASING)
		return mam_might_alias;

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

	/* If the store is definitely shared and the load is
	   definitely private then they can't alias. */
	if (!shared_load && !private_store)
		return mam_no_alias;

	bool have_private_alias = false;
	for (auto it = load_stores.begin(); it != load_stores.end(); it++) {
		if (it->rip == smses_dr) {
			if (!shared_load) {
				return mam_private;
			} else {
				return mam_might_alias;
			}
		}
	}
	return mam_no_alias;
}
bool
Oracle::memoryAccessesMightAlias(const MaiMap &mai,
				 const IRExprOptimisations &opt,
				 StateMachineSideEffectLoad *smsel,
				 StateMachineSideEffectStore *smses)
{
	if (smsel->tag != smses->tag)
		return false;
	if (smsel->tag == MemoryTag::last_free() || smsel->tag == MemoryTag::mutex()) {
		return true;
	}

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
bool
Oracle::memoryAccessesMightAliasCrossThreadSym(const DynAnalysisRip &acc1, const DynAnalysisRip &acc2)
{
	__set_profiling(might_alias_cross_thread);
	return memoryAccessesMightAliasLS(acc1, acc2) == mam_might_alias ||
		memoryAccessesMightAliasLS(acc2, acc1) == mam_might_alias;
}

Oracle::mam_result
Oracle::memoryAccessesMightAliasLL(const DynAnalysisRip &dr1, const DynAnalysisRip &dr2)
{
	if (CONFIG_NO_DYNAMIC_ALIASING)
		return mam_might_alias;
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
				 const IRExprOptimisations &opt,
				 StateMachineSideEffectLoad *smsel1,
				 StateMachineSideEffectLoad *smsel2)
{
	if (smsel1->tag != smsel2->tag)
		return false;

	if (smsel1->tag == MemoryTag::last_free() || smsel1->tag == MemoryTag::mutex()) {
		return true;
	}

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
	if (CONFIG_NO_DYNAMIC_ALIASING)
		return mam_might_alias;
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
				 const IRExprOptimisations &opt,
				 StateMachineSideEffectStore *smses1,
				 StateMachineSideEffectStore *smses2)
{
	if (smses1->tag != smses2->tag)
		return false;

	if (smses1->tag == MemoryTag::last_free() || smses1->tag == MemoryTag::mutex()) {
		return true;
	}

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
	int cntr = 0;

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
			if (cntr++ % 100 == 0)
				printf("Register liveness: %zd/%zd on current pass\n",
				       it - functions.begin(), functions.size());
		}
		printf("Register liveness progress: %ld/%ld\n", changed, changed+unchanged);
	} while (done_something);
}

#if !CONFIG_NO_STATIC_ALIASING
void
Oracle::calculateAliasing(VexPtr<Oracle> &ths, GarbageCollectionToken token)
{
	bool done_something;
	std::vector<StaticRip> functions;
	int cntr = 0;
	ths->getFunctions(functions);
	for (auto it = functions.begin();
	     it != functions.end();
	     it++) {
		LibVEX_maybe_gc(token);
		Function f(*it);
		if (!f.aliasingConfigCorrect()) {
			do {
				done_something = false;
				f.calculateAliasing(ths->ms->addressSpace, ths, &done_something);
			} while (done_something);
			f.setAliasingConfigCorrect(true);
		}
		if (cntr++ % 100 == 0)
			printf("Aliasing progress: %zd/%zd\n",
			       it - functions.begin(), functions.size());
	}
}
#endif

static Oracle::LivenessSet
irexprUsedValues(Oracle::LivenessSet old, const IRExpr *w)
{
	if (!w)
		return old;
	struct {
		static visit_result Get(Oracle::LivenessSet *old, const IRExprGet *e) {
			if (!e->reg.isTemp())
				*old = old->use(e->reg.asReg());
			return visit_continue;
		}
	} foo;
	static irexpr_visitor<Oracle::LivenessSet> visitor;
	visitor.Get = foo.Get;
	Oracle::LivenessSet res(old);
	visit_irexpr(&res, &visitor, w);
	return res;
}

#if !CONFIG_NO_STATIC_ALIASING
static PointerAliasingSet
irexprAliasingClass(IRExpr *expr,
		    const Oracle::RegisterAliasingConfiguration &config,
		    std::map<threadAndRegister, PointerAliasingSet> *temps,
		    const IRExprOptimisations &opt,
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
	case Iex_GetI:
		/* x86 decoder never uses GetI for anything which is
		   likely to contain a pointer. */
		return PointerAliasingSet::notAPointer;
	case Iex_Const: {
		IRExprConst *con = (IRExprConst *)expr;
		if (con->Ico.content.U64 < 4096)
			return PointerAliasingSet::notAPointer;
		bool t;
		if (opt.addressAccessible(((IRExprConst *)expr)->Ico.content.U64, &t) && !t)
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
		case Iop_F32toF64:
		case Iop_I32toF64:
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
		case Iop_MullU32:
		case Iop_MullS32:
		case Iop_F64toI64:
		case Iop_32HLto64:
		case Iop_DivModU64to32:
		case Iop_DivModS64to32:
		case Iop_I64toF64:
		case Iop_I32toF64:
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
				long k = ((IRExprConst *)e->contents[0])->Ico.content.U64;
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
		case Iop_Mul64:
			return PointerAliasingSet::notAPointer;
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
#endif

enum read_cg_vexrip_res {
	read_cg_vexrip_error,
	read_cg_vexrip_take,
	read_cg_vexrip_skip
};

static read_cg_vexrip_res
read_cg_vexrip(FILE *f, DynAnalysisRip *out, AddressSpace *as, bool *is_call,
	       bool new_format)
{
	if (!new_format) {
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
			if (as->isReadable(a))
				stack.push_back(a);
		}
		if (rip & (1ul << 63)) {
			*is_call = true;
			rip &= ~(1ul << 63);
		} else {
			*is_call = false;
		}
		read_cg_vexrip_res res;
		if (as->isReadable(rip)) {
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
	} else {
		unsigned long rip;
		if (fread(&rip, sizeof(rip), 1, f) != 1) {
			return read_cg_vexrip_error;
		}
		if (rip & (1ul << 63)) {
			*is_call = true;
			rip &= ~(1ul << 63);
		} else {
			*is_call = false;
		}
		out->nr_rips = 1;
		out->rips[0] = rip;
		if (as->isReadable(rip)) {
			return read_cg_vexrip_take;
		} else {
			return read_cg_vexrip_skip;
		}
	}
}

static sqlite3 *_database;

static void
create_index(const char *name, const char *table, const char *field)
{
	char *s = my_asprintf("CREATE INDEX %s ON %s (%s)", name, table, field);
	sqlite3_exec(_database, s, NULL, NULL, NULL);
	free(s);
}

static bool
open_database(const char *path)
{
	bool res;
	int rc;

	rc = sqlite3_open_v2(path, &_database, SQLITE_OPEN_READONLY, NULL);
	if (rc == SQLITE_OK) {
		/* Return existing database */
		res = false;
		goto disable_journalling;
	}

	res = true;
	/* Create new database */
	rc = sqlite3_open_v2(path, &_database, SQLITE_OPEN_READWRITE|SQLITE_OPEN_CREATE, NULL);
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
			  "functionHead INTEGER)",
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
	rc = sqlite3_exec(_database, "CREATE TABLE functionAttribs (functionHead INTEGER PRIMARY KEY, registerLivenessCorrect INTEGER NOT NULL, aliasingCorrect INTEGER NOT NULL)",
			  NULL, NULL, NULL);
	assert(rc == SQLITE_OK);
#if CONFIG_FIXED_REGS
	rc = sqlite3_exec(_database, "CREATE TABLE fixedRegs (rip INTEGER PRIMARY KEY, content TEXT)",
			  NULL, NULL, NULL);
	assert(rc == SQLITE_OK);
#endif

disable_journalling:
	/* All of the information in the database can be regenerated
	   by just blowing it away and starting over, so there's not
	   much point in doing lots of journaling and fsync()
	   operations. */
	rc = sqlite3_exec(_database, "PRAGMA journal_mode = OFF", NULL, NULL, NULL);
	assert(rc == SQLITE_OK);
	rc = sqlite3_exec(_database, "PRAGMA synchronous = OFF", NULL, NULL, NULL);
	assert(rc == SQLITE_OK);

	return res;
}

void
Oracle::loadCallGraph(VexPtr<Oracle> &ths,
		      const char *cg_fname,
		      const char *db_fname,
		      GarbageCollectionToken token)
{
	__set_profiling(oracle_load_call_graph);

	callgraph_t callgraph; 
	std::vector<StaticRip> roots;
	FILE *f = fopen(cg_fname, "r");
	unsigned long magic = 0;
	fread(&magic, sizeof(magic), 1, f);
	bool new_format;
	if (magic == 0xaabbccddeeff) {
		new_format = true;
	} else {
		fseeko(f, 0, SEEK_SET);
		new_format = false;
	}
	while (!feof(f)) {
		callgraph_entry ce;
		bool is_call;
		DynAnalysisRip branch_rip;
		auto res = read_cg_vexrip(f, &branch_rip, ths->ms->addressSpace, &is_call, new_format);
		if (res == read_cg_vexrip_error) {
			if (feof(f))
				break;
			err(1, "reading rip from %s", cg_fname);
		}
		unsigned nr_callees;
		if (fread(&nr_callees, sizeof(nr_callees), 1, f) != 1)
			err(1, "reading number of callees from %s\n", cg_fname);
		for (unsigned x = 0; x < nr_callees; x++) {
			unsigned long callee;
			if (fread(&callee, sizeof(callee), 1, f) != 1)
				err(1, "reading callee rip from %s", cg_fname);
			if (!new_format) {
				if (x == 0) {
					if (callee & (1ul << 63)) {
						is_call = true;
					} else {
						is_call = false;
					}
				} else {
					if (callee & (1ul << 63)) {
						assert(is_call);
					} else {
						assert(!is_call);
					}
				}
			}
			callee &= ~(1ul << 63);
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

	bool need_rebuild_database = open_database(db_fname);
	if (need_rebuild_database) {
		make_unique(roots);
		Oracle::findInstructions(ths, roots, callgraph, token);
	}
}

template <typename underlying>
class range_set {
	std::vector<std::pair<underlying, underlying> > content;
	underlying amt_set;

public:
	range_set() : amt_set(0) {}
	unsigned nr_ranges() const { return content.size(); }
	underlying min() const { assert(!content.empty()); return content.front().first; }
	underlying max() const { assert(!content.empty()); return content.back().first; }
	bool empty() const { return content.empty(); }
	void sanity_check() const {
		/* These are expensive, so turn them off by default
		 * even in debug builds. */
#if 0
		for (unsigned x = 0; x + 1 < content.size(); x++) {
			assert(content[x].second < content[x+1].first);
			assert(content[x].first < content[x].second);
		}
		if (!content.empty())
			assert(content.back().first < content.back().second);
#endif
	}
	bool contains(unsigned long x) const {
		sanity_check();
		int low, high;
		low = 0;
		high = content.size();
		/* Avoid nasty edge cases by just finishing up with a
		 * linear scan once we get anywhere near to them. */
		while (low < high - 10) {
			int probe = (low + high) / 2;
			if (content[probe].first <= x &&
			    content[probe].second > x) {
				return true;
			}
			if (x == content[probe].second) {
				return false;
			}
			if (content[probe].first > x) {
				high = probe;
			} else {
				low = probe;
			}
		}
		for (int i = std::max(0, low - 10); i < std::min(high + 10, (int)content.size()); i++) {
			if (content[i].first <= x && content[i].second > x) {
				return true;
			}
		}
		return false;
	}
	double coverage() const {
		if (content.empty())
			return 0;
		return amt_set / (double)(content.back().second - content.front().first);
	}
	void insert(underlying start, underlying end) {
		sanity_check();
		for (unsigned idx = 0; idx != content.size(); ) {
			if (start > content[idx].second) {
				idx++;
				continue;
			}
			if (end < content[idx].first) {
				content.insert(content.begin() + idx, std::pair<underlying, underlying>(start, end));
				amt_set += end - start;
				assert(contains(start));
				sanity_check();
				return;
			}
			if (content[idx].first > start) {
				amt_set += content[idx].first - start;
				content[idx].first = start;
			}

			if (content[idx].second >= end) {
				assert(contains(start));
				sanity_check();
				return;
			}

			amt_set += end - content[idx].second;
			content[idx].second = end;
			while (idx + 1 != content.size() &&
			       content[idx+1].second <= content[idx].second) {
				amt_set -= content[idx + 1].second - content[idx].first;
				content.erase(content.begin() + idx + 1);
			}
			if (idx + 1 != content.size() &&
			    content[idx+1].first <= content[idx].second) {
				amt_set += content[idx + 1].second - content[idx].second;
				content[idx].second = content[idx+1].second;
				amt_set -= content[idx + 1].second - content[idx + 1].first;
				content.erase(content.begin() + idx + 1);
			}
			sanity_check();
			assert(contains(start));
			return;
		}
		content.push_back(std::pair<underlying, underlying>(start, end));
		amt_set += end - start;
		sanity_check();
		assert(contains(start));
	}
};

static sqlite3 *
database(void)
{
	assert(_database);
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
	void bindInt64(int idx, unsigned long val) {
		bind_int64(stmt, idx, val);
	}
	void bindString(int idx, const char *what) {
		int rc = sqlite3_bind_text(stmt, idx, what, strlen(what), SQLITE_TRANSIENT);
		assert(rc == SQLITE_OK);
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
Oracle::findInstructions(VexPtr<Oracle> &ths,
			 std::vector<StaticRip> &heads,
			 const callgraph_t &callgraph,
			 GarbageCollectionToken token)
{
	std::vector<unsigned long> pendingInstrs;
	std::set<unsigned long> known_heads;
	for (auto it = heads.begin(); it != heads.end(); it++) {
		pendingInstrs.push_back(it->rip);
		known_heads.insert(it->rip);
	}
	range_set<unsigned long> covered;
	static prepared_stmt add_attributes("INSERT INTO instructionAttributes (rip) VALUES (?)");
	static prepared_stmt add_branch("INSERT INTO branchRips (rip, dest) VALUES (?, ?)");
	static prepared_stmt add_fallthrough("INSERT INTO fallThroughRips (rip, dest) VALUES (?, ?)");
	static prepared_stmt add_return("INSERT INTO returnRips (rip, dest) VALUES (?, 0)");
	static prepared_stmt add_call("INSERT INTO callRips (rip, dest) VALUES (?, ?)");
	static prepared_stmt add_callsucc("INSERT INTO callSuccRips (rip, dest) VALUES (?, ?)");

	sqlite3_exec(database(), "BEGIN TRANSACTION", NULL, NULL, NULL);
	unsigned cntr = 0;
	while (!pendingInstrs.empty()) {
		unsigned long rip(pendingInstrs.back());
		pendingInstrs.pop_back();

		if (!covered.empty() && ++cntr % 1000 == 0) {
			printf("Current coverage %f%% [%lx, %lx); %zd in queue, %d ranges, %zd known heads\n",
			       covered.coverage() * 100,
			       covered.min(),
			       covered.max(),
			       pendingInstrs.size(),
			       covered.nr_ranges(),
			       known_heads.size());
			LibVEX_maybe_gc(token);
			sqlite3_exec(database(), "END TRANSACTION", NULL, NULL, NULL);
			sqlite3_exec(database(), "BEGIN TRANSACTION", NULL, NULL, NULL);
		}
		if (covered.contains(rip))
			continue;
		IRSB *irsb = ths->getIRSBForRip(ths->ms->addressSpace, StaticRip(rip), false);
		if (!irsb) {
			known_heads.erase(rip);
			continue;
		}
		int i;
		i = 0;
		bool done = false;
		while (1) {
			assert(irsb->stmts[i]->tag == Ist_IMark);
			IRStmtIMark *mark = (IRStmtIMark *)irsb->stmts[i];
			rip = mark->addr.rip.unwrap_vexrip();
			if (covered.contains(rip)) {
				done = true;
				break;
			}
			covered.insert(rip, rip + mark->len);
			i++;

			add_attributes.bindInt64(1, rip);
			add_attributes.run();

			std::set<unsigned long> exits;
			while (i < irsb->stmts_used && irsb->stmts[i]->tag != Ist_IMark) {
				if (irsb->stmts[i]->tag == Ist_Exit) {
					IRStmtExit *ex = (IRStmtExit *)irsb->stmts[i];
					exits.insert(ex->dst.rip.unwrap_vexrip());
				}
				i++;
			}

			for (auto it = exits.begin(); it != exits.end(); it++) {
				add_branch.bindInt64(1, rip);
				add_branch.bindInt64(2, *it);
				add_branch.run();

				pendingInstrs.push_back(*it);
			}

			if (i == irsb->stmts_used)
				break;

			add_fallthrough.bindInt64(1, rip);
			add_fallthrough.bindInt64(2, ((IRStmtIMark *)irsb->stmts[i])->addr.rip.unwrap_vexrip());
			add_fallthrough.run();
		}
		if (done)
			continue;

		if (irsb->jumpkind == Ijk_Call) {
			if (!irsb->next_is_const ||
			    !ths->functionNeverReturns(StaticRip(irsb->next_const.rip))) {
				unsigned long succ = extract_call_follower(irsb).unwrap_vexrip();
				add_callsucc.bindInt64(1, rip);
				add_callsucc.bindInt64(2, succ);
				add_callsucc.run();

				pendingInstrs.push_back(succ);
			}

			std::vector<StaticRip> targets;
			if (irsb->next_is_const)
				targets.push_back(StaticRip(irsb->next_const.rip));
			else
				ths->findPossibleJumpTargets(StaticRip(rip), callgraph, targets);
			for (auto it = targets.begin(); it != targets.end(); it++) {
				add_call.bindInt64(1, rip);
				add_call.bindInt64(2, it->rip);
				add_call.run();

				known_heads.insert(it->rip);
				pendingInstrs.push_back(it->rip);
			}
		} else {
			if (irsb->jumpkind == Ijk_Ret) {
				add_return.bindInt64(1, rip);
				add_return.run();
			}

			std::vector<StaticRip> targets;
			if (irsb->next_is_const) {
				targets.push_back(StaticRip(irsb->next_const.rip));
			} else {
				ths->findPossibleJumpTargets(StaticRip(rip), callgraph, targets);
			}
			for (auto it = targets.begin();
			     it != targets.end();
			     it++) {
				add_fallthrough.bindInt64(1, rip);
				add_fallthrough.bindInt64(2, it->rip);
				add_fallthrough.run();

				pendingInstrs.push_back(it->rip);
			}
		}
	}

	sqlite3_exec(database(), "END TRANSACTION", NULL, NULL, NULL);

	printf("Building indices...\n");
	create_index("branchDest", "branchRips", "dest");
	create_index("callDest", "callRips", "dest");
	create_index("fallThroughDest", "fallThroughRips", "dest");
	create_index("callSuccDest", "callSuccRips", "dest");
	create_index("branchRip", "branchRips", "rip");
	create_index("callRip", "callRips", "rip");
	create_index("fallThroughRip", "fallThroughRips", "rip");
	create_index("callSuccRip", "callSuccRips", "rip");
	create_index("instructionAttributesRip", "instructionAttributes", "rip");

	printf("Assigning instructions to functions...\n");

	/* Now we need to go and discover all of the functions in the
	 * program.  This may be a bit more than just those in
	 * known_heads because of tail-call effects. */
	std::vector<unsigned long> pending_heads(known_heads.begin(),
						 known_heads.end());
#ifndef NDEBUG
	std::set<unsigned long> processed_heads;
#endif
	while (!pending_heads.empty()) {
		unsigned long this_head(pending_heads.back());
		pending_heads.pop_back();
#ifndef NDEBUG
		assert(!processed_heads.count(this_head));
		processed_heads.insert(this_head);
#endif
		if (cntr++ % 100 == 0)
			printf("%zd heads left...\n", pending_heads.size());
		std::set<unsigned long> alreadyProcessedThisHead;
		std::vector<unsigned long> instrsThisHead;
		instrsThisHead.push_back(this_head);
		while (!instrsThisHead.empty()) {
			unsigned long instr(instrsThisHead.back());
			instrsThisHead.pop_back();

			if (alreadyProcessedThisHead.count(instr))
				continue;
			alreadyProcessedThisHead.insert(instr);

			static sqlite3_stmt *getOldHead;
			if (!getOldHead)
				getOldHead = prepare_statement("SELECT functionHead FROM instructionAttributes WHERE rip = ?");
			bind_int64(getOldHead, 1, instr);
			int rc = sqlite3_step(getOldHead);
			if (rc == SQLITE_DONE) {
				/* Woohoo, tail call into a library
				 * function.  Just ignore it. */
				sqlite3_reset(getOldHead);
				continue;
			}
			assert(rc == SQLITE_ROW);
			unsigned long old_head;
			if (sqlite3_column_type(getOldHead, 0) == SQLITE_NULL)
				old_head = 0;
			else if (sqlite3_column_type(getOldHead, 0) == SQLITE_INTEGER)
				old_head = sqlite3_column_int64(getOldHead, 0);
			else
				abort();
			rc = sqlite3_step(getOldHead);
			assert(rc == SQLITE_DONE);
			sqlite3_reset(getOldHead);

			if (old_head != 0) {
				assert(old_head != this_head);
				/* Whoops: tail call.  That means we
				   have to insert a new head here and
				   re-do @old_head. */

				printf("Correct for tail call: %lx was assigned to function %lx, but also to %lx\n",
				       instr, old_head, this_head);
				/* Remove @old_head, since it's now
				 * incorrect */
				static prepared_stmt purgeFunction("UPDATE instructionAttributes SET functionHead = 0 WHERE functionHead = ?");
				purgeFunction.bindInt64(1, old_head);
				purgeFunction.run();

				/* We've discovered a new head */
				known_heads.insert(instr);
				/* Need to process both of them again. */
				pending_heads.push_back(instr);
				pending_heads.push_back(old_head);
				
#ifndef NDEBUG
				processed_heads.erase(old_head);
#endif
				continue;
			}

			/* Add this instruction to the current function */
			static prepared_stmt addInstrToFunction("UPDATE instructionAttributes SET functionHead = ? WHERE rip = ?");
			addInstrToFunction.bindInt64(1, this_head);
			addInstrToFunction.bindInt64(2, instr);
			addInstrToFunction.run();

			/* And now figure out where we're going
			 * next */
			std::vector<StaticRip> succ;
			Function(StaticRip(this_head)).getSuccessors(StaticRip(instr), succ);
			for (auto it = succ.rbegin(); it != succ.rend(); it++) {
				if (!known_heads.count(it->rip))
					instrsThisHead.push_back(it->rip);
			}
		}
	}
	
	create_index("instructionAttributesFunctionHead", "instructionAttributes", "functionHead");

#if CONFIG_FIXED_REGS
	printf("Calculate fixed regs...\n");
	calculateFixedRegs(ths, token);
#endif

	ths->buildReturnAddressTable();
	create_index("returnDest", "returnRips", "dest");

	printf("Calculate register liveness...\n");
	calculateRegisterLiveness(ths, token);
#if !CONFIG_NO_STATIC_ALIASING
	printf("Calculate aliasing map...\n");
	calculateAliasing(ths, token);
#endif
	printf("Done static analysis phase\n");
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

#if !CONFIG_NO_STATIC_ALIASING
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

	if (CONFIG_NO_STATIC_ALIASING)
		return ThreadRegisterAliasingConfiguration::unknown;

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

Oracle::ThreadRegisterAliasingConfiguration
Oracle::Function::aliasConfigOnEntryToInstruction(const StaticRip &rip)
{
	bool ign;
	return aliasConfigOnEntryToInstruction(rip, &ign);
}
#endif

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
		{ "pthread_exit", "exit", "err", "errx", "verr", "verrx", "__pthread_unwind_next",
		  "longjmp", "_longjmp", "siglongjmp",
		  "quick_exit", "_exit", "_Exit", "__error_noreturn",
		  "__error_at_line_noreturn",

		  "SLang_exit_error",

		  "png_error", "png_chunk_error", "png_err",

		  "_ZSt9terminatev", "_ZSt10unexpectedv",
		  NULL };
	/* Some functions which always just crash.  The distinction
	   between ``crash'' and ``fail to return'' is kind of
	   arbitrary (e.g. err() might be considered a crash or a
	   normal termination, depending on what you're doing), so be
	   just a little bit conservative. */
	static const char *const crashers[] =
		{ "abort", "__stack_chk_fail", "__assert_fail",
		  "__assert_perror_fail", "__assert",

		  "g_assertion_message", "g_assertion_message_expr",
		  "g_assertion_message_cmpstr", "g_assertion_message_cmpnum",
		  "g_assertion_message_error", "g_assert_warning",

		  "_ZSt9terminatev", "_ZSt10unexpectedv",
		  NULL };
	/* Functions which act like free(). */
	static const char *const freers[] =
		{ "free", "_ZdlPv", NULL };
	for (int i = 0; crashers[i]; i++) {
		unsigned long r;
		r = ms->elfData->getPltAddress(ms->addressSpace, crashers[i]);
		if (r) {
			crashingFunctions.push_back(StaticRip(r));
			terminalFunctions.push_back(StaticRip(r));
		}
	}
	for (int i = 0; terminals[i]; i++) {
		unsigned long r;
		r = ms->elfData->getPltAddress(ms->addressSpace, terminals[i]);
		if (r)
			terminalFunctions.push_back(StaticRip(r));
	}
	for (int i = 0; freers[i]; i++) {
		unsigned long r;
		r = ms->elfData->getPltAddress(ms->addressSpace, freers[i]);
		if (r)
			freeFunctions.push_back(StaticRip(r));
	}
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

#if !CONFIG_NO_STATIC_ALIASING
void
Oracle::Function::calculateAliasing(AddressSpace *as, Oracle *oracle, bool *done_something)
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
		updateSuccessorInstructionsAliasing(rip, as, &needsUpdating, oracle, done_something);
	}

	if (debug_static_alias) {
		printf("Finished recomputing aliasing for function head %s\n", rip.name());
		printf("Exit configuration:\n");
		dbg_database_queryf("SELECT rip, alias0, alias1, alias2, alias3, alias4, alias5, alias6, alias7, alias8, alias9, alias10, alias11, alias12, alias13, alias14, alias15, stackEscape FROM instructionAttributes WHERE functionHead = %ld ORDER BY rip",
				    rip.rip);
	}
}
#endif

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

#if !CONFIG_NO_STATIC_ALIASING
/* We know that @what is definitely a valid pointer.  Try to update
   @config so that irexprAliasingClass will say that as well. */
static void
makeValidPointer(Oracle::ThreadRegisterAliasingConfiguration &config,
		 IRExpr *what)
{
	if (what->tag == Iex_Get &&
	    ((IRExprGet *)what)->reg.isReg() &&
	    ((IRExprGet *)what)->reg.asReg() < Oracle::NR_REGS * 8) {
		int idx = ((IRExprGet *)what)->reg.asReg() / 8;
		config.v[idx].nonPointer = false;
		config.v[idx].clearName();
	} else if (what->tag == Iex_Associative &&
		   ((IRExprAssociative *)what)->op == Iop_Add64 &&
		   ((IRExprAssociative *)what)->nr_arguments == 2 &&
		   ((IRExprAssociative *)what)->contents[0]->tag == Iex_Const) {
		makeValidPointer(config, ((IRExprAssociative *)what)->contents[1]);
	} else {
		/* Can't do anything with these. */
	}
}

void
Oracle::Function::updateSuccessorInstructionsAliasing(const StaticRip &rip,
						      AddressSpace *as,
						      std::vector<StaticRip> *changed,
						      Oracle *oracle,
						      bool *done_something)
{
	const IRExprOptimisations opt(AllowableOptimisations::defaultOptimisations.setAddressSpace(as));
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
			makeValidPointer(tconfig, ((IRStmtStore *)st)->addr);
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
				IRExpr *add = NULL;
				if ((tconfig.stackInStack && tconfig.stackInMemory) ||
				    strcmp(((IRStmtDirty *)st)->details->cee->name, "helper_load_64")) {
					res = PointerAliasingSet::anything;
				} else {
					add = ((IRStmtDirty *)st)->details->args[0];
					PointerAliasingSet addr(
						irexprAliasingClass(add,
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

				if (add) {
					makeValidPointer(tconfig, add);
				}
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
		if (tconfig.stackInMemory)
			stackEscapes = true;
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
		if (stackEscapes) {
			tconfig.v[0] = tconfig.v[0] | PointerAliasingSet::stackPointer;
			tconfig.stackInStack = true;
			tconfig.stackInMemory = true;
		}
		tconfig.v[0] = tconfig.v[0] | PointerAliasingSet::nonStackPointer;
		/* Clear call-clobbered registers.  Shouldn't really
		   make a great deal of difference, but it's a bit
		   prettier like this. */
		tconfig.v[1] = PointerAliasingSet::notAPointer; /* rcx */
		tconfig.v[2] = PointerAliasingSet::notAPointer; /* rdx */
		tconfig.v[6] = PointerAliasingSet::notAPointer; /* rsi */
		tconfig.v[7] = PointerAliasingSet::notAPointer; /* rdi */
		tconfig.v[8] = PointerAliasingSet::notAPointer; /* r8 */
		tconfig.v[9] = PointerAliasingSet::notAPointer; /* r9 */
		tconfig.v[10] = PointerAliasingSet::notAPointer; /* r10 */
		tconfig.v[11] = PointerAliasingSet::notAPointer; /* r11 */
	}
	
	std::vector<StaticRip> _fallThroughRips;
	if (nr_statements == irsb->stmts_used) {
		if (irsb->jumpkind != Ijk_Call) {
			if (irsb->next_is_const)
				_fallThroughRips.push_back(StaticRip(irsb->next_const.rip));
			else
				getInstructionFallThroughs(rip, _fallThroughRips);
		} else {
			if (!irsb->next_is_const ||
			    !oracle->functionNeverReturns(StaticRip(irsb->next_const.rip)))
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
#endif

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

#if !CONFIG_NO_STATIC_ALIASING
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
#endif

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
		stmt = prepare_statement("INSERT OR REPLACE INTO functionAttribs (functionHead, registerLivenessCorrect, aliasingCorrect) VALUES (?, ?, 0)");
	bind_oraclerip(stmt, 1, rip);
	bind_int64(stmt, 2, x);

	int rc;
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE);
	rc = sqlite3_reset(stmt);
	assert(rc == SQLITE_OK);
}

#if !CONFIG_NO_STATIC_ALIASING
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
#endif

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
		if (cwidth > 40) {
			cwidth = 40;
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
		stmt = prepare_statement("SELECT functionHead FROM instructionAttributes WHERE rip = ?");
	bind_oraclerip(stmt, 1, sr);
	std::vector<unsigned long> a;
	extract_int64_column(stmt, 0, a);
	if (a.size() == 0)
		return false;
	assert(a.size() == 1);
	return a[0] == sr.rip;
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

	std::vector<StaticRip> pred;
	f.addPredecessorsNonCall(sr, pred);
	f.addPredecessorsCall(sr, pred);
	f.addPredecessorsReturn(sr, pred);
	for (auto it = pred.begin(); it != pred.end(); it++)
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
	unsigned idx = ms->addressSpace->fetch<unsigned>(r + 7);
	const char *name;

	name = ms->elfData->lookupPltSymbol(idx);
	if (!name) {
		warning("Warning: don't know what library function to call at %s\n",
			vr.name());
		return LibraryFunctionTemplate::none;
	}
	return LibraryFunctionTemplate::parse(name);
}

#if !CONFIG_NO_STATIC_ALIASING
PointerAliasingSet
Oracle::RegisterAliasingConfiguration::lookupRegister(const threadAndRegister &r, bool buildingAliasTable) const
{
	if (buildingAliasTable)
		assert(r.gen() == 0);

	/* Assume that anything which isn't a GPR isn't a pointer.
	   Reasonable for x86. */
	if (r.asReg() >= Oracle::NR_REGS * 8)
		return PointerAliasingSet::notAPointer;
	if (!buildingAliasTable)
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
#if TRACK_FRAMES
	if (!res.otherStackPointer) {
		res.stackPointers.insert(res.stackPointers.end(), stackPointers.begin(), stackPointers.end());
		res.stackPointers.insert(res.stackPointers.end(), o.stackPointers.begin(), o.stackPointers.end());
		std::sort(res.stackPointers.begin(), res.stackPointers.end());
		auto i = std::unique(res.stackPointers.begin(), res.stackPointers.end());
		res.stackPointers.erase(i, res.stackPointers.end());
	}
#endif
	res.valid = true;
	return res;
}

PointerAliasingSet
PointerAliasingSet::operator &(const PointerAliasingSet &o) const
{
	if (!valid)
		return o;
	if (!o.valid)
		return *this;
	PointerAliasingSet res;
	res.valid = true;
	res.nonPointer = nonPointer & o.nonPointer;
	res.nonStckPointer = nonPointer & o.nonStckPointer;
	res.otherStackPointer = otherStackPointer & o.otherStackPointer;
#if TRACK_FRAMES
	if (otherStackPointer && o.otherStackPointer) {
	} else if (otherStackPointer && !o.otherStackPointer) {
		res.stackPointers = o.stackPointers;
	} else if (!otherStackPointer && o.otherStackPointer) {
		res.stackPointers = stackPointers;
	} else { /* !otherStackPointers && !o.otherStackPointers */
		for (auto it1 = stackPointers.begin();
		     it1 != stackPointers.end();
		     it1++) {
			bool found = false;
			for (auto it2 = o.stackPointers.begin();
			     !found && it2 != o.stackPointers.end();
			     it2++) {
				found |= *it1 == *it2;
			}
			if (found)
				res.stackPointers.push_back(*it1);
		}
	}
#endif
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
#if TRACK_FRAMES
	if (!otherStackPointer &&
	    stackPointers != o.stackPointers)
		return false;
#endif
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
#if TRACK_FRAMES
	if (otherStackPointer && !o.stackPointers.empty())
		return true;
	if (o.otherStackPointer && !stackPointers.empty())
		return true;
	for (auto it = stackPointers.begin(); it != stackPointers.end(); it++)
		if (o.mightPointAt(*it))
			return true;
#endif
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

#if TRACK_FRAMES
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
#endif

	if (res)
		clearName();
	return res;
}

bool
PointerAliasingSet::operator <(const PointerAliasingSet &o) const
{
	if (valid < o.valid)
		return true;
	if (valid > o.valid || !valid)
		return false;
	if (nonPointer < o.nonPointer)
		return true;
	if (nonPointer > o.nonPointer)
		return false;
	if (nonStckPointer < o.nonStckPointer)
		return true;
	if (nonStckPointer > o.nonStckPointer)
		return false;
	if (otherStackPointer < o.otherStackPointer)
		return true;
	if (otherStackPointer)
		return false;
#if TRACK_FRAMES
	return stackPointers < o.stackPointers;
#else
	return false;
#endif
}

#if TRACK_FRAMES
PointerAliasingSet
PointerAliasingSet::frames(const PointerAliasingSet *base, const std::set<FrameId> &frames)
{
	if (!base->valid) {
		return *base;
	}
	PointerAliasingSet res(*base);
	res.otherStackPointer = false;
	res.stackPointers.clear();
	res.stackPointers.insert(res.stackPointers.end(),
				 frames.begin(),
				 frames.end());
	res.clearName();
	return res;
}
#endif
#endif

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
						q.second -= ((IRExprConst *)iea->contents[0])->Ico.content.U64;
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
			if (irsb->jumpkind == Ijk_Call) {
				/* Assume that calling another
				 * function doesn't adjust the stack
				 * pointer. */
				VexRip follower(extract_call_follower(irsb));
				q.first = StaticRip(follower.unwrap_vexrip());
				/* Pop the return address off the
				 * stack. */
				q.second -= 8;
				queue.push(q);
			} else {
				if (irsb->next_is_const) {
					q.first = StaticRip(irsb->next_const.rip.unwrap_vexrip());
					queue.push(q);
				} else if (irsb->jumpkind != Ijk_Ret) {
					/* XXX write me: should query
					 * the oracle for branch
					 * targets. */
					Oracle::Function f(q.first);
					std::vector<StaticRip> fthru;
					f.getInstructionFallThroughs(q.first, fthru);
					for (auto it = fthru.begin();
					     it != fthru.end();
					     it++) {
						q.first = *it;
						queue.push(q);
					}
				}
			}
		}
	}

	if (!offsets.count(sr))
		return 0;
	return offsets[sr];
}

bool
Oracle::isCrashingAddr(const VexRip &vr) const
{
	for (auto it = crashingFunctions.begin(); it != crashingFunctions.end(); it++)
		if (*it == StaticRip(vr))
			return true;
	return false;
}

bool
Oracle::isFreeAddr(const VexRip &vr) const
{
	for (auto it = freeFunctions.begin(); it != freeFunctions.end(); it++)
		if (*it == StaticRip(vr))
			return true;
	return false;
}

void
Oracle::findAssertions(std::vector<DynAnalysisRip> &drs)
{
	static sqlite3_stmt *stmt;
	if (!stmt)
		stmt = prepare_statement("SELECT rip FROM callRips WHERE dest = ?");
	for (auto it = crashingFunctions.begin(); it != crashingFunctions.end(); it++) {
		bind_oraclerip(stmt, 1, *it);
		std::vector<StaticRip> res;
		extract_oraclerip_column(stmt, 0, res);
		for (auto it = res.begin(); it != res.end(); it++)
			drs.push_back(DynAnalysisRip(VexRip::invent_vex_rip(it->rip)));
	}
}

void
Oracle::findFrees(std::vector<DynAnalysisRip> &drs)
{
	static sqlite3_stmt *stmt;
	if (!stmt)
		stmt = prepare_statement("SELECT rip FROM callRips WHERE dest = ?");
	for (auto it = freeFunctions.begin(); it != freeFunctions.end(); it++) {
		bind_oraclerip(stmt, 1, *it);
		std::vector<StaticRip> res;
		extract_oraclerip_column(stmt, 0, res);
		for (auto it = res.begin(); it != res.end(); it++)
			drs.push_back(DynAnalysisRip(VexRip::invent_vex_rip(it->rip)));
	}
}

bool
OracleInterface::memoryAccessesMightAlias(const MaiMap &decode, const IRExprOptimisations &opt,
					  StateMachineSideEffectMemoryAccess *a,
					  StateMachineSideEffectMemoryAccess *b)
{
	
	if (a->type == StateMachineSideEffect::Load) {
		if (b->type == StateMachineSideEffect::Load)
			return memoryAccessesMightAlias(decode, opt, (StateMachineSideEffectLoad *)a, (StateMachineSideEffectLoad *)b);
		else
			return memoryAccessesMightAlias(decode, opt, (StateMachineSideEffectLoad *)a, (StateMachineSideEffectStore *)b);
	} else {
		if (b->type == StateMachineSideEffect::Load)
			return memoryAccessesMightAlias(decode, opt, (StateMachineSideEffectLoad *)b, (StateMachineSideEffectStore *)a);
		else
			return memoryAccessesMightAlias(decode, opt, (StateMachineSideEffectStore *)a, (StateMachineSideEffectStore *)b);
	}
}

char *
Oracle::LivenessSet::mkName() const
{
	int i;
	char *acc;
	char *acc2;
	bool first = true;
	acc = strdup("<");
	for (i = 0; i < NR_REGS; i++) {
		if (!(mask & (1ul << i)))
			continue;
		if (!first) {
			acc2 = my_asprintf("%s|", acc);
			free(acc);
			acc = acc2;
		}
		first = false;
		switch (i * 8) {
#define do_reg(name) case OFFSET_amd64_ ## name : acc2 = my_asprintf("%s" #name , acc); break
			do_reg(RAX);
			do_reg(RDX);
			do_reg(RCX);
			do_reg(RBX);
			do_reg(RSP);
			do_reg(RBP);
			do_reg(RSI);
			do_reg(RDI);
			do_reg(R8);
			do_reg(R9);
			do_reg(R10);
			do_reg(R11);
			do_reg(R12);
			do_reg(R13);
			do_reg(R14);
			do_reg(R15);
#undef do_reg
		default:
			abort();
		}
		free(acc);
		acc = acc2;
	}
	acc2 = my_asprintf("%s>", acc);
	free(acc);
	return acc2;
}

#if CONFIG_FIXED_REGS
void
Oracle::setFixedRegs(const StaticRip &vr, const FixedRegs &fr)
{
	static prepared_stmt stmt("INSERT INTO fixedRegs (rip, content) VALUES (?, ?)");
	stmt.bindOracleRip(1, vr);
	stmt.bindString(2, fr.name());
	stmt.run();
}

bool
Oracle::getFixedRegs(const StaticRip &sr, FixedRegs *out)
{
	static prepared_stmt stmt("SELECT content FROM fixedRegs WHERE rip = ?");
	stmt.bindOracleRip(1, sr);
	int r = sqlite3_step(stmt.stmt);
	if (r == SQLITE_DONE) {
		sqlite3_reset(stmt.stmt);
		return false;
	}
	assert(r == SQLITE_ROW);
	const unsigned char *t = sqlite3_column_text(stmt.stmt, 0);
	const char *e;
	bool r2 = out->parse((const char *)t, &e);
	assert(r2);
	assert(*e == '\0');
	sqlite3_reset(stmt.stmt);
	return true;
}
#endif
