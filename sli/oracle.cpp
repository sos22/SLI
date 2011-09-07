#include <err.h>
#include <stdlib.h>

#include <map>
#include <queue>

#include <sqlite3.h>

#include "sli.h"
#include "oracle.hpp"
#include "simplify_irexpr.hpp"
#include "offline_analysis.hpp"

#include "libvex_prof.hpp"

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

void
mergeUlongSets(gc_pair_ulong_set_t *dest, const gc_pair_ulong_set_t *src)
{
	for (gc_pair_ulong_set_t::iterator it = src->begin();
	     it != src->end();
	     it++)
		dest->set(it.key(), it.value());
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

Oracle::LivenessSet
Oracle::LivenessSet::use(Int offset)
{
	if (offset >= 8 * NR_REGS)
		return *this;
	else
		return LivenessSet(mask | (1ul << (offset / 8)));
}

Oracle::LivenessSet
Oracle::LivenessSet::define(Int offset)
{
	if (offset >= 8 * NR_REGS)
		return *this;
	else
		return LivenessSet(mask & ~(1ul << (offset / 8)));
}

bool
Oracle::LivenessSet::isLive(Int offset) const
{
	if (offset >= 8 * NR_REGS)
		return true;
	else
		return !!(mask & (1ul << (offset / 8)));
}

const Oracle::PointerAliasingSet Oracle::PointerAliasingSet::notAPointer(1);
const Oracle::PointerAliasingSet Oracle::PointerAliasingSet::stackPointer(2);
const Oracle::PointerAliasingSet Oracle::PointerAliasingSet::nonStackPointer(4);
const Oracle::PointerAliasingSet Oracle::PointerAliasingSet::anything(7);

Oracle::RegisterAliasingConfiguration Oracle::RegisterAliasingConfiguration::functionEntryConfiguration(5.3f);
Oracle::RegisterAliasingConfiguration::RegisterAliasingConfiguration(float f)
{
	/* On function entry, the only pointer to the current stack
	   frame should be in RSP.  Anythign else indicates that the
	   guest program is doing something non-C-like. */
	stackHasLeaked = false;
	for (int i = 0; i < NR_REGS; i++)
		v[i] = Oracle::PointerAliasingSet::notAPointer | Oracle::PointerAliasingSet::nonStackPointer;
	v[4] = Oracle::PointerAliasingSet::stackPointer; /* rsp */
}

Oracle::RegisterAliasingConfiguration Oracle::RegisterAliasingConfiguration::unknown(5.3f, 12);
Oracle::RegisterAliasingConfiguration::RegisterAliasingConfiguration(float, int)
{
	stackHasLeaked = true;
	for (int i = 0; i < NR_REGS; i++)
		v[i] = Oracle::PointerAliasingSet::anything;
}

void
Oracle::RegisterAliasingConfiguration::prettyPrint(FILE *f) const
{
       for (int i = 0; i < NR_REGS; i++)
               fprintf(f, "\t%8d: %s\n", i, v[i].name());
}

void
Oracle::findPreviousInstructions(std::vector<unsigned long> &out)
{
	std::vector<unsigned long> fheads;
	getDominators(crashedThread, ms, out, fheads);
}

bool
Oracle::functionCanReturn(unsigned long rip)
{
#warning Horrible, horrible hack
	if (rip == 0x768440 /* ut_dbg_assertion_failed */ ||
	    rip == 0x7683e0 /* ut_dbg_stop_thread */)
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
Oracle::findConflictingStores(StateMachineSideEffectLoad *smsel,
			      std::set<unsigned long> &out)
{
	for (std::vector<tag_entry>::iterator it = tag_table.begin();
	     it != tag_table.end();
	     it++) {
		if (it->loads.count(smsel->rip.rip)) {
			for (std::set<unsigned long>::iterator it2 = it->stores.begin();
			     it2 != it->stores.end();
			     it2++) {
				if (!(*it2 & (1ul << 63)))
					out.insert(*it2);
			}
		}
	}
}

/* Try to guess whether this store might ever be consumed by another
   thread.  We approximate this by saying that anything not included
   in our database of dynamic information is thread-local. */
bool
Oracle::storeIsThreadLocal(StateMachineSideEffectStore *s)
{
	__set_profiling(storeIsThreadLocal);
	static std::set<unsigned long> threadLocal;
	static std::set<unsigned long> notThreadLocal;
	if (threadLocal.count(s->rip.rip))
		return true;
	if (notThreadLocal.count(s->rip.rip))
		return false;
	for (std::vector<tag_entry>::iterator it = tag_table.begin();
	     it != tag_table.end();
	     it++) {
		if (it->stores.count(s->rip.rip) ||
		    it->stores.count(s->rip.rip | (1ul << 63))) {
			notThreadLocal.insert(s->rip.rip);
			return false;
		}
	}
	threadLocal.insert(s->rip.rip);
	return true;
}
bool
Oracle::loadIsThreadLocal(StateMachineSideEffectLoad *s)
{
	__set_profiling(loadIsThreadLocal);
	static std::set<unsigned long> threadLocal;
	static std::set<unsigned long> notThreadLocal;
	if (threadLocal.count(s->rip.rip))
		return true;
	if (notThreadLocal.count(s->rip.rip))
		return false;
	for (std::vector<tag_entry>::iterator it = tag_table.begin();
	     it != tag_table.end();
	     it++)
		if (it->loads.count(s->rip.rip) ||
		    it->loads.count(s->rip.rip | (1ul << 63))) {
			notThreadLocal.insert(s->rip.rip);
			return false;
		}
	threadLocal.insert(s->rip.rip);
	return true;
}

void
Oracle::getAllMemoryAccessingInstructions(std::vector<unsigned long> &out) const
{
	std::set<unsigned long> allInstructions;
	
	for (std::vector<tag_entry>::const_iterator it = tag_table.begin();
	     it != tag_table.end();
	     it++) {
		for (std::set<unsigned long>::iterator it2 = it->stores.begin();
		     it2 != it->stores.end();
		     it2++)
			allInstructions.insert(*it2 & ~(1ul << 63));
		for (std::set<unsigned long>::iterator it2 = it->loads.begin();
		     it2 != it->loads.end();
		     it2++)
			allInstructions.insert(*it2 & ~(1ul << 63));
	}
	for (std::set<unsigned long>::iterator it = allInstructions.begin();
	     it != allInstructions.end();
	     it++)
		out.push_back(*it);
}

bool
Oracle::memoryAccessesMightAlias(StateMachineSideEffectLoad *smsel,
				 StateMachineSideEffectStore *smses)
{
	__set_profiling(might_alias_load_store);
	static unsigned nr_queries;
	static unsigned nr_bloom_hits;
	static unsigned nr_bloom_hits2;
	static unsigned nr_trues;
	static unsigned nr_falses;

	/* The tag database doesn't include anything which doesn't
	 * cross threads, so for those we have to use a slightly more
	 * stupid approach. */
	if (storeIsThreadLocal(smses)) {
		if (!loadIsThreadLocal(smsel))
			return false;
		if (!definitelyNotEqual(smsel->addr, smses->addr, AllowableOptimisations::defaultOptimisations))
			return true;
		else
			return false;
	}

	unsigned long h = hashRipPair(smses->rip.rip, smsel->rip.rip);
	nr_queries++;
	if (!(memoryAliasingFilter[h/64] & (1ul << (h % 64)))) {
		nr_bloom_hits++;
		return false;
	}
	h = hashRipPair(smses->rip.rip * 23, smsel->rip.rip * 17);
	if (!(memoryAliasingFilter2[h/64] & (1ul << (h % 64)))) {
		nr_bloom_hits2++;
		return false;
	}

	if (aliasingTable.count(std::pair<unsigned long, unsigned long>(smsel->rip.rip, smses->rip.rip))) {
		nr_trues++;
		return true;
	} else {
		nr_falses++;
		return false;
	}
}

bool
Oracle::memoryAccessesMightAlias(StateMachineSideEffectLoad *smsel1,
				 StateMachineSideEffectLoad *smsel2)
{
	__set_profiling(memory_accesses_might_alias_load_load);
	if (loadIsThreadLocal(smsel1)) {
		if (!loadIsThreadLocal(smsel2))
			return false;
		if (!definitelyNotEqual(smsel1->addr, smsel2->addr, AllowableOptimisations::defaultOptimisations))
			return true;
		else
			return false;
	} else if (loadIsThreadLocal(smsel2))
		return false;

	return !!aliasingTable.count(std::pair<unsigned long, unsigned long>(smsel1->rip.rip, smsel2->rip.rip));
}

bool
Oracle::memoryAccessesMightAlias(StateMachineSideEffectStore *smses1,
				 StateMachineSideEffectStore *smses2)
{
	__set_profiling(memory_accesses_might_alias_store_store);
	if (storeIsThreadLocal(smses1) && storeIsThreadLocal(smses2)) {
		if (!definitelyNotEqual(smses2->addr, smses1->addr, AllowableOptimisations::defaultOptimisations))
			return true;
		else
			return false;
	}
	return !!aliasingTable.count(std::pair<unsigned long, unsigned long>(smses1->rip.rip, smses2->rip.rip));
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
			if (pe->parent)
				e->parent = pe->parent;
			x = e->parent;
		}
	}
};

void
findInstrSuccessorsAndCallees(AddressSpace *as,
			      unsigned long rip,
			      std::vector<unsigned long> &directExits,
			      gc_pair_ulong_set_t *callees)
{
	__set_profiling(findInstrSuccessorsAndCallees);
	IRSB *irsb;
	try {
		irsb = as->getIRSBForAddress(-1, rip);
	} catch (BadMemoryException &e) {
		return;
	}
	int i;

	for (i = 1; i < irsb->stmts_used; i++) {
		if (irsb->stmts[i]->tag == Ist_IMark) {
			/* That's the end of this instruction */
			directExits.push_back(irsb->stmts[i]->Ist.IMark.addr);
			return;
		}
		if (irsb->stmts[i]->tag == Ist_Exit)
			directExits.push_back(irsb->stmts[i]->Ist.Exit.dst->Ico.U64);
	}

	/* If we get here then there are no other marks in the IRSB,
	   so we need to look at the fall through addresses. */
	if (irsb->jumpkind == Ijk_Call) {
		if (irsb->next->tag != Iex_Const ||
		    ((IRExprConst *)irsb->next)->con->Ico.U64 != __STACK_CHK_FAILED)
			directExits.push_back(extract_call_follower(irsb));
		/* Emit the target as well, if possible. */
		if (irsb->next->tag == Iex_Const)
			callees->set(std::pair<unsigned long, unsigned long>(rip, ((IRExprConst *)irsb->next)->con->Ico.U64),
				     true);
		return;
	}

	if (irsb->jumpkind != Ijk_NoDecode &&
	    irsb->next->tag == Iex_Const) {
		directExits.push_back(((IRExprConst *)irsb->next)->con->Ico.U64);
	} else {
		/* Should really do something more clever here,
		   possibly based on dynamic analysis. */
	}
}

static void
findSuccessors(AddressSpace *as, unsigned long rip, std::vector<unsigned long> &out)
{
	gc_pair_ulong_set_t *callees = new gc_pair_ulong_set_t();
	findInstrSuccessorsAndCallees(as, rip, out, callees);
	for (gc_pair_ulong_set_t::iterator it = callees->begin();
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
Oracle::clusterRips(const std::set<unsigned long> &inputRips,
		    std::set<InstructionSet> &outputClusters)
{
	__set_profiling(clusterRips);
	union_find<unsigned long> results;
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
		std::vector<unsigned long> discoveredInstructions;
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
	for (std::set<unsigned long>::const_iterator it = inputRips.begin();
	     it != inputRips.end();
	     it++) {
		unsigned long item = *it;
		
		results.insert(item);

		/* Map from rips to the ``best'' depth we've visited
		 * with so far. */
		std::map<unsigned long, int> visited;
		std::vector<std::pair<unsigned long, int> > pending;
		pending.push_back(std::pair<unsigned long, int>(item, 20));
		while (!pending.empty()) {
			std::pair<unsigned long, int> next = pending.back();
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
			std::vector<unsigned long> s;
			findSuccessors(ms->addressSpace, next.first, s);
			for (std::vector<unsigned long>::iterator it2 = s.begin();
			     it2 != s.end();
			     it2++)
				pending.push_back(std::pair<unsigned long, int>(*it2, next.second - 1));
		}
	}
#endif

	/* Now explode the union-find structure into a set of sets. */
	std::set<unsigned long> unprocessedInput(inputRips);
	while (!unprocessedInput.empty()) {
		unsigned long r = *unprocessedInput.begin();

		InstructionSet thisSet;
		unsigned long representative = results.representative(r);
		for (std::set<unsigned long>::iterator it = unprocessedInput.begin();
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

struct tag_hdr {
	int nr_loads;
	int nr_stores;
};

void
Oracle::loadTagTable(const char *path)
{
	__set_profiling(loadTagTable);

	FILE *f = fopen(path, "r");
	if (!f)
		err(1, "opening %s", path);
	while (!feof(f)) {
		struct tag_hdr hdr;
		if (fread(&hdr, sizeof(hdr), 1, f) < 1) {
			if (ferror(f)) 
				err(1, "reading %s", path);
			assert(feof(f));
			continue;
		}
		tag_entry t;
		for (int x = 0; x < hdr.nr_loads; x++) {
			unsigned long buf;
			if (fread(&buf, sizeof(buf), 1, f) != 1)
				err(1, "reading load address from %s", path);
			t.loads.insert(buf);
		}
		for (int x = 0; x < hdr.nr_stores; x++) {
			unsigned long buf;
			if (fread(&buf, sizeof(buf), 1, f) != 1)
				err(1, "reading load address from %s", path);
			t.stores.insert(buf);
		}
		for (std::set<unsigned long>::iterator it1 = t.stores.begin();
		     it1 != t.stores.end();
		     it1++) {
			if (*it1 & (1ul << 63))
				continue;
			for (std::set<unsigned long>::iterator it2 = t.stores.begin();
			     it2 != t.stores.end();
			     it2++) {
				if (!(*it2 & (1ul << 63)))
					aliasingTable.insert(std::pair<unsigned long, unsigned long>(*it1, *it2));
			}
			for (std::set<unsigned long>::iterator it2 = t.loads.begin();
			     it2 != t.loads.end();
			     it2++) {
				if (!(*it2 & (1ul << 63))) {
					unsigned long h = hashRipPair(*it1, *it2);
					memoryAliasingFilter[h / 64] |= 1ul << (h % 64);
					h = hashRipPair(*it1 * 23, *it2 * 17);
					memoryAliasingFilter2[h / 64] |= 1ul << (h % 64);
					aliasingTable.insert(std::pair<unsigned long, unsigned long>(*it1, *it2));
				}
			}
		}
		for (std::set<unsigned long>::iterator it1 = t.loads.begin();
		     it1 != t.loads.end();
		     it1++) {
			if (*it1 & (1ul << 63))
				continue;
			for (std::set<unsigned long>::iterator it2 = t.stores.begin();
			     it2 != t.stores.end();
			     it2++) {
				if (!(*it2 & (1ul << 63)))
					aliasingTable.insert(std::pair<unsigned long, unsigned long>(*it1, *it2));
			}
			for (std::set<unsigned long>::iterator it2 = t.loads.begin();
			     it2 != t.loads.end();
			     it2++) {
				if (!(*it2 & (1ul << 63)))
					aliasingTable.insert(std::pair<unsigned long, unsigned long>(*it1, *it2));
			}
		}
		tag_table.push_back(t);
	}
}

template <typename t>
bool
vector_contains(const std::vector<t> &v, const t &val)
{
	for (typename std::vector<t>::const_iterator it = v.begin();
	     it != v.end();
	     it++)
		if (*it == val)
			return true;
	return false;
}

void
Oracle::calculateRegisterLiveness(VexPtr<Oracle> &ths,
				  GarbageCollectionToken token)
{
	bool done_something;
	unsigned long changed;
	unsigned long unchanged;
	std::vector<unsigned long> functions;

	do {
		changed = 0;
		unchanged = 0;
		done_something = false;
		ths->getFunctions(functions);
		for (std::vector<unsigned long>::iterator it = functions.begin();
		     it != functions.end();
		     it++) {
			LibVEX_maybe_gc(token);
			bool this_did_something = false;
			Function f(*it);
			f.calculateRegisterLiveness(ths->ms->addressSpace, &this_did_something, ths);
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
	std::vector<unsigned long> functions;
	ths->getFunctions(functions);
	for (std::vector<unsigned long>::iterator it = functions.begin();
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
	std::vector<unsigned long> functions;

	ths->getFunctions(functions);
	for (std::vector<unsigned long>::iterator it = functions.begin();
	     it != functions.end();
	     it++) {
		LibVEX_maybe_gc(token);
		do {
			done_something = false;
			Function f(*it);
			f.calculateAliasing(ths->ms->addressSpace, &done_something, ths);
		} while (done_something);
	}
}

static Oracle::LivenessSet
irexprUsedValues(Oracle::LivenessSet old, IRExpr *w)
{
	class _ : public IRExprTransformer {
	public:
		Oracle::LivenessSet old;
		IRExpr *transformIex(IRExprGet *e) {
			old = old.use(e->offset);
			return IRExprTransformer::transformIex(e);
		}
		_(Oracle::LivenessSet &_old)
			: old(_old)
		{}
	} t(old);
	t.transformIRExpr(w);
	return t.old;
}

static Oracle::PointerAliasingSet
irexprAliasingClass(IRExpr *expr,
		    IRTypeEnv *tyenv,
		    const Oracle::RegisterAliasingConfiguration &config,
		    bool freeVariablesCannotAccessStack,
		    std::map<IRTemp, Oracle::PointerAliasingSet> *temps)
{
	if (tyenv && expr->type(tyenv) != Ity_I64)
		/* Not a 64 bit value -> not a pointer */
		return Oracle::PointerAliasingSet::notAPointer;

	switch (expr->tag) {
	case Iex_Get: {
		IRExprGet *e = (IRExprGet *)expr;
		if (e->offset < 0) {
			if (!temps)
				return Oracle::PointerAliasingSet::anything;
			std::map<IRTemp, Oracle::PointerAliasingSet>::iterator it;
			it = temps->find(-e->offset - 1);
			assert(it != temps->end());
			return it->second;
		} else if (e->offset < Oracle::NR_REGS * 8)
			return config.v[e->offset / 8];
		else {
			/* Assume that those are the only pointer registers */
			return Oracle::PointerAliasingSet::notAPointer;
		}
	}
	case Iex_Const:
		return Oracle::PointerAliasingSet::notAPointer | Oracle::PointerAliasingSet::nonStackPointer;
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
			return Oracle::PointerAliasingSet::notAPointer;
		default:
			break;
		}
		break;
	case Iex_Binop: {
		IRExprBinop *e = (IRExprBinop *)expr;
		Oracle::PointerAliasingSet a1 = irexprAliasingClass(
			e->arg1,
			tyenv,
			config,
			freeVariablesCannotAccessStack,
			temps);
		Oracle::PointerAliasingSet a2 = irexprAliasingClass(
			e->arg2,
			tyenv,
			config,
			freeVariablesCannotAccessStack,
			temps);
		switch (e->op) {
		case Iop_Sub64:
			/* x - y is a pointer to zone A if x is a
			 * pointer to zone A and y is not a pointer of
			 * any sort.  Otherwise, it's just not a
			 * pointer. */ {
			if (a2 & Oracle::PointerAliasingSet::notAPointer) {
				Oracle::PointerAliasingSet res = a1;
				if (a2 & (Oracle::PointerAliasingSet::stackPointer |
					  Oracle::PointerAliasingSet::nonStackPointer))
					res = res | Oracle::PointerAliasingSet::notAPointer;
				return res;
			} else {
				return Oracle::PointerAliasingSet::notAPointer;
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
		case Iop_Add32:
		case Iop_And32:
			return Oracle::PointerAliasingSet::notAPointer;
		default:
			break;
		}
		break;
	}
	case Iex_Mux0X: {
		IRExprMux0X *e = (IRExprMux0X *)expr;
		return irexprAliasingClass(e->expr0,
					   tyenv,
					   config,
					   freeVariablesCannotAccessStack,
					   temps) |
			irexprAliasingClass(e->exprX,
					    tyenv,
					    config,
					    freeVariablesCannotAccessStack,
					    temps);
	}
	case Iex_Associative: {
		IRExprAssociative *e = (IRExprAssociative *)expr;
		switch (e->op) {
		case Iop_Add64:
		case Iop_And64:
		{
			for (int i = 0; i < e->nr_arguments; i++) {
				if (e->contents[i]->tag != Iex_Const) {
					Oracle::PointerAliasingSet res = 
						irexprAliasingClass(e->contents[i],
								    tyenv,
								    config,
								    freeVariablesCannotAccessStack,
								    temps);
					for (int j = i + 1; j < e->nr_arguments; j++) {
						if (e->contents[j]->tag != Iex_Const)
							res = res | 
								irexprAliasingClass(e->contents[j],
										    tyenv,
										    config,
										    freeVariablesCannotAccessStack,
										    temps);
					}
					if (!(res & Oracle::PointerAliasingSet::anything))
						return Oracle::PointerAliasingSet::notAPointer;
					else
						return res;
				}
			}
			return Oracle::PointerAliasingSet::notAPointer;
		}
		case Iop_Add32:
		case Iop_And32:
			return Oracle::PointerAliasingSet::notAPointer;
		default:
			break;
		}
		break;
	}

	case Iex_CCall: {
		IRExprCCall *e = (IRExprCCall *)expr;
		if (!strcmp(e->cee->name, "amd64g_calculate_rflags_c") ||
		    !strcmp(e->cee->name, "amd64g_calculate_rflags_all"))
			return Oracle::PointerAliasingSet::notAPointer;
		break;
	}

	case Iex_FreeVariable:
		if (freeVariablesCannotAccessStack)
			return Oracle::PointerAliasingSet::notAPointer |
				Oracle::PointerAliasingSet::nonStackPointer;
		else
			return Oracle::PointerAliasingSet::anything;

	case Iex_ClientCall: {
		IRExprClientCall *e = (IRExprClientCall *)expr;
		bool mightReturnStack = false;
		for (int x = 0; !mightReturnStack && e->args[x]; x++) {
			if (irexprAliasingClass(e->args[x],
						tyenv,
						config,
						freeVariablesCannotAccessStack,
						temps) &
			    Oracle::PointerAliasingSet::stackPointer)
				mightReturnStack = true;
		}
		if (mightReturnStack)
			return Oracle::PointerAliasingSet::anything;
		else
			return Oracle::PointerAliasingSet::notAPointer |
				Oracle::PointerAliasingSet::nonStackPointer;
	}
						
	default:
		break;
	}
	fprintf(_logfile, "Don't know how to compute aliasing sets for ");
	ppIRExpr(expr, _logfile);
	fprintf(_logfile, "\n");
	return Oracle::PointerAliasingSet::anything;
}

bool
Oracle::RegisterAliasingConfiguration::ptrsMightAlias(IRExpr *a, IRExpr *b, bool fvcas) const
{
	return irexprAliasingClass(a, NULL, *this, fvcas, NULL) &
		irexprAliasingClass(b, NULL, *this, fvcas, NULL) &
		~PointerAliasingSet::notAPointer;
}

Oracle::RegisterAliasingConfiguration
Oracle::getAliasingConfigurationForRip(unsigned long rip)
{
	Function f(rip);
	return f.aliasConfigOnEntryToInstruction(rip);
}

struct cg_header {
	unsigned long rip;
	unsigned long nr;
};

void
Oracle::loadCallGraph(VexPtr<Oracle> &ths, const char *path, GarbageCollectionToken token)
{
	__set_profiling(oracle_load_call_graph);

	if (ths->callGraphMapping.init(path) < 0)
		err(1, "opening %s", path);
	std::vector<unsigned long> roots;
	unsigned offset = 0;
	while (1) {
		const struct cg_header *h;
		h = ths->callGraphMapping.get<struct cg_header>(offset);
		if (!h)
			break;
		offset += sizeof(*h);
		const unsigned long *c = ths->callGraphMapping.get<unsigned long>(offset, h->nr);
		assert(c);
		for (unsigned i = 0; i < h->nr; i++) {
			if (c[i] & (1ul << 63))
				roots.push_back(c[i] & ~(1ul << 63));
		}
		offset += sizeof(unsigned long) * h->nr;
	}

	make_unique(roots);
	discoverFunctionHeads(ths, roots, token);
}

void
Oracle::findPossibleJumpTargets(unsigned long rip, std::vector<unsigned long> &output)
{
	if (!callGraphMapping.live())
		return;
	unsigned offset = 0;
	while (1) {
		const struct cg_header *h;
		h = callGraphMapping.get<struct cg_header>(offset);
		if (!h)
			return;
		offset += sizeof(*h);
		if (h->rip == rip) {
			const unsigned long *c = callGraphMapping.get<unsigned long>(offset, h->nr);
			assert(c);
			for (unsigned i = 0; i < h->nr; i++)
				output.push_back(c[i] & ~(1ul << 63));
			make_unique(output);
			return;
		}
		offset += sizeof(unsigned long) * h->nr;
	}
}

void
Oracle::findPreviousInstructions(std::vector<unsigned long> &output,
				 unsigned long rip)
{
	unsigned long r = functionHeadForInstruction(rip);
	if (!r) {
		fprintf(_logfile, "No function for %lx\n", rip);
		return;
	}
	Function f(r);

	/* Build the shortest path from the start of the function to
	   the desired rip using Dijkstra's algorithm.  */
	/* Distance from start of function to key.  Non-present keys
	 * should be assumed to have an infinite length. */
	std::map<unsigned long, unsigned> pathLengths;
	/* Predecessor on best path from start to key. */
	std::map<unsigned long, unsigned long> predecessors; 
	/* We push stuff in here when we discover a new shortest path
	   to that node. */
	std::priority_queue<std::pair<unsigned, unsigned long> > grey;

	pathLengths[f.rip] = 0;
	grey.push(std::pair<unsigned, unsigned long>(0, f.rip));
	while (!grey.empty()) {
		std::pair<unsigned, unsigned long> e(grey.top());
		grey.pop();

		assert(pathLengths.count(e.second));
		unsigned p = pathLengths[e.second] + 1;
		std::vector<unsigned long> successors;
		f.getSuccessors(e.second, successors);
		for (std::vector<unsigned long>::iterator it = successors.begin();
		     it != successors.end();
		     it++) {
			unsigned long ft = *it;
			if (!pathLengths.count(ft) || pathLengths[ft] >= p) {
				pathLengths[ft] = p;
				predecessors[ft] = e.second;
				grey.push(std::pair<unsigned, unsigned long>(p, ft));
			}
		}
	}
	
	if (!predecessors.count(rip)) {
		/* This can happen if the information from the oracle
		   is inconsistent. */
		fprintf(_logfile, "Dijkstra failed in %s\n", __func__);
		return;
	}

	for (unsigned long i = predecessors[rip]; i; i = predecessors[i])
		output.push_back(i);
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
	
	rc = sqlite3_open_v2("static.db", &_database, SQLITE_OPEN_READWRITE, NULL);
	if (rc == SQLITE_OK) {
		/* Return existing database */
		goto disable_journalling;
	}

	/* Create new database */
	rc = sqlite3_open_v2("static.db", &_database, SQLITE_OPEN_READWRITE|SQLITE_OPEN_CREATE, NULL);
	assert(rc == SQLITE_OK);

	rc = sqlite3_exec(_database,
			  "CREATE TABLE instructionAttributes (rip INTEGER PRIMARY KEY, liveOnEntry INTEGER,"
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
			  "stackHasLeaked INTEGER," /* 0 or NULL -> false, 1 -> true */
			  "rbpToRspDeltaState INTEGER NOT NULL DEFAULT 0,"  /* 0 -> unknown, 1 -> known, 2 -> incalculable */
			  "rbpToRspDelta INTEGER NOT NULL DEFAULT 0,"
			  "functionHead INTEGER NOT NULL)",
			  NULL,
			  NULL,
			  NULL);
	assert(rc == SQLITE_OK);
	rc = sqlite3_exec(_database, "CREATE TABLE fallThroughRips (rip INTEGER, dest INTEGER, UNIQUE (rip, dest))", NULL, NULL, NULL);
	assert(rc == SQLITE_OK);
	rc = sqlite3_exec(_database, "CREATE TABLE branchRips (rip INTEGER, dest INTEGER, UNIQUE (rip, dest))", NULL, NULL, NULL);
	assert(rc == SQLITE_OK);
	rc = sqlite3_exec(_database, "CREATE TABLE callRips (rip INTEGER, dest INTEGER, UNIQUE (rip, dest))", NULL, NULL, NULL);
	assert(rc == SQLITE_OK);
	rc = sqlite3_exec(_database, "CREATE TABLE functionAttribs (functionHead INTEGER PRIMARY KEY, registerLivenessCorrect INTEGER NOT NULL, rbpOffsetCorrect INTEGER NOT NULL, aliasingCorrect INTEGER NOT NULL)",
			  NULL, NULL, NULL);
	assert(rc == SQLITE_OK);

	create_index("instructionAttributesFunctionHead", "instructionAttributes", "functionHead");

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
bind_int64(sqlite3_stmt *stmt, int idx, unsigned long val)
{
	int rc;
	rc = sqlite3_bind_int64(stmt, idx, val);
	assert(rc == SQLITE_OK);
}

static void
drop_index(const char *name)
{
	char *s = my_asprintf("DROP INDEX %s", name);
	sqlite3_exec(database(), s, NULL, NULL, NULL);
	free(s);
}

void
Oracle::discoverFunctionHeads(VexPtr<Oracle> &ths, std::vector<unsigned long> &heads, GarbageCollectionToken token)
{
	drop_index("branchDest");
	drop_index("callDest");
	drop_index("fallThroughDest");

	std::set<unsigned long> visited;
	while (!heads.empty()) {
		unsigned long head;
		head = heads.back();
		heads.pop_back();
		if (visited.count(head))
			continue;
		visited.insert(head);
		ths->discoverFunctionHead(head, heads);
		printf("%zd heads left to process...\n", heads.size());
	}

	create_index("branchDest", "branchRips", "dest");
	create_index("callDest", "callRips", "dest");
	create_index("fallThroughDest", "fallThroughRips", "dest");

	calculateRegisterLiveness(ths, token);
	calculateAliasing(ths, token);
	calculateRbpToRspOffsets(ths, token);
}

Oracle::LivenessSet
Oracle::Function::liveOnEntry(unsigned long rip, bool isHead)
{
	static sqlite3_stmt *stmt;
	int rc;

	if (!stmt)
		stmt = prepare_statement("SELECT liveOnEntry FROM instructionAttributes WHERE rip = ?");
	bind_int64(stmt, 1, rip);
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

Oracle::RegisterAliasingConfiguration
Oracle::Function::aliasConfigOnEntryToInstruction(unsigned long rip, bool *b)
{
	static sqlite3_stmt *stmt;
	int rc;

	if (!stmt)
		stmt = prepare_statement(
			"SELECT alias0, alias1, alias2, alias3, alias4, alias5, alias6, alias7, alias8, alias9, alias10, alias11, alias12, alias13, alias14, alias15, stackHasLeaked FROM instructionAttributes WHERE rip = ?");
	bind_int64(stmt, 1, rip);
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE || rc == SQLITE_ROW);
	if (rc == SQLITE_DONE) {
		sqlite3_reset(stmt);
		*b = false;
		return RegisterAliasingConfiguration::unknown;
	}
	int i;
	RegisterAliasingConfiguration res;
	for (i = 0; i < NR_REGS; i++) {
		unsigned long r;
		if (sqlite3_column_type(stmt, i) == SQLITE_NULL) {
			r = 0;
		} else {
			assert(sqlite3_column_type(stmt, i) == SQLITE_INTEGER);
			r = sqlite3_column_int64(stmt, i);
		}
		res.v[i] = PointerAliasingSet(r);
	}
	if (sqlite3_column_type(stmt, i) == SQLITE_NULL) {
		res.stackHasLeaked = false;
	} else {
		assert(sqlite3_column_type(stmt, i) == SQLITE_INTEGER);
		unsigned long r = sqlite3_column_int64(stmt, i);
		assert(r == 0 || r == 1);
		if (r)
			res.stackHasLeaked = true;
		else
			res.stackHasLeaked = false;
	}
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE);
	sqlite3_reset(stmt);
	*b = true;
	return res;
}

bool
Oracle::Function::aliasConfigOnEntryToInstruction(unsigned long rip, Oracle::RegisterAliasingConfiguration *out)
{
	bool res;
	*out = aliasConfigOnEntryToInstruction(rip, &res);
	return res;
}

Oracle::RegisterAliasingConfiguration
Oracle::Function::aliasConfigOnEntryToInstruction(unsigned long rip)
{
	bool ign;
	return aliasConfigOnEntryToInstruction(rip, &ign);
}

void
Oracle::discoverFunctionHead(unsigned long x, std::vector<unsigned long> &heads)
{
	Function work(x);

	if (work.exists())
		return;

	/* Start by building a CFG of the function's instructions. */
	std::vector<unsigned long> unexplored;
	std::set<unsigned long> explored;
	unexplored.push_back(x);
	while (!unexplored.empty()) {
		unsigned long rip = unexplored.back();
		unexplored.pop_back();

		if (explored.count(rip))
			continue;

		IRSB *irsb;
		try {
			irsb = ms->addressSpace->getIRSBForAddress(STATIC_THREAD, rip);
		} catch (BadMemoryException &e) {
			irsb = NULL;
		}
		if (!irsb)
			continue;

		int end_of_instruction;
		int start_of_instruction = 0;
		while (start_of_instruction < irsb->stmts_used) {
			assert(irsb->stmts[start_of_instruction]->tag == Ist_IMark);
			unsigned long r = irsb->stmts[start_of_instruction]->Ist.IMark.addr;
			if (explored.count(r))
				break;

			std::vector<unsigned long> branch;
			std::vector<unsigned long> fallThrough;
			std::vector<unsigned long> callees;
			for (end_of_instruction = start_of_instruction + 1;
			     end_of_instruction < irsb->stmts_used && irsb->stmts[end_of_instruction]->tag != Ist_IMark;
			     end_of_instruction++) {
				if (irsb->stmts[end_of_instruction]->tag == Ist_Exit)
					branch.push_back(irsb->stmts[end_of_instruction]->Ist.Exit.dst->Ico.U64);
			}

			if (end_of_instruction == irsb->stmts_used) {
				if (irsb->jumpkind == Ijk_Call) {
					if (irsb->next->tag != Iex_Const ||
					    ((IRExprConst *)irsb->next)->con->Ico.U64 != __STACK_CHK_FAILED)
						fallThrough.push_back(extract_call_follower(irsb));
					if (irsb->next->tag == Iex_Const)
						callees.push_back(((IRExprConst *)irsb->next)->con->Ico.U64);
					else
						findPossibleJumpTargets(rip, callees);
				} else {
					if (irsb->next->tag == Iex_Const)
						fallThrough.push_back(((IRExprConst *)irsb->next)->con->Ico.U64);
					else if (irsb->jumpkind != Ijk_Ret)
						findPossibleJumpTargets(rip, fallThrough);
				}
			} else {
				fallThrough.push_back(irsb->stmts[end_of_instruction]->Ist.IMark.addr);
			}

			heads.insert(heads.end(), callees.begin(), callees.end());
			unexplored.insert(unexplored.end(), fallThrough.begin(), fallThrough.end());
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
			if (!work.addInstruction(r, callees, fallThrough, branch)) {
				/* Already explored this instruction
				 * as part of some other function.
				 * Meh. */
				break;
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

	std::vector<unsigned long> instrsToRecalculate1;
	std::vector<unsigned long> instrsToRecalculate2;

	getInstructionsInFunction(instrsToRecalculate1);

	while (1) {
		for (std::vector<unsigned long>::iterator it = instrsToRecalculate1.begin();
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

		for (std::vector<unsigned long>::iterator it = instrsToRecalculate2.begin();
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
Oracle::Function::calculateRegisterLiveness(AddressSpace *as, bool *done_something, Oracle *oracle)
{
	bool changed;

	if (registerLivenessCorrect())
		return;

	std::vector<unsigned long> instrsToRecalculate1;
	std::vector<unsigned long> instrsToRecalculate2;

	getInstructionsInFunction(instrsToRecalculate1);

	std::reverse(instrsToRecalculate1.begin(),
		     instrsToRecalculate1.end());

	changed = false;
	while (1) {
		for (std::vector<unsigned long>::iterator it = instrsToRecalculate1.begin();
		     it != instrsToRecalculate1.end();
		     it++) {
			bool t = false;
			updateLiveOnEntry(*it, as, &t, oracle);
			if (t)
				addPredecessors(*it, instrsToRecalculate2);
		}
		instrsToRecalculate1.clear();
		if (instrsToRecalculate2.empty())
			break;
		changed = true;

		for (std::vector<unsigned long>::iterator it = instrsToRecalculate2.begin();
		     it != instrsToRecalculate2.end();
		     it++) {
			bool t = false;
			updateLiveOnEntry(*it, as, &t, oracle);
			if (t)
				addPredecessors(*it, instrsToRecalculate1);
		}

		instrsToRecalculate2.clear();
		if (instrsToRecalculate1.empty())
			break;
	}

	setRegisterLivenessCorrect(true);

	if (changed) {
		*done_something = true;
		std::vector<unsigned long> callers;
		getFunctionCallers(callers, oracle);
		for (std::vector<unsigned long>::iterator it = callers.begin();
		     it != callers.end();
		     it++)
			(Function(*it)).setRegisterLivenessCorrect(false);
	}
}

void
Oracle::Function::calculateAliasing(AddressSpace *as, bool *done_something, Oracle *oracle)
{
	if (aliasingConfigCorrect())
		return;

	bool aValid;
	RegisterAliasingConfiguration a(aliasConfigOnEntryToInstruction(rip, &aValid));
	if (aValid) {
	RegisterAliasingConfiguration b(a);
		b |= RegisterAliasingConfiguration::functionEntryConfiguration;
		if (a != b) {
			*done_something = true;
			setAliasConfigOnEntryToInstruction(rip, b);
		}
	} else {
		*done_something = true;
		setAliasConfigOnEntryToInstruction(rip, RegisterAliasingConfiguration::functionEntryConfiguration);
	}

	std::vector<unsigned long> needsUpdating;
	std::vector<unsigned long> allInstrs;
	getInstructionsInFunction(allInstrs);
	for (std::vector<unsigned long>::iterator it = allInstrs.begin();
	     it != allInstrs.end();
	     it++)
		updateSuccessorInstructionsAliasing(*it, as, &needsUpdating, oracle);
	while (!needsUpdating.empty()) {
		*done_something = true;
		unsigned long rip = needsUpdating.back();
		needsUpdating.pop_back();
		updateSuccessorInstructionsAliasing(rip, as, &needsUpdating, oracle);
	}

	setAliasingConfigCorrect(true);
}

void
Oracle::Function::updateLiveOnEntry(const unsigned long rip, AddressSpace *as, bool *changed, Oracle *oracle)
{
	LivenessSet res;

	IRSB *irsb = as->getIRSBForAddress(-1, rip);
	IRStmt **statements = irsb->stmts;
	int nr_statements;
	for (nr_statements = 1;
	     nr_statements < irsb->stmts_used && statements[nr_statements]->tag != Ist_IMark;
	     nr_statements++)
		;

	std::vector<unsigned long> fallThroughRips;
	std::vector<unsigned long> callees;

	if (nr_statements == irsb->stmts_used) {
		if (irsb->jumpkind == Ijk_Call) {
			if (irsb->next->tag != Iex_Const ||
			    ((IRExprConst *)irsb->next)->con->Ico.U64 != __STACK_CHK_FAILED)
				fallThroughRips.push_back(extract_call_follower(irsb));
			if (irsb->next->tag == Iex_Const)
				callees.push_back(((IRExprConst *)irsb->next)->con->Ico.U64);
			else
				getInstructionCallees(rip, callees, oracle);
		} else {
			if (irsb->next->tag == Iex_Const)
				fallThroughRips.push_back(((IRExprConst *)irsb->next)->con->Ico.U64);
			else
				getInstructionFallThroughs(rip, fallThroughRips);
		}
	} else {
		fallThroughRips.push_back(statements[nr_statements]->Ist.IMark.addr);
	}

	for (std::vector<unsigned long>::iterator it = fallThroughRips.begin();
	     it != fallThroughRips.end();
	     it++)
		res |= liveOnEntry(*it, false);
	for (std::vector<unsigned long>::iterator it = callees.begin();
	     it != callees.end();
	     it++) {
		Function f(*it);
		res |= f.liveOnEntry(*it, true) & LivenessSet::argRegisters;
	}

	for (int i = nr_statements - 1; i >= 1; i--) {
		switch (statements[i]->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			abort();
		case Ist_AbiHint:
			break;
		case Ist_Put:
			res = res.define(statements[i]->Ist.Put.offset);
			res = irexprUsedValues(res, statements[i]->Ist.Put.data);
			break;
		case Ist_PutI:
			res = irexprUsedValues(res, statements[i]->Ist.PutI.data);
			res = irexprUsedValues(res, statements[i]->Ist.PutI.ix);
			break;
		case Ist_WrTmp:
			res = irexprUsedValues(res, statements[i]->Ist.WrTmp.data);
			break;
		case Ist_Store:
			res = irexprUsedValues(res, statements[i]->Ist.Store.data);
			res = irexprUsedValues(res, statements[i]->Ist.Store.addr);
			break;
		case Ist_CAS:
			res = irexprUsedValues(res, statements[i]->Ist.CAS.details->addr);
			res = irexprUsedValues(res, statements[i]->Ist.CAS.details->expdHi);
			res = irexprUsedValues(res, statements[i]->Ist.CAS.details->expdLo);
			res = irexprUsedValues(res, statements[i]->Ist.CAS.details->dataHi);
			res = irexprUsedValues(res, statements[i]->Ist.CAS.details->dataLo);
			break;
		case Ist_Dirty:
			res = irexprUsedValues(res, statements[i]->Ist.Dirty.details->guard);
			for (int j = 0; statements[i]->Ist.Dirty.details->args[j]; j++)
				res = irexprUsedValues(res, statements[i]->Ist.Dirty.details->args[j]);
			res = irexprUsedValues(res, statements[i]->Ist.Dirty.details->mAddr);
			break;
		case Ist_MBE:
			abort();
		case Ist_Exit: {
			unsigned long _branchRip = statements[i]->Ist.Exit.dst->Ico.U64;
			if (_branchRip)
				res |= liveOnEntry(_branchRip, false);
			res = irexprUsedValues(res, statements[i]->Ist.Exit.guard);
			break;
		}
		default:
			abort();
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
		bind_int64(stmt, 2, rip);
		rc = sqlite3_step(stmt);
		assert(rc == SQLITE_DONE);
		sqlite3_reset(stmt);
	}
}

class RewriteRegisterExpr : public IRExprTransformer {
	unsigned idx;
	IRExpr *to;
protected:
	IRExpr *transformIex(IRExprGet *what) {
		if (what->offset == (int)idx)
			return to;
		else
			return NULL;
	}
public:
	RewriteRegisterExpr(unsigned _idx, IRExpr *_to)
		: idx(_idx), to(_to)
	{
	}
};
static IRExpr *
rewriteRegister(IRExpr *expr, int offset, IRExpr *to)
{
	RewriteRegisterExpr rre(offset, to);
	bool ign;
	return rre.transformIRExpr(expr, &ign);
}

class RewriteTemporaryExpr : public IRExprTransformer {
	IRTemp tmp;
	IRExpr *to;
protected:
	IRExpr *transformIex(IRExprGet *what)
	{
		if (what->offset == -(Int)tmp - 1)
			return to;
		else
			return NULL;
	}
public:
	RewriteTemporaryExpr(IRTemp _tmp, IRExpr *_to)
		: tmp(_tmp), to(_to)
	{
	}
};
static IRExpr *
rewriteTemporary(IRExpr *expr,
		 IRTemp tmp,
		 IRExpr *newval)
{
	RewriteTemporaryExpr rt(tmp, newval);
	return rt.transformIRExpr(expr);
}

void
Oracle::Function::updateRbpToRspOffset(unsigned long rip, AddressSpace *as, bool *changed, Oracle *oracle)
{
	RbpToRspOffsetState current_state;
	unsigned long current_offset;
	RbpToRspOffsetState state;
	unsigned long offset = -99999999; /* Shut the compiler up. */

	oracle->getRbpToRspOffset(rip, &current_state, &current_offset);
	if (current_state == RbpToRspOffsetStateImpossible) {
		/* By monotonicity, the result will be
		   RbpToRspOffsetStateImpossible, so bypass and get
		   out early. */
		return;
	}

	/* Try to figure out what this instruction actually does. */
	IRSB *irsb;
	try {
		irsb = as->getIRSBForAddress(-1, rip);
	} catch (BadMemoryException e) {
		return;
	}
	IRStmt **statements = irsb->stmts;
	int nr_statements;
	for (nr_statements = 1;
	     nr_statements < irsb->stmts_used && statements[nr_statements]->tag != Ist_IMark;
	     nr_statements++)
		;

	long delta_offset = 0;
	IRExpr *rbp = NULL;
	IRExpr *rsp = NULL;
	int j;

	/* We assume called functions never change rsp or rbp, so
	 * treat calls as nops. */
	if (nr_statements == irsb->stmts_used &&
	    irsb->jumpkind == Ijk_Call)
		goto join_predecessors;
	/* Scan backwards through the instruction for any writes to
	   either of the registers of interest. */
	for (j = nr_statements - 1; j >= 0; j--) {
		IRStmt *stmt = statements[j];
		if (stmt->tag == Ist_Put) {
			if (stmt->Ist.Put.offset == OFFSET_amd64_RSP && !rsp)
				rsp = IRExpr_Get(OFFSET_amd64_RSP, Ity_I64, -1);
			if (stmt->Ist.Put.offset == OFFSET_amd64_RBP && !rbp)
				rbp = IRExpr_Get(OFFSET_amd64_RBP, Ity_I64, -1);
			if (rsp)
				rsp = rewriteRegister(rsp,
						      stmt->Ist.Put.offset,
						      stmt->Ist.Put.data);
			if (rbp)
				rbp = rewriteRegister(rbp,
						      stmt->Ist.Put.offset,
						      stmt->Ist.Put.data);
		} else if (stmt->tag == Ist_WrTmp) {
			if (rsp)
				rsp = rewriteTemporary(rsp,
						       stmt->Ist.WrTmp.tmp,
						       stmt->Ist.WrTmp.data);
			if (rbp)
				rbp = rewriteTemporary(rbp,
						       stmt->Ist.WrTmp.tmp,
						       stmt->Ist.WrTmp.data);
		} else if (stmt->tag == Ist_CAS) {
			if (stmt->Ist.CAS.details->oldLo == OFFSET_amd64_RSP ||
			    stmt->Ist.CAS.details->oldLo == OFFSET_amd64_RBP)
				goto impossible;
		} else if (stmt->tag == Ist_Dirty) {
			IRTemp tmp = stmt->Ist.Dirty.details->tmp;
			IRType t = Ity_I1;
			if (!strcmp(stmt->Ist.Dirty.details->cee->name,
				    "helper_load_128"))
				t = Ity_I128;
			else if (!strcmp(stmt->Ist.Dirty.details->cee->name,
				    "helper_load_64"))
				t = Ity_I64;
			else if (!strcmp(stmt->Ist.Dirty.details->cee->name,
					 "helper_load_32"))
				t = Ity_I32;
			else if (!strcmp(stmt->Ist.Dirty.details->cee->name,
					 "helper_load_16"))
				t = Ity_I16;
			else if (!strcmp(stmt->Ist.Dirty.details->cee->name,
					 "helper_load_8"))
				t = Ity_I8;
			else if (!strcmp(stmt->Ist.Dirty.details->cee->name,
					 "amd64g_dirtyhelper_RDTSC"))
				goto impossible_clean;
			else
				goto impossible;
			IRExpr *v = IRExpr_Load(False, Iend_LE,
						t,
						stmt->Ist.Dirty.details->args[0],
						ThreadRip::mk(9999, rip));
			if (rsp)
				rsp = rewriteTemporary(rsp, tmp, v);
			if (rbp)
				rbp = rewriteTemporary(rbp, tmp, v);
		}
	}

	if (rsp)
		rsp = simplifyIRExpr(rsp, AllowableOptimisations::defaultOptimisations);
	if (rbp)
		rbp = simplifyIRExpr(rbp, AllowableOptimisations::defaultOptimisations);
	if (rsp && rsp->tag == Iex_Get && ((IRExprGet *)rsp)->offset == OFFSET_amd64_RSP)
		rsp = NULL;
	if (rbp && rbp->tag == Iex_Get && ((IRExprGet *)rbp)->offset == OFFSET_amd64_RBP)
		rbp = NULL;
	if (!rsp && !rbp)
		goto join_predecessors;
	if (rsp && rbp)
		goto impossible_clean;

	if (rsp) {
		if (rsp->tag == Iex_Get) {
			IRExprGet *g = (IRExprGet *)rsp;
			if (g->offset == OFFSET_amd64_RSP) {
				abort();
			} else if (g->offset == OFFSET_amd64_RBP) {
				offset = 0;
				state = RbpToRspOffsetStateValid;
				goto done;
			}
		} else if (rsp->tag == Iex_Associative) {
			IRExprAssociative *a = (IRExprAssociative *)rsp;
			if (a->op == Iop_Add64 &&
			    a->nr_arguments >= 2 &&
			    a->contents[0]->tag == Iex_Const &&
			    a->contents[1]->tag == Iex_Get) {
				IRExprGet *base = (IRExprGet *)a->contents[1];
				if (base->offset == OFFSET_amd64_RSP) {
					delta_offset = ((IRExprConst *)a->contents[0])->con->Ico.U64;
					goto join_predecessors;
				} else if (base->offset == OFFSET_amd64_RBP) {
					offset = ((IRExprConst *)a->contents[0])->con->Ico.U64;
					state = RbpToRspOffsetStateValid;
					goto done;
				}
			}
		}

		goto impossible_clean;
	} else {
		assert(rbp);

		if (rbp->tag == Iex_Get) {
			IRExprGet *g = (IRExprGet *)rbp;
			if (g->offset == OFFSET_amd64_RBP) {
				abort();
			} else if (g->offset == OFFSET_amd64_RSP) {
				offset = 0;
				state = RbpToRspOffsetStateValid;
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
				if (base->offset == OFFSET_amd64_RBP) {
					delta_offset = -o->Ico.U64;
					goto join_predecessors;
				} else if (base->offset == OFFSET_amd64_RSP) {
					offset = -o->Ico.U64;
					state = RbpToRspOffsetStateValid;
					goto done;
				}
			}
		}

		/* If the compiler's done base pointer elimination
		   then RBP can contain almost anything and it's not
		   worth trying to warn about it. */
		goto impossible_clean;
	}

join_predecessors:
	state = RbpToRspOffsetStateUnknown;
	{
		std::vector<unsigned long> predecessors;
		addPredecessorsNonCall(rip, predecessors);

		for (std::vector<unsigned long>::iterator it = predecessors.begin();
		     it != predecessors.end();
		     it++) {
			enum RbpToRspOffsetState pred_state;
			unsigned long pred_offset;
			oracle->getRbpToRspOffset(*it, &pred_state, &pred_offset);
			if (pred_state == RbpToRspOffsetStateImpossible)
				goto impossible_clean;
			if (pred_state == RbpToRspOffsetStateUnknown)
				continue;
			assert(pred_state == RbpToRspOffsetStateValid);
			if (state == RbpToRspOffsetStateUnknown) {
				state = RbpToRspOffsetStateValid;
				offset = pred_offset;
				continue;
			}
			assert(state == RbpToRspOffsetStateValid);
			if (offset != pred_offset)
				goto impossible_clean;
		}
	}
	if (state == RbpToRspOffsetStateUnknown) {
		/* Predecessor state is still unknown, nothing
		 * we can do. */
		return;
	}

	offset += delta_offset;

done:
	if (current_state == state && current_offset == offset) {
		/* Already correct, nothing to do */
		return;
	}

	*changed = true;
	oracle->setRbpToRspOffset(rip, state, offset);
	return;

impossible:
	printf("Cannot do stack offset calculations in first instruction of: ");
	ppIRSB(irsb, stdout);

	dbg_break("badness");

impossible_clean:
	state = RbpToRspOffsetStateImpossible;
	offset = 0;
	goto done;
}

void
Oracle::Function::updateSuccessorInstructionsAliasing(unsigned long rip, AddressSpace *as, std::vector<unsigned long> *changed,
						      Oracle *oracle)
{
	RegisterAliasingConfiguration config(aliasConfigOnEntryToInstruction(rip));
	std::map<IRTemp, PointerAliasingSet> temporaryAliases;
	IRStmt *st;

	int nr_statements;
	IRSB *irsb;
	try {
		irsb = as->getIRSBForAddress(-1, rip);
	} catch (BadMemoryException &e) {
		return;
	}
	IRStmt **statements = irsb->stmts;
	for (nr_statements = 1;
	     nr_statements < irsb->stmts_used && statements[nr_statements]->tag != Ist_IMark;
	     nr_statements++)
		;
	IRTypeEnv *tyenv = irsb->tyenv;
	for (int i = 1; i < nr_statements; i++) {
		st = statements[i];
		switch (st->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			abort();
		case Ist_AbiHint:
			break;
		case Ist_Put:
			if (st->Ist.Put.offset < NR_REGS * 8 &&
			    st->Ist.Put.offset != OFFSET_amd64_RSP) {
				config.v[st->Ist.Put.offset / 8] =
					irexprAliasingClass(st->Ist.Put.data,
							    tyenv,
							    config,
							    false,
							    &temporaryAliases);
			}
			break;
		case Ist_PutI:
			/* Assume that PutIs never target the NR_REGS registers */
			break;
		case Ist_WrTmp:
			temporaryAliases.insert(
				std::pair<IRTemp, PointerAliasingSet>(st->Ist.WrTmp.tmp,
								      irexprAliasingClass(st->Ist.WrTmp.data,
											  tyenv,
											  config,
											  false,
											  &temporaryAliases)));
			break;
		case Ist_Store:
			if (!config.stackHasLeaked) {
				PointerAliasingSet addr = irexprAliasingClass(st->Ist.Store.data,
									      tyenv,
									      config,
									      false,
									      &temporaryAliases);
				PointerAliasingSet data = irexprAliasingClass(st->Ist.Store.data,
									      tyenv,
									      config,
									      false,
									      &temporaryAliases);
				if ((addr & PointerAliasingSet::nonStackPointer) &&
				    (data & PointerAliasingSet::stackPointer))
					config.stackHasLeaked = true;
			}
			break;
		case Ist_CAS:
			temporaryAliases.insert(
				std::pair<IRTemp, PointerAliasingSet>(
					st->Ist.CAS.details->oldLo,
					PointerAliasingSet::anything));
			break;
		case Ist_Dirty:
			if (st->Ist.Dirty.details->tmp != IRTemp_INVALID) {
				PointerAliasingSet res =
					(tyenv->types[st->Ist.Dirty.details->tmp] == Ity_I64) ?
					((strcmp(st->Ist.Dirty.details->cee->name, "helper_load_64") ||
					  config.stackHasLeaked) ?
					 PointerAliasingSet::anything :
					 PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer) :
					PointerAliasingSet::notAPointer;
				temporaryAliases.insert(
					std::pair<IRTemp, PointerAliasingSet>(
						st->Ist.Dirty.details->tmp,
						res));
			}
			break;
		case Ist_MBE:
			abort();
		case Ist_Exit: {
			unsigned long _branchRip = st->Ist.Exit.dst->Ico.U64;
			if (_branchRip) {
				RegisterAliasingConfiguration bConfig(aliasConfigOnEntryToInstruction(_branchRip));
				RegisterAliasingConfiguration newExitConfig(bConfig);
				newExitConfig |= config;
				if (newExitConfig != bConfig) {
					changed->push_back(_branchRip);
					setAliasConfigOnEntryToInstruction(_branchRip, newExitConfig);
				}
			}
			break;
		}
		default:
			abort();
		}
	}

	std::vector<unsigned long> callees;
	getInstructionCallees(rip, callees, oracle);
	if (!callees.empty())
		config.v[0] = PointerAliasingSet::notAPointer;
	for (std::vector<unsigned long>::iterator it = callees.begin();
	     config.v[0] != PointerAliasingSet::anything && it != callees.end();
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
			if (config.v[i] & PointerAliasingSet::stackPointer)
				stackEscapes = true;
		}
#undef ARG_REGISTERS
		if (stackEscapes)
			config.v[0] = config.v[0] | PointerAliasingSet::stackPointer;
		config.v[0] = config.v[0] | PointerAliasingSet::nonStackPointer;
	}
	std::vector<unsigned long> _fallThroughRips;
	getInstructionFallThroughs(rip, _fallThroughRips);
	for (std::vector<unsigned long>::iterator it = _fallThroughRips.begin();
	     it != _fallThroughRips.end();
	     it++) {
		bool b;
		RegisterAliasingConfiguration succ_config =
			aliasConfigOnEntryToInstruction(*it, &b);
		if (b) {
			RegisterAliasingConfiguration new_config = succ_config;
			new_config |= config;
			if (new_config != succ_config) {
				changed->push_back(*it);
				setAliasConfigOnEntryToInstruction(*it, new_config);
			}
		} else {
			changed->push_back(*it);
			setAliasConfigOnEntryToInstruction(*it, config);
		}
	}
}

void
Oracle::Function::addPredecessorsNonCall(unsigned long rip, std::vector<unsigned long> &out)
{
	static sqlite3_stmt *stmt1, *stmt2;

	if (!stmt1 || !stmt2) {
		assert(!stmt1 && !stmt2);
		stmt1 = prepare_statement("SELECT rip FROM fallThroughRips WHERE dest = ?");
		stmt2 = prepare_statement("SELECT rip FROM branchRips WHERE dest = ?");
	}
	bind_int64(stmt1, 1, rip);
	bind_int64(stmt2, 1, rip);
	extract_int64_column(stmt1, 0, out);
	extract_int64_column(stmt2, 0, out);
}

void
Oracle::Function::addPredecessors(unsigned long rip, std::vector<unsigned long> &out)
{
	static sqlite3_stmt *stmt;

	addPredecessorsNonCall(rip, out);
	if (!stmt)
		stmt = prepare_statement("SELECT rip FROM callRips WHERE dest = ?");
	bind_int64(stmt, 1, rip);
	extract_int64_column(stmt, 0, out);
}

void
Oracle::Function::getInstructionFallThroughs(unsigned long rip, std::vector<unsigned long> &succ)
{
	static sqlite3_stmt *stmt1;

	if (!stmt1)
		stmt1 = prepare_statement("SELECT dest FROM fallThroughRips WHERE rip = ?");
	bind_int64(stmt1, 1, rip);

	succ.clear();
	extract_int64_column(stmt1, 0, succ);
}

void
Oracle::Function::getInstructionsInFunction(std::vector<unsigned long> &succ) const
{
	static sqlite3_stmt *stmt1;

	if (!stmt1)
		stmt1 = prepare_statement("SELECT rip FROM instructionAttributes WHERE functionHead = ?");
	bind_int64(stmt1, 1, rip);

	succ.clear();
	extract_int64_column(stmt1, 0, succ);	
}

void
Oracle::Function::getSuccessors(unsigned long rip, std::vector<unsigned long> &succ)
{
	static sqlite3_stmt *stmt1, *stmt2;

	if (!stmt1 || !stmt2) {
		assert(!stmt1 && !stmt2);
		stmt1 = prepare_statement("SELECT dest FROM fallThroughRips WHERE rip = ?");
		stmt2 = prepare_statement("SELECT dest FROM branchRips WHERE rip = ?");
	}
	bind_int64(stmt1, 1, rip);
	bind_int64(stmt2, 1, rip);

	extract_int64_column(stmt1, 0, succ);
	extract_int64_column(stmt2, 0, succ);
}

void
Oracle::Function::setAliasConfigOnEntryToInstruction(unsigned long r,
						     const RegisterAliasingConfiguration &config)
{
	static sqlite3_stmt *stmt;
	int i;
	int rc;

	if (!stmt)
		stmt = prepare_statement(
			"UPDATE instructionAttributes SET alias0 = ?, alias1 = ?, alias2 = ?, alias3 = ?, alias4 = ?, alias5 = ?, alias6 = ?, alias7 = ?, alias8 = ?, alias9 = ?, alias10 = ?, alias11 = ?, alias12 = ?, alias13 = ?, alias14 = ?, alias15 = ?, stackHasLeaked = ? WHERE rip = ?"
			);
	for (i = 0; i < NR_REGS; i++)
		bind_int64(stmt, i + 1, config.v[i]);
	bind_int64(stmt, NR_REGS + 1, config.stackHasLeaked);
	bind_int64(stmt, NR_REGS + 2, r);
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE);
	sqlite3_reset(stmt);
}

bool
Oracle::Function::addInstruction(unsigned long rip,
				 const std::vector<unsigned long> &callees,
				 const std::vector<unsigned long> &fallThrough,
				 const std::vector<unsigned long> &branch)
{
	sqlite3_stmt *stmt;
	int rc;

	stmt = prepare_statement("INSERT INTO instructionAttributes (rip, functionHead) VALUES (?, ?)");
	bind_int64(stmt, 1, rip);
	bind_int64(stmt, 2, this->rip);
	rc = sqlite3_step(stmt);
	sqlite3_finalize(stmt);
	if (rc == SQLITE_CONSTRAINT) {
		return false;
	}
	assert(rc == SQLITE_DONE);

	stmt = prepare_statement("INSERT INTO fallThroughRips (rip, dest) VALUES (?, ?)");
	for (std::vector<unsigned long>::const_iterator it = fallThrough.begin();
	     it != fallThrough.end();
	     it++) {
		bind_int64(stmt, 1, rip);
		bind_int64(stmt, 2, *it);
		rc = sqlite3_step(stmt);
		assert(rc == SQLITE_DONE);
		rc = sqlite3_reset(stmt);
		assert(rc == SQLITE_OK);
	}
	sqlite3_finalize(stmt);

	stmt = prepare_statement("INSERT INTO branchRips (rip, dest) VALUES (?, ?)");
	for (std::vector<unsigned long>::const_iterator it = branch.begin();
	     it != branch.end();
	     it++) {
		bind_int64(stmt, 1, rip);
		bind_int64(stmt, 2, *it);
		rc = sqlite3_step(stmt);
		assert(rc == SQLITE_DONE);
		rc = sqlite3_reset(stmt);
		assert(rc == SQLITE_OK);
	}
	sqlite3_finalize(stmt);

	stmt = prepare_statement("INSERT INTO callRips (rip, dest) VALUES (?, ?)");
	for (std::vector<unsigned long>::const_iterator it = callees.begin();
	     it != callees.end();
	     it++) {
		bind_int64(stmt, 1, rip);
		bind_int64(stmt, 2, *it);
		rc = sqlite3_step(stmt);
		assert(rc == SQLITE_DONE);
		rc = sqlite3_reset(stmt);
		assert(rc == SQLITE_OK);
	}
	sqlite3_finalize(stmt);

	return true;
}

void
Oracle::Function::getInstructionCallees(unsigned long rip, std::vector<unsigned long> &out, Oracle *oracle)
{
	static sqlite3_stmt *stmt;

	if (!stmt)
		stmt = prepare_statement("SELECT dest FROM callRips WHERE rip = ?");
	bind_int64(stmt, 1, rip);
	extract_int64_column(stmt, 0, out);
}

void
Oracle::Function::getFunctionCallers(std::vector<unsigned long> &out, Oracle *oracle)
{
	static sqlite3_stmt *stmt;

	if (!stmt)
		stmt = prepare_statement("SELECT rip FROM callRips WHERE dest = ?");
	bind_int64(stmt, 1, rip);
	extract_int64_column(stmt, 0, out);
}

void
Oracle::getFunctions(std::vector<unsigned long> &out)
{
	static sqlite3_stmt *stmt;

	if (!stmt)
		stmt = prepare_statement("SELECT DISTINCT functionHead FROM instructionAttributes");
	extract_int64_column(stmt, 0, out);
}

bool
Oracle::Function::registerLivenessCorrect() const
{
	static sqlite3_stmt *stmt;
	if (!stmt)
		stmt = prepare_statement("SELECT registerLivenessCorrect FROM functionAttribs WHERE functionHead = ?");
	bind_int64(stmt, 1, rip);
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
	bind_int64(stmt, 1, rip);
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
	bind_int64(stmt, 1, rip);
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
	bind_int64(stmt, 1, rip);
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
	bind_int64(stmt, 2, rip);
	bind_int64(stmt, 1, x);

	int rc;
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE);
	rc = sqlite3_reset(stmt);
	assert(rc == SQLITE_OK);
}

void
Oracle::getRbpToRspOffset(unsigned long rip, enum RbpToRspOffsetState *state, unsigned long *offset)
{
	static sqlite3_stmt *stmt;
	if (!stmt)
		stmt = prepare_statement("SELECT rbpToRspDeltaState,rbpToRspDelta FROM instructionAttributes WHERE rip = ?");
	bind_int64(stmt, 1, rip);
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
Oracle::setRbpToRspOffset(unsigned long r,
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
	bind_int64(stmt, 3, r);
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
	bind_int64(stmt, 2, rip);
	bind_int64(stmt, 1, x);

	int rc;
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE);
	rc = sqlite3_reset(stmt);
	assert(rc == SQLITE_OK);
}

bool
Oracle::Function::exists() const
{
	static sqlite3_stmt *stmt;
	if (!stmt)
		stmt = prepare_statement("SELECT COUNT(*) FROM instructionAttributes WHERE functionHead = ?");
	bind_int64(stmt, 1, rip);
	std::vector<unsigned long> x;
	extract_int64_column(stmt, 0, x);
	assert(x.size() == 1);
	return x[0] != 0;
}

unsigned long
Oracle::functionHeadForInstruction(unsigned long rip)
{
	__set_profiling(functionHeadForInstruction);
	static sqlite3_stmt *stmt;
	if (!stmt)
		stmt = prepare_statement("SELECT functionHead FROM instructionAttributes WHERE rip = ?");
	bind_int64(stmt, 1, rip);
	std::vector<unsigned long> x;
	extract_int64_column(stmt, 0, x);
	if (x.size() == 0)
		return 0;
	assert(x.size() == 1);
	return x[0];
}

static unsigned
getInstructionSize(AddressSpace *as, unsigned long rip)
{
	IRSB *irsb;
	try {
		irsb = as->getIRSBForAddress(-1, rip);
	} catch (BadMemoryException &e) {
		return 0;
	}
	assert(irsb->stmts[0]->tag == Ist_IMark);
	return irsb->stmts[0]->Ist.IMark.len;
}

/* Find an instruction which is guaranteed to be executed before any
   in @instrs.  Where multiple such instructions exist, we pick the
   latest one (in the sense that there should be no instruction I such
   that I dominates @instrs and also dominates @instrs plus the chosen
   dominator).  If minimum_size is non-zero we further restrict things
   so that we only consider dominating instructions whose size is at
   least minimum_size bytes, or the head instruction in a function. */
unsigned long
Oracle::dominator(const std::set<unsigned long> &instrs,
		  AddressSpace *as,
		  unsigned minimum_size)
{
	__set_profiling(oracle_dominator);
	assert(!instrs.empty());

	/* For now, only handle the case where everything is in the
	 * same function. */
	unsigned long f = 0;
	for (std::set<unsigned long>::iterator it = instrs.begin();
	     it != instrs.end();
	     it++) {
		if (!f)
			f = functionHeadForInstruction(*it);
		else if (f != functionHeadForInstruction(*it)) {
			printf("Can't find dominator for instruction set which crosses functions\n");
			for (it = instrs.begin();
			     it != instrs.end();
			     it++)
				printf("%lx in function %lx\n", f, functionHeadForInstruction(*it));
			return 0;
		}
	}

	if (!f) {
		printf("Eh? can't find function which contains instructions which need to be dominated.\n");
		return 0;
	}

	/* Find the dominator chains for each individual instruction,
	   intersect them, and then take the last one. This is perhaps
	   not the most efficient algorithm imaginable. */
	std::vector<unsigned long> dominators;
	std::set<unsigned long>::iterator it = instrs.begin();
	findDominators(f, *it, as, dominators);
	std::reverse(dominators.begin(), dominators.end());
	dominators.push_back(*it);
	it++;
	while (it != instrs.end()) {
		if (TIMEOUT)
			break;
		std::vector<unsigned long> newDominators;
		findDominators(f, *it, as, newDominators);
		std::reverse(newDominators.begin(), newDominators.end());
		newDominators.push_back(*it);
		for (unsigned x = 0;
		     x < dominators.size() && x < newDominators.size();
		     x++) {
			if (dominators[x] != newDominators[x])
				dominators.resize(x);
		}
		it++;
	}

	/* The dominator list should at least contain the head of the
	 * function, unless we timed out. */
	if (dominators.empty()) {
		printf("Dominator set empty!\n");
		return 0;
	}

	/* Eliminate excessively small instructions. */
	unsigned x;
	for (x = dominators.size() - 1; minimum_size != 0 && x > 0; x--)
		if (getInstructionSize(as, dominators[x]) >= minimum_size)
			break;
	return dominators[x];
}

bool
Oracle::getRbpToRspDelta(unsigned long rip, long *out)
{
	RbpToRspOffsetState state;
	unsigned long o;
	getRbpToRspOffset(rip, &state, &o);
	if (state == RbpToRspOffsetStateValid) {
		*out = o;
		return true;
	} else {
		return false;
	}
}

Oracle::LivenessSet
Oracle::liveOnEntryToFunction(unsigned long rip)
{
	Function f(rip);
	return f.liveOnEntry(rip, true);
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
