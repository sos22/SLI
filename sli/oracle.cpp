#include <err.h>
#include <stdlib.h>

#include <map>
#include <queue>

#include <sqlite3.h>

#include "sli.h"
#include "oracle.hpp"
#include "simplify_irexpr.hpp"

static bool
operator<(const InstructionSet &a, const InstructionSet &b)
{
	return a.rips < b.rips;
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

const Oracle::PointerAliasingSet Oracle::PointerAliasingSet::notAPointer(1);
const Oracle::PointerAliasingSet Oracle::PointerAliasingSet::stackPointer(2);
const Oracle::PointerAliasingSet Oracle::PointerAliasingSet::nonStackPointer(4);
const Oracle::PointerAliasingSet Oracle::PointerAliasingSet::anything(7);

Oracle::RegisterAliasingConfiguration Oracle::RegisterAliasingConfiguration::functionEntryConfiguration(5.3f);
Oracle::RegisterAliasingConfiguration::RegisterAliasingConfiguration(float f)
{
	stackHasLeaked = false;
	v[1] = Oracle::PointerAliasingSet::notAPointer | Oracle::PointerAliasingSet::nonStackPointer; /* rcx */
	v[2] = Oracle::PointerAliasingSet::notAPointer | Oracle::PointerAliasingSet::nonStackPointer; /* rdx */
	v[4] = Oracle::PointerAliasingSet::stackPointer; /* rsp */
	v[6] = Oracle::PointerAliasingSet::notAPointer | Oracle::PointerAliasingSet::nonStackPointer; /* rsi */
	v[7] = Oracle::PointerAliasingSet::notAPointer | Oracle::PointerAliasingSet::nonStackPointer; /* rdi */
	v[8] = Oracle::PointerAliasingSet::notAPointer | Oracle::PointerAliasingSet::nonStackPointer; /* r8 */
	v[9] = Oracle::PointerAliasingSet::notAPointer | Oracle::PointerAliasingSet::nonStackPointer; /* r9 */
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
		if (it->loads.count(smsel->rip))
			out |= it->stores;
	}
}

/* Try to guess whether this store might ever be consumed by another
   thread.  We approximate this by saying that anything not included
   in our database of dynamic information is thread-local. */
bool
Oracle::storeIsThreadLocal(StateMachineSideEffectStore *s)
{
	static std::set<unsigned long> threadLocal;
	static std::set<unsigned long> notThreadLocal;
	if (threadLocal.count(s->rip))
		return true;
	if (notThreadLocal.count(s->rip))
		return false;
	for (std::vector<tag_entry>::iterator it = tag_table.begin();
	     it != tag_table.end();
	     it++)
		if (it->stores.count(s->rip)) {
			notThreadLocal.insert(s->rip);
			return false;
		}
	threadLocal.insert(s->rip);
	return true;
}
bool
Oracle::loadIsThreadLocal(StateMachineSideEffectLoad *s)
{
	static std::set<unsigned long> threadLocal;
	static std::set<unsigned long> notThreadLocal;
	if (threadLocal.count(s->rip))
		return true;
	if (notThreadLocal.count(s->rip))
		return false;
	for (std::vector<tag_entry>::iterator it = tag_table.begin();
	     it != tag_table.end();
	     it++)
		if (it->loads.count(s->rip)) {
			notThreadLocal.insert(s->rip);
			return false;
		}
	threadLocal.insert(s->rip);
	return true;
}

unsigned long
Oracle::selectRandomLoad() const
{
	std::set<unsigned long> allRelevantLoads;
	unsigned idx;
	
	for (std::vector<tag_entry>::const_iterator it = tag_table.begin();
	     it != tag_table.end();
	     it++)
		if (it->stores.size() != 0) {
			for (std::set<unsigned long>::iterator it2 =
				     it->loads.begin();
			     it2 != it->loads.end();
			     it2++)
				allRelevantLoads.insert(*it2);
		}
	idx = random() % allRelevantLoads.size();
	std::set<unsigned long>::iterator it = allRelevantLoads.begin();
	while (idx) {
		assert(it != allRelevantLoads.end());
		it++;
		idx--;
	}
	return *it;
}

bool
Oracle::memoryAccessesMightAlias(StateMachineSideEffectLoad *smsel,
				 StateMachineSideEffectStore *smses)
{
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
		if (!definitelyNotEqual(smsel->smsel_addr, smses->addr, AllowableOptimisations::defaultOptimisations))
			return true;
		else
			return false;
	}

	unsigned long h = hashRipPair(smses->rip, smsel->rip);
	nr_queries++;
	if (!(memoryAliasingFilter[h/64] & (1ul << (h % 64)))) {
		nr_bloom_hits++;
		return false;
	}
	h = hashRipPair(smses->rip * 23, smsel->rip * 17);
	if (!(memoryAliasingFilter2[h/64] & (1ul << (h % 64)))) {
		nr_bloom_hits2++;
		return false;
	}
	for (std::vector<tag_entry>::iterator it = tag_table.begin();
	     it != tag_table.end();
	     it++)
		if (it->loads.count(smsel->rip) &&
		    it->stores.count(smses->rip)) {
			nr_trues++;
			return true;
		}
	nr_falses++;
	return false;
}

bool
Oracle::memoryAccessesMightAlias(StateMachineSideEffectLoad *smsel1,
				 StateMachineSideEffectLoad *smsel2)
{
	if (loadIsThreadLocal(smsel1)) {
		if (!loadIsThreadLocal(smsel2))
			return false;
		if (!definitelyNotEqual(smsel1->smsel_addr, smsel2->smsel_addr, AllowableOptimisations::defaultOptimisations))
			return true;
		else
			return false;
	} else if (loadIsThreadLocal(smsel2))
		return false;

	for (std::vector<tag_entry>::iterator it = tag_table.begin();
	     it != tag_table.end();
	     it++)
		if (it->loads.count(smsel1->rip) &&
		    it->loads.count(smsel2->rip))
			return true;
	return false;
}

bool
Oracle::memoryAccessesMightAlias(StateMachineSideEffectStore *smses1,
				 StateMachineSideEffectStore *smses2)
{
	if (storeIsThreadLocal(smses1) && storeIsThreadLocal(smses2)) {
		if (!definitelyNotEqual(smses2->addr, smses1->addr, AllowableOptimisations::defaultOptimisations))
			return true;
		else
			return false;
	}
	for (std::vector<tag_entry>::iterator it = tag_table.begin();
	     it != tag_table.end();
	     it++)
		if (it->loads.count(smses1->rip) &&
		    it->stores.count(smses2->rip))
			return true;
	return false;
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
		directExits.push_back(extract_call_follower(irsb));
		/* Emit the target as well, if possible. */
		if (irsb->next->tag == Iex_Const)
			callees->set(std::pair<unsigned long, unsigned long>(rip, irsb->next->Iex.Const.con->Ico.U64),
				     true);
		return;
	}

	if (irsb->jumpkind != Ijk_NoDecode &&
	    irsb->next->tag == Iex_Const) {
		directExits.push_back(irsb->next->Iex.Const.con->Ico.U64);
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
			for (std::set<unsigned long>::iterator it2 = t.loads.begin();
			     it2 != t.loads.end();
			     it2++) {
				unsigned long h = hashRipPair(*it1, *it2);
				memoryAliasingFilter[h / 64] |= 1ul << (h % 64);
				h = hashRipPair(*it1 * 23, *it2 * 17);
				memoryAliasingFilter2[h / 64] |= 1ul << (h % 64);
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
Oracle::calculateRegisterLiveness(VexPtr<Oracle> &ths, GarbageCollectionToken token)
{
	bool done_something;
	unsigned long changed;
	unsigned long unchanged;
	std::vector<unsigned long> functions;

	do {
		LibVEX_maybe_gc(token);
		changed = 0;
		unchanged = 0;
		done_something = false;
		ths->getFunctions(functions);
		for (std::vector<unsigned long>::iterator it = functions.begin();
		     it != functions.end();
		     it++) {
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
Oracle::calculateAliasing()
{
	bool done_something;
	std::vector<unsigned long> functions;

	getFunctions(functions);
	for (std::vector<unsigned long>::iterator it = functions.begin();
	     it != functions.end();
	     it++) {
		do {
			done_something = false;
			Function f(*it);
			f.calculateAliasing(ms->addressSpace, &done_something, this);
		} while (done_something);
	}
}

static Oracle::LivenessSet
irexprUsedValues(Oracle::LivenessSet old, IRExpr *w)
{
	if (!w)
		return old;
	switch (w->tag) {
	case Iex_Binder:
		return old;
	case Iex_Get:
		return old.use(w->Iex.Get.offset);
	case Iex_GetI:
		return Oracle::LivenessSet::everything;
	case Iex_RdTmp:
		return old;
	case Iex_Qop:
		old = irexprUsedValues(old, w->Iex.Qop.arg4);
	case Iex_Triop:
		old = irexprUsedValues(old, w->Iex.Qop.arg3);
	case Iex_Binop:
		old = irexprUsedValues(old, w->Iex.Qop.arg2);
	case Iex_Unop:
		return irexprUsedValues(old, w->Iex.Qop.arg1);
	case Iex_Load:
		return irexprUsedValues(old, w->Iex.Load.addr);
	case Iex_Const:
		return old;
	case Iex_CCall:
		for (int i = 0; w->Iex.CCall.args[i]; i++)
			old = irexprUsedValues(old, w->Iex.CCall.args[i]);
		return old;
	case Iex_Mux0X:
		old = irexprUsedValues(old, w->Iex.Mux0X.cond);
		old = irexprUsedValues(old, w->Iex.Mux0X.expr0);
		old = irexprUsedValues(old, w->Iex.Mux0X.exprX);
		return old;
	case Iex_Associative:
		for (int i = 0; i < w->Iex.Associative.nr_arguments; i++)
			old = irexprUsedValues(old, w->Iex.Associative.contents[i]);
		return old;
	case Iex_FreeVariable:
		return old;
	}
	abort();
}

static bool
operator >(const Oracle::LivenessSet &a, const Oracle::LivenessSet &b)
{
	return a.mask != b.mask && (b.mask & ~a.mask) == 0;
}

static Oracle::PointerAliasingSet
irexprAliasingClass(IRExpr *expr,
		    IRTypeEnv *tyenv,
		    const Oracle::RegisterAliasingConfiguration &config,
		    std::map<IRTemp, Oracle::PointerAliasingSet> *temps)
{
	if (tyenv && typeOfIRExpr(tyenv, expr) != Ity_I64)
		/* Not a 64 bit value -> not a pointer */
		return Oracle::PointerAliasingSet::notAPointer;

	switch (expr->tag) {
	case Iex_Get:
		if (expr->Iex.Get.offset < Oracle::NR_REGS * 8)
			return config.v[expr->Iex.Get.offset / 8];
		else {
			/* Assume that those are the only pointer registers */
			return Oracle::PointerAliasingSet::notAPointer;
		}
	case Iex_Binder:
		/* Binders are loaded from memory, and we only track
		 * registers. */
		/* Hackety hackety hack */
		return Oracle::PointerAliasingSet::anything;
	case Iex_RdTmp:
		assert(temps);
		return (*temps)[expr->Iex.RdTmp.tmp];
	case Iex_Const:
		return Oracle::PointerAliasingSet::notAPointer | Oracle::PointerAliasingSet::nonStackPointer;
	case Iex_Unop:
		switch (expr->Iex.Unop.op) {
		case Iop_8Uto64:
		case Iop_8Sto64:
		case Iop_16Uto64:
		case Iop_16Sto64:
		case Iop_32Uto64:
		case Iop_32Sto64:
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
		Oracle::PointerAliasingSet a1 = irexprAliasingClass(
			expr->Iex.Binop.arg1,
			tyenv,
			config,
			temps);
		Oracle::PointerAliasingSet a2 = irexprAliasingClass(
			expr->Iex.Binop.arg2,
			tyenv,
			config,
			temps);
		switch (expr->Iex.Binop.op) {
		case Iop_Sub64:
			/* x - y is a pointer to zone A if x is a
			 * pointer to zone A and y is not a pointer of
			 * any sort.  Otherwise, it's just not a
			 * pointer. */ {
			Oracle::PointerAliasingSet res;
			if (a2 & Oracle::PointerAliasingSet::notAPointer) {
				res = a1;
				if (a2 & (Oracle::PointerAliasingSet::stackPointer |
					  Oracle::PointerAliasingSet::nonStackPointer))
					res = res | Oracle::PointerAliasingSet::notAPointer;
			} else {
				res = Oracle::PointerAliasingSet::notAPointer;
			}
			return res;
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
			return Oracle::PointerAliasingSet::notAPointer;
		default:
			break;
		}
		break;
	}
	case Iex_Mux0X:
		return irexprAliasingClass(expr->Iex.Mux0X.expr0,
					   tyenv,
					   config,
					   temps) |
			irexprAliasingClass(expr->Iex.Mux0X.exprX,
					    tyenv,
					    config,
					    temps);
	case Iex_Associative:
		switch (expr->Iex.Associative.op) {
		case Iop_Add64:
		case Iop_And64:
		{
			Oracle::PointerAliasingSet res;
			for (int i = 0; i < expr->Iex.Associative.nr_arguments; i++) {
				if (expr->Iex.Associative.contents[i]->tag != Iex_Const)
					res = res | irexprAliasingClass(expr->Iex.Associative.contents[i],
									tyenv,
									config,
									temps);
			}
			if (!(res & Oracle::PointerAliasingSet::anything))
				res = Oracle::PointerAliasingSet::notAPointer;
			return res;
		}
		default:
			break;
		}
		break;

	case Iex_CCall:
		if (!strcmp(expr->Iex.CCall.cee->name, "amd64g_calculate_rflags_c") ||
		    !strcmp(expr->Iex.CCall.cee->name, "amd64g_calculate_rflags_all"))
			return Oracle::PointerAliasingSet::notAPointer;
		break;

	case Iex_FreeVariable:
		return Oracle::PointerAliasingSet::anything;

	default:
		break;
	}
	printf("Don't know how to compute aliasing sets for ");
	ppIRExpr(expr, stdout);
	printf("\n");
	return Oracle::PointerAliasingSet::anything;
}

bool
Oracle::RegisterAliasingConfiguration::mightAlias(IRExpr *a, IRExpr *b) const
{
	return irexprAliasingClass(a, NULL, *this, NULL) &
		irexprAliasingClass(b, NULL, *this, NULL);
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

	std::sort(roots.begin(), roots.end());
	std::unique(roots.begin(), roots.end());
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
		printf("No function for %lx\n", rip);
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

	assert(predecessors.count(rip));
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
		return _database;
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
	rc = sqlite3_exec(_database, "CREATE TABLE functionAttribs (functionHead INTEGER PRIMARY KEY, registerLivenessCorrect INTEGER NOT NULL, aliasingCorrect INTEGER NOT NULL)",
			  NULL, NULL, NULL);
	assert(rc == SQLITE_OK);

	/* All of the information in the database can be regenerated
	   by just blowing it away and starting over, so there's not
	   much point in doing lots of journaling and fsync()
	   operations. */
	rc = sqlite3_exec(_database, "PRAGMA journal_mode = OFF", NULL, NULL, NULL);
	assert(rc == SQLITE_OK);
	rc = sqlite3_exec(_database, "PRAGMA synchronous = OFF", NULL, NULL, NULL);
	assert(rc == SQLITE_OK);

	create_index("instructionAttributesFunctionHead", "instructionAttributes", "functionHead");

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
	ths->calculateAliasing();
}

Oracle::LivenessSet
Oracle::Function::liveOnEntry(unsigned long rip)
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
		return Oracle::LivenessSet();
	}
	unsigned long r;
	r = sqlite3_column_int64(stmt, 0);
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE);
	sqlite3_reset(stmt);
	return LivenessSet(r);
}

Oracle::LivenessSet
Oracle::Function::liveOnEntry()
{
	return liveOnEntry(rip);
}

Oracle::RegisterAliasingConfiguration
Oracle::Function::aliasConfigOnEntryToInstruction(unsigned long rip)
{
	static sqlite3_stmt *stmt;
	int rc;

	if (!stmt)
		stmt = prepare_statement(
			"SELECT alias0, alias1, alias2, alias3, alias4, alias5, alias6, alias7, alias8, alias9, alias10, alias11, alias12, alias13, alias14, alias15 FROM instructionAttributes WHERE rip = ?");
	bind_int64(stmt, 1, rip);
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE || rc == SQLITE_ROW);
	if (rc == SQLITE_DONE || sqlite3_column_type(stmt, 0) == SQLITE_NULL) {
		sqlite3_reset(stmt);
		return RegisterAliasingConfiguration::unknown;
	}
	RegisterAliasingConfiguration rac;
	int i;
	for (i = 0; i < NR_REGS; i++) {
		unsigned long r;
		assert(sqlite3_column_type(stmt, i) == SQLITE_INTEGER);
		r = sqlite3_column_int64(stmt, i);
		rac.v[r] = PointerAliasingSet(r);
	}
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE);
	sqlite3_reset(stmt);
	return rac;
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
					fallThrough.push_back(extract_call_follower(irsb));
					if (irsb->next->tag == Iex_Const)
						callees.push_back(irsb->next->Iex.Const.con->Ico.U64);
					else
						findPossibleJumpTargets(rip, callees);
				} else {
					if (irsb->next->tag == Iex_Const)
						fallThrough.push_back(irsb->next->Iex.Const.con->Ico.U64);
					else if (irsb->jumpkind != Ijk_Ret)
						findPossibleJumpTargets(rip, fallThrough);
				}
			} else {
				fallThrough.push_back(irsb->stmts[end_of_instruction]->Ist.IMark.addr);
			}

			heads.insert(heads.end(), callees.begin(), callees.end());
			unexplored.insert(unexplored.end(), fallThrough.begin(), fallThrough.end());
			unexplored.insert(unexplored.end(), branch.begin(), branch.end());

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

	RegisterAliasingConfiguration a(aliasConfigOnEntryToInstruction(rip));
	RegisterAliasingConfiguration b(a);
	b |= RegisterAliasingConfiguration::functionEntryConfiguration;
	if (a != b) {
		*done_something = true;
		setAliasConfigOnEntryToInstruction(rip, b);
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
Oracle::Function::updateLiveOnEntry(unsigned long rip, AddressSpace *as, bool *changed, Oracle *oracle)
{
	LivenessSet res;

	std::vector<unsigned long> fallThroughRips;
	getInstructionFallThroughs(rip, fallThroughRips);
	for (std::vector<unsigned long>::iterator it = fallThroughRips.begin();
	     it != fallThroughRips.end();
	     it++)
		res |= liveOnEntry(*it);
	std::vector<unsigned long> callees;
	getInstructionCallees(rip, callees, oracle);
	for (std::vector<unsigned long>::iterator it = callees.begin();
	     it != callees.end();
	     it++) {
		Function f(*it);
		res |= f.liveOnEntry(*it) & LivenessSet::argRegisters;
	}
	IRSB *irsb = as->getIRSBForAddress(-1, rip);
	IRStmt **statements = irsb->stmts;
	int nr_statements;
	for (nr_statements = 1;
	     nr_statements < irsb->stmts_used && statements[nr_statements]->tag != Ist_IMark;
	     nr_statements++)
		;

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
				res |= liveOnEntry(_branchRip);
			res = irexprUsedValues(res, statements[i]->Ist.Exit.guard);
			break;
		}
		default:
			abort();
		}
	}

	if (res != liveOnEntry(rip)) {
		assert(res > liveOnEntry(rip));
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

void
Oracle::Function::updateSuccessorInstructionsAliasing(unsigned long rip, AddressSpace *as, std::vector<unsigned long> *changed,
						      Oracle *oracle)
{
	RegisterAliasingConfiguration config(aliasConfigOnEntryToInstruction(rip));
	std::map<IRTemp, PointerAliasingSet> temporaryAliases;
	IRStmt *st;

	int nr_statements;
	IRSB *irsb = as->getIRSBForAddress(-1, rip);
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
							    &temporaryAliases);
			}
			break;
		case Ist_PutI:
			/* Assume that PutIs never target the NR_REGS registers */
			break;
		case Ist_WrTmp:
			temporaryAliases[st->Ist.WrTmp.tmp] =
				irexprAliasingClass(st->Ist.WrTmp.data,
						    tyenv,
						    config,
						    &temporaryAliases);
			break;
		case Ist_Store:
			if (!config.stackHasLeaked) {
				PointerAliasingSet addr, data;
				addr = irexprAliasingClass(st->Ist.Store.data,
							   tyenv,
							   config,
							   &temporaryAliases);
				data = irexprAliasingClass(st->Ist.Store.data,
							   tyenv,
							   config,
							   &temporaryAliases);
				if ((addr & PointerAliasingSet::nonStackPointer) &&
				    (data & PointerAliasingSet::stackPointer))
					config.stackHasLeaked = true;
			}
			break;
		case Ist_CAS:
			temporaryAliases[st->Ist.CAS.details->oldLo] =
				PointerAliasingSet::anything;
			break;
		case Ist_Dirty: {
			PointerAliasingSet res;
			if (tyenv->types[st->Ist.Dirty.details->tmp] == Ity_I64) {
				if (!strcmp(st->Ist.Dirty.details->cee->name,
					    "helper_load_64")) {
					if (config.stackHasLeaked)
						res = PointerAliasingSet::anything;
					else
						res = PointerAliasingSet::notAPointer |
							PointerAliasingSet::nonStackPointer;
				} else {
					res = PointerAliasingSet::anything;
				}
			} else {
				res = PointerAliasingSet::notAPointer;
			}
			temporaryAliases[st->Ist.Dirty.details->tmp] = res;
			break;
		}
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
		LivenessSet ls = (Function(*it)).liveOnEntry(*it);
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
	     it++)
		config |= aliasConfigOnEntryToInstruction(*it);
	for (std::vector<unsigned long>::iterator it = _fallThroughRips.begin();
	     it != _fallThroughRips.end();
	     it++) {
		if (config != aliasConfigOnEntryToInstruction(*it)) {
			changed->push_back(*it);
			setAliasConfigOnEntryToInstruction(*it, config);
		}
	}
}

void
Oracle::Function::addPredecessors(unsigned long rip, std::vector<unsigned long> &out)
{
	static sqlite3_stmt *stmt1, *stmt2, *stmt3;

	if (!stmt1 || !stmt2 || !stmt3) {
		assert(!stmt1 && !stmt2 && !stmt3);
		stmt1 = prepare_statement("SELECT rip FROM fallThroughRips WHERE dest = ?");
		stmt2 = prepare_statement("SELECT rip FROM branchRips WHERE dest = ?");
		stmt3 = prepare_statement("SELECT rip FROM callRips WHERE dest = ?");
	}
	bind_int64(stmt1, 1, rip);
	bind_int64(stmt2, 1, rip);
	bind_int64(stmt3, 1, rip);
	extract_int64_column(stmt1, 0, out);
	extract_int64_column(stmt2, 0, out);
	extract_int64_column(stmt3, 0, out);
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
			"UPDATE instructionAttributes SET alias0 = ?, alias1 = ?, alias2 = ?, alias3 = ?, alias4 = ?, alias5 = ?, alias6 = ?, alias7 = ?, alias8 = ?, alias9 = ?, alias10 = ?, alias11 = ?, alias12 = ?, alias13 = ?, alias14 = ?, alias15 = ? WHERE rip = ?"
			);
	for (i = 0; i < NR_REGS; i++)
		sqlite3_bind_int64(stmt, i, config.v[i]);
	sqlite3_bind_int64(stmt, NR_REGS, r);
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
		stmt = prepare_statement("INSERT OR REPLACE INTO functionAttribs (functionHead, registerLivenessCorrect, aliasingCorrect) VALUES (?, ?, 0)");
	bind_int64(stmt, 1, rip);
	bind_int64(stmt, 2, x);

	int rc;
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE);
	rc = sqlite3_reset(stmt);
	assert(rc == SQLITE_OK);
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
	assert(!instrs.empty());

	/* For now, only handle the case where everything is in the
	 * same function. */
	unsigned long f = 0;
	for (std::set<unsigned long>::iterator it = instrs.begin();
	     it != instrs.end();
	     it++) {
		if (!f)
			f = functionHeadForInstruction(*it);
		else
			assert(f == functionHeadForInstruction(*it));
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
	 * function. */
	assert(!dominators.empty());

	/* Eliminate excessively small instructions. */
	unsigned x;
	for (x = dominators.size() - 1; minimum_size != 0 && x > 0; x--)
		if (getInstructionSize(as, dominators[x]) >= minimum_size)
			break;
	return dominators[x];
}
