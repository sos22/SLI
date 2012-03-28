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

#include "libvex_prof.hpp"
#include "libvex_parse.h"

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

#if 0
void
mergeUlongSets(gc_pair_ulong_set_t *dest, const gc_pair_ulong_set_t *src)
{
	for (gc_pair_ulong_set_t::iterator it = src->begin();
	     it != src->end();
	     it++)
		dest->set(it.key(), it.value());
}
#endif

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
Oracle::getIRSBForRip(AddressSpace *as, const StaticRip &sr)
{
	return getIRSBForRip(as, VexRip::invent_vex_rip(sr.rip));
}

IRSB *
Oracle::getIRSBForRip(AddressSpace *as, const VexRip &sr)
{
	try {
		return as->getIRSBForAddress(ThreadRip::mk(STATIC_THREAD, sr));
	} catch (BadMemoryException e) {
		return NULL;
	}
}

IRSB *
Oracle::getIRSBForRip(const VexRip &vr)
{
	return getIRSBForRip(ms->addressSpace, vr);
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
Oracle::findPreviousInstructions(std::vector<VexRip> &out)
{
	std::vector<VexRip> fheads;
	getDominators(crashedThread, ms, out, fheads);
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

struct tag_hdr {
	int nr_loads;
	int nr_stores;
};

struct vexrip_hdr {
	unsigned long rip;
	unsigned nr_entries;
};
static bool
read_vexrip(VexRip *out, const Mapping &mapping, AddressSpace *as, unsigned long offset, bool *is_private, unsigned long *sz)
{
	const struct vexrip_hdr *hdr = mapping.get<vexrip_hdr>(offset);
	if (!hdr)
		err(1, "reading vexrip header");

	/* sizeof(vexrip_hdr) would be 12 if we'd properly packed
	 * vexrip_hdr. :( */
	*sz = 12 + sizeof(unsigned long) * hdr->nr_entries;

	unsigned long rip = hdr->rip;
	if (rip & (1ul << 63)) {
		*is_private = true;
		rip &= ~(1ul << 63);
	} else {
		*is_private = false;
	}
	assert(as->isReadable(rip, 1));

	const unsigned long *body = mapping.get<unsigned long>(offset + 12, hdr->nr_entries);
	std::vector<unsigned long> stack;
	stack.reserve(hdr->nr_entries+1);
	for (unsigned x = 0; x < hdr->nr_entries; x++) {
		assert(as->isReadable(body[x], 1));
		stack.push_back(body[x]);
	}
	stack.push_back(rip);
	*out = VexRip(stack);
	return true;
}

enum read_vexrip_res {
	read_vexrip_take,
	read_vexrip_skip,
	read_vexrip_error
};

static read_vexrip_res
read_vexrip(FILE *f, VexRip *out, AddressSpace *as, bool *is_private)
{
       unsigned long rip;
       unsigned nr_entries;
       std::vector<unsigned long> stack;

       if (fread(&rip, sizeof(rip), 1, f) != 1 ||
           fread(&nr_entries, sizeof(nr_entries), 1, f) != 1)
               return read_vexrip_error;
       stack.reserve(nr_entries);
       for (unsigned x = 0; x < nr_entries; x++) {
               unsigned long a;
               if (fread(&a, sizeof(a), 1, f) != 1)
                       return read_vexrip_error;
	       if (as->isReadable(a, 1))
		       stack.push_back(a);
       }
       if (rip & (1ul << 63)) {
               *is_private = true;
               rip &= ~(1ul << 63);
       } else {
               *is_private = false;
       }
       read_vexrip_res res;
       if (as->isReadable(rip, 1)) {
	       stack.push_back(rip);
	       res = read_vexrip_take;
       } else {
	       res = read_vexrip_skip;
       }
       *out = VexRip(stack);
       return res;
}

unsigned long
Oracle::fetchTagEntry(tag_entry *te, const Mapping &mapping, unsigned long offset, AddressSpace *as)
{
	const struct tag_hdr *hdr = mapping.get<tag_hdr>(offset);
	if (!hdr)
		return 0;
	unsigned long sz = sizeof(*hdr);
	struct {
		void operator()(int nr_items, const Mapping &mapping,
				unsigned long offset, unsigned long *sz,
				AddressSpace *as,
				std::set<VexRip> &private_set,
				std::set<VexRip> &shared_set) {
			for (int x = 0; x < nr_items; x++) {
				VexRip buf;
				bool is_private;
				unsigned long s;
				bool use_it;
				use_it = read_vexrip(&buf, mapping, as, offset + *sz, &is_private, &s);
				*sz += s;
				if (use_it) {
					if (is_private)
						private_set.insert(buf);
					else
						shared_set.insert(buf);
				}
			}
		}
	} doit;

	doit(hdr->nr_loads, mapping, offset, &sz, as, te->private_loads, te->shared_loads);
	doit(hdr->nr_stores, mapping, offset, &sz, as, te->private_stores, te->shared_stores);

	return sz;
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
			      std::set<VexRip> &out)
{
	std::vector<unsigned long> offsets;
	type_index->findOffsets(smsel->rip.rip, offsets);
	for (auto it = offsets.begin();
	     it != offsets.end();
	     it++) {
		tag_entry te;
		fetchTagEntry(&te, raw_types_database, *it, ms->addressSpace);
		if (te.shared_loads.count(smsel->rip.rip))
			out |= te.shared_stores;
	}
}

bool
Oracle::notInTagTable(StateMachineSideEffectMemoryAccess *access)
{
	__set_profiling(notInTagTable);
	std::vector<unsigned long> offsets;
	type_index->findOffsets(access->rip.rip, offsets);
	return offsets.size() == 0;
}

bool
Oracle::hasConflictingRemoteStores(StateMachineSideEffectMemoryAccess *access)
{
	__set_profiling(hasConflictingRemoteStores);
	std::vector<unsigned long> offsets;
	type_index->findOffsets(access->rip.rip, offsets);
	for (auto it = offsets.begin(); it != offsets.end(); it++) {
		unsigned long offset = *it;
		const struct tag_hdr *hdr = raw_types_database.get<tag_hdr>(offset);
		if (!hdr)
			abort();
		if (hdr->nr_stores == 0)
			continue;

		/* We want to return true if the entry contains *any*
		   shared stores at all and the access matches with
		   either the shared store set or the shared load set.
		   Ideally, you'd check whether you have shared stores
		   first and then go and check the load set
		   afterwards, but the file format means that you have
		   to parse the load set first.  Meh. */
		bool relevant_load = false;
		offset += sizeof(*hdr);
		for (int x = 0; x < hdr->nr_loads; x++) {
			VexRip buf;
			bool is_private;
			unsigned long s;
			bool use_it = read_vexrip(&buf, raw_types_database, ms->addressSpace, offset, &is_private, &s);
			offset += s;
			if (use_it && !is_private && buf == access->rip.rip) {
				/* You might think that we should
				   break out of the loop here.  Not
				   so: we need to parse all of the
				   loads to find the start of the
				   store set. */
				relevant_load = true;
			}
		}
		for (int x = 0; x < hdr->nr_stores; x++) {
			VexRip buf;
			bool is_private;
			unsigned long s;
			bool use_it = read_vexrip(&buf, raw_types_database, ms->addressSpace, offset, &is_private, &s);
			offset += s;
			if (use_it && !is_private &&
			    (relevant_load || buf == access->rip.rip))
				return true;
		}
	}
	return false;
}

bool
Oracle::memoryAccessesMightAlias(const AllowableOptimisations &opt,
				 StateMachineSideEffectLoad *smsel,
				 StateMachineSideEffectStore *smses)
{
	__set_profiling(might_alias_load_store);
	std::vector<unsigned long> offsets;
	type_index->findOffsets(smses->rip.rip, offsets);
	if (offsets.size() == 0) {
		if (!notInTagTable(smsel))
			return false;
		if (!definitelyNotEqual(smsel->addr, smses->addr, opt))
                        return true;
		else
			return false;
	} else if (notInTagTable(smsel))
		return false;

	static QueryCache<StateMachineSideEffectLoad, StateMachineSideEffectStore, bool> cache(__func__);
	int idx = cache.hash(smsel, smses);
	bool res;
	if (cache.query(smsel, smses, idx, &res))
		return res;

	for (auto it = offsets.begin(); it != offsets.end(); it++) {
		unsigned long offset = *it;
		const struct tag_hdr *hdr = raw_types_database.get<tag_hdr>(offset);
		assert(hdr);
		unsigned long sz = sizeof(*hdr);
		struct {
			bool operator()(int nr_items,
					const VexRip &desiredRip,
					const Mapping &mapping,
					unsigned long offset,
					unsigned long *sz,
					AddressSpace *as)
			{
				for (int x = 0; x < nr_items; x++) {
					VexRip buf;
					bool is_private;
					unsigned long s;
					bool use_it;
					use_it = read_vexrip(&buf, mapping, as, offset + *sz, &is_private, &s);
					*sz += s;
					if (use_it && buf == desiredRip)
						return true;
				}
				return false;
			}
		} doit;

		if (doit(hdr->nr_loads, smsel->rip.rip, raw_types_database, offset, &sz, ms->addressSpace) ||
		    doit(hdr->nr_stores, smses->rip.rip, raw_types_database, offset, &sz, ms->addressSpace)) {
			cache.set(smsel, smses, idx, true);
			return true;
		}
	}
	cache.set(smsel, smses, idx, false);
	return false;
}

bool
Oracle::memoryAccessesMightAlias(const AllowableOptimisations &opt,
				 StateMachineSideEffectLoad *smsel1,
				 StateMachineSideEffectLoad *smsel2)
{
	__set_profiling(memory_accesses_might_alias_load_load);
	std::vector<unsigned long> offsets;
	type_index->findOffsets(smsel1->rip.rip, offsets);
	if (offsets.size() == 0) {
		if (!notInTagTable(smsel2))
			return false;
		if (!definitelyNotEqual(smsel1->addr, smsel2->addr, opt))
			return true;
		else
			return false;
	} else if (notInTagTable(smsel2))
		return false;

	for (auto it = offsets.begin(); it != offsets.end(); it++) {
		tag_entry te;
		fetchTagEntry(&te, raw_types_database, *it, ms->addressSpace);
		if ((te.shared_loads.count(smsel2->rip.rip) ||
		     te.private_loads.count(smsel2->rip.rip)) &&
		    (te.shared_loads.count(smsel1->rip.rip) ||
		     te.private_loads.count(smsel1->rip.rip)))
			return true;
	}
	return false;
}

bool
Oracle::memoryAccessesMightAlias(const AllowableOptimisations &opt,
				 StateMachineSideEffectStore *smses1,
				 StateMachineSideEffectStore *smses2)
{
	__set_profiling(memory_accesses_might_alias_store_store);
	std::vector<unsigned long> offsets;
	type_index->findOffsets(smses1->rip.rip, offsets);
	if (offsets.size() == 0) {
		if (!notInTagTable(smses2))
			return false;
		if (!definitelyNotEqual(smses2->addr, smses1->addr, opt))
			return true;
		else
			return false;
	} else if (notInTagTable(smses2))
		return false;

	for (auto it = offsets.begin(); it != offsets.end(); it++) {
		tag_entry te;
		fetchTagEntry(&te, raw_types_database, *it, ms->addressSpace);
		if ((te.shared_stores.count(smses2->rip.rip) ||
		     te.private_stores.count(smses2->rip.rip)) &&
		    (te.shared_stores.count(smses1->rip.rip) ||
		     te.private_stores.count(smses1->rip.rip)))
			return true;
	}
	return false;
}

void
Oracle::findRacingRips(const AllowableOptimisations &opt, StateMachineSideEffectLoad *smsel, std::set<VexRip> &out)
{
	findConflictingStores(smsel, out);
}

void
Oracle::findRacingRips(StateMachineSideEffectStore *smses, std::set<VexRip> &out)
{
	__set_profiling(findRacingRips__store);
	std::vector<unsigned long> offsets;
	type_index->findOffsets(smses->rip.rip, offsets);
	for (auto it = offsets.begin(); it != offsets.end(); it++) {
		tag_entry te;
		fetchTagEntry(&te, raw_types_database, *it, ms->addressSpace);
		if (te.shared_stores.count(smses->rip.rip))
			out |= te.shared_loads;
	}
	return;
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
findInstrSuccessorsAndCallees(AddressSpace *as,
			      const VexRip &rip,
			      std::vector<VexRip> &directExits,
			      gc_pair_VexRip_set_t *callees)
{
	__set_profiling(findInstrSuccessorsAndCallees);
	IRSB *irsb = Oracle::getIRSBForRip(as, rip);
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
		    irsb->next_const.rip.unwrap_vexrip() != __STACK_CHK_FAILED)
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
findSuccessors(AddressSpace *as, VexRip rip, std::vector<VexRip> &out)
{
	gc_pair_VexRip_set_t *callees = new gc_pair_VexRip_set_t();
	findInstrSuccessorsAndCallees(as, rip, out, callees);
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
			findSuccessors(ms->addressSpace, next.first, s);
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

	if (raw_types_database.init(path) < 0)
		err(1, "opening %s as raw types database", path);
	char *idx_path = my_asprintf("%s.idx", path);
	type_index = new TypesDb(idx_path);
	free(idx_path);
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
			f.calculateRegisterLiveness(ths->ms->addressSpace, &this_did_something, ths);
			if (this_did_something)
				changed++;
			else
				unchanged++;
			done_something |= this_did_something;
			printf("Liveness: Done %zd/%zd functions\n",
			       it - functions.begin(),
			       functions.size());
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
		printf("RBP map: Done %zd/%zd functions\n",
		       it - functions.begin(),
		       functions.size());
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
		do {
			done_something = false;
			f.calculateAliasing(ths->ms->addressSpace, &done_something, ths);
		} while (done_something);
		f.setAliasingConfigCorrect(true);
		printf("Aliasing: Done %zd/%zd functions\n",
		       it - functions.begin(),
		       functions.size());
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

static Oracle::PointerAliasingSet
irexprAliasingClass(IRExpr *expr,
		    IRTypeEnv *tyenv,
		    const Oracle::RegisterAliasingConfiguration &config,
		    bool freeVariablesCannotAccessStack,
		    std::map<threadAndRegister, Oracle::PointerAliasingSet, threadAndRegister::fullCompare> *temps)
{
	if (tyenv && expr->type(tyenv) != Ity_I64)
		/* Not a 64 bit value -> not a pointer */
		return Oracle::PointerAliasingSet::notAPointer;

	switch (expr->tag) {
	case Iex_Get: {
		IRExprGet *e = (IRExprGet *)expr;
		if (e->reg.isTemp()) {
			if (!temps)
				return Oracle::PointerAliasingSet::anything;
			auto it = temps->find(e->reg);
			assert(it != temps->end());
			return it->second;
		} else if (e->reg.asReg() < Oracle::NR_REGS * 8)
			return config.v[e->reg.asReg() / 8];
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
		case Iop_And16:
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
Oracle::getAliasingConfigurationForRip(const StaticRip &rip)
{
	Function f(rip);
	return f.aliasConfigOnEntryToInstruction(rip);
}
Oracle::RegisterAliasingConfiguration
Oracle::getAliasingConfigurationForRip(const VexRip &rip)
{
	return getAliasingConfigurationForRip(StaticRip(rip));
}

struct cg_header {
	unsigned long rip;
	unsigned long nr;
};

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
		VexRip branch_rip;
		auto res = read_vexrip(f, &branch_rip, ths->ms->addressSpace, &is_call);
		if (res == read_vexrip_error) {
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
		fprintf(_logfile, "No function for %s\n", rip.name());
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
		fprintf(_logfile, "Dijkstra failed in %s\n", __func__);
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
	
	rc = sqlite3_open_v2("static.db", &_database, SQLITE_OPEN_READWRITE, NULL);
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
			  "stackHasLeaked INTEGER," /* 0 or NULL -> false, 1 -> true */
			  "rbpToRspDeltaState INTEGER NOT NULL DEFAULT 0,"  /* 0 -> unknown, 1 -> known, 2 -> incalculable */
			  "rbpToRspDelta INTEGER NOT NULL DEFAULT 0,"
			  "functionHead INTEGER NOT NULL)",
			  NULL,
			  NULL,
			  NULL);
	assert(rc == SQLITE_OK);
	rc = sqlite3_exec(_database, "CREATE TABLE fallThroughRips (rip INTEGER, dest INTEGER)", NULL, NULL, NULL);
	assert(rc == SQLITE_OK);
	rc = sqlite3_exec(_database, "CREATE TABLE branchRips (rip INTEGER, dest INTEGER)", NULL, NULL, NULL);
	assert(rc == SQLITE_OK);
	rc = sqlite3_exec(_database, "CREATE TABLE callRips (rip INTEGER, dest INTEGER)", NULL, NULL, NULL);
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
		drop_index("branchRip");
		drop_index("callRip");
		drop_index("fallThroughRip");
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
			ths->discoverFunctionHead(head, heads, callgraph);
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
		create_index("branchRip", "branchRips", "rip");
		create_index("callRip", "callRips", "rip");
		create_index("fallThroughRip", "fallThroughRips", "rip");
		create_index("instructionAttributesFunctionHead", "instructionAttributes", "functionHead");
		create_index("instructionAttributesRip", "instructionAttributes", "rip");
	}

	printf("Calculate register liveness...\n");
	calculateRegisterLiveness(ths, token);
	printf("Calculate aliasing map...\n");
	calculateAliasing(ths, token);
	printf("Calculate RBP map...\n");
	calculateRbpToRspOffsets(ths, token);
	printf("Done static analysis phase\n");
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

Oracle::RegisterAliasingConfiguration
Oracle::Function::aliasConfigOnEntryToInstruction(const StaticRip &rip, bool *b)
{
	static sqlite3_stmt *stmt;
	int rc;

	if (!stmt)
		stmt = prepare_statement(
			"SELECT alias0, alias1, alias2, alias3, alias4, alias5, alias6, alias7, alias8, alias9, alias10, alias11, alias12, alias13, alias14, alias15, stackHasLeaked FROM instructionAttributes WHERE rip = ?");
	bind_oraclerip(stmt, 1, rip);
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
Oracle::Function::aliasConfigOnEntryToInstruction(const StaticRip &rip, Oracle::RegisterAliasingConfiguration *out)
{
	bool res;
	*out = aliasConfigOnEntryToInstruction(rip, &res);
	return res;
}

Oracle::RegisterAliasingConfiguration
Oracle::Function::aliasConfigOnEntryToInstruction(const StaticRip &rip)
{
	bool ign;
	return aliasConfigOnEntryToInstruction(rip, &ign);
}

void
Oracle::discoverFunctionHead(const StaticRip &x, std::vector<StaticRip> &heads, const callgraph_t &callgraph_table)
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

		IRSB *irsb = getIRSBForRip(ms->addressSpace, rip);
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

			std::vector<StaticRip> branch;
			std::vector<StaticRip> fallThrough;
			std::vector<StaticRip> callees;
			for (end_of_instruction = start_of_instruction + 1;
			     end_of_instruction < irsb->stmts_used && irsb->stmts[end_of_instruction]->tag != Ist_IMark;
			     end_of_instruction++) {
				stmt = irsb->stmts[end_of_instruction];
				if (stmt->tag == Ist_Exit)
					branch.push_back(StaticRip(((IRStmtExit *)stmt)->dst.rip));
			}

			if (end_of_instruction == irsb->stmts_used) {
				if (irsb->jumpkind == Ijk_Call) {
					if (!irsb->next_is_const ||
					    irsb->next_const.rip.unwrap_vexrip() != __STACK_CHK_FAILED)
						fallThrough.push_back(StaticRip(extract_call_follower(irsb)));
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
Oracle::Function::calculateRegisterLiveness(AddressSpace *as, bool *done_something, Oracle *oracle)
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
			updateLiveOnEntry(*it, as, &t, oracle);
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
			updateLiveOnEntry(*it, as, &t, oracle);
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
		getFunctionCallers(callers, oracle);
		for (auto it = callers.begin();
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

	std::vector<StaticRip> needsUpdating;
	std::vector<StaticRip> allInstrs;
	getInstructionsInFunction(allInstrs);
	for (auto it = allInstrs.begin();
	     it != allInstrs.end();
	     it++)
		updateSuccessorInstructionsAliasing(*it, as, &needsUpdating, done_something, oracle);
	while (!needsUpdating.empty()) {
		StaticRip rip(needsUpdating.back());
		needsUpdating.pop_back();
		updateSuccessorInstructionsAliasing(rip, as, &needsUpdating, done_something, oracle);
	}
}

void
Oracle::Function::updateLiveOnEntry(const StaticRip &rip, AddressSpace *as, bool *changed, Oracle *oracle)
{
	LivenessSet res;

	IRSB *irsb = getIRSBForRip(as, rip);
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
			    irsb->next_const.rip.unwrap_vexrip() != __STACK_CHK_FAILED)
				fallThroughRips.push_back(StaticRip(extract_call_follower(irsb)));
			if (irsb->next_is_const)
				callees.push_back(StaticRip(irsb->next_const.rip));
			else
				getInstructionCallees(rip, callees, oracle);
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
		if (threadAndRegister::fullEq(what->reg, idx))
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
	if (current_state == RbpToRspOffsetStateImpossible) {
		/* By monotonicity, the result will be
		   RbpToRspOffsetStateImpossible, so bypass and get
		   out early. */
		return;
	}

	/* Try to figure out what this instruction actually does. */
	IRSB *irsb = getIRSBForRip(as, rip);
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
					 "amd64g_dirtyhelper_RDTSC"))
				goto impossible_clean;
			else
				goto impossible;
			IRExpr *v = IRExpr_Load(t,
						((IRStmtDirty *)stmt)->details->args[0],
						ThreadRip::mk(STATIC_THREAD,
							      VexRip::invent_vex_rip(rip.rip)));
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
	if (!rsp && !rbp)
		goto join_predecessors;
	if (rsp && rbp)
		goto impossible_clean;

	if (rsp) {
		if (rsp->tag == Iex_Get) {
			IRExprGet *g = (IRExprGet *)rsp;
			if (g->reg.asReg() == OFFSET_amd64_RSP) {
				abort();
			} else if (g->reg.asReg() == OFFSET_amd64_RBP) {
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
				if (base->reg.asReg() == OFFSET_amd64_RSP) {
					delta_offset = ((IRExprConst *)a->contents[0])->con->Ico.U64;
					goto join_predecessors;
				} else if (base->reg.asReg() == OFFSET_amd64_RBP) {
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
			if (g->reg.asReg() == OFFSET_amd64_RBP) {
				abort();
			} else if (g->reg.asReg() == OFFSET_amd64_RSP) {
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
				if (base->reg.asReg() == OFFSET_amd64_RBP) {
					delta_offset = -o->Ico.U64;
					goto join_predecessors;
				} else if (base->reg.asReg() == OFFSET_amd64_RSP) {
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
		std::vector<StaticRip> predecessors;
		addPredecessorsNonCall(rip, predecessors);

		for (auto it = predecessors.begin();
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
Oracle::Function::updateSuccessorInstructionsAliasing(const StaticRip &rip,
						      AddressSpace *as,
						      std::vector<StaticRip> *changed,
						      bool *done_something,
						      Oracle *oracle)
{
	RegisterAliasingConfiguration config(aliasConfigOnEntryToInstruction(rip));
	std::map<threadAndRegister, PointerAliasingSet, threadAndRegister::fullCompare> temporaryAliases;
	IRStmt *st;

	int nr_statements;
	IRSB *irsb = getIRSBForRip(as, rip);
	if (!irsb)
		return;
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
		case Ist_Put: {
			IRStmtPut *p = (IRStmtPut *)st;
			if (p->target.isReg()) {
				if (p->target.asReg() < NR_REGS * 8 &&
				    p->target.asReg() != OFFSET_amd64_RSP) {
					config.v[p->target.asReg() / 8] =
						irexprAliasingClass(p->data,
								    tyenv,
								    config,
								    false,
								    &temporaryAliases);
				}
			} else {
				temporaryAliases.insert(
					std::pair<threadAndRegister, PointerAliasingSet>(p->target,
											 irexprAliasingClass(p->data,
													     tyenv,
													     config,
													     false,
													     &temporaryAliases)));
			}
			break;
		}
		case Ist_PutI:
			/* Assume that PutIs never target the NR_REGS registers */
			break;
		case Ist_Store:
			if (!config.stackHasLeaked) {
				PointerAliasingSet addr = irexprAliasingClass(((IRStmtStore *)st)->data,
									      tyenv,
									      config,
									      false,
									      &temporaryAliases);
				PointerAliasingSet data = irexprAliasingClass(((IRStmtStore *)st)->data,
									      tyenv,
									      config,
									      false,
									      &temporaryAliases);
				if ((addr & PointerAliasingSet::nonStackPointer) &&
				    (data & PointerAliasingSet::stackPointer))
					config.stackHasLeaked = true;
			}
			break;
		case Ist_CAS: {
			IRStmtCAS *s = (IRStmtCAS *)st;
			if (s->details->oldLo.isTemp()) {
				temporaryAliases.insert(
					std::pair<threadAndRegister, PointerAliasingSet>(
						s->details->oldLo,
						PointerAliasingSet::anything));
			} else if (s->details->oldLo.asReg() < NR_REGS * 8) {
				config.v[s->details->oldLo.asReg() / 8] = PointerAliasingSet::anything;
			}
			break;
		}
		case Ist_Dirty:
			if (((IRStmtDirty *)st)->details->tmp.isValid()) {
				PointerAliasingSet res =
					(strcmp(((IRStmtDirty *)st)->details->cee->name, "helper_load_64") ||
					 config.stackHasLeaked) ?
					 PointerAliasingSet::anything :
					PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer;
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
			RegisterAliasingConfiguration bConfig(aliasConfigOnEntryToInstruction(_branchRip));
			RegisterAliasingConfiguration newExitConfig(bConfig);
			newExitConfig |= config;
			if (newExitConfig != bConfig) {
#warning This isn't even slightly right in the case where _branchRip hasn't been visited yet.
				changed->push_back(_branchRip);
				setAliasConfigOnEntryToInstruction(_branchRip, newExitConfig);
			}
			break;
		}
		default:
			abort();
		}
	}

	std::vector<StaticRip> callees;
	getInstructionCallees(rip, callees, oracle);
	if (!callees.empty())
		config.v[0] = PointerAliasingSet::notAPointer;
	for (auto it = callees.begin();
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
		RegisterAliasingConfiguration succ_config =
			aliasConfigOnEntryToInstruction(*it, &b);
		if (b) {
			RegisterAliasingConfiguration new_config = succ_config;
			new_config |= config;
			if (new_config != succ_config) {
				*done_something = true;
				changed->push_back(*it);
				setAliasConfigOnEntryToInstruction(*it, new_config);
			}
		} else {
			printf("No instruction %s?\n", it->name());
		}
	}
}

void
Oracle::Function::addPredecessorsNonCall(const StaticRip &rip, std::vector<StaticRip> &out)
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
Oracle::Function::addPredecessors(const StaticRip &rip, std::vector<StaticRip> &out)
{
	static sqlite3_stmt *stmt;

	addPredecessorsNonCall(rip, out);
	if (!stmt)
		stmt = prepare_statement("SELECT rip FROM callRips WHERE dest = ?");
	bind_oraclerip(stmt, 1, rip);
	extract_oraclerip_column(stmt, 0, out);
}

void
Oracle::Function::getInstructionFallThroughs(const StaticRip &rip, std::vector<StaticRip> &succ)
{
	static sqlite3_stmt *stmt1;

	if (!stmt1)
		stmt1 = prepare_statement("SELECT dest FROM fallThroughRips WHERE rip = ?");
	bind_oraclerip(stmt1, 1, rip);

	succ.clear();
	extract_oraclerip_column(stmt1, 0, succ);
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
	static sqlite3_stmt *stmt1, *stmt2;

	if (!stmt1 || !stmt2) {
		assert(!stmt1 && !stmt2);
		stmt1 = prepare_statement("SELECT dest FROM fallThroughRips WHERE rip = ?");
		stmt2 = prepare_statement("SELECT dest FROM branchRips WHERE rip = ?");
	}
	bind_oraclerip(stmt1, 1, rip);
	bind_oraclerip(stmt2, 1, rip);

	extract_oraclerip_column(stmt1, 0, succ);
	extract_oraclerip_column(stmt2, 0, succ);
}

void
Oracle::Function::setAliasConfigOnEntryToInstruction(const StaticRip &r,
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
	bind_oraclerip(stmt, NR_REGS + 2, r);
	rc = sqlite3_step(stmt);
	assert(rc == SQLITE_DONE);
	sqlite3_reset(stmt);
}

bool
Oracle::Function::addInstruction(const StaticRip &rip,
				 const std::vector<StaticRip> &callees,
				 const std::vector<StaticRip> &fallThrough,
				 const std::vector<StaticRip> &branch)
{
	static sqlite3_stmt *stmt1;
	static sqlite3_stmt *stmt2;
	static sqlite3_stmt *stmt3;
	static sqlite3_stmt *stmt4;
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

	return true;
}

void
Oracle::Function::getInstructionCallees(const StaticRip &rip, std::vector<StaticRip> &out, Oracle *oracle)
{
	static sqlite3_stmt *stmt;

	if (!stmt)
		stmt = prepare_statement("SELECT dest FROM callRips WHERE rip = ?");
	bind_oraclerip(stmt, 1, rip);
	extract_oraclerip_column(stmt, 0, out);
}

void
Oracle::Function::getFunctionCallers(std::vector<StaticRip> &out, Oracle *oracle)
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

static unsigned
getInstructionSize(AddressSpace *as, const StaticRip &rip)
{
	IRSB *irsb = Oracle::getIRSBForRip(as, rip);
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

/* Find an instruction which is guaranteed to be executed before any
   in @instrs.  Where multiple such instructions exist, we pick the
   latest one (in the sense that there should be no instruction I such
   that I dominates @instrs and also dominates @instrs plus the chosen
   dominator).  If minimum_size is non-zero we further restrict things
   so that we only consider dominating instructions whose size is at
   least minimum_size bytes, or the head instruction in a function. */
VexRip
Oracle::dominator(const std::set<VexRip> &instrs,
		  AddressSpace *as,
		  unsigned minimum_size)
{
	__set_profiling(oracle_dominator);
	assert(!instrs.empty());

	/* For now, only handle the case where everything is in the
	 * same function. */
#warning Not quite right... e.g. if instrs are in same function but have different call stacks
	StaticRip f(0);
	bool have_f = false;
	for (auto it = instrs.begin();
	     it != instrs.end();
	     it++) {
		if (!have_f) {
			f = functionHeadForInstruction(StaticRip(*it));
			have_f = true;
		} else if (f != functionHeadForInstruction(StaticRip(*it))) {
			printf("Can't find dominator for instruction set which crosses functions\n");
			for (it = instrs.begin();
			     it != instrs.end();
			     it++)
				printf("%s in function %s\n", f.name(), functionHeadForInstruction(StaticRip(*it)).name());
			return VexRip();
		}
	}

	if (!have_f) {
		printf("Eh? can't find function which contains instructions which need to be dominated.\n");
		return VexRip();
	}

	/* Find the dominator chains for each individual instruction,
	   intersect them, and then take the last one. This is perhaps
	   not the most efficient algorithm imaginable. */
	std::vector<StaticRip> dominators;
	auto it = instrs.begin();
	findDominators(f, StaticRip(*it), as, dominators);
	std::reverse(dominators.begin(), dominators.end());
	dominators.push_back(StaticRip(*it));
	it++;
	while (it != instrs.end()) {
		if (TIMEOUT)
			break;
		std::vector<StaticRip> newDominators;
		findDominators(f, StaticRip(*it), as, newDominators);
		std::reverse(newDominators.begin(), newDominators.end());
		newDominators.push_back(StaticRip(*it));
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
		return VexRip();
	}

	/* Eliminate excessively small instructions. */
	unsigned x;
	for (x = dominators.size() - 1; minimum_size != 0 && x > 0; x--)
		if (getInstructionSize(as, dominators[x]) >= minimum_size)
			break;
	return dominators[x].makeVexRip(*instrs.begin());
}

bool
Oracle::getRbpToRspDelta(const StaticRip &rip, long *out)
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
bool
Oracle::getRbpToRspDelta(const VexRip &rip, long *out)
{
	return getRbpToRspDelta(StaticRip(rip), out);
}

Oracle::LivenessSet
Oracle::liveOnEntryToFunction(const StaticRip &rip)
{
	Function f(rip);
	return f.liveOnEntry(rip, true);
}
Oracle::LivenessSet
Oracle::liveOnEntryToFunction(const VexRip &rip)
{
	return liveOnEntryToFunction(StaticRip(rip));
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

bool
parseThreadVexRip(ThreadVexRip *tr, const char *str, const char **suffix)
{
	if (!parseDecimalUInt(&tr->thread, str, &str) ||
	    !parseThisChar(':', str, &str) ||
	    !parseVexRip(&tr->rip, str, suffix))
		return false;
	return true;
}
