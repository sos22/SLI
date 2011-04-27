#include <err.h>

#include <map>

#include "sli.h"
#include "oracle.hpp"

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


void
Oracle::findPreviousInstructions(std::vector<unsigned long> &out)
{
	std::vector<unsigned long> fheads;
	getDominators(crashedThread, ms, out, fheads);
	discoverFunctionHeads(fheads);
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
Oracle::memoryAccessesMightAlias(StateMachineSideEffectLoad *smsel,
				 StateMachineSideEffectStore *smses)
{
	for (std::vector<tag_entry>::iterator it = tag_table.begin();
	     it != tag_table.end();
	     it++)
		if (it->loads.count(smsel->rip) &&
		    it->stores.count(smses->rip))
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

		std::set<unsigned long> visited;
		std::vector<unsigned long> pending;
		pending.push_back(item);
		while (!pending.empty()) {
			unsigned long next = pending.back();
			pending.pop_back();
			if (visited.count(next)) {
				/* Okay, we've already been to this
				   instruction starting from this
				   root, so don't need to do anything
				   more. */
				continue;
			}
			visited.insert(next);
			if (inputRips.count(next)) {
				/* This root can reach another one of
				   the input instructions.  That means
				   that they need to be clustered.  Do
				   so. */
				results.insert(item, next);

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
			findSuccessors(ms->addressSpace, next, pending);
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
		tag_table.push_back(t);
	}
}

void
Oracle::discoverFunctionHeads(std::vector<unsigned long> &heads)
{
	while (!heads.empty()) {
		unsigned long head;
		head = heads.back();
		heads.pop_back();
		discoverFunctionHead(head, heads);
	}

	for (gc_heap_map<unsigned long, Function>::type::iterator it = addrToFunction->begin();
	     it != addrToFunction->end();
	     it++)
		it.value()->resolveCallGraph(this);
	calculateRegisterLiveness();
	calculateAliasing();
}

void
Oracle::discoverFunctionHead(unsigned long x, std::vector<unsigned long> &heads)
{
	if (addrToFunction->hasKey(x)) {
		/* Already done */
		return;
	}

	printf("Discovered function head at %lx\n", x);

	Function *work = new Function(x);

	/* Start by building a CFG of the function's instructions. */
	std::vector<unsigned long> unexplored;
	unexplored.push_back(x);
	while (!unexplored.empty()) {
		unsigned long rip = unexplored.back();
		unexplored.pop_back();

		if (work->hasInstruction(rip))
			continue;
		IRSB *irsb = ms->addressSpace->getIRSBForAddress(STATIC_THREAD, rip);
		if (!irsb) {
			printf("WARNING: No IRSB for %lx!\n", rip);
			continue;
		}
		assert(irsb->stmts[0]->tag == Ist_IMark);
		int end_of_instruction;
		for (end_of_instruction = 1;
		     end_of_instruction < irsb->stmts_used && irsb->stmts[end_of_instruction]->tag != Ist_IMark;
		     end_of_instruction++)
			;
		Instruction *i = new Instruction(rip, irsb->stmts + 1, end_of_instruction - 1, irsb->tyenv);
		if (end_of_instruction == irsb->stmts_used) {
			if (irsb->jumpkind == Ijk_Call) {
				i->_fallThroughRip = extract_call_follower(irsb);
				if (irsb->next->tag == Iex_Const)
					i->_calleeRip = irsb->next->Iex.Const.con->Ico.U64;
			} else {
				if (irsb->next->tag == Iex_Const)
					i->_fallThroughRip = irsb->next->Iex.Const.con->Ico.U64;
			}
		} else {
			i->_fallThroughRip = irsb->stmts[end_of_instruction]->Ist.IMark.addr;
		}
		work->addInstruction(i);
		if (i->_fallThroughRip)
			unexplored.push_back(i->_fallThroughRip);
		if (i->_branchRip)
			unexplored.push_back(i->_branchRip);
		if (i->_calleeRip)
			heads.push_back(i->_calleeRip);
	}

	/* Now go through and set successor pointers etc. */
	for (Function::instr_map_t::iterator it = work->instructions->begin();
	     it != work->instructions->end();
	     it++) {
		Instruction *i = it.value();
		i->resolveSuccessors(work);
	}
	addrToFunction->set(work->rip, work);
}

Oracle::Instruction::Instruction(unsigned long _rip, IRStmt **stmts, int nr_stmts, IRTypeEnv *_tyenv)
	: statements((IRStmt **)__LibVEX_Alloc_Ptr_Array(&ir_heap, nr_stmts)),
	  tyenv(_tyenv),
	  nr_statements(nr_stmts),
	  rip(_rip)
{
	for (int i = 0; i < nr_statements; i++) {
		statements[i] = stmts[i];
		if (statements[i]->tag == Ist_Exit)
			_branchRip = statements[i]->Ist.Exit.dst->Ico.U64;
	}
}

void
Oracle::Instruction::resolveCallGraph(Oracle *oracle)
{
	if (_calleeRip) {
		callee = oracle->addrToFunction->get(_calleeRip);
		assert(callee);
	}
}

void
Oracle::Instruction::resolveSuccessors(Function *f)
{
	if (_fallThroughRip) {
		fallThrough = f->ripToInstruction(_fallThroughRip);
		assert(fallThrough);
	}
	if (_branchRip) {
		branch = f->ripToInstruction(_branchRip);
		assert(branch);
	}
}

void
Oracle::calculateRegisterLiveness(void)
{
	bool done_something;

	do {
		done_something = false;
		for (gc_heap_map<unsigned long, Function>::type::iterator it = addrToFunction->begin();
		     it != addrToFunction->end();
		     it++)
			it.value()->calculateRegisterLiveness(&done_something);
	} while (done_something);
}

void
Oracle::calculateAliasing(void)
{
	bool done_something;

	for (gc_heap_map<unsigned long, Function>::type::iterator it = addrToFunction->begin();
	     it != addrToFunction->end();
	     it++) {
		do {
			done_something = false;
			it.value()->calculateAliasing(&done_something);
		} while (done_something);
	}
}

void
Oracle::Function::resolveCallGraph(Oracle *oracle)
{
	for (instr_map_t::iterator it = instructions->begin();
	     it != instructions->end();
	     it++)
		it.value()->resolveCallGraph(oracle);
}

void
Oracle::Function::calculateRegisterLiveness(bool *done_something)
{
	for (instr_map_t::iterator it = instructions->begin();
	     it != instructions->end();
	     it++)
		it.value()->updateLiveOnEntry(done_something);
}

void
Oracle::Function::calculateAliasing(bool *done_something)
{
	Instruction *head = instructions->get(rip);
	RegisterAliasingConfiguration a(head->aliasOnEntry);
	a |= RegisterAliasingConfiguration::functionEntryConfiguration;
	if (head->aliasOnEntry != a) {
		*done_something = true;
		head->aliasOnEntry = a;
	}

	std::vector<Instruction *> needsUpdating;
	for (instr_map_t::iterator it = instructions->begin();
	     it != instructions->end();
	     it++)
		it.value()->updateSuccessorInstructionsAliasing(&needsUpdating);
	while (!needsUpdating.empty()) {
		*done_something = true;
		Instruction *i = needsUpdating.back();
		needsUpdating.pop_back();
		i->updateSuccessorInstructionsAliasing(&needsUpdating);
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
	}
	abort();
}

void
Oracle::Instruction::updateLiveOnEntry(bool *changed)
{
	LivenessSet res;

	if (callee) {
		res = callee->instructions->get(callee->rip)->liveOnEntry & LivenessSet::argRegisters;
		if (fallThrough)
			res |= fallThrough->liveOnEntry;
	} else if (fallThrough)
		res = fallThrough->liveOnEntry;
	for (int i = nr_statements - 1; i >= 0; i--) {
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
		case Ist_Exit:
			if (branch)
				res |= branch->liveOnEntry;
			res = irexprUsedValues(res, statements[i]->Ist.Exit.guard);
			break;
		default:
			abort();
		}
	}
	if (res != liveOnEntry)
		*changed = true;
	liveOnEntry = res;
}

static Oracle::PointerAliasingSet
irexprAliasingClass(IRExpr *expr,
		    IRTypeEnv *tyenv,
		    const Oracle::RegisterAliasingConfiguration &config,
		    std::map<IRTemp, Oracle::PointerAliasingSet> &temps)
{
	if (typeOfIRExpr(tyenv, expr) != Ity_I64)
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
	case Iex_RdTmp:
		return temps[expr->Iex.RdTmp.tmp];
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
		case Iop_Add64: {
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

	default:
		break;
	}
	printf("Don't know how to compute aliasing sets for ");
	ppIRExpr(expr, stdout);
	printf("\n");
	return Oracle::PointerAliasingSet::anything;
}

void
Oracle::Instruction::updateSuccessorInstructionsAliasing(std::vector<Instruction *> *changed)
{
	RegisterAliasingConfiguration config(aliasOnEntry);
	std::map<IRTemp, PointerAliasingSet> temporaryAliases;
	IRStmt *st;

	for (int i = 0; i < nr_statements; i++) {
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
							    config, temporaryAliases);
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
						    temporaryAliases);
			break;
		case Ist_Store:
			if (!config.stackHasLeaked) {
				PointerAliasingSet addr, data;
				addr = irexprAliasingClass(st->Ist.Store.data,
							   tyenv,
							   config,
							   temporaryAliases);
				data = irexprAliasingClass(st->Ist.Store.data,
							   tyenv,
							   config,
							   temporaryAliases);
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
			if (branch) {
				RegisterAliasingConfiguration newExitConfig(branch->aliasOnEntry);
				newExitConfig |= config;
				if (newExitConfig != branch->aliasOnEntry) {
					changed->push_back(branch);
					branch->aliasOnEntry = newExitConfig;
				}
			}
			break;
		}
		default:
			abort();
		}
	}
	if (fallThrough) {
		if (callee) {
			LivenessSet ls = callee->instructions->get(callee->rip)->liveOnEntry;
			/* If any of the argument registers contain
			   stack pointers on entry, the return value
			   can potentially also contain stack
			   pointers. */
			/* This isn't perfectly accurate, but it's a
			   pretty close approximation. */
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
			config.v[0] = PointerAliasingSet::notAPointer;
			if (stackEscapes)
				config.v[0] = config.v[0] | PointerAliasingSet::stackPointer;
			config.v[0] = config.v[0] | PointerAliasingSet::nonStackPointer;
		}
		config |= fallThrough->aliasOnEntry;
		if (config != fallThrough->aliasOnEntry) {
			changed->push_back(fallThrough);
			fallThrough->aliasOnEntry = config;
		}
	}
}
