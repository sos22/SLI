#include <string.h>
#include <asm/unistd.h>
#include <sys/time.h>

#include "sli.h"

#include "libvex.h"
#include "libvex_ir.h"
#include "libvex_emwarn.h"
#include "libvex_guest_amd64.h"
#include "guest_generic_bb_to_IR.h"
#include "guest_generic_x87.h"
#include "guest_amd64_defs.h"
#include "main_util.h"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"
#include "visitor.hpp"

#define FOOTSTEP_REGS_ONLY
#include "ppres.h"

#include "sli.h"

static Bool chase_into_ok(void *, Addr64 )
{
	return False;
}

class AddressSpaceGuestFetcher : public GuestMemoryFetcher {
	AddressSpace *aspace;
	unsigned long offset;
	mutable UChar cache[16];
	mutable unsigned long cache_start;
	mutable bool have_cache;
public:
	virtual UChar operator[](unsigned long idx) const
	{
		unsigned long desired = idx + offset;
		if (have_cache && desired >= cache_start && desired < cache_start + sizeof(cache))
			return cache[desired - cache_start];
		cache_start = desired;
		unsigned long v[16];
		aspace->readMemory(desired, 16, v);
		for (unsigned x = 0; x < sizeof(cache); x++)
			cache[x] = v[x];
		have_cache = true;
		return cache[0];
	}
	AddressSpaceGuestFetcher(AddressSpace *_aspace,
				 const ThreadRip &_offset) :
		GuestMemoryFetcher(_offset),
		aspace(_aspace),
		offset(_offset.rip.unwrap_vexrip()),
		cache_start(0),
		have_cache(false)
	{
	}
};

class DecodeCache : public GarbageCollected<DecodeCache, &ir_heap> {
	class DecodeCacheEntry : public GarbageCollected<DecodeCacheEntry, &ir_heap> {
	public:
		DecodeCacheEntry *next;
		ThreadRip key;
		IRSB *irsb;

		void visit(HeapVisitor &) { abort(); }

		NAMED_CLASS
	};

	static const unsigned nr_slots = 2053;
	DecodeCacheEntry *slots[nr_slots];
	static unsigned long rip_hash(const ThreadRip &tr)
	{
		unsigned long hash = tr.hash();
		while (hash >= nr_slots)
			hash = (hash % nr_slots) ^ (hash / nr_slots);
		return hash;
	}

public:
	IRSB **search(const ThreadRip &tr);

	void visit(HeapVisitor &) { abort(); }
	NAMED_CLASS
};
IRSB **
DecodeCache::search(const ThreadRip &tr)
{
	DecodeCacheEntry **pdce, *dce;
	unsigned hash = rip_hash(tr);
	pdce = &slots[hash];
	while (*pdce && (*pdce)->key != tr)
		pdce = &(*pdce)->next;
	dce = *pdce;
	if (dce) {
		*pdce = dce->next;
	} else {
		dce = new DecodeCacheEntry();
		dce->key = tr;
	}
	dce->next = slots[hash];
	slots[hash] = dce;
	return &dce->irsb;
}

static VexPtr<WeakRef<DecodeCache, &ir_heap>, &ir_heap> decode_cache;

/* Do some very basic optimisations directly on the IRSB, to keep
   everything else a bit simpler.  This relies on the fact that IRSBs
   are single-entry. */
static void
optimiseIRSB(IRSB *irsb)
{
	irsb->sanity_check();
	/* First, basic copy propagation. */
	std::map<threadAndRegister, IRExpr *> tmps;
	struct : public IRExprTransformer {
		std::map<threadAndRegister, IRExpr *> *tmps;
		IRExpr *transformIex(IRExprGet *what) {
			auto it = tmps->find(((IRExprGet *)what)->reg);
			if (it == tmps->end() || what->type() > it->second->type())
				return what;
			else
				return coerceTypes(what->type(), it->second);
		}
		void operator()(IRExpr **k) {
			if (*k)
				*k = doit(*k);
		}
	} useTmps;
	useTmps.tmps = &tmps;
	struct {
		static visit_result Get(const threadAndRegister *c, const IRExprGet *ieg) {
			if (ieg->reg == *c)
				return visit_abort;
			else
				return visit_continue;
		}
		bool mentionsRegister(const threadAndRegister &tr, const IRExpr *e)
		{
			static irexpr_visitor<const threadAndRegister> visitor;
			visitor.Get = Get;
			return visit_irexpr(&tr, &visitor, e) == visit_abort;
		}
		std::map<threadAndRegister, IRExpr *> *tmps;
		void operator()(const threadAndRegister &tr) {
			for (auto it = tmps->begin(); it != tmps->end(); ) {
				if (mentionsRegister(tr, it->second))
					tmps->erase(it++);
				else
					it++;
			}
		}
	} invalidateTmp = {&tmps};
	for (int i = 0; i < irsb->stmts_used; i++) {
		IRStmt *stmt = irsb->stmts[i];
		stmt->sanity_check();
		switch (stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			break;
		case Ist_AbiHint:
			useTmps(&((IRStmtAbiHint *)stmt)->base);
			useTmps(&((IRStmtAbiHint *)stmt)->nia);
			break;
		case Ist_Put: {
			IRStmtPut *p = (IRStmtPut *)stmt;
			useTmps(&p->data);
			tmps[p->target] = p->data;
			invalidateTmp(p->target);
			break;
		}
		case Ist_PutI:
			useTmps(&((IRStmtPutI *)stmt)->ix);
			useTmps(&((IRStmtPutI *)stmt)->data);
			break;
		case Ist_Store:
			useTmps(&((IRStmtStore *)stmt)->addr);
			useTmps(&((IRStmtStore *)stmt)->data);
			break;
		case Ist_CAS:
			useTmps(&((IRStmtCAS *)stmt)->details->addr);
			useTmps(&((IRStmtCAS *)stmt)->details->expdLo);
			useTmps(&((IRStmtCAS *)stmt)->details->dataLo);
			invalidateTmp( ((IRStmtCAS *)stmt)->details->oldLo);
			break;
		case Ist_Dirty: {
			IRStmtDirty *d = (IRStmtDirty *)stmt;
			useTmps(&d->details->guard);
			useTmps(&d->details->mAddr);
			for (int i = 0; d->details->args[i]; i++)
				useTmps(&d->details->args[i]);
			invalidateTmp(d->details->tmp);
			break;
		}
		case Ist_MBE:
			break;
		case Ist_Exit:
			useTmps(&((IRStmtExit *)stmt)->guard);
			break;
		case Ist_StartAtomic:
			break;
		case Ist_EndAtomic:
			break;
		}
		stmt->sanity_check();
	}

	if (!irsb->next_is_const)
		useTmps(&irsb->next_nonconst);

	/* Now do deadcode and local IRExpr optimisation. */
	IRStmt *noop = NULL;
	std::set<threadAndRegister> neededRegs;
	struct : public IRExprTransformer {
		std::set<threadAndRegister> *neededRegs;
		static visit_result Get(std::set<threadAndRegister> *neededRegs, const IRExprGet *ieg) {
			neededRegs->insert(ieg->reg);
			return visit_continue;
		}
		void operator()(IRExpr **i) {
			static irexpr_visitor<std::set<threadAndRegister> > visitor;
			visitor.Get = Get;
			if (*i) {
				*i = simplifyIRExpr(*i, AllowableOptimisations::defaultOptimisations);
				visit_irexpr(neededRegs, &visitor, *i);
			}
		}
	} useExpr;
	useExpr.neededRegs = &neededRegs;
	if (!irsb->next_is_const)
		useExpr(&irsb->next_nonconst);

	for (int i = irsb->stmts_used - 1; i >= 0; i--) {
		IRStmt *stmt = irsb->stmts[i];
		switch (stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			break;
		case Ist_AbiHint:
			useExpr(&((IRStmtAbiHint *)stmt)->base);
			useExpr(&((IRStmtAbiHint *)stmt)->nia);
			break;
		case Ist_Put: {
			IRStmtPut *p = (IRStmtPut *)stmt;
			if (p->target.isTemp() && !neededRegs.count(p->target)) {
				if (noop == NULL)
					noop = IRStmt_NoOp();
				irsb->stmts[i] = noop;
			} else {
				neededRegs.erase(p->target);
				useExpr(&p->data);
			}
			break;
		}
		case Ist_PutI:
			useExpr(&((IRStmtPutI *)stmt)->ix);
			useExpr(&((IRStmtPutI *)stmt)->data);
			break;
		case Ist_Store:
			useExpr(&((IRStmtStore *)stmt)->addr);
			useExpr(&((IRStmtStore *)stmt)->data);
			break;
		case Ist_CAS:
			neededRegs.erase(((IRStmtCAS *)stmt)->details->oldLo);
			useExpr(&((IRStmtCAS *)stmt)->details->addr);
			useExpr(&((IRStmtCAS *)stmt)->details->expdLo);
			useExpr(&((IRStmtCAS *)stmt)->details->dataLo);
			break;
		case Ist_Dirty: {
			IRStmtDirty *d = (IRStmtDirty *)stmt;
			neededRegs.erase(d->details->tmp);
			useExpr(&d->details->guard);
			useExpr(&d->details->mAddr);
			for (int i = 0; d->details->args[i]; i++)
				useExpr(&d->details->args[i]);
			break;
		}
		case Ist_MBE:
			break;
		case Ist_Exit:
			useExpr(&((IRStmtExit *)stmt)->guard);
			break;
		case Ist_StartAtomic:
			break;
		case Ist_EndAtomic:
			break;
		}
		stmt->sanity_check();
	}

	/* And now kill off any noop statements. */
	int in = 0;
	int out = 0;
	while (in < irsb->stmts_used) {
		if (irsb->stmts[in]->tag != Ist_NoOp) {
			irsb->stmts[out] = irsb->stmts[in];
			out++;
		}
		in++;
	}
	irsb->stmts_used = out;
}

IRSB *
AddressSpace::getIRSBForAddress(const ThreadRip &tr, bool singleInstr)
{
	unsigned tid = tr.thread;

	if (!decode_cache.get())
		decode_cache.set(new WeakRef<DecodeCache, &ir_heap>());
	DecodeCache *dc = decode_cache.get()->get();
	if (!dc) {
		dc = new DecodeCache();
		decode_cache.get()->set(dc);
	}
	IRSB **cacheSlot = dc->search(tr);
	assert(cacheSlot != NULL);
	IRSB *irsb = *cacheSlot;
	if (!irsb) {
		VexArchInfo archinfo_guest;
		VexAbiInfo abiinfo_both;
		LibVEX_default_VexArchInfo(&archinfo_guest);
		archinfo_guest.hwcaps =
			VEX_HWCAPS_AMD64_SSE3|
			VEX_HWCAPS_AMD64_CX16;
		LibVEX_default_VexAbiInfo(&abiinfo_both);
		abiinfo_both.guest_stack_redzone_size = 128;
		abiinfo_both.guest_amd64_assume_fs_is_zero = 1;
		AddressSpaceGuestFetcher fetcher(this, tr);
		irsb = bb_to_IR(tid,
				NULL, /* Context for chase_into_ok */
				disInstr_AMD64,
				fetcher,
				tr,
				chase_into_ok,
				False, /* host bigendian */
				&archinfo_guest,
				&abiinfo_both,
				False, /* do_self_check */
				NULL,
				singleInstr);
		if (!irsb)
			abort();

		irsb->sanity_check();

		irsb = instrument_func(tid, NULL, irsb, NULL, NULL, Ity_I64, Ity_I64);

		optimiseIRSB(irsb);

		*cacheSlot = irsb;
	}

	return irsb;
}

VexRip
extract_call_follower(IRSB *irsb)
{
	/* We expect a call to look like this:

	   0:   ------ IMark(0x7fde5bdd85a7, 5) ------
	   1:   t0 = Sub64(GET:I64(32),0x8:I64)
	   2:   PUT(32) = t0
	   3:   STle(t0) = 0x7fde5bdd85ac:I64
	   4:   t1 = 0x7fde5be62750:I64
	   5:   ====== AbiHint(Sub64(t0,0x80:I64), 128, t1) ======
	   goto {Call} 0x7fde5be62750:I64
   
	   Or so.  The WrTmp at statement 4 is optional, but the rest
	   has to be there.  We process statements in reverse order
	   from the end, checking that things match as we go. */
	int idx = irsb->stmts_used - 1;

	if (idx < 0 ||
	    irsb->stmts[idx]->tag != Ist_AbiHint)
		abort();
	idx--;
	if (idx < 0)
		abort();
	if (irsb->stmts[idx]->tag == Ist_Put)
		idx--;
	if (idx < 0)
		abort();
	if (irsb->stmts[idx]->tag != Ist_Store)
		abort();
	IRStmtStore *s = (IRStmtStore *)irsb->stmts[idx];
	if (s->data->tag != Iex_Const)
		abort();
	while (idx >= 0 && irsb->stmts[idx]->tag != Ist_IMark)
		idx--;
	assert(idx >= 0);
	VexRip r( ((IRStmtIMark *)irsb->stmts[idx])->addr.rip );
	r.jump(((IRExprConst *)s->data)->Ico.content.U64);
	return r;
}
