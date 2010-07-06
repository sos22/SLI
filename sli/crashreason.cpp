#include <err.h>
#include <deque>

#include "sli.h"

#define FOOTSTEP_REGS_ONLY
#include "ppres.h"

History *History::truncate(unsigned long idx, bool inclusive)
{
	assert(idx <= last_valid_idx);
	History *work = this;
	while (work->parent && work->parent->last_valid_idx >= idx)
		work = work->parent;
	if (inclusive)
		return work;
	else
		return work->parent;
}

struct PartialTimestamp {
	ThreadId tid;
	unsigned long idx;
};

static bool
syntax_check_expression(Expression *e, std::map<ThreadId, unsigned long> &last_valid_idx,
			PartialTimestamp *why = NULL)
{
	std::map<ThreadId, unsigned long> neededIdxes;
	e->lastAccessMap(neededIdxes);
	for (std::map<ThreadId, unsigned long>::iterator it = neededIdxes.begin();
	     it != neededIdxes.end();
	     it++) {
		if (it->second > last_valid_idx[it->first]) {
			if (why) {
				why->tid = it->first;
				why->idx = it->second;
			}
			return false;
		}
	}
	return true;
}

template <typename k, typename v>
const v &hashget(const std::map<k,v> &m, const k &key)
{
	std::map<k,v> *non_const_m = 
		const_cast<std::map<k,v> *>(&m);
	return (*non_const_m)[key];
}

class HistoryMapHolder {
	VexGcVisitor<HistoryMapHolder> v;
	std::map<ThreadId, History *> *p;
public:
	HistoryMapHolder(std::map<ThreadId, History *> *_p)
		: v(this, "HistoryMapHolder"),
		  p(_p)
	{
	}
	void visit(HeapVisitor &hv) const
	{
		for (std::map<ThreadId, History *>::const_iterator it = p->begin();
		     it != p->end();
		     it++)
			hv(it->second);
	}
};

static void
fixup_expression(Expression **e,
		 std::map<ThreadId, unsigned long> &last_valid_idx,
		 std::map<ThreadId, History *> &spare_histories,
		 const MachineState<abstract_interpret_value> *ms,
		 LogReader<abstract_interpret_value> *global_lf,
		 LogReaderPtr global_lf_start)
{
top:
	if (syntax_check_expression(*e, last_valid_idx, NULL))
		return;

	if (dynamic_cast<ConstExpression *>(*e))
		return;

	if (UnaryExpression *ue = dynamic_cast<UnaryExpression *>(*e)) {
		fixup_expression(&ue->l, last_valid_idx, spare_histories, ms, global_lf, global_lf_start);
		return;
	}

	if (BinaryExpression *be = dynamic_cast<BinaryExpression *>(*e)) {
		fixup_expression(&be->l, last_valid_idx, spare_histories, ms, global_lf, global_lf_start);
		fixup_expression(&be->r, last_valid_idx, spare_histories, ms, global_lf, global_lf_start);
		return;
	}

	if (ternarycondition *tc = dynamic_cast<ternarycondition *>(*e)) {
		fixup_expression(&tc->cond, last_valid_idx, spare_histories, ms, global_lf, global_lf_start);
		fixup_expression(&tc->t, last_valid_idx, spare_histories, ms, global_lf, global_lf_start);
		fixup_expression(&tc->f, last_valid_idx, spare_histories, ms, global_lf, global_lf_start);
		return;
	}

	if (ExpressionBadPointer *ebp = dynamic_cast<ExpressionBadPointer *>(*e)) {
		fixup_expression(&ebp->addr, last_valid_idx, spare_histories, ms, global_lf, global_lf_start);
		return;
	}

	if (ExpressionRip *er = dynamic_cast<ExpressionRip *>(*e)) {
		History *it;
		std::map<ThreadId, unsigned long> new_last_valid_idx(last_valid_idx);
		unsigned long &idx_entry = new_last_valid_idx[er->tid];
		for (it = er->history;
		     it != NULL;
		     it = it->parent) {
			PartialTimestamp needed;
			idx_entry = it->last_valid_idx;
			if (!syntax_check_expression(it->condition,
						     new_last_valid_idx,
						     &needed)) {
				/* Okay, so we have something like this:

				   rip(tidA, {abc,X,def}, cond)

				   where X references index N in tidB
				   which isn't currently available.  Try to
				   turn it into

				   rip(tidA, {abc}, rip(tidB, {...}, rip(tidA {X,def}, cond)))

				   This has a couple of phases:

				   -- First, we split the existing
				      history into {abc} and {X,def}
				   -- Next, we grab a history for
  				      tidB, denoted ... above.  We
  				      pull this out of the
  				      pre-existing spare history map.
				*/                                                                                                              
                                                                                                                                               
				History *newOuterHist;                                                                                          
				History *newMiddleHist;                                                                                         
				History *newInnerHist;

				newOuterHist = er->history->truncateExclusive(idx_entry);
				newMiddleHist = spare_histories[needed.tid]->truncateInclusive(needed.idx);
				newInnerHist = er->history;
                                                                                                                                               
				*e = ExpressionRip::get(                                                                                        
					er->tid,                                                                                                
					newOuterHist,                                                                                           
					ExpressionRip::get(
						needed.tid,
						newMiddleHist,
						ExpressionRip::get(
							er->tid,
							newInnerHist,
							er->cond,
							er->model_execution,
							er->model_exec_start),
						er->model_execution,
						er->model_exec_start),
					er->model_execution,
					er->model_exec_start);

				/* Run the check again on that. */
				goto top;
			}
		}
		idx_entry = er->history->last_valid_idx;
		fixup_expression(&er->cond, new_last_valid_idx,
				 spare_histories, ms, global_lf, global_lf_start);
		return;
	}

	if (ExpressionHappensBefore *ehb = dynamic_cast<ExpressionHappensBefore *>(*e)) {
		EventTimestamp when;
		bool needFixup = false;
		if (ehb->before.idx > hashget(last_valid_idx, ehb->before.tid)) {
			when = ehb->before;
			needFixup = true;
		}
		if (ehb->after.idx > hashget(last_valid_idx, ehb->after.tid)) {
			when = ehb->after;
			needFixup = true;
		}
		if (needFixup) {
			*e = ExpressionRip::get(when.tid,
						spare_histories[when.tid]->truncateInclusive(when.idx),
						ehb,
						global_lf,
						global_lf_start);
			goto top;
		}
		return;
	}

	if (LoadExpression *le = dynamic_cast<LoadExpression *>(*e)) {
		EventTimestamp when;
		bool needFixup = false;
		if (le->when.idx > hashget(last_valid_idx, le->when.tid)) {
			when = le->when;
			needFixup = true;
		}
		if (le->store.idx > hashget(last_valid_idx, le->store.tid)) {
			when = le->store;
			needFixup = true;
		}
		if (needFixup) {
			/* We have a reference to location @when which
			   isn't currently in scope.  Synthesise a RIP
			   expression which brings it in. */
			*e = ExpressionRip::get(when.tid,
						spare_histories[when.tid]->truncateInclusive(when.idx),
						le,
						global_lf,
						global_lf_start);
			fixup_expression(e, last_valid_idx, spare_histories, ms, global_lf, global_lf_start);
			return;
		}
		fixup_expression(&le->val, last_valid_idx, spare_histories, ms, global_lf, global_lf_start);
		fixup_expression(&le->addr, last_valid_idx, spare_histories, ms, global_lf, global_lf_start);
		return;
	}

	if (ExpressionLastStore *els = dynamic_cast<ExpressionLastStore *>(*e)) {
		fixup_expression(&els->vaddr, last_valid_idx, spare_histories, ms,
				 global_lf, global_lf_start);
		return;
	}

	abort();
}

/* Given a trace, extract a precondition which is necessary for it to
   crash in the observed way. */
class CrashReasonExtractor : public EventRecorder<abstract_interpret_value> {
	static VexAllocTypeWrapper<CrashReasonExtractor> allocator;
public:
	std::map<ThreadId, History *> thread_histories;

	SignalEvent<abstract_interpret_value> *signal;
	Thread<abstract_interpret_value> *thr;
	UseFreeMemoryEvent<abstract_interpret_value> *uafe;

private:
	CrashReasonExtractor()
		: thread_histories(), signal(NULL), thr(NULL), uafe(NULL)
	{
	}
public:
	static CrashReasonExtractor *get()
	{
		return new (allocator.alloc()) CrashReasonExtractor();
	}

	void record(Thread<abstract_interpret_value> *thr, ThreadEvent<abstract_interpret_value> *evt);

	void destruct() { this->~CrashReasonExtractor(); }
	void visit(HeapVisitor &hv) const {
		hv(thr);
		hv(signal);
		hv(uafe);
		for (std::map<ThreadId, History *>::const_iterator it = thread_histories.begin();
		     it != thread_histories.end();
		     it++)
			hv(it->second);
	}

	History *getHistory(const EventTimestamp &evt) {
		History *&ptr = thread_histories[evt.tid];
		if (!ptr)
			ptr = new History(ConstExpression::get(1),
					  evt,
					  NULL);
		return ptr;
	}
	void setHistory(ThreadId tid, History *hs)
	{
		thread_histories[tid] = hs;
	}
	NAMED_CLASS
};
VexAllocTypeWrapper<CrashReasonExtractor> CrashReasonExtractor::allocator;
void CrashReasonExtractor::record(Thread<abstract_interpret_value> *_thr, ThreadEvent<abstract_interpret_value> *evt)
{
	if (uafe)
		return;
	if (const InstructionEvent<abstract_interpret_value> *fe =
	    dynamic_cast<const InstructionEvent<abstract_interpret_value> *>(evt)) {
		unsigned long c;
		if (!fe->rip.origin->isConstant(&c))
			this->setHistory(_thr->tid,
					 this->getHistory(evt->when)->control_expression(
						 evt->when,
						 equals::get(fe->rip.origin, ConstExpression::get(fe->rip.v))));
		this->getHistory(evt->when)->footstep(fe->rip.v);
	}

	if (SignalEvent<abstract_interpret_value> *es =
	    dynamic_cast<SignalEvent<abstract_interpret_value> *>(evt)) {
		thr = _thr;
		signal = es;
	}

	if (UseFreeMemoryEvent<abstract_interpret_value> *uaf =
	    dynamic_cast<UseFreeMemoryEvent<abstract_interpret_value> *>(evt)) {
		uafe = uaf;
		thr = _thr;
	}
}
static Expression *getCrashReason(MachineState<abstract_interpret_value> *ms,
				  LogReader<abstract_interpret_value> *script,
				  LogReaderPtr ptr)
{
	VexGcRoot root0((void **)&ms, "root0");
	MachineState<abstract_interpret_value> *ms2 = ms->dupeSelf();
	Interpreter<abstract_interpret_value> i(ms2);
	CrashReasonExtractor *extr = CrashReasonExtractor::get();
	VexGcRoot root1((void **)&extr, "root1");

	i.replayLogfile(script, ptr, NULL, NULL, extr);
	if (!ms2->crashed())
		return NULL;

	for (std::map<ThreadId, History *>::const_iterator it = extr->thread_histories.begin();
	     it != extr->thread_histories.end();
	     it++) {
		it->second->finish(ms2->findThread(it->first)->nrEvents);
	}

	/* For now, we assume that the only reason to crash is
	   dereferencing a bad pointer, which has only two cases:

	   1) Chasing bad data.
	   2) Chasing bad instructions.

	   We further assume that a crash is due to a bad instruction
	   if the faulting address matches the RIP, and bad data
	   otherwise. */
	Expression *res;
	if (extr->uafe) {
		res = logicaland::get(
			ExpressionHappensBefore::get(extr->uafe->whenFreed,
						     extr->uafe->when),
			equals::get(
				extr->uafe->free_addr.origin,
				extr->uafe->use_addr.origin));
	} else {
		assert(extr->signal);
		assert(extr->thr->crashed);
		if (extr->signal->signr == 11) {
			if (force(extr->thr->regs.rip() == extr->signal->virtaddr))
				res = equals::get(extr->thr->regs.rip().origin,
						  ConstExpression::get(extr->thr->regs.rip().v));
			else
				res = ExpressionBadPointer::get(extr->signal->when, extr->signal->virtaddr.origin);
		} else {
			res = equals::get(extr->thr->regs.rip().origin,
					  ConstExpression::get(extr->thr->regs.rip().v));
		}
	}

	res = ExpressionRip::get(extr->thr->tid,
				 extr->getHistory(extr->thr->lastEvent),
				 res,
				 script,
				 ptr);

	VexGcRoot root2((void **)&res, "root2");
	std::map<ThreadId, unsigned long> m;
	fixup_expression(&res,
			 m,
			 extr->thread_histories,
			 ms,
			 script,
			 ptr);
	std::map<ThreadId, unsigned long> v;
	//assert(syntax_check_expression(res, v));
	return res;
}

/* Most of the time, things more than half a dozen control flow                                      
   operations back are pretty damn useless, and they're also very                                    
   expensive to analyse.  Strip them off. */                                                         
static Expression *                                                                                  
strip_outer_rips(Expression *e, MachineState<abstract_interpret_value> *ms,
		 LogReader<abstract_interpret_value> **lf,
		 LogReaderPtr *lfstart)
{
	/* Phase 1: count how many RIP wrappers there are. */                                         
	unsigned cntr;                                                                                
	Expression *cursor;                                                                           
	ExpressionRip *crip;                                                                          
	cursor = e;                                                                                   
	cntr = 0;                                                                                     
	while (1) {                                                                                   
		crip = dynamic_cast<ExpressionRip *>(cursor);                                         
		if (!crip)                                                                            
			break;                                                                        
		cursor = crip->cond;                                                                  
		cntr++;                                                                               
	}                                                                                             
	
	/* Phase 2: Strip them. */
	if (cntr <= 6)
		return e;
	cntr -= 6;
	cursor = e;
	while (cntr) {
		crip = dynamic_cast<ExpressionRip *>(cursor);
		assert(crip);
		cursor = crip->cond;
		cntr--;
	}

	crip = dynamic_cast<ExpressionRip *>(cursor);
	assert(crip);

	/* Phase 3: generate a new machine state representing the very
	   start of the current history. */
	Interpreter<abstract_interpret_value> i(ms);
	i.runToEvent(crip->history->when, crip->model_execution, crip->model_exec_start, lfstart);
	*lf = crip->model_execution;
	return getCrashReason(ms->dupeSelf(), crip->model_execution, *lfstart);
}

int
main(int argc, char *argv[])
{
	init_sli();

	LibVEX_alloc_sanity_check();

	LogFile *lf;
	LogReaderPtr ptr;

	lf = LogFile::open(argv[1], &ptr);
	if (!lf)
		err(1, "opening %s", argv[1]);
	VexGcRoot logroot((void **)&lf, "logroot");
	LibVEX_alloc_sanity_check();

	MachineState<unsigned long> *concrete = MachineState<unsigned long>::initialMachineState(lf, ptr, &ptr);
	MachineState<abstract_interpret_value> *abstract = concrete->abstract<abstract_interpret_value>();
	VexGcRoot keeper((void **)&abstract, "keeper");

	LibVEX_alloc_sanity_check();
	LogReader<abstract_interpret_value> *al = lf->abstract<abstract_interpret_value>();
	VexGcRoot al_keeper((void **)&al, "al_keeper");

	Expression *cr = getCrashReason(abstract->dupeSelf(), al, ptr);
	VexGcRoot crkeeper((void **)&cr, "crkeeper");
	printf("%s\n", cr->name());
	LogReader<abstract_interpret_value> *lf2 = al;
	VexGcRoot lf2keeper((void **)&lf2, "lf2keeper");
	LogReaderPtr lf2start = ptr;
	cr = strip_outer_rips(cr, abstract, &lf2, &lf2start);

	LibVEX_alloc_sanity_check();
	std::map<ThreadId, unsigned long> m1;
	bool progress;
	do {
		progress = false;
		printf("Crash reason %s\n", cr->name());
		//assert(syntax_check_expression(cr, m1));
		std::map<ThreadId, unsigned long> v;
		LibVEX_alloc_sanity_check();
		cr = cr->refine(abstract, lf2, lf2start, &progress, v, cr->timestamp());
		LibVEX_alloc_sanity_check();
	} while (progress);
	printf("Crash reason %s\n", cr->name());

	dbg_break("Finished.");

	return 0;
}
