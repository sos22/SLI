#include <err.h>
#include <deque>

#include "sli.h"

#define FOOTSTEP_REGS_ONLY
#include "ppres.h"

typedef gc_map<ThreadId, History *, __default_hash_function, __default_eq_function, __visit_function_heap> history_map;

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
syntax_check_expression(Expression *e, gc_map<ThreadId, unsigned long> &last_valid_idx,
			PartialTimestamp *why = NULL)
{
	const gc_map<ThreadId, unsigned long> *neededIdxes = 
		e->lastAccessMap();
	for (gc_map<ThreadId, unsigned long>::iterator it = neededIdxes->begin();
	     it != neededIdxes->end();
	     it++) {
		if (it.value() > last_valid_idx[it.key()]) {
			if (why) {
				why->tid = it.key();
				why->idx = it.value();
			}
			return false;
		}
	}
	return true;
}

static void
fixup_expression(Expression **e,
		 gc_map<ThreadId, unsigned long> &last_valid_idx,
		 history_map &spare_histories,
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
		gc_map<ThreadId, unsigned long> *new_last_valid_idx = new gc_map<ThreadId, unsigned long>(last_valid_idx);
		unsigned long &idx_entry = (*new_last_valid_idx)[er->tid];
		for (it = er->history;
		     it != NULL;
		     it = it->parent) {
			PartialTimestamp needed;
			idx_entry = it->last_valid_idx;
			if (!syntax_check_expression(it->condition,
						     *new_last_valid_idx,
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
		if (er->history)
			idx_entry = er->history->last_valid_idx;
		fixup_expression(&er->cond, *new_last_valid_idx,
				 spare_histories, ms, global_lf, global_lf_start);
		return;
	}

	if (ExpressionHappensBefore *ehb = dynamic_cast<ExpressionHappensBefore *>(*e)) {
		EventTimestamp when;
		bool needFixup = false;
		if (ehb->before.idx > last_valid_idx[ehb->before.tid]) {
			when = ehb->before;
			needFixup = true;
		}
		if (ehb->after.idx > last_valid_idx[ehb->after.tid]) {
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
		if (le->when.idx > last_valid_idx[le->when.tid]) {
			when = le->when;
			needFixup = true;
		}
		if (le->store.idx > last_valid_idx[le->store.tid]) {
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
public:
	history_map *thread_histories;

	SignalEvent<abstract_interpret_value> *signal;
	Thread<abstract_interpret_value> *thr;
	UseFreeMemoryEvent<abstract_interpret_value> *uafe;

	CrashReasonExtractor() {
		thread_histories = new history_map();
	}
	static CrashReasonExtractor *get()
	{
		return new CrashReasonExtractor();
	}

	void record(Thread<abstract_interpret_value> *thr, ThreadEvent<abstract_interpret_value> *evt);

	void destruct() { this->~CrashReasonExtractor(); }
	void visit(HeapVisitor &hv) {
		hv(thr);
		hv(signal);
		hv(uafe);
		hv(thread_histories);
	}

	History *getHistory(const EventTimestamp &evt) {
		History *&ptr((*thread_histories)[evt.tid]);
		if (!ptr)
			ptr = new History(ConstExpression::get(1),
					  evt,
					  NULL);
		return ptr;
	}
	void setHistory(ThreadId tid, History *hs)
	{
		(*thread_histories)[tid] = hs;
	}
	NAMED_CLASS
};
void CrashReasonExtractor::record(Thread<abstract_interpret_value> *_thr, ThreadEvent<abstract_interpret_value> *evt)
{
	if (uafe)
		return;
	this->getHistory(evt->when);

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
static Expression *getCrashReason(VexPtr<MachineState<abstract_interpret_value> > &ms,
				  VexPtr<LogReader<abstract_interpret_value> > &script,
				  LogReaderPtr ptr,
				  GarbageCollectionToken tok)
{
	VexPtr<MachineState<abstract_interpret_value> > ms2(ms->dupeSelf());
	Interpreter<abstract_interpret_value> i(ms2);
	VexPtr<CrashReasonExtractor> extr(CrashReasonExtractor::get());

	VexPtr<LogWriter<abstract_interpret_value> > dummy(NULL);
	VexPtr<EventRecorder<abstract_interpret_value> > extr2(extr);
	i.replayLogfile(script, ptr, tok, NULL, dummy, extr2);
	if (!ms2->crashed()) {
		abort();
		return NULL;
	}

	for (history_map::iterator it = extr->thread_histories->begin();
	     it != extr->thread_histories->end();
	     it++) {
		it.value()->finish(ms2->findThread(it.key())->nrEvents);
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

	gc_map<ThreadId, unsigned long> *m = new gc_map<ThreadId, unsigned long>();
	fixup_expression(&res,
			 *m,
			 *extr->thread_histories,
			 ms,
			 script,
			 ptr);
	//std::map<ThreadId, unsigned long> v;
	//assert(syntax_check_expression(res, v));
	return res;
}

/* Most of the time, things more than half a dozen control flow                                      
   operations back are pretty damn useless, and they're also very                                    
   expensive to analyse.  Strip them off. */                                                         
static Expression *                                                                                  
strip_outer_rips(VexPtr<Expression> &e,
		 VexPtr<MachineState<abstract_interpret_value> > &ms,
		 VexPtr<LogReader<abstract_interpret_value> > *lf,
		 LogReaderPtr *lfstart,
		 GarbageCollectionToken tok)
{
	/* Phase 1: count how many RIP wrappers there are. */                                         
	unsigned cntr;                                                                                
	VexPtr<Expression> cursor;
	ExpressionRip *crip;
	cursor = e;                                                                                   
	cntr = 0;                                                                                     
	while (1) {                                                                                   
		crip = dynamic_cast<ExpressionRip *>(cursor.get());
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
		crip = dynamic_cast<ExpressionRip *>(cursor.get());
		assert(crip);
		cursor = crip->cond;
		cntr--;
	}

	crip = dynamic_cast<ExpressionRip *>(cursor.get());
	assert(crip);

	/* Phase 3: generate a new machine state representing the very
	   start of the current history. */
	Interpreter<abstract_interpret_value> i(ms);
	VexPtr<LogReader<abstract_interpret_value> > model_exec(crip->model_execution);
	i.runToEvent(crip->history->when, model_exec, crip->model_exec_start, tok, lfstart);
        crip = dynamic_cast<ExpressionRip *>(cursor.get());
	assert(crip);
        lf->set(crip->model_execution);
        VexPtr<MachineState<abstract_interpret_value> > ms2(ms->dupeSelf());
        model_exec = crip->model_execution;
        return getCrashReason(ms2, model_exec, *lfstart, tok);
}

int
main(int argc, char *argv[])
{
	init_sli();

	LibVEX_alloc_sanity_check();

	LogReaderPtr ptr;

	VexPtr<LogReader<unsigned long> > lf(LogFile::open(argv[1], &ptr));
	if (!lf)
		err(1, "opening %s", argv[1]);

	LibVEX_alloc_sanity_check();

	MachineState<unsigned long> *concrete = MachineState<unsigned long>::initialMachineState(lf, ptr, &ptr, ALLOW_GC);
	concrete->findThread(ThreadId(7))->clear_child_tid = 0x7faa32f5d9e0;
	VexPtr<MachineState<abstract_interpret_value> > abstract(concrete->abstract<abstract_interpret_value>());
	concrete = NULL;

	LibVEX_alloc_sanity_check();
	VexPtr<LogReader<abstract_interpret_value> > al(lf->abstract<abstract_interpret_value>());

	VexPtr<MachineState<abstract_interpret_value> > abstract2(abstract->dupeSelf());
        VexPtr<Expression> cr(getCrashReason(abstract2, al, ptr, ALLOW_GC));
	printf("%s\n", cr->name());
        VexPtr<LogReader<abstract_interpret_value> > lf2(al);
	LogReaderPtr lf2start = ptr;
        cr = strip_outer_rips(cr, abstract, &lf2, &lf2start, ALLOW_GC);

	LibVEX_alloc_sanity_check();
	bool progress;
	do {
		progress = false;
		printf("Crash reason %s\n", cr->name());
		VexPtr<gc_map<ThreadId, unsigned long> > v(new gc_map<ThreadId, unsigned long>());
		cr = cr->refine(abstract, lf2, lf2start, &progress, v, cr->timestamp(), ALLOW_GC);
	} while (progress);
	printf("Crash reason %s\n", cr->name());

	dbg_break("Finished.");

	return 0;
}
