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

static bool
syntax_check_expression(Expression *e, std::map<ThreadId, unsigned long> &last_valid_idx,
			EventTimestamp *why = NULL)
{
	if (dynamic_cast<ConstExpression *>(e) ||
	    dynamic_cast<ImportExpression *>(e) ||
	    dynamic_cast<BottomExpression *>(e))
		return true;

	if (UnaryExpression *ue = dynamic_cast<UnaryExpression *>(e))
		return syntax_check_expression(ue->l, last_valid_idx, why);

	if (BinaryExpression *be = dynamic_cast<BinaryExpression *>(e))
		return syntax_check_expression(be->l, last_valid_idx, why) &&
			syntax_check_expression(be->r, last_valid_idx, why);

	if (ternarycondition *tc = dynamic_cast<ternarycondition *>(e))
		return syntax_check_expression(tc->cond, last_valid_idx, why) &&
			syntax_check_expression(tc->t, last_valid_idx, why) &&
			syntax_check_expression(tc->f, last_valid_idx, why);

	if (ExpressionBadPointer *ebp = dynamic_cast<ExpressionBadPointer *>(e))
		return syntax_check_expression(ebp->addr, last_valid_idx, why);

	if (ExpressionRip *er = dynamic_cast<ExpressionRip *>(e)) {
		History *it;
		std::map<ThreadId, unsigned long> new_last_valid_idx(last_valid_idx);
		unsigned long &idx_entry = new_last_valid_idx[er->tid];
		for (it = er->history;
		     it != NULL;
		     it = it->parent) {
			idx_entry = it->last_valid_idx;
			if (!syntax_check_expression(it->condition,
						     new_last_valid_idx,
						     why))
				return false;
		}
		idx_entry = er->history->last_valid_idx;
		return syntax_check_expression(er->cond, new_last_valid_idx, why);
	}

	if (LoadExpression *le = dynamic_cast<LoadExpression *>(e)) {
		if (le->when.idx > last_valid_idx[le->when.tid]) {
			printf("Syntax check failed: %d:%ld is after %ld\n",
			       le->when.tid._tid(), le->when.idx,
			       last_valid_idx[le->when.tid]);
			if (why)
				*why = le->when;
			return false;
		}
		if (le->store.idx > last_valid_idx[le->store.tid]) {
			printf("Syntax check failed: store %d:%ld is after %ld\n",
			       le->store.tid._tid(), le->store.idx,
			       last_valid_idx[le->store.tid]);
			if (why)
				*why = le->store;
			return false;
		}
		return syntax_check_expression(le->val, last_valid_idx, why) &&
			syntax_check_expression(le->addr, last_valid_idx, why);
	}

	if (ExpressionLastStore *els =
	    dynamic_cast<ExpressionLastStore *>(e)) {
		if (els->load.idx > last_valid_idx[els->load.tid]) {
			printf("Syntax check failed at %s: load %d:%ld is after %ld\n",
			       els->name(), els->load.tid._tid(),
			       els->load.idx, last_valid_idx[els->load.tid]);
			if (why)
				*why = els->load;
			return false;
		}
		if (els->store.idx > last_valid_idx[els->store.tid]) {
			printf("Syntax check failed at %s: store %d:%ld is after %ld\n",
			       els->name(), els->store.tid._tid(),
			       els->store.idx, last_valid_idx[els->store.tid]);
			if (why)
				*why = els->store;
			return false;
		}
		return syntax_check_expression(els->vaddr, last_valid_idx, why);
	}

	if (ExpressionHappensBefore *ehb =
	    dynamic_cast<ExpressionHappensBefore *>(e)) {
		if (ehb->before.idx > last_valid_idx[ehb->before.tid]) {
			printf("Syntax check failed at %s: %d:%ld is after %ld\n",
			       ehb->name(), ehb->before.tid._tid(),
			       ehb->before.idx, last_valid_idx[ehb->before.tid]);
			if (why)
				*why = ehb->before;
			return false;
		}
		if (ehb->after.idx > last_valid_idx[ehb->after.tid]) {
			printf("Syntax check failed at %s: %d:%ld is after %ld\n",
			       ehb->name(), ehb->after.tid._tid(),
			       ehb->after.idx, last_valid_idx[ehb->after.tid]);
			if (why)
				*why = ehb->after;
			return false;
		}
		return true;
	}
	abort();
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
dump_spare_list_idx(const std::map<ThreadId, History *> &spare_histories)
{
	for (std::map<ThreadId, History *>::const_iterator it = spare_histories.begin();
	     it != spare_histories.end();
	     it++)
		printf("%d -> last %ld\n",
		       it->first._tid(),
		       it->second->last_valid_idx);
}

static void
fixup_expression(Expression **e,
		 const std::map<ThreadId, unsigned long> &last_valid_idx,
		 std::map<ThreadId, History *> &spare_histories,
		 const MachineState<abstract_interpret_value> *ms,
		 LogReader<abstract_interpret_value> *global_lf,
		 LogReaderPtr global_lf_start)
{
	dump_spare_list_idx(spare_histories);

	if (dynamic_cast<ConstExpression *>(*e) ||
	    dynamic_cast<ImportExpression *>(*e))
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
			EventTimestamp needed;
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
				fixup_expression(e, last_valid_idx, spare_histories, ms, global_lf, global_lf_start);
				return;
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
			fixup_expression(e, last_valid_idx, spare_histories, ms, global_lf, global_lf_start);
			return;
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


private:
	CrashReasonExtractor()
		: thread_histories(), signal(NULL), thr(NULL)
	{
	}
public:
	static CrashReasonExtractor *get()
	{
		return new (allocator.alloc()) CrashReasonExtractor();
	}

	void record(Thread<abstract_interpret_value> *thr, const ThreadEvent<abstract_interpret_value> *evt);

	void destruct() { this->~CrashReasonExtractor(); }
	void visit(HeapVisitor &hv) const {
		hv(thr);
		hv(signal);
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
void CrashReasonExtractor::record(Thread<abstract_interpret_value> *_thr, const ThreadEvent<abstract_interpret_value> *evt)
{
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

	if (const SignalEvent<abstract_interpret_value> *es =
	    dynamic_cast<const SignalEvent<abstract_interpret_value> *>(evt)) {
		thr = _thr;
		signal = (SignalEvent<abstract_interpret_value> *)es->dupe();
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
	assert(extr->signal);
	assert(extr->thr->crashed);
	Expression *res;
	if (force(extr->thr->regs.rip() == extr->signal->virtaddr))
		res = ExpressionRip::get(extr->thr->tid, extr->getHistory(extr->thr->lastEvent),
					 equals::get(extr->thr->regs.rip().origin,
						     ConstExpression::get(extr->thr->regs.rip().v)),
					 script,
					 ptr);
	else
		res = ExpressionRip::get(extr->thr->tid,
					 extr->getHistory(extr->thr->lastEvent),
					 ExpressionBadPointer::get(extr->signal->when, extr->signal->virtaddr.origin),
					 script,
					 ptr);

	VexGcRoot root2((void **)&res, "root2");
	fixup_expression(&res,
			 std::map<ThreadId, unsigned long>(),
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
	LogReader<abstract_interpret_value> *lf2 = NULL;
	VexGcRoot lf2keeper((void **)&lf2, "lf2keeper");
	LogReaderPtr lf2start;
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

	return 0;
}
