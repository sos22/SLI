#include <err.h>

#include "sli.h"

#define FOOTSTEP_REGS_ONLY
#include "ppres.h"

/* A HistorySegment represents a chunk of per-thread history.  In
   theory, the only part which is really necessary, and the only part
   which is semantically important, is the condition, which is just a
   condition which is evaluated at the start of the segment and has to
   be true.

   We also store a timestamp, which is the point in the model
   execution at which the condition was evaluated.  This is used in
   the heuristic which decides which branch of an expression to refine
   first.

   We also store a log of the RIPs touched between each conditional
   expression (the ones in the vector are touched *after* the current
   condition is evaluated).  This is in theory redundant with the
   condition, because if you pass the condition then you ought to
   always follow the same RIP path, but it makes it a *lot* easier to
   see if something's gone wrong.

   Finally, we store the number of memory operations which the thread
   will perform after it passes this condition before it reaches the
   next one.  This is extremely useful when checking whether a given
   expression is syntactically valid, in the sense that all memory
   indexes are defined by enclosing RIP expressions.
*/
class HistorySegment : public Named {
public:
	Expression *condition;
	unsigned long nr_memory_operations;
	EventTimestamp when;
	std::vector<unsigned long> rips;
private:
	static const VexAllocTypeWrapper<HistorySegment> allocator;
	HistorySegment(Expression *_condition,
		       EventTimestamp _when)
		: condition(_condition),
		  nr_memory_operations(0),
		  when(_when),
		  rips()
	{
		assert(when.tid.valid());
	}
	HistorySegment(ThreadId tid)
		: condition(ConstExpression::get(1)),
		  nr_memory_operations(0),
		  when(EventTimestamp(tid, 0)),
		  rips()
	{
		assert(when.tid.valid());
	}
	HistorySegment(std::vector<unsigned long> &_rips,
		       unsigned long nr_memory_ops,
		       ThreadId tid)
		: condition(ConstExpression::get(1)),
		  nr_memory_operations(nr_memory_ops),
		  when(EventTimestamp(tid, 0)),
		  rips(_rips)
	{
		assert(when.tid.valid());
	}
protected:
	char *mkName() const {
		char *buf = my_asprintf("%s@%d:%lx", condition->name(), when.tid._tid(), when.idx);
		for (std::vector<unsigned long>::const_iterator it = rips.begin();
		     it != rips.end();
		     it++) {
			char *b2 = my_asprintf("%s:%lx", buf, *it);
			free(buf);
			buf = b2;
		}
		return buf;
	}
public:
	static HistorySegment *get(Expression *condition,
				   EventTimestamp when)
	{
		return new (allocator.alloc()) HistorySegment(condition,
							      when);
	}
	static HistorySegment *get(ThreadId when)
	{
		return new (allocator.alloc()) HistorySegment(when);
	}
	static HistorySegment *get(std::vector<unsigned long> &rips,
				   unsigned long nr_memory_ops,
				   ThreadId when)
	{
		return new (allocator.alloc()) HistorySegment(rips, nr_memory_ops, when);
	}
	void destruct()
	{
		this->~HistorySegment();
	}
	void visit(HeapVisitor &hv) const
	{
		hv(condition);
	}

	bool isEqual(const HistorySegment *h) const
	{
		if (when != h->when)
			return false;
		if (rips.size() != h->rips.size())
			return false;
		if (!condition->isEqual(h->condition))
			return false;
		std::vector<unsigned long>::const_iterator it1;
		std::vector<unsigned long>::const_iterator it2;
		it1 = rips.begin();
		it2 = h->rips.begin();
		while (it1 != rips.end()) {
			assert(it2 != h->rips.end());
			if (*it1 != *it2)
				return false;
		}
		return false;
	}
	void finish(EventTimestamp fin)
	{
		nr_memory_operations = fin.idx - when.idx;
	}
};
const VexAllocTypeWrapper<HistorySegment> HistorySegment::allocator;

class History : public Named {
public:
	std::vector<HistorySegment *>history;
	unsigned long last_valid_idx;
	unsigned long first_valid_idx;
	ThreadId tid;
	void calc_last_valid_idx() {
		last_valid_idx = first_valid_idx;
		for (std::vector<HistorySegment *>::iterator it = history.begin();
		     it != history.end();
		     it++)
			last_valid_idx += (*it)->nr_memory_operations;
	}
private:
	static const VexAllocTypeWrapper<History> allocator;
	History(std::vector<HistorySegment *>::const_iterator start,
		std::vector<HistorySegment *>::const_iterator end,
		unsigned long _first,
		ThreadId _tid)
		: history(start, end),
		  first_valid_idx(_first),
		  tid(_tid)
	{
		calc_last_valid_idx();
	}
	History(std::vector<unsigned long> rips, unsigned long nr_memory_ops,
		unsigned long _first, ThreadId _tid)
		: first_valid_idx(_first),
		  tid(_tid)
	{
		history.push_back(HistorySegment::get(rips, nr_memory_ops, tid));
		calc_last_valid_idx();
	}
	History(unsigned long _first_valid_idx, ThreadId _tid)
		: first_valid_idx(_first_valid_idx),
		  tid(_tid)
	{
		history.push_back(HistorySegment::get(tid));
		calc_last_valid_idx();
	}
protected:
	char *mkName() const {
		char *buf = NULL;
		for (std::vector<HistorySegment *>::const_iterator it = history.begin();
		     it != history.end();
		     it++) {
			const char *component = (*it)->name();
			if (buf) {
				char *b2 = my_asprintf("%s{%s}", buf, component);
				free(buf);
				buf = b2;
			} else {
				buf = my_asprintf("{%s}", component);
			}
		}
		if (buf)
			return buf;
		else
			return strdup("<empty history>");
	}
public:
	static History *get(std::vector<HistorySegment *>::const_iterator start,
			    std::vector<HistorySegment *>::const_iterator end,
			    unsigned long first_valid_idx,
			    ThreadId tid)
	{
		return new (allocator.alloc()) History(start, end, first_valid_idx, tid);
	}
	static History *get(std::vector<unsigned long> &rips,
			    unsigned long nr_memory_ops,
			    unsigned long first_valid_idx,
			    ThreadId tid)
	{
		return new (allocator.alloc()) History(rips, nr_memory_ops, first_valid_idx, tid);
	}
	static History *get(unsigned long first_valid_idx,
			    ThreadId tid)
	{
		return new (allocator.alloc()) History(first_valid_idx, tid);
	}
	void destruct()
	{
		this->~History();
	}
	void visit(HeapVisitor &hv) const
	{
		for (std::vector<HistorySegment *>::const_iterator it = history.begin();
		     it != history.end();
		     it++)
			hv(*it);
	}
	bool isEqual(const History *h) const
	{
		if (history.size() != h->history.size())
			return false;
		std::vector<HistorySegment *>::const_iterator it1;
		std::vector<HistorySegment *>::const_iterator it2;
		it1 = history.begin();
		it2 = h->history.begin();
		while (it1 != history.end()) {
			assert(it2 != h->history.end());
			if (!(*it1)->isEqual(*it2))
				return false;
		}
		return false;
	}
	void control_expression(EventTimestamp when, Expression *e)
	{
		finish(when);
		history.push_back(HistorySegment::get(e, when));
	}
	void finish(EventTimestamp when)
	{
		history.back()->finish(when);
	}
	void footstep(unsigned long rip)
	{
		history.back()->rips.push_back(rip);
	}
	EventTimestamp timestamp() const
	{
		return history.back()->when;
	}
	void splitAt(unsigned idx, History **firstBit, History **secondBit) const;
	void extractSubModel(
		ThreadId tid,
		const MachineState<abstract_interpret_value> *ms,
		const std::vector<unsigned long> &discardRips,
		LogReader<abstract_interpret_value> *lf,
		LogReaderPtr ptr,
		LogReader<abstract_interpret_value> **newModel,
		LogReaderPtr *newPtr,
		LogReader<abstract_interpret_value> **newModel2,
		LogReaderPtr *newPtr2,
		std::vector<unsigned long> *newPrefix);
};
const VexAllocTypeWrapper<History> History::allocator;

/* A RIP expression asserts that a particular thread will follow a
 * particular control flow path, and hence that memory operations can
 * be identified by their position in the memory operation stream.
 */
class ExpressionRip : public Expression {
public:
	ThreadId tid;
	History *history;
	Expression *cond;
	LogReader<abstract_interpret_value> *model_execution;
	LogReaderPtr model_exec_start;

	/* The model will start from the very beginning, whereas the
	   history is relative to the previous history.  We therefore
	   expect that when we replay the model we'll see a few RIPs
	   which aren't in the model.  They go here. */
	std::vector<unsigned long> prefix_rips;
private:
	static VexAllocTypeWrapper<ExpressionRip> allocator;
	ExpressionRip(ThreadId _tid, History *_history, Expression *_cond,
		      LogReader<abstract_interpret_value> *model,
		      LogReaderPtr start, std::vector<unsigned long> &_prefix_rips)
		: tid(_tid),
		  history(_history),
		  cond(_cond),
		  model_execution(model),
		  model_exec_start(start),
		  prefix_rips(_prefix_rips)
	{
	}
protected:
	char *mkName(void) const {
		return my_asprintf("(rip %d:{...}:%s)", tid._tid(), cond->name());
	}
	unsigned _hash() const {
		return history->history.size() ^ tid._tid() ^ cond->hash();
	}
	bool _isEqual(const Expression *other) const {
		const ExpressionRip *oth = dynamic_cast<const ExpressionRip *>(other);
		if (oth && oth->tid == tid && cond->isEqual(oth->cond) &&
		    oth->history->isEqual(history))
			return true;
		else
			return false;
	}
public:
	static Expression *get(ThreadId tid, History *history, Expression *cond,
			       LogReader<abstract_interpret_value> *model,
			       LogReaderPtr start, std::vector<unsigned long> &prefix_rips)
	{
		return new (allocator.alloc()) ExpressionRip(tid, history, cond,
							     model, start,
							     prefix_rips);
	}
	void visit(HeapVisitor &hv) const
	{
		hv(history);
		hv(cond);
		hv(model_execution);
	}
	EventTimestamp timestamp() const {
		return max<EventTimestamp>(history->timestamp(),
					    cond->timestamp());
	}
	bool isLogical() const { return cond->isLogical(); }
};

VexAllocTypeWrapper<ExpressionRip> ExpressionRip::allocator;

/* A bad pointer expression asserts that a particular memory location
 * is inaccessible at a particular time. */
class ExpressionBadPointer : public Expression {
public:
	Expression *addr;
	EventTimestamp when;
private:
	static VexAllocTypeWrapper<ExpressionBadPointer> allocator;
	ExpressionBadPointer(EventTimestamp _when, Expression *_addr)
		: addr(_addr), when(_when)
	{
	}
protected:
	char *mkName(void) const {
		return my_asprintf("(bad ptr %d:%lx:%s)", when.tid._tid(), when.idx, addr->name());
	}
	unsigned _hash() const {
		return addr->hash() ^ when.hash();
	}
	bool _isEqual(const Expression *other) const {
		const ExpressionBadPointer *oth = dynamic_cast<const ExpressionBadPointer *>(other);
		if (oth && oth->addr->isEqual(addr) && oth->when == when)
			return true;
		else
			return false;
	}
public:
	static Expression *get(EventTimestamp _when, Expression *_addr)
	{
		return new (allocator.alloc()) ExpressionBadPointer(_when, _addr);
	}
	void visit(HeapVisitor &hv) const { hv(addr); }
	EventTimestamp timestamp() const { return when; }
};
VexAllocTypeWrapper<ExpressionBadPointer> ExpressionBadPointer::allocator;

class ExpressionLastStore : public Expression {
public:
	EventTimestamp load;
	EventTimestamp store;
	Expression *vaddr;
private:
	static VexAllocTypeWrapper<ExpressionLastStore> allocator;
	ExpressionLastStore(EventTimestamp _load, EventTimestamp _store,
			    Expression *_vaddr)
		: load(_load), store(_store), vaddr(_vaddr)
	{
	}
protected:
	char *mkName(void) const {
		return my_asprintf("(lastStore@%d:%lx:%s -> %d:%lx)",
				   load.tid._tid(),
				   load.idx,
				   vaddr->name(),
				   store.tid._tid(),
				   store.idx);
	}
	unsigned _hash() const {
		return load.hash() ^ store.hash() ^ vaddr->hash();
	}
	bool _isEqual(const Expression *other) const {
		const ExpressionLastStore *oth = dynamic_cast<const ExpressionLastStore *>(other);
		if (oth &&
		    load == oth->load &&
		    store == oth->store &&
		    vaddr->isEqual(oth->vaddr))
			return true;
		else
			return false;
	}
public:
	static Expression *get(EventTimestamp load, EventTimestamp store,
			       Expression *vaddr)
	{
		return new (allocator.alloc()) ExpressionLastStore(load, store, vaddr);
	}
	void visit(HeapVisitor &hv) const { hv(vaddr); }
	EventTimestamp timestamp() const { return load; }
	bool isLogical() const { return true; }
};
VexAllocTypeWrapper<ExpressionLastStore> ExpressionLastStore::allocator;

void History::splitAt(unsigned idx, History **firstBit, History **secondBit) const
{
	History *first;
	History *second;
	if (firstBit)
		first = History::get(first_valid_idx, tid);
	else
		first = NULL;
	unsigned long cntr = first_valid_idx;
	std::vector<HistorySegment *>::const_iterator it;
	for (it = history.begin();
	     it != history.end() && cntr < idx;
	     it++) {
		if (first)
			first->history.push_back(*it);
		cntr += (*it)->nr_memory_operations;
	}
	if (firstBit) {
		first->calc_last_valid_idx();
		*firstBit = first;
	}
	if (secondBit) {
		second = History::get(cntr, tid);
		for ( ;
		     it != history.end();
		     it++) {
			second->history.push_back(*it);
		}
		second->calc_last_valid_idx();
		*secondBit = second;
	}
}

static bool
syntax_check_expression(Expression *e, std::map<ThreadId, unsigned long> &last_valid_idx,
			EventTimestamp *why = NULL)
{
	if (dynamic_cast<ConstExpression *>(e) ||
	    dynamic_cast<ImportExpression *>(e))
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
		std::vector<HistorySegment *>::iterator it;
		std::map<ThreadId, unsigned long> new_last_valid_idx(last_valid_idx);
		unsigned long &idx_entry = new_last_valid_idx[er->tid];
		for (it = er->history->history.begin();
		     it != er->history->history.end();
		     it++) {
			HistorySegment *hs = *it;
			if (!syntax_check_expression(hs->condition,
						     new_last_valid_idx,
						     why))
				return false;
			idx_entry += hs->nr_memory_operations;
		}
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
	abort();
}

class ModelExtractor : public LogWriter<abstract_interpret_value> {
public:
	MemLog<abstract_interpret_value> *model;
private:
	const std::map<ThreadId, unsigned long> &horizon;
	std::map<ThreadId, unsigned long> seen_to;
	bool finished;
	ThreadId collectRipsTid;
	std::vector<unsigned long> *collected_rips;
	unsigned long stop_collecting_rips_idx;

	static const VexAllocTypeWrapper<ModelExtractor> allocator;
public:
	static void *operator new(size_t s)
	{
		return (void *)LibVEX_Alloc_Sized(&allocator.type, s);
	}
	void append(const LogRecord<abstract_interpret_value> &lr,
		    unsigned long idx);

	ModelExtractor(const std::map<ThreadId, unsigned long> &_horizon,
		       ThreadId tid,
		       std::vector<unsigned long> *rips,
		       unsigned long ripIdx)
		: model(MemLog<abstract_interpret_value>::emptyMemlog()),
		  horizon(_horizon),
		  seen_to(),
		  finished(false),
		  collectRipsTid(tid),
		  collected_rips(rips),
		  stop_collecting_rips_idx(ripIdx)
	{
	}
	void destruct() { this->~ModelExtractor(); }
	void visit(HeapVisitor &hv) const { hv(model); }
};
const VexAllocTypeWrapper<ModelExtractor> ModelExtractor::allocator;

template <typename k, typename v>
const v &hashget(const std::map<k,v> &m, const k &key)
{
	std::map<k,v> *non_const_m = 
		const_cast<std::map<k,v> *>(&m);
	return (*non_const_m)[key];
}

void ModelExtractor::append(const LogRecord<abstract_interpret_value> &lr,
			    unsigned long idx)
{
	if (lr.thread() == collectRipsTid &&
	    idx < stop_collecting_rips_idx) {
		const LogRecordFootstep<abstract_interpret_value> *lrf =
			dynamic_cast<const LogRecordFootstep<abstract_interpret_value> *>
			(&lr);
		if (lrf)
			collected_rips->push_back(lrf->rip.v);
	}
	if (finished)
		return;
	model->append(lr, idx);
	seen_to[lr.thread()] = idx;
	if (seen_to[lr.thread()] >= hashget(horizon, lr.thread())) {
		finished = true;
		for (std::map<ThreadId, unsigned long>::const_iterator it =
			     horizon.begin();
		     finished && it != horizon.end();
		     it++)
			if (seen_to[it->first] < it->second)
				finished = false;
	}
}

static LogReader<abstract_interpret_value> *
extract_model_exec(LogReader<abstract_interpret_value> *lf,
		   LogReaderPtr start,
		   const MachineState<abstract_interpret_value> *ms,
		   const std::map<ThreadId, unsigned long> &horizon,
		   LogReaderPtr *newStart,

		   ThreadId collectRipsForTid,
		   std::vector<unsigned long> *rips,
		   unsigned long stopCollectingRipsIdx)
{
	ModelExtractor *work = new ModelExtractor(horizon,
						  collectRipsForTid,
						  rips,
						  stopCollectingRipsIdx);
	VexGcRoot root((void **)&work, "modelextractor");
	
	Interpreter<abstract_interpret_value> i(ms->dupeSelf());
	i.replayLogfile(lf, start, NULL, work);

	*newStart = work->model->startPtr();
	return work->model;
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
		 const std::map<ThreadId, History *> &spare_histories,
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
		std::vector<HistorySegment *>::iterator it;
		std::map<ThreadId, unsigned long> new_last_valid_idx(last_valid_idx);
		std::map<ThreadId, History *> new_histories(spare_histories);
		HistoryMapHolder h(&new_histories);
		History *&threadSpareHistory = new_histories[er->tid];
		unsigned long &idx_entry = new_last_valid_idx[er->tid];
		for (it = er->history->history.begin();
		     it != er->history->history.end();
		     it++) {
			HistorySegment *hs = *it;
			EventTimestamp needed;
			if (!syntax_check_expression(hs->condition,
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
				   -- We then synthesise three
                                      suitable model executions.
				*/

				History *newOuterHist;
				History *newMiddleHist;
				History *newInnerHist;
				LogReader<abstract_interpret_value> *outerModel;
				LogReaderPtr outerStart;
				LogReader<abstract_interpret_value> *middleModel;
				LogReaderPtr middleStart;
				LogReader<abstract_interpret_value> *innerModel;
				LogReaderPtr innerStart;
				std::vector<unsigned long> outerRips;
				std::vector<unsigned long> middleRips;
				std::vector<unsigned long> innerRips;
				er->history->splitAt(idx_entry,
						     &newOuterHist,
						     &newInnerHist);

				/* Make sure that the roots go out of
				   scope before we recurse, or we risk
				   running out of roots. */
				{
					VexGcRoot r1((void **)&newOuterHist, "r1");
					VexGcRoot r2((void **)&newInnerHist, "r2");
					new_histories[needed.tid]->splitAt(needed.idx,
									   &newMiddleHist,
									   NULL);
					VexGcRoot r3((void **)&newMiddleHist, "r3");

					new_last_valid_idx[er->tid] = newOuterHist->last_valid_idx;
					outerModel = extract_model_exec(er->model_execution,
									er->model_exec_start,
									ms,
									new_last_valid_idx,
									&outerStart,
									er->tid,
									&outerRips,
									newOuterHist->first_valid_idx);
					VexGcRoot r4((void **)&outerModel, "r4");
					new_last_valid_idx[needed.tid] = newMiddleHist->last_valid_idx;
					middleModel = extract_model_exec(er->model_execution,
									 er->model_exec_start,
									 ms,
									 new_last_valid_idx,
									 &middleStart,
									 needed.tid,
									 &middleRips,
									 newMiddleHist->first_valid_idx);
					VexGcRoot r6((void **)&middleModel, "r6");
					new_last_valid_idx[er->tid] = newInnerHist->last_valid_idx;
					innerModel = extract_model_exec(er->model_execution,
									er->model_exec_start,
									ms,
									new_last_valid_idx,
									&innerStart,
									er->tid,
									&innerRips,
									newInnerHist->first_valid_idx);
				}

				/* Turn e into the outer history */
				er->history = newOuterHist;
				er->model_execution = outerModel;
				er->model_exec_start = outerStart;
				er->prefix_rips = outerRips;

				er->cond =
					ExpressionRip::get(
						needed.tid,
						newMiddleHist,
						ExpressionRip::get(
							er->tid,
							newInnerHist,
							er->cond,
							innerModel,
							innerStart,
							innerRips),
						middleModel,
						middleStart,
						middleRips);

				/* Run the check again on that. */
				fixup_expression(e, last_valid_idx, spare_histories, ms, global_lf, global_lf_start);
				return;
			}
			idx_entry += hs->nr_memory_operations;
		}
		threadSpareHistory->splitAt(idx_entry,
					    NULL,
					    &threadSpareHistory);
		fixup_expression(&er->cond, new_last_valid_idx,
				 new_histories, ms, global_lf, global_lf_start);
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
			History *newHistory;
			LogReader<abstract_interpret_value> *newModel;
			LogReaderPtr modelStart;
			std::map<ThreadId, unsigned long> new_last_valid_idx(last_valid_idx);
			std::vector<unsigned long> rips;

			spare_histories.find(when.tid)->second->splitAt(when.idx,
									&newHistory,
									NULL);
			{
				VexGcRoot r5((void **)&newHistory, "r5");
				new_last_valid_idx[when.tid] = newHistory->last_valid_idx;
				newModel = extract_model_exec(global_lf,
							      global_lf_start,
							      ms,
							      new_last_valid_idx,
							      &modelStart,
							      when.tid,
							      &rips,
							      newHistory->first_valid_idx);
			}
			*e = ExpressionRip::get(when.tid,
						newHistory,
						le,
						newModel,
						modelStart,
						rips);
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

	History *operator[](ThreadId tid)
	{
		std::map<ThreadId, History *>::iterator it = thread_histories.find(tid);
		if (it == thread_histories.end()) {
			History *r = History::get(0, tid);
			thread_histories[tid] = r;
			return r;
		} else {
			return it->second;
		}
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
};
VexAllocTypeWrapper<CrashReasonExtractor> CrashReasonExtractor::allocator;
void CrashReasonExtractor::record(Thread<abstract_interpret_value> *_thr, const ThreadEvent<abstract_interpret_value> *evt)
{
	if (const InstructionEvent<abstract_interpret_value> *fe =
	    dynamic_cast<const InstructionEvent<abstract_interpret_value> *>(evt)) {
		unsigned long c;
		if (!fe->rip.origin->isConstant(&c))
			(*this)[_thr->tid]->control_expression(
				evt->when,
				equals::get(fe->rip.origin, ConstExpression::get(fe->rip.v)));
		(*this)[_thr->tid]->footstep(fe->rip.v);
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
		it->second->finish(ms2->findThread(it->first)->lastEvent);
		it->second->calc_last_valid_idx();
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
	std::vector<unsigned long> t;
	if (force(extr->thr->regs.rip() == extr->signal->virtaddr))
		res = ExpressionRip::get(extr->thr->tid, (*extr)[extr->thr->tid],
					 equals::get(extr->thr->regs.rip().origin,
						     ConstExpression::get(extr->thr->regs.rip().v)),
					 script,
					 ptr,
					 t);
	else
		res = ExpressionRip::get(extr->thr->tid, (*extr)[extr->thr->tid],
					 ExpressionBadPointer::get(extr->signal->when, extr->signal->virtaddr.origin),
					 script,
					 ptr,
					 t);

	VexGcRoot root2((void **)&res, "root2");
	fixup_expression(&res,
			 std::map<ThreadId, unsigned long>(),
			 extr->thread_histories,
			 ms,
			 script,
			 ptr);
	return res;
}

static Expression *refine(Expression *expr,
			  const MachineState<abstract_interpret_value> *ms,
			  LogReader<abstract_interpret_value> *lf,
			  LogReaderPtr ptr,
			  bool *progress);

/* We refine a RIP expression by just splitting the very last segment
   off of the history and turning it into a direct expression. */
static Expression *refine(ExpressionRip *er,
			  const MachineState<abstract_interpret_value> *ms,
			  LogReader<abstract_interpret_value> *lf,
			  LogReaderPtr ptr,
			  bool *progress)
{
	printf("Refine %s\n", er->name());

	/* Try to refine the subcondition first, since that's usually
	 * cheaper. */
	Expression *newSubCond;
	bool subCondProgress = false;
	newSubCond = refine(er->cond, ms, lf, ptr, &subCondProgress);
	if (subCondProgress) {
		/* Yay. */
		*progress = true;
		return ExpressionRip::get(
			er->tid,
			er->history,
			newSubCond,
			er->model_execution,
			er->model_exec_start,
			er->prefix_rips);
	}

	/* Okay, done as much as we can here.  Go back to previous
	   conditional branch. */

	if (er->history->history.size() == 1) {
		/* Okay, there were no previous conditional branches.
		   We're doomed. */
		return er;
	}

	std::vector<HistorySegment *>::const_iterator start =
		er->history->history.begin();
	std::vector<HistorySegment *>::const_iterator end =
		er->history->history.end();
	end--;

	History *newHist = History::get(start, end, er->history->first_valid_idx,
					er->history->tid);
	LogReaderPtr newPtr;
	LogReaderPtr newPtr2;
	LogReader<abstract_interpret_value> *newModel;
	LogReader<abstract_interpret_value> *newModel2;

	std::vector<unsigned long> newPrefix;
	newHist->extractSubModel(er->tid, ms, er->prefix_rips, lf, ptr, &newModel, &newPtr,
				 &newModel2, &newPtr2, &newPrefix);
	*progress = true;

	return ExpressionRip::get(
		er->tid,
		newHist,
		logicaland::get((*end)->condition,
				ExpressionRip::get(er->tid,
						   History::get((*end)->rips,
								(*end)->nr_memory_operations,
								er->history->last_valid_idx -
								(*end)->nr_memory_operations,
								er->history->tid),
						   er->cond,
						   newModel2,
						   newPtr2,
						   newPrefix)),
		newModel,
		newPtr,
		er->prefix_rips);
}

/* We handle precisely one interesting case when refining ==:
   
   (load@L:S la:sa -> val) == R

   becomes

   laststore(L,S,la) && (la == sa) && (val == R)

   i.e. in order for the load to be satisfied by the store, the store
   has to be the last write to the load address, and the load and
   store virtual addresses have to match up.  This allows us to
   ``unwrap'' the load expression, so the meat of the expression is
   just val == R.
*/
static Expression *
refine(equals *eq, 
       const MachineState<abstract_interpret_value> *ms,
       LogReader<abstract_interpret_value> *lf,
       LogReaderPtr ptr,
       bool *progress)
{
	if (LoadExpression *le = dynamic_cast<LoadExpression *>(eq->l)) {
		*progress = true;
		return logicaland::get(
			ExpressionLastStore::get(le->when, le->store, le->addr),
			logicaland::get(
				equals::get(le->addr, le->storeAddr),
				equals::get(le->val, eq->r)));
	}
	return eq;
}

Expression *refine(Expression *expr,
		   const MachineState<abstract_interpret_value> *ms,
		   LogReader<abstract_interpret_value> *lf,
		   LogReaderPtr ptr,
		   bool *progress)
{
	if (ExpressionRip *er = dynamic_cast<ExpressionRip *>(expr)) {
		return refine(er, ms, lf, ptr, progress);
	} else if (equals *eq = dynamic_cast<equals *>(expr)) {
		return refine(eq, ms, lf, ptr, progress);
	} else {
		printf("Cannot refine %s\n", expr->name());
		return expr;
	}
}

class HistoryLogTruncater : public LogWriter<abstract_interpret_value> {
	History *hist;
	std::vector<HistorySegment *>::iterator current_history_segment;
	unsigned current_segment_index;
	ThreadId desired_thread;
	static const VexAllocTypeWrapper<HistoryLogTruncater> allocator;
	const std::vector<unsigned long> &prefix_rips;
	unsigned prefix_rips_idx;
	std::vector<unsigned long> *prefix_rips_out;
public:
	static void *operator new(size_t s)
	{
		return (void *)LibVEX_Alloc_Sized(&allocator.type, s);
	}
	MemLog<abstract_interpret_value> *model1;
	MemLog<abstract_interpret_value> *model2;
	bool finishedFirstPhase;
	void append(const LogRecord<abstract_interpret_value> &lr,
		    unsigned long idx);
	HistoryLogTruncater(ThreadId tid, History *_hist,
			    const std::vector<unsigned long> &_prefix_rips,
			    std::vector<unsigned long> *_prefix_rips_out)
		: hist(_hist),
		  current_history_segment(hist->history.begin()),
		  current_segment_index(0),
		  desired_thread(tid),
		  prefix_rips(_prefix_rips),
		  prefix_rips_idx(0),
		  prefix_rips_out(_prefix_rips_out),
		  model1(MemLog<abstract_interpret_value>::emptyMemlog()),
		  model2(MemLog<abstract_interpret_value>::emptyMemlog()),
		  finishedFirstPhase(false)
	{
	}
	void destruct() { this->~HistoryLogTruncater(); }
	void visit(HeapVisitor &hv) const { hv(hist); hv(model1); hv(model2); }
};
const VexAllocTypeWrapper<HistoryLogTruncater> HistoryLogTruncater::allocator;

void HistoryLogTruncater::append(const LogRecord<abstract_interpret_value> &lr,
				 unsigned long idx)
{
	while (!finishedFirstPhase &&
	       current_segment_index ==
	       (*current_history_segment)->rips.size()) {
		current_segment_index = 0;
		current_history_segment++;
		if (current_history_segment == hist->history.end())
			finishedFirstPhase = true;
	}

	if (finishedFirstPhase) {
		model2->append(lr, idx);
		return;
	}

	if (lr.thread() == desired_thread) {
		const LogRecordFootstep<abstract_interpret_value> *lrf =
			dynamic_cast<const LogRecordFootstep<abstract_interpret_value> *>(&lr);
		if (lrf) {
			prefix_rips_out->push_back(lrf->rip.v);
			if (prefix_rips_idx < prefix_rips.size()) {
				assert(lrf->rip.v == prefix_rips[prefix_rips_idx]);
				prefix_rips_idx++;
			} else {
				assert(lrf->rip.v ==
				       (*current_history_segment)->rips[current_segment_index]);
				current_segment_index++;
			}
		}
	}

	return model1->append(lr, idx);
}
void History::extractSubModel(
	ThreadId tid,
	const MachineState<abstract_interpret_value> *ms,
	const std::vector<unsigned long> &discardRips,
	LogReader<abstract_interpret_value> *lf,
	LogReaderPtr ptr,
	LogReader<abstract_interpret_value> **newModel,
	LogReaderPtr *newPtr,
	LogReader<abstract_interpret_value> **newModel2,
	LogReaderPtr *newPtr2,
	std::vector<unsigned long> *newRips)
{
	HistoryLogTruncater *work = new HistoryLogTruncater(tid, this, discardRips, newRips);
	VexGcRoot root((void **)&work, "extractSubModel");

	Interpreter<abstract_interpret_value> i(ms->dupeSelf());
	i.replayLogfile(lf, ptr, NULL, work);

	*newModel = work->model1;
	*newPtr = work->model1->startPtr();
	*newModel2 = work->model2;
	*newPtr2 = work->model2->startPtr();
}

int
main(int argc, char *argv[])
{
	init_sli();

	LogFile *lf;
	LogReaderPtr ptr;

	lf = LogFile::open(argv[1], &ptr);
	if (!lf)
		err(1, "opening %s", argv[1]);
	VexGcRoot logroot((void **)&lf, "logroot");

	MachineState<unsigned long> *concrete = MachineState<unsigned long>::initialMachineState(lf, ptr, &ptr);
	MachineState<abstract_interpret_value> *abstract = concrete->abstract<abstract_interpret_value>();
	VexGcRoot keeper((void **)&abstract, "keeper");

	LogReader<abstract_interpret_value> *al = lf->abstract<abstract_interpret_value>();
	VexGcRoot al_keeper((void **)&al, "al_keeper");

	Expression *cr = getCrashReason(abstract->dupeSelf(), al, ptr);
	printf("%s\n", cr->name());
	std::map<ThreadId, unsigned long> m1;
	VexGcRoot crkeeper((void **)&cr, "crkeeper");

	bool progress;

	do {
		progress = false;
		printf("Crash reason %s\n", cr->name());
		if (!syntax_check_expression(cr, m1)) {
			fixup_expression(&cr,
					 std::map<ThreadId, unsigned long>(),
					 std::map<ThreadId, History *>(),
					 abstract,
					 al,
					 ptr);
			printf("Post fixup %s\n", cr->name());
			assert(syntax_check_expression(cr, m1));
		}
		cr = refine(cr, abstract, al, ptr, &progress);
	} while (progress);
	printf("Crash reason %s\n", cr->name());

	return 0;
}
