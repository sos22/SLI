#ifndef enforceCrash_hpp__
#define enforceCrash_hpp__

#include <set>
#include <map>
#include "libvex_ir.h"
#include "libvex_parse.h"
#include "genfix.hpp"
#include "dnf.hpp"
#include "offline_analysis.hpp"
#include "intern.hpp"
#include "inferred_information.hpp"

class CrashCfg;
class crashEnforcementRoots;

class SummaryId : public Named {
	static unsigned next_id;
	unsigned id;
	char *mkName() const {
		return my_asprintf("%d", id);
	}
public:
	static SummaryId uninitialised()
	{
		return SummaryId(-1);
	}
	explicit SummaryId(unsigned _id)
		: id(_id)
	{}
	bool parse(const char *str, const char **suffix)
	{
		if (!parseDecimalUInt(&id, str, suffix))
			return false;
		clearName();
		return true;
	}
	bool operator==(const SummaryId &o) const
	{
		return id == o.id;
	}
	bool operator<(const SummaryId &o) const
	{
		return id < o.id;
	}
	unsigned long hash() const
	{
		return id * 10114771ul;
	}
};

class ConcreteThread : public Named {
	SummaryId summary_id;
	unsigned id;

	char *mkName() const {
		return my_asprintf("T%s:%d", summary_id.name(), id);
	}
public:
	ConcreteThread(const SummaryId &_summary_id, unsigned _id)
		: summary_id(_summary_id), id(_id)
	{}
	static ConcreteThread uninitialised() {
		return ConcreteThread(SummaryId::uninitialised(), -1);
	}
	bool parse(const char *str, const char **suffix)
	{
		clearName();
		if (!parseThisChar('T', str, &str) ||
		    !summary_id.parse(str, &str) ||
		    !parseThisChar(':', str, &str) ||
		    !parseDecimalUInt(&id, str, suffix))
			return false;
		return true;
	}
	bool operator==(const ConcreteThread &o) const
	{
		return summary_id == o.summary_id && id == o.id;
	}
	bool operator<(const ConcreteThread &o) const
	{
		return summary_id < o.summary_id ||
			(summary_id == o.summary_id && id < o.id);
	}
	unsigned long hash() const
	{
		return id * 10113569ul + summary_id.hash() * 10118387ul;
	}
	const SummaryId &summary() const { return summary_id; }
};

class AbstractThread : public Named {
	friend class ThreadAbstracter;
	char *mkName() const {
		return my_asprintf("t%d", id);
	}
	AbstractThread(unsigned _id)
		: id(_id)
	{}
	unsigned id;
public:
	AbstractThread(const AbstractThread &o)
		: id (o.id)
	{}
	static AbstractThread uninitialised() {
		return AbstractThread(-1);
	}
	bool parse(const char *str, const char **suffix)
	{
		if (!parseThisChar('t', str, &str) ||
		    !parseDecimalUInt(&id, str, suffix))
			return false;
		clearName();
		return true;
	}
	bool operator==(const AbstractThread &o) const
	{
		return id == o.id;
	}
	bool operator<(const AbstractThread &o) const
	{
		return id < o.id;
	}
	unsigned long hash() const
	{
		return id * 10113109ul;
	}
};

class ConcreteCfgLabel : public Named {
	char *mkName() const {
		return my_asprintf("%s:%s", summary.name(), label.name());
	}
public:
	SummaryId summary;
	CfgLabel label;
	ConcreteCfgLabel(const SummaryId &_summary, const CfgLabel &_label)
		: summary(_summary), label(_label)
	{}
	ConcreteCfgLabel()
		: summary(SummaryId::uninitialised()), label(CfgLabel::uninitialised())
	{}
	bool operator <(const ConcreteCfgLabel &o) const {
		return summary < o.summary ||
			(summary == o.summary && label < o.label);
	}
	bool operator!=(const ConcreteCfgLabel &o) const {
		return (*this < o) || (o < *this);
	}
	bool operator==(const ConcreteCfgLabel &o) const {
		return !(*this != o);
	}
	unsigned long hash() const {
		return summary.hash() * 10120421 + label.hash() * 10123909;
	}
	bool parse(const char *str, const char **suffix) {
		CfgLabel l(CfgLabel::uninitialised());
		SummaryId t(SummaryId::uninitialised());
		if (t.parse(str, &str) &&
		    parseThisChar(':', str, &str) &&
		    l.parse(str, suffix)) {
			label = l;
			summary = t;
			clearName();
			return true;
		}
		return false;
	}
};

class ThreadCfgLabel : public Named {
	char *mkName() const {
		return my_asprintf("%s:%s", label.name(), thread.name());
	}
public:
	AbstractThread thread;
	CfgLabel label;
	ThreadCfgLabel(const AbstractThread &_thread, const CfgLabel &_label)
		: thread(_thread), label(_label)
	{}
	ThreadCfgLabel()
		: thread(AbstractThread::uninitialised()), label(CfgLabel::uninitialised())
	{}
	bool operator <(const ThreadCfgLabel &o) const {
		return thread < o.thread ||
			(thread == o.thread && label < o.label);
	}
	bool operator!=(const ThreadCfgLabel &o) const {
		return (*this < o) || (o < *this);
	}
	bool operator==(const ThreadCfgLabel &o) const {
		return !(*this != o);
	}
	unsigned long hash() const {
		return thread.hash() * 874109 + label.hash() * 877939;
	}
	bool parse(const char *str, const char **suffix) {
		CfgLabel l(CfgLabel::uninitialised());
		AbstractThread t(AbstractThread::uninitialised());
		if (l.parse(str, &str) &&
		    parseThisChar(':', str, &str) &&
		    t.parse(str, suffix)) {
			label = l;
			thread = t;
			clearName();
			return true;
		}
		return false;
	}
};

class ThreadAbstracter {
	std::map<ConcreteThread, std::set<AbstractThread> > content;
	AbstractThread nxtThread;
public:
	ThreadAbstracter()
		: nxtThread(1)
	{}
	class iterator {
		std::set<AbstractThread>::const_iterator it;
		std::set<AbstractThread>::const_iterator endIt;
	public:
		iterator(const std::set<AbstractThread> &a)
			: it(a.begin()), endIt(a.end())
		{}
		bool finished() const { return it == endIt; }
		void advance() { it++; }
		AbstractThread get() const { return *it; }

		iterator(double, double, double) {}
	};
	iterator begin(const ConcreteThread &tid) const {
		auto it = content.find(tid);
		assert(it != content.end());
		return iterator(it->second);
	}
	AbstractThread newThread(const ConcreteThread &oldTid)
	{
		AbstractThread res = nxtThread;
		nxtThread.id++;
		content[oldTid].insert(res);
		return res;
	}
	class thread_cfg_iterator {
		iterator content;
		CfgLabel where;
	public:
		thread_cfg_iterator(const iterator &_content, const CfgLabel &_where)
			: content(_content), where(_where)
		{}
		bool finished() const { return content.finished(); }
		void advance() { content.advance(); }
		ThreadCfgLabel get() const { return ThreadCfgLabel(content.get(), where); }

		/* Should only be used by mai_iterator */
		thread_cfg_iterator(double, double, double)
			: content(1.0, 1.0, 1.0),
			  where(CfgLabel::uninitialised())
		{}
	};
	thread_cfg_iterator begin(const ConcreteThread &tid, const CfgLabel &where) const
	{
		return thread_cfg_iterator( begin(tid), where);
	}

	class mai_iterator {
		MaiMap::const_iterator hl_iter;
		thread_cfg_iterator ll_iter;
		bool _finished;
		ThreadCfgLabel current_item;
		ConcreteThread tid;
		ThreadAbstracter *_this;
	public:
		bool finished() const { return _finished; }
		void advance() {
			if (hl_iter.finished()) {
				_finished = true;
				return;
			}
			assert(!ll_iter.finished());
			current_item = ll_iter.get();
			ll_iter.advance();
			if (!ll_iter.finished())
				return;
			while (1) {
				hl_iter.advance();
				if (hl_iter.finished())
					return;
				ll_iter = _this->begin(tid, hl_iter.label());
				if (!ll_iter.finished())
					return;
				ll_iter.advance();
			}
		}
		mai_iterator(const SummaryId &summary, const MaiMap &mai, const MemoryAccessIdentifier &rip, ThreadAbstracter *__this)
			: hl_iter(mai.begin(rip)),
			  ll_iter(1.0, 1.0, 1.0),
			  _finished(false),
			  tid(ConcreteThread(summary, rip.tid)),
			  _this(__this)
		{
			if (hl_iter.finished()) {
				_finished = true;
				return;
			}
			ll_iter = _this->begin(tid, hl_iter.label());
			while (ll_iter.finished()) {
				hl_iter.advance();
				if (hl_iter.finished()) {
					_finished = true;
					return;
				}
				ll_iter = _this->begin(tid, hl_iter.label());
			}
			advance();
		}
		ThreadCfgLabel get() const { return current_item; }
	};
	mai_iterator begin(const SummaryId &summary, const MaiMap &mai, const MemoryAccessIdentifier &rip)
	{
		return mai_iterator(summary, mai, rip, this);
	}

	class instr_iterator {
		mai_iterator underlying;
		CrashCfg &cfg;
	public:
		bool finished() const { return underlying.finished(); }
		void advance() { underlying.advance(); }
		Instruction<ThreadCfgLabel> *get() const;
		instr_iterator(const mai_iterator &_underlying, CrashCfg &_cfg)
			: underlying(_underlying), cfg(_cfg)
		{}
	};
	instr_iterator begin(const SummaryId &summary, const MaiMap &mai, const MemoryAccessIdentifier &rip, CrashCfg &cfg)
	{
		return instr_iterator(begin(summary, mai, rip), cfg);
	}
};

void enumerateNeededExpressions(IRExpr *e, std::set<IRExpr *> &out);

struct exprEvalPoint;
class happensBeforeEdge;

class internmentState {
public:
	std::set<happensBeforeEdge *> hbes;
	internStateMachineTable exprs;
	IRExpr *intern(IRExpr *e) { return internIRExpr(e, exprs); }
	IRExprGet *intern(IRExprGet *e) {
		IRExpr *res = internIRExpr(e, exprs);
		assert(res->tag == Iex_Get);
		return (IRExprGet *)res;
	}
	AbstractThread intern(const AbstractThread &x) { return x; }
	exprEvalPoint intern(const exprEvalPoint &);
	template <typename a, typename b> std::pair<a, b> intern(const std::pair<a, b> &x) {
		return std::pair<a, b>(intern(x.first), intern(x.second));
	}
	template <typename a> std::set<a> intern(const std::set<a> &x) {
		std::set<a> out;
		for (auto it = x.begin(); it != x.end(); it++)
			out.insert(intern(*it));
		return out;
	}
	template <typename a> std::vector<a> intern(const std::vector<a> &in) {
		std::vector<a> out;
		out.reserve(in.size());
		for (auto it = in.begin(); it != in.end(); it++)
			out.push_back(intern(*it));
		return out;
	}
};

class instrToInstrSetMap : public std::map<Instruction<ThreadCfgLabel> *, std::set<Instruction<ThreadCfgLabel> *> > {
public:
	void print(FILE *f) const;
};

/* Map from instructions to instructions which happen immediately
   before them, including those ordered by happens-before
   relationships. */
class predecessorMapT : public instrToInstrSetMap {
public:
	predecessorMapT() {}
	predecessorMapT(CrashCfg &cfg);
};

/* An encoding of the happens-before edges in a DNF clause into a map
   over Instructions. */
class happensAfterMapT {
public:
	/* happensBefore[i] -> the set of all instructions ordered before i */
	instrToInstrSetMap happensBefore;
	/* happensBefore[i] -> the set of all instructions ordered after i */
	instrToInstrSetMap happensAfter;
	happensAfterMapT(const SummaryId &summary, DNF_Conjunction &c, ThreadAbstracter &abs, CrashCfg &cfg, const MaiMap &mai);
	happensAfterMapT() {}
	void print(FILE *f) {
		fprintf(f, "before:\n");
		happensBefore.print(f);
		fprintf(f, "after:\n");
		happensAfter.print(f);
	}
};

/* A map from Instruction * to the set of instructions which must
 * complete before that instruction, based purely on the control flow
 * graph. */
class instructionDominatorMapT : public instrToInstrSetMap {
public:
	instructionDominatorMapT(CrashCfg &cfg,
				 predecessorMapT &predecessors,
				 happensAfterMapT &happensAfter);
	instructionDominatorMapT() {}
};

class expressionStashMapT : public std::map<ThreadCfgLabel, std::set<IRExpr *> >,
			    private GcCallback<&ir_heap> {
	void runGc(HeapVisitor &hv) {
		for (auto it = begin(); it != end(); it++) {
			std::vector<IRExpr *> f(it->second.begin(), it->second.end());
			for (auto it2 = f.begin(); it2 != f.end(); it2++)
				hv(*it2);
			it->second.clear();
			it->second.insert(f.begin(), f.end());
		}
	}
public:
	expressionStashMapT() {}
	expressionStashMapT(const SummaryId &summary,
			    std::set<IRExpr *> &neededExpressions,
			    ThreadAbstracter &abs,
			    StateMachine *probeMachine,
			    StateMachine *storeMachine,
			    crashEnforcementRoots &roots,
			    const MaiMap &mai);

	void operator|=(const expressionStashMapT &esm) {
		for (auto it = esm.begin(); it != esm.end(); it++) {
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				(*this)[it->first].insert(*it2);
		}
	}
	bool parse(const char *str, const char **suffix) {
		if (!parseThisString("Stash map:\n", str, &str))
			return false;
		clear();
		while (1) {
			ThreadCfgLabel where;
			if (!where.parse(str, &str) ||
			    !parseThisString(" -> {", str, &str))
				break;
			std::set<IRExpr *> b;
			while (1) {
				IRExpr * s;
				if (!parseIRExpr(&s, str, &str) ||
				    !parseThisString(", ", str, &str))
					break;
				b.insert(s);
			}
			if (!parseThisString("}\n", str, &str))
				return false;
			assert(b.size() > 0);
			(*this)[where] = b;
		}
		*suffix = str;
		return true;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "\tStash map:\n");
		for (auto it = begin(); it != end(); it++) {
			fprintf(f, "\t\t%s -> {", it->first.name());
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				(*it2)->prettyPrint(f);
				fprintf(f, ", ");
			}
			fprintf(f, "}\n");
		}
	}
	void internSelf(internmentState &state) {
		for (auto it = begin(); it != end(); it++) {
			std::set<IRExpr *> out;
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				out.insert(state.intern(*it2));
			it->second = out;
		}
	}
};

class expressionDominatorMapT : public std::map<Instruction<ThreadCfgLabel> *, std::set<std::pair<bool, IRExpr *> > > {
	class trans1 : public IRExprTransformer {
		std::set<IRExpr *> &availExprs;
		void failed() {
			isGood = false;
			abortTransform();
		}
		IRExpr *transformIex(IRExprGet *e) {
			if (!availExprs.count(e))
				failed();
			return NULL;
		}
		IRExpr *transformIex(IRExprHappensBefore *) {
			failed();
			return NULL;
		}
		IRExpr *transformIex(IRExprEntryPoint *e) {
			if (!availExprs.count(e))
				failed();
			return NULL;
		}
		IRExpr *transformIex(IRExprControlFlow *e) {
			if (!availExprs.count(e))
				failed();
			return NULL;
		}
	public:
		bool isGood;
		trans1(std::set<IRExpr *> &_availExprs)
			: availExprs(_availExprs),
			  isGood(true)
		{}
	};
	static bool evaluatable(IRExpr *e,
				std::set<IRExpr *> &availExprs) {
		trans1 t(availExprs);
		t.doit(e);
		return t.isGood;
	}
public:
	expressionDominatorMapT() {};
	expressionDominatorMapT(DNF_Conjunction &,
				expressionStashMapT &,
				instructionDominatorMapT &,
				predecessorMapT &,
				happensAfterMapT &);
	void prettyPrint(FILE *f) const;
};

class simulationSlotT {
public:
	int idx;
	simulationSlotT(int _idx) : idx(_idx) {}
	simulationSlotT() : idx(-10000) {}
	bool operator<(const simulationSlotT &o) const { return idx < o.idx; }
};

template <typename src, typename dest> void
setToVector(const std::set<src> &in, std::vector<dest> &out)
{
	out.reserve(in.size());
	for (typename std::set<src>::iterator it = in.begin();
	     it != in.end();
	     it++)
		out.push_back(*it);
}

template <typename t> void
visit_set(std::set<t> &s, HeapVisitor &hv)
{
	/* Ugg, can't just visit a set of GC'd
	   pointers because it rearranges them, so
	   have to do it via a vector. */
	std::vector<t> n;
	setToVector(s, n);
	visit_container(n, hv);
	s.clear();
	for (auto it2 = n.begin(); it2 != n.end(); it2++)
		s.insert(*it2);
}

class happensBeforeEdge : public GarbageCollected<happensBeforeEdge, &ir_heap>, public Named {
	happensBeforeEdge(Instruction<ThreadCfgLabel> *_before,
			  Instruction<ThreadCfgLabel> *_after,
			  const std::vector<IRExpr *> &_content,
			  unsigned _msg_id)
		: before(_before), after(_after), content(_content), msg_id(_msg_id)
	{}
	char *mkName() const {
		std::vector<const char *> fragments;
		fragments.push_back(my_asprintf(
					    "%d: %s <-< %s {",
					    msg_id,
					    before->rip.name(),
					    after->rip.name()));
		for (auto it = content.begin(); it != content.end(); it++) {
			fragments.push_back(nameIRExpr(*it));
			fragments.push_back(", ");
		}
		fragments.push_back("}");

		char *res_vex = flattenStringFragments(fragments);
		char *res_malloc = strdup(res_vex);
		_LibVEX_free(&main_heap, res_vex);
		free((void *)fragments[0]);
		for (unsigned x = 1; x < fragments.size() - 1; x += 2)
			_LibVEX_free(&main_heap, (void *)fragments[x]);
		return res_malloc;
	}
public:
	Instruction<ThreadCfgLabel> *before;
	Instruction<ThreadCfgLabel> *after;
	std::vector<IRExpr *> content;
	unsigned msg_id;

	happensBeforeEdge *intern(internmentState &state) {
		content = state.intern(content);
		for (auto it = state.hbes.begin(); it != state.hbes.end(); it++) {
			if ( (*it)->msg_id == msg_id &&
			     (*it)->before == before &&
			     (*it)->after == after &&
			     (*it)->content == content )
				return (*it);
		}
		state.hbes.insert(this);
		return this;
	}
	happensBeforeEdge(Instruction<ThreadCfgLabel> *_before,
			  Instruction<ThreadCfgLabel> *_after,
			  instructionDominatorMapT &idom,
			  expressionStashMapT &stashMap,
			  unsigned _msg_id)
		: before(_before),
		  after(_after),
		  msg_id(_msg_id)
	{
		std::set<Instruction<ThreadCfgLabel> *> &liveInstructions(
			idom[before]);
		for (auto it = liveInstructions.begin();
		     it != liveInstructions.end();
		     it++) {
			auto *i = *it;
			std::set<IRExpr *> &exprs(stashMap[i->rip]);
			for (auto it2 = exprs.begin();
			     it2 != exprs.end();
			     it2++)
				content.push_back(*it2);
		}
	}

	void prettyPrint(FILE *f) const {
		fprintf(f, "%s", name());
	}
	static happensBeforeEdge *parse(CrashCfg &cfg, const char *str, const char **suffix);
	void visit(HeapVisitor &hv) {
		visit_container(content, hv);
	}
	NAMED_CLASS
};

class slotMapT : public std::map<IRExpr *, simulationSlotT>,
		 private GcCallback<&ir_heap> {
	void mk_slot(IRExpr *e, simulationSlotT &next_slot) {
		if (!count(e))
			insert(std::pair<IRExpr *, simulationSlotT>(e, allocateSlot(next_slot)));
	}
	void runGc(HeapVisitor &hv) {
		slotMapT n(*this);
		clear();
		for (auto it = n.begin(); it != n.end(); it++) {
			IRExpr *e = it->first;
			hv(e);
			insert(std::pair<IRExpr *, simulationSlotT>(e, it->second));
		}
	}
public:
	simulationSlotT rflagsSlot() {
		return simulationSlotT(0);
	}
	simulationSlotT allocateSlot(simulationSlotT &next_slot) {
		simulationSlotT r = next_slot;
		next_slot.idx++;
		return r;
	}

	simulationSlotT operator()(IRExpr *e) const {
		auto it = find(e);
		assert(it != end());
		return it->second;
	}

	void internSelf(internmentState &state) {
		std::map<IRExpr *, simulationSlotT> work;
		for (auto it = begin(); it != end(); it++)
			work[state.intern(it->first)] = it->second;
		clear();
		insert(work.begin(), work.end());
	}

	slotMapT() { }

	slotMapT(std::map<ThreadCfgLabel, std::set<IRExpr *> > &neededExpressions,
		 std::map<ThreadCfgLabel, std::set<happensBeforeEdge *> > &happensBefore)
	{
		simulationSlotT next_slot(1);
		/* Allocate slots for expressions which we know we're
		 * going to have to stash at some point. */
		for (auto it = neededExpressions.begin();
		     it != neededExpressions.end();
		     it++) {
			std::set<IRExpr *> &s((*it).second);
			for (auto it2 = s.begin(); it2 != s.end(); it2++)
				mk_slot(*it2, next_slot);
		}
		/* That should also cover all of the stuff we're going
		   to receive over HB edges: if we receive it then
		   someone must have stashed it, and we'll have
		   allocated a slot at the stash point. */
		for (auto it = happensBefore.begin();
		     it != happensBefore.end();
		     it++) {
			std::set<happensBeforeEdge *> &s(it->second);
			for (std::set<happensBeforeEdge *>::iterator it2 = s.begin();
			     it2 != s.end();
			     it2++) {
				happensBeforeEdge *hb = *it2;
				for (unsigned x = 0; x < hb->content.size(); x++)
					assert(count(hb->content[x]));
			}
		}
	}

	void operator|=(const slotMapT &sm) {
		for (auto it = sm.begin(); it != sm.end(); it++)
			if (!count(it->first))
				insert(*it);
	}

	void prettyPrint(FILE *f) const {
		fprintf(f, "\tSlot map:\n");
		for (auto it = begin(); it != end(); it++) {
			fprintf(f, "\t\t");
			it->first->prettyPrint(f);
			fprintf(f, " -> %d\n", it->second.idx);
		}
	}
	bool parse(const char *str, const char **suffix) {
		if (!parseThisString("Slot map:\n", str, &str))
			return false;
		clear();
		while (1) {
			simulationSlotT value;
			IRExpr *k;
			if (!parseIRExpr(&k, str, &str) ||
			    !parseThisString(" -> ", str, &str) ||
			    !parseDecimalInt(&value.idx, str, &str) ||
			    !parseThisChar('\n', str, &str))
				break;
			(*this)[k] = value;
		}
		*suffix = str;
		return true;
	}
};

/* Note that this needs manual visiting (from the IR heap), despite
 * not being GC allocated itself! */
struct exprEvalPoint {
	bool invert;
	IRExpr *e;

	void visit(HeapVisitor &hv) {
		hv(e);
	}

	exprEvalPoint(bool _invert,
		      IRExpr *_e)
		: invert(_invert), e(_e)
	{}
	bool operator <(const exprEvalPoint &o) const {
		if (invert < o.invert)
			return true;
		if (o.invert < invert)
			return false;
		return e < o.e;
	}

	void prettyPrint(FILE *f) const {
		fprintf(f, "%s", invert ? "!" : "");
		e->prettyPrint(f);
	}
	bool parse(const char *str, const char **suffix) {
		bool inv = false;
		if (parseThisChar('!', str, &str))
			inv = true;
		if (!parseIRExpr(&e, str, &str))
			return false;
		invert = inv;
		*suffix = str;
		return true;
	}

	/* partially instantiating an exprEvalPoint is bad news, but
	   it's okay if done temporarily before calling parse().
	   Discourage people from hitting it by accident. */
	class YesIReallyMeanIt {};
	exprEvalPoint(const YesIReallyMeanIt &) {}
};

class expressionEvalMapT : public std::map<ThreadCfgLabel, std::set<exprEvalPoint> >,
			   private GcCallback<&ir_heap> {
	void runGc(HeapVisitor &hv) {
		for (auto it = begin(); it != end(); it++) {
			std::vector<exprEvalPoint> n;
			setToVector(it->second, n);
			it->second.clear();
			for (auto it2 = n.begin(); it2 != n.end(); it2++) {
				it2->visit(hv);
				it->second.insert(*it2);
			}
		}
	}
public:

	void internSelf(internmentState &state) {
		for (auto it = begin(); it != end(); it++)
			it->second = state.intern(it->second);
	}

	expressionEvalMapT(expressionDominatorMapT &exprDominatorMap) {
		for (expressionDominatorMapT::iterator it = exprDominatorMap.begin();
		     it != exprDominatorMap.end();
		     it++) {
			for (std::set<std::pair<bool, IRExpr *> >::iterator it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++)
				(*this)[it->first->rip].insert(
					exprEvalPoint(
						it2->first,
						it2->second));
		}
	}
	expressionEvalMapT() {}
	void operator|=(const expressionEvalMapT &eem) {
		for (auto it = eem.begin(); it != eem.end(); it++)
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				(*this)[it->first].insert(*it2);
	}

	void prettyPrint(FILE *f) const {
		fprintf(f, "\tEval map:\n");
		for (auto it = begin(); it != end(); it++) {
			fprintf(f, "\t\t%s -> {", it->first.name());
			for (auto it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++) {
				it2->prettyPrint(f);
				fprintf(f, ", ");
			}
			fprintf(f, "}\n");
		}
	}
	bool parse(const char *str, const char **suffix) {
		if (!parseThisString("Eval map:\n", str, &str))
			return false;
		clear();
		while (1) {
			ThreadCfgLabel key;
			std::set<exprEvalPoint> value;
			const char *a;
			if (!key.parse(str, &a) ||
			    !parseThisString(" -> {", a, &str))
				break;
			while (1) {
				exprEvalPoint::YesIReallyMeanIt y;
				exprEvalPoint p(y);
				if (!p.parse(str, &str))
					break;
				if (!parseThisString(", ", str, &str))
					return false;
				value.insert(p);
			}
			if (!parseThisString("}\n", str, &str))
				return false;
			(*this)[key] = value;
		}
		*suffix = str;
		return true;
	}
};

class crashEnforcementRoots {
	std::map<ConcreteThread, std::set<AbstractThread> > threadAbs;
	std::map<AbstractThread, std::set<CfgLabel> > content;
public:
	crashEnforcementRoots() {}

	crashEnforcementRoots(std::map<ConcreteThread, std::set<CfgLabel> > &roots, ThreadAbstracter &abs) {
		for (auto it = roots.begin(); it != roots.end(); it++) {
			assert(!threadAbs.count(it->first));
			AbstractThread tid(abs.newThread(it->first));
			threadAbs[it->first].insert(tid);
			content[tid] = it->second;
		}
	}

	void insert(ConcreteThread concrete_tid, const ThreadCfgLabel &root)
	{
		threadAbs[concrete_tid].insert(root.thread);
		content[root.thread].insert(root.label);
	}

	void operator|=(const crashEnforcementRoots &cer) {
		for (auto it = cer.threadAbs.begin(); it != cer.threadAbs.end(); it++)
			threadAbs[it->first].insert(it->second.begin(), it->second.end());
		for (auto it = cer.content.begin(); it != cer.content.end(); it++) {
			assert(!content.count(it->first));
			content[it->first] = it->second;
		}
	}

	void prettyPrint(FILE *f) const {
		fprintf(f, "\tThreads: ");
		for (auto it = threadAbs.begin(); it != threadAbs.end(); it++) {
			if (it != threadAbs.begin())
				fprintf(f, "; ");
			fprintf(f, "%s = {", it->first.name());
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				if (it2 != it->second.begin())
					fprintf(f, ",");
				fprintf(f, "%s", it2->name());
			}
			fprintf(f, "}");
		}
		fprintf(f, "\n\tRoots: ");
		for (auto it = content.begin(); it != content.end(); it++) {
			if (it != content.begin())
				fprintf(f, "; ");
			fprintf(f, "%s = {", it->first.name());
			for (auto it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++) {
				if (it2 != it->second.begin())
					fprintf(f, ",");
				fprintf(f, "%s", it2->name());
			}
			fprintf(f, "}");
		}
		fprintf(f, "\n");
	}
	bool parse(const char *str, const char **suffix) {
		content.clear();
		threadAbs.clear();
		if (!parseThisString("Threads: ", str, &str))
			return false;
		while (1) {
			ConcreteThread concrete_tid(ConcreteThread::uninitialised());
			if (!concrete_tid.parse(str, &str) ||
			    threadAbs.count(concrete_tid) ||
			    !parseThisString(" = {", str, &str))
				return false;
			std::set<AbstractThread> &abs(threadAbs[concrete_tid]);
			while (1) {
				AbstractThread a(AbstractThread::uninitialised());
				if (!a.parse(str, &str))
					return false;
				abs.insert(a);
				if (parseThisString("}", str, &str))
					break;
				if (!parseThisChar(',', str, &str))
					return false;
			}
			if (parseThisChar('\n', str, &str))
				break;
			if (!parseThisString("; ", str, &str))
				return false;
		}
		if (!parseThisString("Roots: ", str, &str))
			return false;
		while (1) {
			AbstractThread abs(AbstractThread::uninitialised());
			if (!abs.parse(str, &str) ||
			    content.count(abs) ||
			    !parseThisString(" = {", str, &str))
				return false;
			std::set<CfgLabel> &roots(content[abs]);
			while (1) {
				CfgLabel a(CfgLabel::uninitialised());
				if (!a.parse(str, &str))
					return false;
				roots.insert(a);
				if (parseThisString("}", str, &str))
					break;
				if (!parseThisChar(',', str, &str))
					return false;
			}
			if (parseThisChar('\n', str, suffix))
				break;
			if (!parseThisString("; ", str, &str))
				return false;
		}
		return true;
	}

	/* Iterate over all of the ThreadCfgLabels with a given
	 * concrete tid. */
	class conc_iterator {
		const std::set<AbstractThread> *i2set;
		const std::map<AbstractThread, std::set<CfgLabel> > *content;
		const std::set<CfgLabel> *i3set;
		std::set<AbstractThread>::const_iterator it2;
		std::set<CfgLabel>::const_iterator it3;

	public:
		bool finished() const { return it2 == i2set->end(); }
		void advance() {
			assert(it2 != i2set->end());
			it3++;
			while (it3 == i3set->end()) {
				it2++;
				if (it2 == i2set->end())
					return;
				auto foo = content->find(*it2);
				assert(foo != content->end());
				i3set = &foo->second;
				it3 = i3set->begin();
			}
		}
		ThreadCfgLabel get() const { return ThreadCfgLabel(*it2, *it3); }
		const AbstractThread &abstract_tid() const { return *it2; }
		conc_iterator(const std::set<AbstractThread> *_i2set,
			      const std::map<AbstractThread, std::set<CfgLabel> > &_content)
			: i2set(_i2set), content(&_content)
		{
			it2 = i2set->begin();
			if (it2 == i2set->end())
				return;

			auto foo = content->find(*it2);
			assert(foo != content->end());
			i3set = &foo->second;

			it3 = i3set->begin();
			while (it3 == i3set->end()) {
				it2++;
				if (it2 == i2set->end())
					return;

				auto foo = content->find(*it2);
				assert(foo != content->end());
				i3set = &foo->second;

				it3 = i3set->begin();
			}
		}
		conc_iterator() {}
	};
	conc_iterator begin(ConcreteThread concrete_tid) {
		auto it = threadAbs.find(concrete_tid);
		assert(it != threadAbs.end());
		return conc_iterator(&it->second, content);
	}

	/* Iterate over all of the ThreadCfgLabels. */
	class iterator {
		const std::map<ConcreteThread, std::set<AbstractThread> > &threadAbs;
		std::map<ConcreteThread, std::set<AbstractThread> >::const_iterator it1;
		conc_iterator it2;

		const std::map<AbstractThread, std::set<CfgLabel> > &content;
	public:
		bool finished() const { return it1 == threadAbs.end(); }
		void advance() {
			assert(it1 != threadAbs.end());
			it2.advance();
			while (it2.finished()) {
				it1++;
				if (it1 == threadAbs.end())
					return;
				it2 = conc_iterator(&it1->second, content);
			}
		}
		ThreadCfgLabel get() const { return it2.get(); }
		ConcreteThread concrete_tid() const { return it1->first; }
		const AbstractThread &abstract_tid() const { return it2.abstract_tid(); }
		iterator(const std::map<ConcreteThread, std::set<AbstractThread> > &_threadAbs,
			 const std::map<AbstractThread, std::set<CfgLabel> > &_content)
			: threadAbs(_threadAbs),
			  content(_content)
		{
			it1 = threadAbs.begin();
			if (it1 == threadAbs.end())
				return;
			it2 = conc_iterator(&it1->second, content);
			while (it2.finished()) {
				it1++;
				if (it1 == threadAbs.end())
					return;
				it2 = conc_iterator(&it1->second, content);
			}
		}
	};
	iterator begin() const { return iterator(threadAbs, content); }

	ConcreteThread lookupAbsThread(const AbstractThread &abs)
	{
#ifndef NDEBUG
		bool found_it = false;
		ConcreteThread res(ConcreteThread::uninitialised());
		for (auto it = threadAbs.begin(); it != threadAbs.end(); it++) {
			if (it->second.count(abs)) {
				assert(!found_it);
				res = it->first;
				found_it = true;
			}
		}
		assert(found_it);
		return res;
#else
		for (auto it = threadAbs.begin(); it != threadAbs.end(); it++) {
			if (it->second.count(abs))
				return it->first;
		}
		abort();
#endif
	}
};

class EnforceCrashCFG : public CFG<ThreadCfgLabel> {
public:
	std::set<ThreadCfgLabel> usefulInstrs;
	bool instructionUseful(Instruction<ThreadCfgLabel> *i) {
		if (usefulInstrs.count(i->rip))
			return true;
		else
			return false;
	}
	bool exploreFunction(ThreadRip) {
		return true;
	}
	EnforceCrashCFG(AddressSpace *as,
			const std::set<ThreadCfgLabel> &_usefulInstrs)
		: CFG<ThreadCfgLabel>(as), usefulInstrs(_usefulInstrs)
	{}
};

class happensBeforeMapT : public std::map<ThreadCfgLabel, std::set<happensBeforeEdge *> >,
			  private GcCallback<&ir_heap> {
	void runGc(HeapVisitor &hv) {
		for (auto it = begin(); it != end(); it++)
			visit_set(it->second, hv);
	}
public:
	happensBeforeMapT() {}
	happensBeforeMapT(const SummaryId &summary,
			  const MaiMap &mai,
			  DNF_Conjunction &c,
			  instructionDominatorMapT &idom,
			  CrashCfg &cfg,
			  expressionStashMapT &exprStashPoints,
			  ThreadAbstracter &abs,
			  int &next_hb_id)
	{
		for (unsigned x = 0; x < c.size(); x++) {
			IRExpr *e = c[x].second;
			bool invert = c[x].first;
			if (e->tag == Iex_HappensBefore) {
				IRExprHappensBefore *hb = (IRExprHappensBefore *)e;
				const MemoryAccessIdentifier &beforeMai(invert ? hb->after : hb->before);
				const MemoryAccessIdentifier &afterMai(invert ? hb->before : hb->after);
				for (auto before_it = abs.begin(summary, mai, beforeMai, cfg); !before_it.finished(); before_it.advance()) {
					Instruction<ThreadCfgLabel> *beforeInstr = before_it.get();
					if (!beforeInstr)
						continue;
					for (auto after_it = abs.begin(summary, mai, afterMai, cfg); !after_it.finished(); after_it.advance()) {
						Instruction<ThreadCfgLabel> *afterInstr = after_it.get();
						if (!afterInstr)
							continue;
						happensBeforeEdge *hbe =
							new happensBeforeEdge(
								beforeInstr,
								afterInstr,
								idom,
								exprStashPoints,
								next_hb_id++);
						(*this)[hbe->before->rip].insert(hbe);
						(*this)[hbe->after->rip].insert(hbe);
					}
				}
			}
		}
	}
	void operator|=(const happensBeforeMapT &hbm) {
		for (auto it = hbm.begin(); it != hbm.end(); it++) {
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				(*this)[it->first].insert(*it2);
		}
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "\tHappens before map:\n");
		for (auto it = begin(); it != end(); it++) {
			fprintf(f, "\t\t%s -> {", it->first.name());
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				(*it2)->prettyPrint(f);
				fprintf(f, ", ");
			}
			fprintf(f, "}\n");
		}
	}
	bool parse(CrashCfg &cfg, const char *str, const char **suffix) {
		if (!parseThisString("Happens before map:\n", str, &str))
			return false;
		clear();
		while (1) {
			ThreadCfgLabel addr;
			std::set<happensBeforeEdge *> edges;
			if (!addr.parse(str, &str) ||
			    !parseThisString(" -> {", str, &str))
				break;
			while (1) {
				happensBeforeEdge *edge = happensBeforeEdge::parse(cfg, str, &str);
				if (!edge)
					break;
				edges.insert(edge);
				if (!parseThisString(", ", str, &str))
					return false;
			}
			if (!parseThisString("}\n", str, &str))
				return false;
			(*this)[addr] = edges;
		}
		*suffix = str;
		return true;
	}
	void internSelf(internmentState &state) {
		for (auto it = begin(); it != end(); it++) {
			std::set<happensBeforeEdge *> out;
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				out.insert( (*it2)->intern(state) );
			it->second = out;
		}
	}
};

class CrashCfg {
	std::map<ThreadCfgLabel, Instruction<ThreadCfgLabel> *> content;
	std::map<ConcreteCfgLabel, VexRip> rips;
public:
	Instruction<ThreadCfgLabel> *findInstr(const ThreadCfgLabel &label) {
		auto it = content.find(label);
		if (it == content.end())
			return NULL;
		else
			return it->second;
	}
	CrashCfg() {};
	CrashCfg(crashEnforcementRoots &roots, const SummaryId &summaryId, CrashSummary *summary, AddressSpace *as);
	bool parse(crashEnforcementRoots &roots, AddressSpace *as, const char *str, const char **suffix);
	void prettyPrint(FILE *f, bool verbose = false);
	void operator|=(const CrashCfg &o) {
		for (auto it = o.content.begin(); it != o.content.end(); it++) {
			auto it2_did_insert = content.insert(*it);
			assert(it2_did_insert.second);
		}
		for (auto it = o.rips.begin(); it != o.rips.end(); it++)
			rips.insert(*it);
	}
	void removeAllBut(const std::set<Instruction<ThreadCfgLabel> *> &retain);

	class iterator {
		std::map<ThreadCfgLabel, Instruction<ThreadCfgLabel> *>::const_iterator it;
		std::map<ThreadCfgLabel, Instruction<ThreadCfgLabel> *>::const_iterator endIt;
	public:
		bool finished() const { return it == endIt; }
		void advance() { it++; }
		Instruction<ThreadCfgLabel> *instr() const { return it->second; }
		iterator(const std::map<ThreadCfgLabel, Instruction<ThreadCfgLabel> *>::const_iterator &_it,
			 const std::map<ThreadCfgLabel, Instruction<ThreadCfgLabel> *>::const_iterator &_endIt)
			: it(_it), endIt(_endIt)
		{}

	};
	iterator begin() const { return iterator(content.begin(), content.end()); }
	const VexRip &labelToRip(const ConcreteCfgLabel &l) const;
};

class crashEnforcementData {
	void internSelf(internmentState &state) {
		exprStashPoints.internSelf(state);
		happensBeforePoints.internSelf(state);
		expressionEvalPoints.internSelf(state);
	}
public:
	crashEnforcementRoots roots;
	CrashCfg crashCfg;
	happensAfterMapT happensBefore;
	predecessorMapT predecessorMap;
	instructionDominatorMapT idom;
	expressionStashMapT exprStashPoints;
	expressionDominatorMapT exprDominatorMap;
	happensBeforeMapT happensBeforePoints;
	expressionEvalMapT expressionEvalPoints;
	std::set<unsigned long> patchPoints;
	std::set<unsigned long> interpretInstrs;

	crashEnforcementData() {}
	crashEnforcementData(const SummaryId &summaryId,
			     const MaiMap &mai,
			     std::set<IRExpr *> &neededExpressions,
			     ThreadAbstracter &abs,
			     std::map<ConcreteThread, std::set<CfgLabel> > &_roots,
			     DNF_Conjunction &conj,
			     int &next_hb_id,
			     CrashSummary *summary,
			     AddressSpace *as)
		: roots(_roots, abs),
		  crashCfg(roots, summaryId, summary, as),
		  happensBefore(summaryId, conj, abs, crashCfg, mai),
		  predecessorMap(crashCfg),
		  idom(crashCfg, predecessorMap, happensBefore),
		  exprStashPoints(summaryId, neededExpressions, abs, summary->loadMachine, summary->storeMachine, roots, mai),
		  exprDominatorMap(conj, exprStashPoints, idom, predecessorMap, happensBefore),
		  happensBeforePoints(summaryId, mai, conj, idom, crashCfg, exprStashPoints, abs, next_hb_id),
		  expressionEvalPoints(exprDominatorMap)
	{}

	bool parse(AddressSpace *as, const char *str, const char **suffix) {
		if (!parseThisString("Crash enforcement data:\n", str, &str) ||
		    !roots.parse(str, &str) ||
		    !crashCfg.parse(roots, as, str, &str) ||
		    !exprStashPoints.parse(str, &str) ||
		    !happensBeforePoints.parse(crashCfg, str, &str) ||
		    !expressionEvalPoints.parse(str, &str) ||
		    !parseThisString("Patch points = [", str, &str))
			return false;
		while (!parseThisString("], contInterpret = [", str, &str)) {
			unsigned long v;
			if (!parseThisString("0x", str, &str) ||
			    !parseHexUlong(&v, str, &str))
				return false;
			patchPoints.insert(v);
			parseThisString(", ", str, &str);
		}
		while (!parseThisString("]\n", str, &str)) {
			unsigned long v;
			if (!parseThisString("0x", str, &str) ||
			    !parseHexUlong(&v, str, &str))
				return false;
			interpretInstrs.insert(v);
			parseThisString(", ", str, &str);
		}
		internmentState state;
		internSelf(state);
		*suffix = str;
		return true;
	}

	void prettyPrint(FILE *f, bool verbose = false) {
		fprintf(f, "Crash enforcement data:\n");
		roots.prettyPrint(f);
		crashCfg.prettyPrint(f, verbose);
		exprStashPoints.prettyPrint(f);
		happensBeforePoints.prettyPrint(f);
		expressionEvalPoints.prettyPrint(f);
		fprintf(f, "Patch points = [");
		for (auto it = patchPoints.begin(); it != patchPoints.end(); it++) {
			if (it != patchPoints.begin())
				fprintf(f, ", ");
			fprintf(f, "0x%lx", *it);
		}
		fprintf(f, "], contInterpret = [");
		for (auto it = interpretInstrs.begin(); it != interpretInstrs.end(); it++) {
			if (it != interpretInstrs.begin())
				fprintf(f, ", ");
			fprintf(f, "0x%lx", *it);
		}
		fprintf(f, "]\n");			
	}

	void operator|=(const crashEnforcementData &ced) {
		roots |= ced.roots;
		exprStashPoints |= ced.exprStashPoints;
		happensBeforePoints |= ced.happensBeforePoints;
		expressionEvalPoints |= ced.expressionEvalPoints;
		crashCfg |= ced.crashCfg;
		patchPoints.insert(ced.patchPoints.begin(), ced.patchPoints.end());
		interpretInstrs.insert(ced.interpretInstrs.begin(), ced.interpretInstrs.end());
	}
};

#endif /* !enforceCrash_hpp__ */
