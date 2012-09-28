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
	std::map<int, std::set<AbstractThread> > content;
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
	iterator begin(int tid) const {
		auto it = content.find(tid);
		assert(it != content.end());
		return iterator(it->second);
	}
	AbstractThread newThread(int oldTid)
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
	thread_cfg_iterator begin(int tid, const CfgLabel &where) const
	{
		return thread_cfg_iterator( begin(tid), where);
	}

	class mai_iterator {
		MaiMap::const_iterator hl_iter;
		thread_cfg_iterator ll_iter;
		bool _finished;
		ThreadCfgLabel current_item;
		unsigned tid;
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
		mai_iterator(const MaiMap &mai, const MemoryAccessIdentifier &rip, ThreadAbstracter *__this)
			: hl_iter(mai.begin(rip)),
			  ll_iter(1.0, 1.0, 1.0),
			  _finished(false),
			  tid(rip.tid),
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
	mai_iterator begin(const MaiMap &mai, const MemoryAccessIdentifier &rip)
	{
		return mai_iterator(mai, rip, this);
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
	instr_iterator begin(const MaiMap &mai, const MemoryAccessIdentifier &rip, CrashCfg &cfg)
	{
		return instr_iterator(begin(mai, rip), cfg);
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
	happensAfterMapT(DNF_Conjunction &c, ThreadAbstracter &abs, CrashCfg &cfg, const MaiMap &mai);
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

class expressionStashMapT : public std::map<ThreadCfgLabel, std::set<IRExprGet *> >,
			    private GcCallback<&ir_heap> {
	void runGc(HeapVisitor &hv) {
		for (auto it = begin(); it != end(); it++) {
			std::vector<IRExprGet *> f(it->second.begin(), it->second.end());
			for (auto it2 = f.begin(); it2 != f.end(); it2++)
				hv(*it2);
			it->second.clear();
			it->second.insert(f.begin(), f.end());
		}
	}
public:
	expressionStashMapT() {}
	expressionStashMapT(std::set<IRExpr *> &neededExpressions,
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
			std::set<IRExprGet *> b;
			while (1) {
				IRExpr * s;
				if (!parseIRExpr(&s, str, &str) ||
				    !parseThisString(", ", str, &str))
					break;
				if (s->tag != Iex_Get)
					return false;
				b.insert((IRExprGet *)s);
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
			std::set<IRExprGet *> out;
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				out.insert(state.intern(*it2));
			it->second = out;
		}
	}
};

class expressionDominatorMapT : public std::map<Instruction<ThreadCfgLabel> *, std::set<std::pair<bool, IRExpr *> > > {
	class trans1 : public IRExprTransformer {
		std::set<threadAndRegister> &availRegs;
		IRExpr *transformIex(IRExprGet *e) {
			if (!availRegs.count(e->reg))
				isGood = false;
			return NULL;
		}
		IRExpr *transformIex(IRExprHappensBefore *) {
			isGood = false;
			return NULL;
		}
	public:
		bool isGood;
		trans1(std::set<threadAndRegister> &_availRegs)
			: availRegs(_availRegs),
			  isGood(true)
		{}
	};
	static bool evaluatable(IRExpr *e,
				std::set<threadAndRegister> &availRegs) {
		trans1 t(availRegs);
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
			  const std::vector<IRExprGet *> &_content,
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
	std::vector<IRExprGet *> content;
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
			std::set<IRExprGet *> &exprs(stashMap[i->rip]);
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

class slotMapT : public std::map<std::pair<AbstractThread, IRExprGet *>, simulationSlotT>,
		 private GcCallback<&ir_heap> {
	typedef std::pair<AbstractThread, IRExprGet *> key_t;
	void mk_slot(const AbstractThread &thr, IRExprGet *e, simulationSlotT &next_slot) {
		key_t key(thr, e);
		if (!count(key)) {
			simulationSlotT s = allocateSlot(next_slot);
			insert(std::pair<key_t, simulationSlotT>(key, s));
		}
	}
	void runGc(HeapVisitor &hv) {
		slotMapT n(*this);
		clear();
		for (auto it = n.begin(); it != n.end(); it++) {
			std::pair<key_t, simulationSlotT> a = *it;
			hv(a.first.second);
			insert(a);
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

	simulationSlotT operator()(const AbstractThread &thr, IRExprGet *e) {
		iterator it = find(key_t(thr, e));
		assert(it != end());
		return it->second;
	}

	void internSelf(internmentState &state) {
		std::map<key_t, simulationSlotT> work;
		for (auto it = begin(); it != end(); it++) {
			work[state.intern(it->first)] = it->second;
		}
		clear();
		for (auto it = work.begin(); it != work.end(); it++)
			insert(std::pair<key_t, simulationSlotT>(it->first, it->second));
	}

	slotMapT() { }

	slotMapT(std::map<ThreadCfgLabel, std::set<IRExprGet *> > &neededExpressions,
		 std::map<ThreadCfgLabel, std::set<happensBeforeEdge *> > &happensBefore,
		 simulationSlotT &next_slot)
	{
		/* Allocate slots for expressions which we know we're
		 * going to have to stash at some point. */
		for (auto it = neededExpressions.begin();
		     it != neededExpressions.end();
		     it++) {
			std::set<IRExprGet *> &s((*it).second);
			for (auto it2 = s.begin(); it2 != s.end(); it2++)
				mk_slot(it->first.thread, *it2, next_slot);
		}
		/* And the ones which we're going to receive in
		 * messages */
		for (auto it = happensBefore.begin();
		     it != happensBefore.end();
		     it++) {
			std::set<happensBeforeEdge *> &s(it->second);
			for (std::set<happensBeforeEdge *>::iterator it2 = s.begin();
			     it2 != s.end();
			     it2++) {
				happensBeforeEdge *hb = *it2;
				for (unsigned x = 0; x < hb->content.size(); x++)
					mk_slot(hb->after->rip.thread, hb->content[x], next_slot);
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
			fprintf(f, "\t\t%s:", it->first.first.name());
			it->first.second->prettyPrint(f);
			fprintf(f, " -> %d\n", it->second.idx);
		}
	}
	bool parse(const char *str, const char **suffix) {
		if (!parseThisString("Slot map:\n", str, &str))
			return false;
		clear();
		while (1) {
			key_t key(AbstractThread::uninitialised(), (IRExprGet *)NULL);
			simulationSlotT value;
			IRExpr *k;
			if (!key.first.parse(str, &str) ||
			    !parseThisChar(':', str, &str) ||
			    !parseIRExpr(&k, str, &str) ||
			    !parseThisString(" -> ", str, &str) ||
			    !parseDecimalInt(&value.idx, str, &str) ||
			    !parseThisChar('\n', str, &str))
				break;
			if (k->tag != Iex_Get)
				return false;
			key.second = (IRExprGet *)k;
			(*this)[key] = value;
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
	std::map<unsigned, std::set<ThreadCfgLabel> > content;
public:
	crashEnforcementRoots() {}

	crashEnforcementRoots(std::map<unsigned, std::set<CfgLabel> > &roots, ThreadAbstracter &abs) {
		for (auto it = roots.begin(); it != roots.end(); it++) {
			AbstractThread tid(abs.newThread(it->first));
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				content[it->first].insert(ThreadCfgLabel(tid, *it2));
		}
	}

	void insert(unsigned concrete_tid, const ThreadCfgLabel &root)
	{
		content[concrete_tid].insert(root);
	}
	void operator|=(const crashEnforcementRoots &cer) {
		for (auto it = cer.content.begin(); it != cer.content.end(); it++)
			content.insert(*it);
	}

	bool parse(const char *str, const char **suffix) {
		content.clear();
		if (!parseThisString("Roots: ", str, &str))
			return false;
		while (!parseThisChar('\n', str, suffix)) {
			unsigned concrete_tid;
			if (!parseDecimalUInt(&concrete_tid, str, &str) ||
			    !parseThisString(" = {", str, &str))
				return false;
			ThreadCfgLabel tcl;
			std::set<ThreadCfgLabel> entry;
			while (!parseThisChar('}', str, &str)) {
				if (!tcl.parse(str, &str))
					return false;
				entry.insert(tcl);
				parseThisChar(',', str, &str);
			}
			content[concrete_tid] = entry;
			parseThisString("; ", str, &str);
		}
		return true;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "\tRoots: ");
		for (auto it = content.begin(); it != content.end(); it++) {
			if (it != content.begin())
				fprintf(f, "; ");
			fprintf(f, "%d = {", it->first);
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				if (it2 != it->second.begin())
					fprintf(f, ",");
				fprintf(f, "%s", it2->name());
			}
			fprintf(f, "}");
		}
		fprintf(f, "\n");
	}

	class iterator {
		const std::map<unsigned, std::set<ThreadCfgLabel> > &content;
		std::map<unsigned, std::set<ThreadCfgLabel> >::const_iterator it1;
		std::set<ThreadCfgLabel>::const_iterator it2;
		ThreadCfgLabel currentItem;
		unsigned currentConcrete;
		bool _finished;
	public:
		bool finished() const { return _finished; }
		void advance() {
			assert(!_finished);
			if (it1 == content.end()) {
				_finished = true;
				return;
			}
			while (it2 == it1->second.end()) {
				it1++;
				if (it1 == content.end()) {
					_finished = true;
					return;
				}
				it2 = it1->second.begin();
			}
			currentItem = *it2;
			currentConcrete = it1->first;
			it2++;
		}
		const ThreadCfgLabel &get() const { return currentItem; }
		unsigned concrete_tid() const { return currentConcrete; }
		iterator(const std::map<unsigned, std::set<ThreadCfgLabel> > &_content)
			: content(_content),
			  it1(_content.begin()),
			  _finished(false)
		{
			if (it1 == _content.end()) {
				_finished = true;
				return;
			}
			it2 = it1->second.begin();
			while (it2 == it1->second.end()) {
				it1++;
				if (it1 == _content.end()) {
					_finished = true;
					return;
				}
				it2 = it1->second.begin();
			}
			currentItem = *it2;
			currentConcrete = it1->first;
			it2++;
		}
	};
	iterator begin() const { return iterator(content); }

	class conc_iterator {
		std::set<ThreadCfgLabel>::const_iterator it1;
		std::set<ThreadCfgLabel>::const_iterator it2;
	public:
		conc_iterator(const std::set<ThreadCfgLabel> &c)
			: it1(c.begin()), it2(c.end())
		{}
		bool finished() const { return it1 == it2; }
		void advance() { it1++; }
		ThreadCfgLabel get() const { return *it1; }
	};
	conc_iterator begin(unsigned concrete_tid) {
		assert(content.count(concrete_tid));
		return conc_iterator(content[concrete_tid]);
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
	happensBeforeMapT(const MaiMap &mai,
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
				for (auto before_it = abs.begin(mai, beforeMai, cfg); !before_it.finished(); before_it.advance()) {
					Instruction<ThreadCfgLabel> *beforeInstr = before_it.get();
					if (!beforeInstr)
						continue;
					for (auto after_it = abs.begin(mai, afterMai, cfg); !after_it.finished(); after_it.advance()) {
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

/* Map that tells us where the various threads have to exit. */
class abstractThreadExitPointsT : public std::set<ThreadCfgLabel> {
public:
	abstractThreadExitPointsT() {}
	abstractThreadExitPointsT(CrashCfg &cfg, happensBeforeMapT &);
	void prettyPrint(FILE *f) const {
		fprintf(f, "\tAbstract thread exit points: {");
		for (auto it = begin(); it != end(); it++) {
			if (it != begin())
				fprintf(f, ", ");
			fprintf(f, "%s", it->name());
		}
		fprintf(f, "}\n");
	}
	bool parse(const char *str, const char **suffix) {
		if (!parseThisString("Abstract thread exit points: {", str, &str))
			return false;
		std::set<ThreadCfgLabel> res;
		if (!parseThisString("}", str, &str)) {
			while (1) {
				ThreadCfgLabel l;
				if (!l.parse(str, &str))
					return false;
				if (parseThisString("}", str, &str))
					break;
				if (!parseThisString(", ", str, &str))
					return false;
			}
		}
		if (!parseThisChar('\n', str, &str))
			return false;
		*suffix = str;
		clear();
		for (auto it = res.begin(); it != res.end(); it++)
			insert(*it);
		return true;
	}
	void operator|=(const abstractThreadExitPointsT &atet) {
		for (auto it = atet.begin(); it != atet.end(); it++)
			this->insert(*it);
	}
};

class CrashCfg {
	std::map<ThreadCfgLabel, Instruction<ThreadCfgLabel> *> content;
	std::map<CfgLabel, VexRip> rips;
public:
	Instruction<ThreadCfgLabel> *findInstr(const ThreadCfgLabel &label) {
		auto it = content.find(label);
		if (it == content.end())
			return NULL;
		else
			return it->second;
	}
	CrashCfg() {};
	CrashCfg(crashEnforcementRoots &roots, CrashSummary *summary, AddressSpace *as);
	bool parse(AddressSpace *as, const char *str, const char **suffix);
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
	const VexRip &labelToRip(const CfgLabel &l) const;
};

class crashEnforcementData {
	void internSelf(internmentState &state) {
		exprStashPoints.internSelf(state);
		happensBeforePoints.internSelf(state);
		exprsToSlots.internSelf(state);
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
	slotMapT exprsToSlots;
	expressionEvalMapT expressionEvalPoints;
	abstractThreadExitPointsT threadExitPoints;
	std::set<unsigned long> dummyEntryPoints;
	std::set<unsigned long> keepInterpretingInstrs;

	crashEnforcementData() {}
	crashEnforcementData(const MaiMap &mai,
			     std::set<IRExpr *> &neededExpressions,
			     ThreadAbstracter &abs,
			     std::map<unsigned, std::set<CfgLabel> > &_roots,
			     DNF_Conjunction &conj,
			     int &next_hb_id,
			     simulationSlotT &next_slot,
			     CrashSummary *summary,
			     AddressSpace *as)
		: roots(_roots, abs),
		  crashCfg(roots, summary, as),
		  happensBefore(conj, abs, crashCfg, mai),
		  predecessorMap(crashCfg),
		  idom(crashCfg, predecessorMap, happensBefore),
		  exprStashPoints(neededExpressions, abs, summary->loadMachine, summary->storeMachine, roots, mai),
		  exprDominatorMap(conj, exprStashPoints, idom, predecessorMap, happensBefore),
		  happensBeforePoints(mai, conj, idom, crashCfg, exprStashPoints, abs, next_hb_id),
		  exprsToSlots(exprStashPoints, happensBeforePoints, next_slot),
		  expressionEvalPoints(exprDominatorMap),
		  threadExitPoints(crashCfg, happensBeforePoints)
	{}

	bool parse(AddressSpace *as, const char *str, const char **suffix) {
		if (!parseThisString("Crash enforcement data:\n", str, &str) ||
		    !roots.parse(str, &str) ||
		    !crashCfg.parse(as, str, &str) ||
		    !exprStashPoints.parse(str, &str) ||
		    !happensBeforePoints.parse(crashCfg, str, &str) ||
		    !exprsToSlots.parse(str, &str) ||
		    !expressionEvalPoints.parse(str, &str) ||
		    !threadExitPoints.parse(str, &str) ||
		    !parseThisString("Dummy entry points = [", str, &str))
			return false;
		while (!parseThisString("], keepInterpreting = [", str, &str)) {
			unsigned long v;
			if (!parseThisString("0x", str, &str) ||
			    !parseHexUlong(&v, str, &str))
				return false;
			dummyEntryPoints.insert(v);
			parseThisString(", ", str, &str);
		}
		while (!parseThisString("]\n", str, &str)) {
			unsigned long v;
			if (!parseThisString("0x", str, &str) ||
			    !parseHexUlong(&v, str, &str))
				return false;
			keepInterpretingInstrs.insert(v);
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
		exprsToSlots.prettyPrint(f);
		expressionEvalPoints.prettyPrint(f);
		threadExitPoints.prettyPrint(f);
		fprintf(f, "Dummy entry points = [");
		for (auto it = dummyEntryPoints.begin(); it != dummyEntryPoints.end(); it++) {
			if (it != dummyEntryPoints.begin())
				fprintf(f, ", ");
			fprintf(f, "0x%lx", *it);
		}
		fprintf(f, "], keepInterpreting = [");
		for (auto it = keepInterpretingInstrs.begin(); it != keepInterpretingInstrs.end(); it++) {
			if (it != keepInterpretingInstrs.begin())
				fprintf(f, ", ");
			fprintf(f, "0x%lx", *it);
		}
		fprintf(f, "]\n");			
	}

	void operator|=(const crashEnforcementData &ced) {
		roots |= ced.roots;
		exprStashPoints |= ced.exprStashPoints;
		happensBeforePoints |= ced.happensBeforePoints;
		exprsToSlots |= ced.exprsToSlots;
		expressionEvalPoints |= ced.expressionEvalPoints;
		threadExitPoints |= ced.threadExitPoints;
		crashCfg |= ced.crashCfg;
		for (auto it = ced.dummyEntryPoints.begin(); it != ced.dummyEntryPoints.end(); it++)
			dummyEntryPoints.insert(*it);
	}
};

#endif /* !enforceCrash_hpp__ */
