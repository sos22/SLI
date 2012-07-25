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

class ThreadCfgLabel : public Named {
	char *mkName() const {
		return my_asprintf("%s:%d", label.name(), thread);
	}
public:
	unsigned thread;
	CfgLabel label;
	ThreadCfgLabel(unsigned _thread, const CfgLabel &_label)
		: thread(_thread), label(_label)
	{}
	ThreadCfgLabel()
		: thread(-1), label(CfgLabel::uninitialised())
	{}
	ThreadCfgLabel(const MemoryAccessIdentifier &mai)
		: thread(mai.tid), label(mai.where)
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
		return thread * 874109 + label.hash() * 877939;
	}
	bool parse(const char *str, const char **suffix) {
		CfgLabel l(CfgLabel::uninitialised());
		int t;
		if (l.parse(str, &str) &&
		    parseThisChar(':', str, &str) &&
		    parseDecimalInt(&t, str, suffix)) {
			label = l;
			thread = t;
			clearName();
			return true;
		}
		return false;
	}
};

class ThreadCfgDecode {
	Instruction<ThreadCfgLabel> *addCfg(int tid, const CFGNode *root);
public:
	std::map<ThreadCfgLabel, Instruction<ThreadCfgLabel> *> content;
	Instruction<ThreadCfgLabel> *operator()(const ThreadCfgLabel &l) {
		auto it = content.find(l);
		assert(it != content.end());
		return it->second;
	}

	class iterator {
		std::map<ThreadCfgLabel, Instruction<ThreadCfgLabel> *>::iterator val;
	public:
		void operator++(int) { val++; }
		Instruction<ThreadCfgLabel> *value() { return val->second; }
		int thread() const { return val->first.thread; }
		bool operator!=(const iterator &o) const { return val != o.val; }
		iterator(const std::map<ThreadCfgLabel, Instruction<ThreadCfgLabel> *>::iterator &_val)
			: val(_val)
		{}
	};

	iterator begin() { return iterator(content.begin()); }
	iterator end() { return iterator(content.end()); }

	void addMachine(StateMachine *sm);
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
	unsigned intern(unsigned x) { return x; }
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
	predecessorMapT(ThreadCfgDecode &cfg) {
		for (auto it = cfg.begin();
		     it != cfg.end();
		     it++) {
			auto *v = it.value();
			if (!count(v))
				(*this)[v];
			for (auto it2 = v->successors.begin(); it2 != v->successors.end(); it2++)
				if (it2->instr)
					(*this)[it2->instr].insert(v);
		}
	}
};

/* An encoding of the happens-before edges in a DNF clause into a map
   over Instructions. */
class happensAfterMapT {
public:
	/* happensBefore[i] -> the set of all instructions ordered before i */
	instrToInstrSetMap happensBefore;
	/* happensBefore[i] -> the set of all instructions ordered after i */
	instrToInstrSetMap happensAfter;
	happensAfterMapT(DNF_Conjunction &c, ThreadCfgDecode &cfg);
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
	instructionDominatorMapT(ThreadCfgDecode &cfg,
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
			    StateMachine *probeMachine,
			    StateMachine *storeMachine,
			    std::map<unsigned, CfgLabel> &roots)
	{
		/* XXX keep this in sync with buildCED */
		std::set<IRExprGet *> neededTemporaries;
		for (auto it = neededExpressions.begin();
		     it != neededExpressions.end();
		     it++) {
			IRExpr *e = *it;
			if (e->tag == Iex_Get) {
				IRExprGet *ieg = (IRExprGet *)e;
				if (ieg->reg.isReg()) {
					auto it_r = roots.find(ieg->reg.tid());
					assert(it_r != roots.end());
					(*this)[ThreadCfgLabel(ieg->reg.tid(), it_r->second)].insert(ieg);
				} else {
					neededTemporaries.insert(ieg);
				}
			} else if (e->tag == Iex_HappensBefore) {
				/* These don't really get stashed in any useful sense */
			} else {
				abort();
			}
		}
		if (!neededTemporaries.empty()) {
			std::set<StateMachineSideEffectLoad *> loads;
			enumSideEffects(probeMachine, loads);
			enumSideEffects(storeMachine, loads);
			for (auto it = neededTemporaries.begin();
			     it != neededTemporaries.end();
			     it++) {
				StateMachineSideEffectLoad *l = NULL;
				for (auto it2 = loads.begin(); it2 != loads.end(); it2++) {
					if ( threadAndRegister::fullEq((*it2)->target, (*it)->reg) ) {
						assert(!l);
						l = *it2;
					}
				}
				assert(l);
				(*this)[ThreadCfgLabel(l->rip.tid, l->rip.where)].insert(*it);
			}
		}
	}
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
		std::set<threadAndRegister, threadAndRegister::fullCompare> &availRegs;
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
		trans1(std::set<threadAndRegister, threadAndRegister::fullCompare> &_availRegs)
			: availRegs(_availRegs),
			  isGood(true)
		{}
	};
	static bool evaluatable(IRExpr *e,
				std::set<threadAndRegister, threadAndRegister::fullCompare> &availRegs) {
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
	happensBeforeEdge(const MemoryAccessIdentifier &_before,
			  const MemoryAccessIdentifier &_after,
			  const std::vector<IRExprGet *> &_content,
			  unsigned _msg_id)
		: before(_before), after(_after), content(_content), msg_id(_msg_id)
	{}
	char *mkName() const {
		std::vector<const char *> fragments;
		fragments.push_back(my_asprintf(
					    "%d: %s <-< %s {",
					    msg_id,
					    before.name(),
					    after.name()));
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
	MemoryAccessIdentifier before;
	MemoryAccessIdentifier after;
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
	happensBeforeEdge(bool invert,
			  IRExprHappensBefore *hb,
			  instructionDominatorMapT &idom,
			  ThreadCfgDecode &cfg,
			  expressionStashMapT &stashMap,
			  unsigned _msg_id)
		: before(invert ? hb->after : hb->before),
		  after(invert ? hb->before : hb->after),
		  msg_id(_msg_id)
	{
		std::set<Instruction<ThreadCfgLabel> *> &liveInstructions(
			idom[cfg(before)]);
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
	static happensBeforeEdge *parse(const char *str, const char **suffix)
	{
		MemoryAccessIdentifier before(MemoryAccessIdentifier::uninitialised());
		MemoryAccessIdentifier after(MemoryAccessIdentifier::uninitialised());
		unsigned msg_id;
		if (!parseDecimalUInt(&msg_id, str, &str) ||
		    !parseThisString(": ", str, &str) ||
		    !parseMemoryAccessIdentifier(&before, str, &str) ||
		    !parseThisString(" <-< ", str, &str) ||
		    !parseMemoryAccessIdentifier(&after, str, &str) ||
		    !parseThisString(" {", str, &str))
			return NULL;
		std::vector<IRExprGet *> content;
		while (1) {
			IRExpr *a;
			if (!parseIRExpr(&a, str, &str))
				break;
			if (!parseThisString(", ", str, &str))
				return NULL;
			if (a->tag != Iex_Get)
				return NULL;
			content.push_back((IRExprGet *)a);
		}
		if (!parseThisChar('}', str, &str))
			return NULL;
		*suffix = str;
		return new happensBeforeEdge(before, after, content, msg_id);
	}
	void visit(HeapVisitor &hv) {
		visit_container(content, hv);
	}
	NAMED_CLASS
};

class slotMapT : public std::map<std::pair<unsigned, IRExprGet *>, simulationSlotT>,
		 private GcCallback<&ir_heap> {
	typedef std::pair<unsigned, IRExprGet *> key_t;
	void mk_slot(unsigned thr, IRExprGet *e, simulationSlotT &next_slot) {
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

	simulationSlotT operator()(unsigned thr, IRExprGet *e) {
		iterator it = find(std::pair<unsigned, IRExprGet *>(thr, e));
		assert(it != end());
		return it->second;
	}

	void internSelf(internmentState &state) {
		std::map<key_t, simulationSlotT> work;
		for (auto it = begin(); it != end(); it++) {
			key_t key;
			work[state.intern(it->first)] = it->second;
		}
		clear();
		for (auto it = work.begin(); it != work.end(); it++)
			(*this)[it->first] = it->second;
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
					mk_slot(hb->after.tid, hb->content[x], next_slot);
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
			fprintf(f, "\t\t%d:", it->first.first);
			it->first.second->prettyPrint(f);
			fprintf(f, " -> %d\n", it->second.idx);
		}
	}
	bool parse(const char *str, const char **suffix) {
		if (!parseThisString("Slot map:\n", str, &str))
			return false;
		clear();
		while (1) {
			key_t key;
			simulationSlotT value;
			IRExpr *k;
			if (!parseDecimalUInt(&key.first, str, &str) ||
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

class crashEnforcementRoots : public std::set<ThreadCfgLabel> {
public:
	crashEnforcementRoots() {}

	crashEnforcementRoots(std::map<unsigned, CfgLabel> &roots) {
		std::map<CfgLabel, std::set<unsigned> > threadsRelevantAtEachEntryPoint;
		for (auto it = roots.begin(); it != roots.end(); it++)
			threadsRelevantAtEachEntryPoint[it->second].insert(it->first);
		for (auto it = roots.begin(); it != roots.end(); it++) {
			std::set<unsigned> &threads(threadsRelevantAtEachEntryPoint[it->second]);
			for (auto it2 = threads.begin(); it2 != threads.end(); it2++)
				insert(ThreadCfgLabel(*it2, it->second));
		}
	}

	void operator|=(const crashEnforcementRoots &cer) {
		for (auto it = cer.begin(); it != cer.end(); it++)
			insert(*it);
	}

	bool parse(const char *str, const char **suffix) {
		clear();
		if (!parseThisString("Roots: ", str, &str))
			return false;
		while (1) {
			ThreadCfgLabel tcl;
			if (!tcl.parse(str, &str))
				break;
			insert(tcl);
			if (!parseThisString(", ", str, &str))
				break;
		}
		if (!parseThisChar('\n', str, &str))
			return false;
		*suffix = str;
		return true;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "\tRoots: ");
		for (auto it = begin(); it != end(); it++) {
			if (it != begin())
				fprintf(f, ", ");
			fprintf(f, "%s", it->name());
		}
		fprintf(f, "\n");
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
	happensBeforeMapT(DNF_Conjunction &c,
			  instructionDominatorMapT &idom,
			  ThreadCfgDecode &cfg,
			  expressionStashMapT &exprStashPoints,
			  int &next_hb_id)
	{
		for (unsigned x = 0; x < c.size(); x++) {
			IRExpr *e = c[x].second;
			bool invert = c[x].first;
			if (e->tag == Iex_HappensBefore) {
				IRExprHappensBefore *hb = (IRExprHappensBefore *)e;
				happensBeforeEdge *hbe = new happensBeforeEdge(invert, hb, idom,
									       cfg, exprStashPoints, next_hb_id++);
				(*this)[ThreadCfgLabel(hbe->before.tid, hbe->before.where)].insert(hbe);
				(*this)[ThreadCfgLabel(hbe->after.tid, hbe->after.where)].insert(hbe);
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
	bool parse(const char *str, const char **suffix) {
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
				happensBeforeEdge *edge = happensBeforeEdge::parse(str, &str);
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
	abstractThreadExitPointsT(ThreadCfgDecode &cfg, happensBeforeMapT &);
	void operator|=(const abstractThreadExitPointsT &atet) {
		for (auto it = atet.begin(); it != atet.end(); it++)
			this->insert(*it);
	}
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
};

class ThreadCfg {
	std::map<ThreadCfgLabel, CFGNode *> content;
	std::map<ThreadCfgLabel, CFGNode *> insertAfterPoints;
public:
	CFGNode *findInstr(const ThreadCfgLabel &label) {
		auto it = content.find(label);
		if (it == content.end())
			return NULL;
		else
			return it->second;
	}
	void addInstr(unsigned thread, CFGNode *node) {
		assert(!content.count(ThreadCfgLabel(thread, node->label)));
		content[ThreadCfgLabel(thread, node->label)] = node;
	}
	void prepLabelAllocator(CfgLabelAllocator &alloc) {
		for (auto it = content.begin(); it != content.end(); it++)
			alloc.reserve(it->first.label);
	}
	ThreadCfg() {};
	ThreadCfg(CrashSummary *summary) {
		assert(summary->loadMachine->origin.size() == 1);
		assert(summary->storeMachine->origin.size() == 1);
		std::queue<std::pair<unsigned, CFGNode *> > pending;
		pending.push(std::pair<unsigned, CFGNode *>
			     (summary->loadMachine->origin[0].first,
			      const_cast<CFGNode *>(summary->loadMachine->cfg_roots[0])));
		pending.push(std::pair<unsigned, CFGNode *>
			     (summary->storeMachine->origin[0].first,
			      const_cast<CFGNode *>(summary->storeMachine->cfg_roots[0])));
		while (!pending.empty()) {
			std::pair<unsigned, CFGNode *> p(pending.front());
			pending.pop();
			auto it_did_insert = content.insert(
				std::pair<ThreadCfgLabel, CFGNode *>(
					ThreadCfgLabel(p.first, p.second->label),
					p.second));
			auto did_insert = it_did_insert.second;
			if (did_insert) {
				for (auto it = p.second->successors.begin();
				     it != p.second->successors.end();
				     it++) {
					if (it->instr)
						pending.push(std::pair<unsigned, CFGNode *>(p.first, it->instr));
				}
			}
		}
	}
	bool parse(AddressSpace *as, const char *str, const char **suffix);
	void prettyPrint(FILE *f, bool verbose = false);
	void insertBefore(const ThreadCfgLabel &existingInstr, CFGNode *newInstr);
	void insertAfter(const ThreadCfgLabel &exitsingInstr, CFGNode *newInstr);
	void insertAfter(const ThreadCfgLabel &exitsingInstr, CFGNode *newInstr, CFGNode *newInstrEnd);
	void rewriteBranches(CFGNode *existingInstr, CFGNode *newInstr);
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
	happensAfterMapT happensBefore;
	predecessorMapT predecessorMap;
	instructionDominatorMapT idom;
	expressionStashMapT exprStashPoints;
	expressionDominatorMapT exprDominatorMap;
	happensBeforeMapT happensBeforePoints;
	slotMapT exprsToSlots;
	expressionEvalMapT expressionEvalPoints;
	abstractThreadExitPointsT threadExitPoints;
	ThreadCfg threadCfg;

	crashEnforcementData(std::set<IRExpr *> &neededExpressions,
			     std::map<unsigned, CfgLabel> &_roots,
			     StateMachine *probeMachine,
			     StateMachine *storeMachine,
			     DNF_Conjunction &conj,
			     ThreadCfgDecode &cfg,
			     int &next_hb_id,
			     simulationSlotT &next_slot)
		: roots(_roots),
		  happensBefore(conj, cfg),
		  predecessorMap(cfg),
		  idom(cfg, predecessorMap, happensBefore),
		  exprStashPoints(neededExpressions, probeMachine, storeMachine, _roots),
		  exprDominatorMap(conj, exprStashPoints, idom, predecessorMap, happensBefore),
		  happensBeforePoints(conj, idom, cfg, exprStashPoints, next_hb_id),
		  exprsToSlots(exprStashPoints, happensBeforePoints, next_slot),
		  expressionEvalPoints(exprDominatorMap),
		  threadExitPoints(cfg, happensBeforePoints)
	{}

	bool parse(AddressSpace *as, const char *str, const char **suffix) {
		if (!parseThisString("Crash enforcement data:\n", str, &str) ||
		    !roots.parse(str, &str) ||
		    !exprStashPoints.parse(str, &str) ||
		    !happensBeforePoints.parse(str, &str) ||
		    !exprsToSlots.parse(str, &str) ||
		    !expressionEvalPoints.parse(str, &str) ||
		    !threadExitPoints.parse(str, &str) ||
		    !threadCfg.parse(as, str, &str))
			return false;
		internmentState state;
		internSelf(state);
		*suffix = str;
		return true;
	}
	crashEnforcementData(CrashSummary *summary)
		: threadCfg(summary)
	{}
	crashEnforcementData()
	{}

	void prettyPrint(FILE *f, bool verbose = false) {
		fprintf(f, "Crash enforcement data:\n");
		roots.prettyPrint(f);
		exprStashPoints.prettyPrint(f);
		happensBeforePoints.prettyPrint(f);
		exprsToSlots.prettyPrint(f);
		expressionEvalPoints.prettyPrint(f);
		threadExitPoints.prettyPrint(f);
		threadCfg.prettyPrint(f, verbose);
	}

	void operator|=(const crashEnforcementData &ced) {
		roots |= ced.roots;
		exprStashPoints |= ced.exprStashPoints;
		happensBeforePoints |= ced.happensBeforePoints;
		exprsToSlots |= ced.exprsToSlots;
		expressionEvalPoints |= ced.expressionEvalPoints;
		threadExitPoints |= ced.threadExitPoints;
	}
};

#endif /* !enforceCrash_hpp__ */
