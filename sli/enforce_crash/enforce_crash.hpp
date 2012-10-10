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
#include "crashcfg.hpp"

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
				ppIRExpr(*it2, f);
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
			ppIRExpr(it->first, f);
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
		ppIRExpr(e, f);
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
		  crashCfg(roots, summaryId, summary, as, false),
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
		    !crashCfg.parse(roots, as, false, str, &str) ||
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
