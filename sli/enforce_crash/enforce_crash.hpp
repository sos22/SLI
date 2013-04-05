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
#include "input_expression.hpp"

template <typename t> class sane_vector {
	unsigned nr_elems;
	unsigned nr_elems_allocated;
	void *content;

	/* Only needed for the name() method when @t is Named */
	mutable const char * _name;
public:
	sane_vector();
	sane_vector(const sane_vector &o);
	sane_vector(sane_vector &&o);
	~sane_vector();
	void operator =(const sane_vector &o);
	void operator =(const sane_vector &&o);

	class iterator {
		friend class sane_vector;
		sane_vector *owner;
		unsigned idx;
		iterator(sane_vector *_owner);
	public:
		const t &get() const;

		void set(const t &);
		/* Erase the current element from the vector.  The
		   iterator remains valid and now points at the next
		   thing in the vector (or it'll be finished). */
		void erase();

		bool finished() const;
		bool started() const; /* True if advance() has ever been called */
		void advance();
	};
	iterator begin();

	class const_iterator {
		friend class sane_vector;
		const sane_vector *owner;
		unsigned idx;
		const_iterator(const sane_vector *_owner);
	public:
		const t &get() const;
		bool finished() const;
		bool started() const;
		void advance();
	};
	const_iterator begin() const;

	bool operator ==(const sane_vector &o) const;

	bool operator |=(const std::set<t> &o);

	void push_back(const t &what);
	void clear();
	size_t size() const;
	bool empty() const { return size() == 0; }
};

class happensBeforeEdge;

class internmentState {
public:
	std::set<happensBeforeEdge *> hbes;
	internStateMachineTable exprs;
};

class instrToInstrSetMap : public std::map<Instruction<ThreadCfgLabel> *, std::set<Instruction<ThreadCfgLabel> *> > {
public:
	void print(FILE *f) const;
};

class expressionStashMapT : public sane_map<ThreadCfgLabel, std::set<input_expression> > {
public:
	expressionStashMapT() {}
	expressionStashMapT(const SummaryId &summary,
			    const std::set<input_expression> &neededExpressions,
			    ThreadAbstracter &abs,
			    crashEnforcementRoots &roots);

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
			std::set<input_expression> b;
			if (!parseThisString("}", str, &str)) {
				while (1) {
					std::pair<input_expression, bool> s(input_expression::parse(str, &str));
					if (!s.second) {
						return false;
					}
					b.insert(s.first);
					if (!parseThisString(", ", str, &str)) {
						if (parseThisString("}", str, &str)) {
							break;
						} else {
							return false;
						}
					}
				}
			}
			if (!parseThisChar('\n', str, &str))
				return false;
			assert(b.size() > 0);
			assert(!count(where));
			insert(where, b);
		}
		*suffix = str;
		return true;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "\tStash map:\n");
		for (auto it = begin(); it != end(); it++) {
			fprintf(f, "\t\t%s -> {", it->first.name());
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				if (it2 != it->second.begin()) {
					fprintf(f, ", ");
				}
				fprintf(f, "%s", it2->name());
			}
			fprintf(f, "}\n");
		}
	}
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

class happensBeforeEdge : public GarbageCollected<happensBeforeEdge, &ir_heap> {
	happensBeforeEdge(Instruction<ThreadCfgLabel> *_before,
			  Instruction<ThreadCfgLabel> *_after,
			  bbdd *_sideCondition,
			  const sane_vector<input_expression> &_content,
			  unsigned _msg_id)
		: before(_before), after(_after), sideCondition(_sideCondition),
		  content(_content), msg_id(_msg_id)
	{}
public:
	Instruction<ThreadCfgLabel> *before;
	Instruction<ThreadCfgLabel> *after;
	/* Note that sideCondition gets set from expressionEvalMapT's
	   constructor, which is perhaps slightly surprising. */
	bbdd *sideCondition;
	sane_vector<input_expression> content;
	unsigned msg_id;

	happensBeforeEdge *intern(internmentState &state) {
		for (auto it = state.hbes.begin(); it != state.hbes.end(); it++) {
			if ( (*it)->msg_id == msg_id &&
			     (*it)->before == before &&
			     (*it)->after == after &&
			     (*it)->sideCondition == sideCondition &&
			     (*it)->content == content )
				return (*it);
		}
		state.hbes.insert(this);
		return this;
	}
	happensBeforeEdge(Instruction<ThreadCfgLabel> *_before,
			  Instruction<ThreadCfgLabel> *_after,
			  unsigned _msg_id)
		: before(_before),
		  after(_after),
		  sideCondition(NULL),
		  msg_id(_msg_id)
	{
	}

	void prettyPrint(FILE *f) const;
	static happensBeforeEdge *parse(bbdd::scope *scope, CrashCfg &cfg, const char *str, const char **suffix);
	void visit(HeapVisitor &hv) { hv(sideCondition); }
	NAMED_CLASS
};

class slotMapT : public sane_map<input_expression, simulationSlotT> {
	void mk_slot(const input_expression &e, simulationSlotT &next_slot) {
		if (!count(e)) {
			insert(e, allocateSlot(next_slot));
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

	simulationSlotT operator()(const input_expression &e) const {
		auto it = find(e);
		assert(it != end());
		return it->second;
	}

	slotMapT() { }

	slotMapT(const std::map<ThreadCfgLabel, std::set<input_expression> > &neededExpressions,
		 const std::map<ThreadCfgLabel, std::set<happensBeforeEdge *> > &happensBefore)
	{
		simulationSlotT next_slot(1);
		/* Allocate slots for expressions which we know we're
		 * going to have to stash at some point. */
		for (auto it = neededExpressions.begin();
		     it != neededExpressions.end();
		     it++) {
			const std::set<input_expression> &s(it->second);
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
			const std::set<happensBeforeEdge *> &s(it->second);
			for (auto it2 = s.begin(); it2 != s.end(); it2++) {
				happensBeforeEdge *hb = *it2;
				for (auto it = hb->content.begin(); !it.finished(); it.advance()) {
					assert(count(it.get()));
				}
			}
		}
	}

	void operator|=(const slotMapT &sm) {
		for (auto it = sm.begin(); it != sm.end(); it++)
			if (!count(it->first))
				insert(it->first, it->second);
	}

	void prettyPrint(FILE *f) const {
		fprintf(f, "\tSlot map:\n");
		for (auto it = begin(); it != end(); it++) {
			fprintf(f, "\t\t%s -> %d\n",
				it->first.name(), it->second.idx);
		}
	}
	bool parse(const char *str, const char **suffix) {
		if (!parseThisString("Slot map:\n", str, &str))
			return false;
		clear();
		while (1) {
			simulationSlotT value;
			std::pair<input_expression, bool> k(input_expression::parse(str, &str));
			if (!k.second ||
			    !parseThisString(" -> ", str, &str) ||
			    !parseDecimalInt(&value.idx, str, &str) ||
			    !parseThisChar('\n', str, &str))
				break;
			assert(!count(k.first));
			insert(k.first, value);
		}
		*suffix = str;
		return true;
	}
};

class happensBeforeMapT;

class expressionEvalMapT : private GcCallback<&ir_heap> {
	struct eval_sequence {
		bbdd *after_regs;
		bbdd *after_control_flow;
		eval_sequence()
			: after_regs(NULL),
			  after_control_flow(NULL)
		{}
	};
	sane_map<ThreadCfgLabel, eval_sequence> evalAt;
	void runGc(HeapVisitor &hv);
public:
	expressionEvalMapT();
	expressionEvalMapT(bbdd::scope *scope,
			   CrashCfg &cfg,
			   crashEnforcementRoots &roots,
			   expressionStashMapT &stashMap,
			   happensBeforeMapT &hbMap,
			   ThreadAbstracter &abs,
			   bbdd *sideCondition);
	void operator|=(const expressionEvalMapT &eem);
	void prettyPrint(FILE *f) const;
	bool parse(bbdd::scope *scope, const char *str, const char **suffix);

	bbdd *after_regs(const ThreadCfgLabel &) const;
	bbdd *after_control_flow(const ThreadCfgLabel &) const;
	bool count(const ThreadCfgLabel &) const;
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
			  const std::set<const IRExprHappensBefore *> &trueHb,
			  const std::set<const IRExprHappensBefore *> &falseHb,
			  CrashCfg &cfg,
			  ThreadAbstracter &abs,
			  int &next_hb_id);
	void operator|=(const happensBeforeMapT &hbm) {
		for (auto it = hbm.begin(); it != hbm.end(); it++) {
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				(*this)[it->first].insert(*it2);
		}
	}
	void prettyPrint(FILE *f) const;
	bool parse(bbdd::scope *scope, CrashCfg &cfg, const char *str, const char **suffix);
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
		happensBeforePoints.internSelf(state);
	}
public:
	crashEnforcementRoots roots;
	CrashCfg crashCfg;
	expressionStashMapT exprStashPoints;
	happensBeforeMapT happensBeforePoints;
	expressionEvalMapT expressionEvalPoints;
	std::set<unsigned long> patchPoints;
	std::set<unsigned long> interpretInstrs;

	crashEnforcementData() {}
	crashEnforcementData(bbdd::scope *scope,
			     const SummaryId &summaryId,
			     const MaiMap &mai,
			     std::set<input_expression> &neededExpressions,
			     ThreadAbstracter &abs,
			     std::map<ConcreteThread, std::set<std::pair<CfgLabel, long> > > &_roots,
			     const std::set<const IRExprHappensBefore *> &trueHb,
			     const std::set<const IRExprHappensBefore *> &falseHb,
			     bbdd *sideCondition,
			     int &next_hb_id,
			     CrashSummary *summary,
			     AddressSpace *as)
		: roots(_roots, abs),
		  crashCfg(roots, summaryId, summary, as, false, abs),
		  exprStashPoints(summaryId, neededExpressions, abs, roots),
		  happensBeforePoints(summaryId, mai, trueHb, falseHb, crashCfg, abs, next_hb_id),
		  expressionEvalPoints(scope, crashCfg, roots, exprStashPoints,
				       happensBeforePoints, abs, sideCondition)
	{}

	bool parse(SMScopes *scopes, AddressSpace *as, const char *str, const char **suffix) {
		if (!parseThisString("Scopes:\n", str, &str) ||
		    !scopes->parse(str, &str) ||
		    !parseThisString("Crash enforcement data:\n", str, &str) ||
		    !roots.parse(str, &str) ||
		    !crashCfg.parse(roots, as, false, str, &str) ||
		    !exprStashPoints.parse(str, &str) ||
		    !happensBeforePoints.parse(&scopes->bools, crashCfg, str, &str) ||
		    !expressionEvalPoints.parse(&scopes->bools, str, &str) ||
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

	void prettyPrint(SMScopes *scopes, FILE *f, bool verbose = false) {
		if (roots.empty()) {
			fprintf(f, "<empty>\n");
			return;
		}
		if (scopes) {
			fprintf(f, "Scopes:\n");
			scopes->prettyPrint(f, NULL);
		}
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

void enumerateNeededExpressions(const bbdd *e, std::set<input_expression> &out);
void optimiseHBEdges(crashEnforcementData &ced);
void optimiseStashPoints(crashEnforcementData &ced, Oracle *oracle);
void optimiseCfg(crashEnforcementData &ced);
void buildPatchStrategy(crashEnforcementData &ced, Oracle *oracle);
crashEnforcementData enforceCrashForMachine(const SummaryId &summaryId,
					    VexPtr<CrashSummary, &ir_heap> summary,
					    VexPtr<Oracle> &oracle,
					    ThreadAbstracter &abs,
					    int &next_hb_id);
int ced_to_cep(const crashEnforcementData &, const char *output, const char *binary,
	       Oracle *oracle);

#endif /* !enforceCrash_hpp__ */
