#ifndef enforceCrash_hpp__
#define enforceCrash_hpp__

#include <set>
#include <map>
#include "libvex_ir.h"
#include "genfix.hpp"
#include "dnf.hpp"
#include "offline_analysis.hpp"

void enumerateNeededExpressions(IRExpr *e, std::set<IRExpr *> &out);

class instrToInstrSetMap : public std::map<Instruction<ThreadRip> *, std::set<Instruction<ThreadRip> *> > {
public:
	void print(FILE *f);
};

/* Map from instructions to instructions which happen immediately
   before them, including those ordered by happens-before
   relationships. */
class predecessorMapT : public instrToInstrSetMap {
public:
	predecessorMapT(CFG<ThreadRip> *cfg) {
		for (CFG<ThreadRip>::ripToInstrT::iterator it = cfg->ripToInstr->begin();
		     it != cfg->ripToInstr->end();
		     it++) {
			Instruction<ThreadRip> *v = it.value();
			if (!count(v))
				(*this)[v];
			if (v->defaultNextI)
				(*this)[v->defaultNextI].insert(v);
			if (v->branchNextI)
				(*this)[v->branchNextI].insert(v);
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
	happensAfterMapT(DNF_Conjunction &c, CFG<ThreadRip> *cfg);
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
	friend class expressionDominatorMapT;
	instructionDominatorMapT() {}
	instructionDominatorMapT(CFG<ThreadRip> *cfg,
				 predecessorMapT &predecessors,
				 happensAfterMapT &happensAfter,
				 const std::set<ThreadRip> &neededInstructions);
};

class expressionDominatorMapT : public std::map<Instruction<ThreadRip> *, std::set<std::pair<bool, IRExpr *> > > {
	class trans1 : public IRExprTransformer {
		std::set<Instruction<ThreadRip> *> &avail;
		std::set<unsigned> &availThreads;
		CFG<ThreadRip> *cfg;
		bool isAvail(ThreadRip rip) {
			Instruction<ThreadRip> *i = cfg->ripToInstr->get(rip);
			assert(i);
			return avail.count(i) != 0;
		}
		IRExpr *transformIex(IRExprGet *e) {
			if (!availThreads.count(e->reg.tid()))
				isGood = false;
			return NULL;
		}
		IRExpr *transformIex(IRExprLoad *e) {
			if (!isAvail(e->rip))
				isGood = false;
			return NULL;
		}
		IRExpr *transformIex(IRExprHappensBefore *e) {
			isGood = false;
			return NULL;
		}
		IRExpr *transformIex(IRExprClientCall *e) {
			if (!isAvail(e->callSite))
				isGood = false;
			return NULL;
		}
	public:
		bool isGood;
		trans1(std::set<Instruction<ThreadRip> *> &_avail, std::set<unsigned> &_availThreads, CFG<ThreadRip> *_cfg)
			: avail(_avail), availThreads(_availThreads), cfg(_cfg), isGood(true) 
		{}
	};
	static bool evaluatable(IRExpr *e, std::set<Instruction<ThreadRip> *> &avail, std::set<unsigned> &availThreads, CFG<ThreadRip> *cfg) {
		trans1 t(avail, availThreads, cfg);
		t.transformIRExpr(e);
		return t.isGood;
	}
public:
	instructionDominatorMapT idom;
	expressionDominatorMapT(DNF_Conjunction &, CFG<ThreadRip> *, const std::set<ThreadRip> &neededRips);
};

class simulationSlotT {
public:
	int idx;
	simulationSlotT(int _idx) : idx(_idx) {}
	simulationSlotT() : idx(-10000) {}
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

class expressionStashMapT : public std::map<unsigned long, std::set<std::pair<unsigned, IRExpr *> > >,
			    private GcCallback<> {
	void runGc(HeapVisitor &hv) {
		for (auto it = begin(); it != end(); it++) {
			std::vector<std::pair<unsigned, IRExpr *> > n;
			setToVector(it->second, n);
			it->second.clear();
			for (auto it2 = n.begin(); it2 != n.end(); it2++) {
				hv(it2->second);
				it->second.insert(*it2);
			}
		}
	}
public:
	expressionStashMapT() {}
	expressionStashMapT(std::set<IRExpr *> &neededExpressions,
			    std::map<unsigned, ThreadRip> &roots)
	{
		for (std::set<IRExpr *>::iterator it = neededExpressions.begin();
		     it != neededExpressions.end();
		     it++) {
			bool doit = true;
			IRExpr *e = *it;
			ThreadRip rip;
			if (e->tag == Iex_Get) {
				rip = roots[((IRExprGet *)e)->reg.tid()];
			} else if (e->tag == Iex_ClientCall) {
				rip = ((IRExprClientCall *)e)->callSite;
			} else if (e->tag == Iex_Load) {
				rip = ((IRExprLoad *)e)->rip;
			} else if (e->tag == Iex_HappensBefore) {
				/* These don't really get stashed in any useful sense */
				doit = false;
			} else {
				abort();
			}
			if (doit)
				(*this)[rip.rip].insert(std::pair<unsigned, IRExpr *>(rip.thread, e));
		}
	}
	void operator|=(const expressionStashMapT &esm) {
		for (auto it = esm.begin(); it != esm.end(); it++) {
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				(*this)[it->first].insert(*it2);
		}
	}
};

class happensBeforeEdge : public GarbageCollected<happensBeforeEdge> {
public:
	static unsigned next_msg_id;

	ThreadRip before;
	ThreadRip after;
	std::vector<IRExpr *> content;
	unsigned msg_id;

	happensBeforeEdge(bool invert, IRExprHappensBefore *hb,
			  instructionDominatorMapT &idom,
			  CFG<ThreadRip> *cfg,
			  expressionStashMapT &stashMap)
		: before(invert ? hb->after : hb->before),
		  after(invert ? hb->before : hb->after),
		  msg_id(next_msg_id++)
	{
		printf("%x: HBE %s -> %s\n",
		       msg_id,
		       before.name(),
		       after.name());
		std::set<Instruction<ThreadRip> *> &liveInstructions(
			idom[cfg->ripToInstr->get(before)]);
		for (std::set<Instruction<ThreadRip> *>::iterator it = liveInstructions.begin();
		     it != liveInstructions.end();
		     it++) {
			Instruction<ThreadRip> *i = *it;
			std::set<std::pair<unsigned, IRExpr *> > &exprs(stashMap[i->rip.rip]);
			for (std::set<std::pair<unsigned, IRExpr *> >::iterator it2 = exprs.begin();
			     it2 != exprs.end();
			     it2++) {
				if (it2->first == i->rip.thread)
					content.push_back(it2->second);
			}
		}
	}

	void visit(HeapVisitor &hv) {
		/* These must not be live at GC time. */
		abort();
	}
	NAMED_CLASS
};

class slotMapT : public std::map<std::pair<unsigned, IRExpr *>, simulationSlotT>,
		 private GcCallback<> {
	typedef std::pair<unsigned, IRExpr *> key_t;
	void mk_slot(unsigned thr, IRExpr *e) {
		key_t key(thr, e);
		if (!count(key)) {
			simulationSlotT s = allocateSlot();
			insert(std::pair<key_t, simulationSlotT>(key, s));
		}
	}
	void runGc(HeapVisitor &hv) {
		slotMapT n(*this);
		clear();
		for (auto it = n.begin(); it != n.end(); it++) {
			std::pair<std::pair<unsigned, IRExpr *>, simulationSlotT> a = *it;
			hv(a.first.second);
			insert(a);
		}
	}
public:
	simulationSlotT next_slot;

	simulationSlotT rflagsSlot() {
		return simulationSlotT(0);
	}
	simulationSlotT allocateSlot() {
		simulationSlotT r = next_slot;
		next_slot.idx++;
		return r;
	}

	simulationSlotT operator()(unsigned thr, IRExpr *e) {
		iterator it = find(std::pair<unsigned, IRExpr *>(thr, e));
		assert(it != end());
		return it->second;
	}

	slotMapT() {}

	slotMapT(std::map<unsigned long, std::set<std::pair<unsigned, IRExpr *> > > &neededExpressions,
		 std::map<unsigned long, std::set<happensBeforeEdge *> > &happensBefore)
		: next_slot(1)
	{
		/* Allocate slots for expressions which we know we're
		 * going to have to stash at some point. */
		for (std::map<unsigned long, std::set<key_t> >::iterator it = neededExpressions.begin();
		     it != neededExpressions.end();
		     it++) {
			std::set<key_t> &s((*it).second);
			for (std::set<key_t>::iterator it2 = s.begin();
			     it2 != s.end();
			     it2++)
				mk_slot(it2->first, it2->second);
		}
		/* And the ones which we're going to receive in
		 * messages */
		for (std::map<unsigned long, std::set<happensBeforeEdge *> >::iterator it = happensBefore.begin();
		     it != happensBefore.end();
		     it++) {
			std::set<happensBeforeEdge *> &s(it->second);
			for (std::set<happensBeforeEdge *>::iterator it2 = s.begin();
			     it2 != s.end();
			     it2++) {
				happensBeforeEdge *hb = *it2;
				for (unsigned x = 0; x < hb->content.size(); x++)
					mk_slot(hb->after.thread, hb->content[x]);
			}
		}
	}

	void operator|=(const slotMapT &sm) {
		for (auto it = sm.begin(); it != sm.end(); it++)
			if (!count(it->first))
				insert(*it);
		if (sm.next_slot.idx > next_slot.idx)
			next_slot = sm.next_slot;
	}
};

/* Note that this needs manual visiting, despite not being GC
 * allocated itself! */
struct exprEvalPoint {
	bool invert;
	unsigned thread;
	IRExpr *e;

	void visit(HeapVisitor &hv) {
		hv(e);
	}

	exprEvalPoint(bool _invert,
		      unsigned _thread,
		      IRExpr *_e)
		: invert(_invert), thread(_thread), e(_e)
	{}
	bool operator <(const exprEvalPoint &o) const {
		if (invert < o.invert)
			return true;
		if (o.invert < invert)
			return false;
		if (thread < o.thread)
			return true;
		if (o.thread < thread)
			return false;
		return e < o.e;
	}
};

class ClientRip {
public:
	unsigned long rip;
	
	/* Each original instruction expands into a sequence of
	 * psuedo-instructions:
	 *
	 * start_of_instruction:
	 * <generate anything which is generated at the start of the instruction>
	 * receive_messages:
	 * <receive any incoming messages>
	 * original_instruction:
	 * <the original instruction>
	 * <store any newly-generated expressions>
	 * post_instr_checks:
	 * <rest of checks>
	 * generate_messages:
	 * <generate any necessary messages>
	 *
	 * When we degrade from thread rips to client rips, we
	 * introduce appropriate zero-length instructions for each of
	 * the new steps.
	 *
	 * We also have a special type of alternative instruction,
	 * restore_flags_and_branch, which just restores rflags and
	 * then jumps to post_instr_checks with the same RIP.
	 */
	enum instruction_type {
		start_of_instruction,
		receive_messages,
		original_instruction,
		post_instr_generate,
		post_instr_checks,
		generate_messages,

		restore_flags_and_branch,

		uninitialised /* Placeholder for a ClientRip whcih
			       * will be initialised later. */
	} type;
	std::set<unsigned> threads;
	std::set<unsigned> origThreads;

	ClientRip(unsigned long _rip, instruction_type _type)
		: rip(_rip), type(_type)
	{}
	ClientRip()
		: type(uninitialised)
	{}
	ClientRip(unsigned long _rip, const std::set<unsigned> &_threads, instruction_type _type)
		: rip(_rip), type(_type), threads(_threads), origThreads(_threads)
	{}
	ClientRip(const ClientRip &orig, instruction_type t)
		: rip(orig.rip), type(t), threads(orig.threads), origThreads(orig.origThreads)
	{}
	ClientRip(const ClientRip &orig, unsigned long _rip, instruction_type t)
		: rip(_rip), type(t), threads(orig.threads), origThreads(orig.origThreads)
	{}
	/* This ordering doesn't mean much, but it means that we can
	   use ClientRips as keys in std::map. */
	bool operator<(const ClientRip &k) const {
		if (type < k.type)
			return true;
		if (type > k.type)
			return false;
		if (rip < k.rip)
			return true;
		else if (rip > k.rip)
			return false;
		else if (threads < k.threads)
			return true;
		else
			return false;
	}
	bool operator!=(const ClientRip &k) const { return *this < k || k < *this; }
	bool operator==(const ClientRip &k) const { return !(*this != k); }

	bool threadLive(unsigned tid) const {
		return threads.count(tid) != 0;
	}
	bool noThreadsLive() const {
		return threads.empty();
	}
	void eraseThread(unsigned tid) {
		threads.erase(tid);
	}
};

class expressionEvalMapT : public std::map<unsigned long, std::set<exprEvalPoint> >,
			   private GcCallback<> {
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

	expressionEvalMapT(expressionDominatorMapT &exprDominatorMap) {
		for (expressionDominatorMapT::iterator it = exprDominatorMap.begin();
		     it != exprDominatorMap.end();
		     it++) {
			for (std::set<std::pair<bool, IRExpr *> >::iterator it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++)
				(*this)[it->first->rip.rip].insert(
					exprEvalPoint(
						it2->first,
						it->first->rip.thread,
						it2->second));
		}
	}
	expressionEvalMapT() {}
	void operator|=(const expressionEvalMapT &eem) {
		for (auto it = eem.begin(); it != eem.end(); it++)
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				(*this)[it->first].insert(*it2);
	}
};

class EnforceCrashPatchFragment : public PatchFragment<ClientRip> {
	std::set<happensBeforeEdge *> edges;

	void generateEpilogue(ClientRip rip);

public:
	EnforceCrashPatchFragment(std::map<unsigned long, std::set<happensBeforeEdge *> > &happensBeforePoints)
		: PatchFragment<ClientRip>()
	{
		for (std::map<unsigned long, std::set<happensBeforeEdge *> >::iterator it = happensBeforePoints.begin();
		     it != happensBeforePoints.end();
		     it++) {
			for (std::set<happensBeforeEdge *>::iterator it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++)
				edges.insert(*it2);
		}
	}

	char *asC(const char *ident, std::set<ClientRip> &entryPoints);
};

#endif /* !enforceCrash_hpp__ */
