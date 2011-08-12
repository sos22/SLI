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
		IRExpr *transformIex(IRExpr::Get *e) {
			if (!availThreads.count(e->tid))
				isGood = false;
			return NULL;
		}
		IRExpr *transformIex(IRExpr::Load *e) {
			if (!isAvail(e->rip))
				isGood = false;
			return NULL;
		}
		IRExpr *transformIex(IRExpr::HappensBefore *e) {
			isGood = false;
			return NULL;
		}
		IRExpr *transformIex(IRExpr::ClientCall *e) {
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
};

class expressionStashMapT : public std::map<unsigned long, std::set<std::pair<unsigned, IRExpr *> > > {
public:
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
				rip = roots[e->Iex.Get.tid];
			} else if (e->tag == Iex_ClientCall) {
				rip = e->Iex.ClientCall.callSite;
			} else if (e->tag == Iex_Load) {
				rip = e->Iex.Load.rip;
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
};

class happensBeforeEdge : public GarbageCollected<happensBeforeEdge> {
public:
	static unsigned next_msg_id;

	ThreadRip before;
	ThreadRip after;
	std::vector<IRExpr *> content;
	unsigned msg_id;

	happensBeforeEdge(bool invert, IRExpr::HappensBefore &hb,
			  instructionDominatorMapT &idom,
			  CFG<ThreadRip> *cfg,
			  expressionStashMapT &stashMap)
		: before(invert ? hb.after : hb.before),
		  after(invert ? hb.before : hb.after),
		  msg_id(next_msg_id++)
	{
		printf("%x: HBE %d:%lx -> %d:%lx\n",
		       msg_id,
		       before.thread,
		       before.rip,
		       after.thread,
		       after.rip);
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

class slotMapT : public std::map<std::pair<unsigned, IRExpr *>, simulationSlotT> {
	typedef std::pair<unsigned, IRExpr *> key_t;
	void mk_slot(unsigned thr, IRExpr *e) {
		key_t key(thr, e);
		if (!count(key)) {
			simulationSlotT s = allocateSlot();
			insert(std::pair<key_t, simulationSlotT>(key, s));
		}
	}
public:
	simulationSlotT next_slot;

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

	slotMapT(std::map<unsigned long, std::set<std::pair<unsigned, IRExpr *> > > &neededExpressions,
		 std::map<unsigned long, std::set<happensBeforeEdge *> > &happensBefore)
		: next_slot(0)
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
};

struct exprEvalPoint {
	bool invert;
	unsigned thread;
	IRExpr *e;
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
private:
	std::set<unsigned> threads;
public:
	std::set<unsigned> origThreads;

	ClientRip(unsigned long _rip)
		: rip(_rip)
	{}
	ClientRip()
		: rip(0)
	{}
	ClientRip(unsigned long _rip, const std::set<unsigned> &_threads)
		: rip(_rip), threads(_threads), origThreads(_threads)
	{}

	bool operator<(const ClientRip &k) const {
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

class EnforceCrashPatchFragment : public PatchFragment<ClientRip> {
	/* Mapping from expressions to the slots in which we've
	 * stashed them. */
	slotMapT &exprsToSlots;
	/* Mapping from instructions to the expressions which we need
	   to stash at those instructions for each thread. */
	std::map<unsigned long, std::set<std::pair<unsigned, IRExpr *> > > &neededExpressions;
	/* Mapping from instructions to the expressions which we need
	   to evaluate at those instructions.  If the expression is
	   equal to the other element of the pair then we will escape
	   from the patch. */
	std::map<unsigned long, std::set<exprEvalPoint> > &expressionEvalPoints;
	/* Mapping from instructions to the happens-before
	   relationships which are relevant at that instruction.
	   ``Relevant'' here means that the instruction is either the
	   start or end of the arc. */
	std::map<unsigned long, std::set<happensBeforeEdge *> > &happensBeforePoints;

	void emitInstruction(Instruction<ClientRip> *i);
	void emitGsPrefix() { emitByte(0x65); }
	ModRM modrmForSlot(simulationSlotT s) { return ModRM::absoluteAddress(s.idx * 8); }
	void emitMovRegToSlot(RegisterIdx offset, simulationSlotT slot);
	void emitMovSlotToReg(simulationSlotT slot, RegisterIdx offset);
	void emitAddRegToSlot(RegisterIdx reg, simulationSlotT slot);
	void emitAddSlotToReg(simulationSlotT slot, RegisterIdx reg);

	/* Emit a sequence to evaluate @e and then exit the patch if
	 * it's false.  The exit target is taken from @i's
	 * defaultNext.  The test is inverted if @invert is set.  @i
	 * must not be a branch instruction (i.e. branchNext must be
	 * clear). */
	void emitCheckExpressionOrEscape(const exprEvalPoint &p, Instruction<ClientRip> *i);

	bool emitEvalExpr(unsigned thread, IRExpr *e, RegisterIdx reg) __attribute__((warn_unused_result));
	bool emitCompareExprToZero(unsigned thread, IRExpr *e) __attribute__((warn_unused_result));

	simulationSlotT emitSaveRflags();
	void emitRestoreRflags(simulationSlotT);
	void emitPushf() { emitByte(0x9C); }
	void emitPopf() { emitByte(0x9D); }

	RegisterIdx instrModrmReg(Instruction<ClientRip> *i);

	void emitTestRegModrm(RegisterIdx, const ModRM &);

	class jcc_code {
		jcc_code(Byte _code) : code(_code) {}
	public:
		Byte code;
		static jcc_code nonzero;
		static jcc_code zero;
	};
	void emitJcc(ClientRip target, jcc_code branchType);

	void emitHappensBeforeEdgeBefore(const happensBeforeEdge *);
	void emitHappensBeforeEdgeAfter(const happensBeforeEdge *, Instruction<ClientRip> *);

	void emitLoadMessageToSlot(unsigned msg_id, unsigned message_slot, simulationSlotT simSlot,
				   RegisterIdx spill_reg);
	void emitStoreSlotToMessage(unsigned msg_id, unsigned message_slot, simulationSlotT simSlot,
				    RegisterIdx spill_reg1, RegisterIdx spill_reg2);

	void generateEpilogue(ClientRip rip);

public:
	EnforceCrashPatchFragment(slotMapT &_exprsToSlots,
				  std::map<unsigned long, std::set<std::pair<unsigned, IRExpr *> > > &_neededExpressions,
				  std::map<unsigned long, std::set<exprEvalPoint> > &_expressionEvalPoints,
				  std::map<unsigned long, std::set<happensBeforeEdge *> > &_happensBeforePoints)
		: PatchFragment<ClientRip>(),
		  exprsToSlots(_exprsToSlots),
		  neededExpressions(_neededExpressions),
		  expressionEvalPoints(_expressionEvalPoints),
		  happensBeforePoints(_happensBeforePoints)
	{
	}

	char *asC(const char *ident, std::set<ClientRip> &entryPoints);
};

#endif /* !enforceCrash_hpp__ */
