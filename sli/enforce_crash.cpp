#include <sys/fcntl.h>
#include <err.h>
#include <stdio.h>
#include <unistd.h>

#include "sli.h"
#include "inferred_information.hpp"
#include "oracle.hpp"
#include "offline_analysis.hpp"
#include "cnf.hpp"
#include "genfix.hpp"
#include "dnf.hpp"

class ShortCircuitFvTransformer : public IRExprTransformer {
public:
	FreeVariableMap &fv;
	ShortCircuitFvTransformer(FreeVariableMap &_fv)
		: fv(_fv)
	{}
	IRExpr *transformIex(IRExpr::FreeVariable *e)
	{
		return transformIRExpr(fv.get(e->key));
	}
};

static void
zapBindersAndFreeVariables(FreeVariableMap &m, StateMachine *sm)
{
	std::set<StateMachineSideEffectLoad *> loads;
	findAllLoads(sm, loads);
	bool done_something;
	do {
		done_something = false;
		/* Step one: zap binders */
		for (std::set<StateMachineSideEffectLoad *>::iterator it = loads.begin();
		     it != loads.end();
		     it++)
			applySideEffectToFreeVariables(*it, m, &done_something);
		/* Step two: short-circuit free variables */
		ShortCircuitFvTransformer trans(m);
		m.applyTransformation(trans, &done_something);
	} while (done_something);
}

class EnumNeededExpressionsTransformer : public IRExprTransformer {
public:
	std::set<IRExpr *> &out;
	EnumNeededExpressionsTransformer(std::set<IRExpr *> &_out)
		: out(_out)
	{}
	IRExpr *transformIex(IRExpr::RdTmp *e) {
		abort(); /* Should all have been eliminated by now */
	}
	IRExpr *transformIex(IRExpr::Get *e) {
		out.insert(currentIRExpr());
		return NULL;
	}
	IRExpr *transformIex(IRExpr::Load *e) {
		out.insert(currentIRExpr());
		/* Note that we don't recurse into the address
		   calculation here.  We can always evaluate this
		   expression after seeing the load itself, regardless
		   of where the address came from. */
		return NULL;
	}
	IRExpr *transformIex(IRExpr::HappensBefore *e) {
		out.insert(currentIRExpr());
		/* Again, we don't recurse into the details of the
		   happens before expression, because we only need the
		   two instructions, and not details of their
		   side-effects. */
		return NULL;
	}
	IRExpr *transformIex(IRExpr::ClientCall *e) {
		out.insert(currentIRExpr());
		return NULL;
	}
};
static void
enumerateNeededExpressions(IRExpr *e, std::set<IRExpr *> &out)
{
	EnumNeededExpressionsTransformer trans(out);
	trans.transformIRExpr(e);
}

class EnforceCrashCFG : public CFG<ThreadRip> {
	std::set<ThreadRip> &neededInstructions;
public:
	bool instructionUseful(Instruction<ThreadRip> *i) {
		return neededInstructions.count(i->rip) != 0;
	}
	EnforceCrashCFG(AddressSpace *as, std::set<ThreadRip> &ni)
		: CFG<ThreadRip>(as), neededInstructions(ni)
	{}
};

class instrToInstrSetMap : public std::map<Instruction<ThreadRip> *, std::set<Instruction<ThreadRip> *> > {
public:
	void print(FILE *f);
};
void
instrToInstrSetMap::print(FILE *f)
{
	for (iterator it = begin(); it != end(); it++) {
		fprintf(f, "%d:%lx[%p] -> {", it->first->rip.thread, it->first->rip.rip, it->first);
		for (std::set<Instruction<ThreadRip> *>::iterator it2 = it->second.begin();
		     it2 != it->second.end();
		     it2++) {
			if (it2 != it->second.begin())
				fprintf(f, ", ");
			fprintf(f, "%d:%lx[%p]", (*it2)->rip.thread, (*it2)->rip.rip, *it2);
		}
		fprintf(f, "}\n");
	}
}

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
happensAfterMapT::happensAfterMapT(DNF_Conjunction &c, CFG<ThreadRip> *cfg)
{
	for (unsigned x = 0; x < c.size(); x++) {
		if (c[x].second->tag == Iex_HappensBefore) {
			ThreadRip beforeRip = c[x].second->Iex.HappensBefore.before->rip;
			ThreadRip afterRip = c[x].second->Iex.HappensBefore.after->rip;
			Instruction<ThreadRip> *before = cfg->ripToInstr->get(beforeRip);
			Instruction<ThreadRip> *after = cfg->ripToInstr->get(afterRip);
			assert(before);
			assert(after);
			if (c[x].first) {
				Instruction<ThreadRip> *t = before;
				before = after;
				after = t;
			}
			happensAfter[before].insert(after);
			happensBefore[after].insert(before);
		}
	}
}

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

class cfgRootSetT : public std::set<Instruction<ThreadRip> *> {
public:
	cfgRootSetT(CFG<ThreadRip> *cfg, predecessorMapT &pred, happensAfterMapT &happensAfter);
};
cfgRootSetT::cfgRootSetT(CFG<ThreadRip> *cfg, predecessorMapT &pred, happensAfterMapT &happensBefore)
{
	std::set<Instruction<ThreadRip> *> toEmit;
	for (CFG<ThreadRip>::ripToInstrT::iterator it = cfg->ripToInstr->begin();
	     it != cfg->ripToInstr->end();
	     it++)
		toEmit.insert(it.value());
	while (!toEmit.empty()) {
		/* Find one with no predecessors and emit that */
		std::set<Instruction<ThreadRip> *>::iterator it;
		for (it = toEmit.begin(); it != toEmit.end(); it++) {
			assert(pred.count(*it));
			if (pred[*it].size() == 0)
				break;
		}
		if (it == toEmit.end()) {
			/* Every instruction is part of a cycle.
			   Arbitrarily declare that the first one is
			   the root and emit that. */
			it = toEmit.begin();
		}
		/* We're going to use *it as a root.  Purge it and
		   everything reachable from it from the toEmit
		   set. */
		std::vector<Instruction<ThreadRip> *> toPurge;
		std::set<Instruction<ThreadRip> *> donePurge;
		toPurge.push_back(*it);
		while (!toPurge.empty()) {
			Instruction<ThreadRip> *purge = toPurge.back();
			toPurge.pop_back();
			if (donePurge.count(purge))
				continue;
			/* The loop breaking heuristic, above, isn't
			   terribly clever, and can sometimes choose a
			   bad node in a way which leads to one root
			   being reachable from another.  Fortunately,
			   it's easy to fix by just purging the
			   pseudo-root here. */
			erase(purge);

			toEmit.erase(purge);
			if (toEmit.count(purge)) {
				if (purge->branchNextI)
					toPurge.push_back(purge->branchNextI);
				if (purge->defaultNextI)
					toPurge.push_back(purge->defaultNextI);
			}
			donePurge.insert(purge);
		}
		/* Emit the new root */
		insert(*it);
	}
}

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
instructionDominatorMapT::instructionDominatorMapT(CFG<ThreadRip> *cfg,
						   predecessorMapT &predecessors,
						   happensAfterMapT &happensAfter,
						   const std::set<ThreadRip> &neededRips)
{
	std::set<Instruction<ThreadRip> *> neededInstructions;
	for (std::set<ThreadRip>::const_iterator it = neededRips.begin();
	     it != neededRips.end();
	     it++)
		neededInstructions.insert(cfg->ripToInstr->get(*it));

	/* Start by assuming that everything dominates everything */
	cfgRootSetT entryPoints(cfg, predecessors, happensAfter);
	std::set<Instruction<ThreadRip> *> needingRecompute;
	for (CFG<ThreadRip>::ripToInstrT::iterator it = cfg->ripToInstr->begin();
	     it != cfg->ripToInstr->end();
	     it++) {
		insert(std::pair<Instruction<ThreadRip> *, std::set<Instruction<ThreadRip> *> >(
			       it.value(),
			       neededInstructions));
		needingRecompute.insert(it.value());
	}

	/* Now iterate to a fixed point. */
	while (!needingRecompute.empty()) {
		Instruction<ThreadRip> *i;
		{
			std::set<Instruction<ThreadRip> *>::iterator it = needingRecompute.begin();
			i = *it;
			needingRecompute.erase(it);
		}

		std::set<Instruction<ThreadRip> *> &slot( (*this)[i] );

		/* new entry domination set is intersection of all of
		 * the predecessor's exit sets.  If there are no
		 * predecessor sets then the entry domination set is
		 * empty. */
		std::set<Instruction<ThreadRip> *> newDominators;
		std::set<Instruction<ThreadRip> *> &allPreds(predecessors[i]);
		if (!allPreds.empty()) {
			newDominators = slot;

			for (std::set<Instruction<ThreadRip> *>::iterator predIt = allPreds.begin();
			     predIt != allPreds.end();
			     predIt++) {
				Instruction<ThreadRip> *predecessor = *predIt;
				assert(count(predecessor));
				std::set<Instruction<ThreadRip> *> &pred_dominators((*this)[predecessor]);
				for (std::set<Instruction<ThreadRip> *>::iterator it2 = newDominators.begin();
				     it2 != newDominators.end();
					) {
					if (pred_dominators.count(*it2)) {
						it2++;
					} else {
						/* *it2 is dominated
						   by us, but not by
						   our predecessor.
						   That's a
						   contradiction.
						   Resolve it by
						   erasing *it2 from
						   our dominator
						   set. */
						newDominators.erase(it2++);
					}
				}
			}
		}

		/* Every instruction dominates itself. */
		if (neededInstructions.count(i))
			newDominators.insert(i);

		/* Anything dominated by something which is ordered
		   before us is also dominated by us.  Happens-before
		   edges are different to ordinary edges, because
		   happens-before edges are always satisfied, whereas
		   for ordinary control edges only one per instruction
		   will be satisfied. */
		std::set<Instruction<ThreadRip> *> &orderedBefore(happensAfter.happensBefore[i]);
		for (std::set<Instruction<ThreadRip> *>::iterator it = orderedBefore.begin();
		     it != orderedBefore.end();
		     it++) {
			std::set<Instruction<ThreadRip> *> &predecessor_dominates( (*this)[*it] );
			for (std::set<Instruction<ThreadRip> *>::iterator it2 = predecessor_dominates.begin();
			     it2 != predecessor_dominates.end();
			     it2++)
				newDominators.insert(*it2);
		}

		if (newDominators != slot) {
			slot = newDominators;
			if (i->branchNextI)
				needingRecompute.insert(i->branchNextI);
			if (i->defaultNextI)
				needingRecompute.insert(i->defaultNextI);
			if (happensAfter.happensAfter.count(i)) {
				std::set<Instruction<ThreadRip> *> &orderedAfter(happensAfter.happensAfter[i]);
				for (std::set<Instruction<ThreadRip> *>::iterator it = orderedAfter.begin();
				     it != orderedAfter.end();
				     it++)
					needingRecompute.insert(*it);
			}
		}
	}
}

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
expressionDominatorMapT::expressionDominatorMapT(DNF_Conjunction &c,
						 CFG<ThreadRip> *cfg,
						 const std::set<ThreadRip> &neededRips)
{
	happensAfterMapT happensBefore(c, cfg);
	predecessorMapT pred(cfg);

	/* Figure out where the various instructions become
	 * available. */
	instructionDominatorMapT idom(cfg, pred, happensBefore, neededRips);
	this->idom = idom;

	/* First, figure out where the various expressions could in
	   principle be evaluated. */
	std::map<Instruction<ThreadRip> *, std::set<std::pair<bool, IRExpr *> > > evalable;
	for (instructionDominatorMapT::iterator it = idom.begin();
	     it != idom.end();
	     it++) {
		evalable[it->first].clear();
		for (unsigned x = 0; x < c.size(); x++) {
			std::set<unsigned> availThreads;
			for (std::set<Instruction<ThreadRip> *>::iterator it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++)
				availThreads.insert((*it2)->rip.thread);
			if (evaluatable(c[x].second, it->second, availThreads, cfg))
				evalable[it->first].insert(c[x]);
		}
	}


	/* Just find all of the things which are evaluatable at X but
	   not at some of X's predecessors, for any instruction X.  I'm
	   not entirely convinced that that's *precisely* what we're
	   after, but it's a pretty reasonable approximation. */
	for (std::map<Instruction<ThreadRip> *, std::set<std::pair<bool, IRExpr *> > >::iterator it = evalable.begin();
	     it != evalable.end();
	     it++) {
		Instruction<ThreadRip> *i = it->first;
		std::set<std::pair<bool, IRExpr *> > &theoreticallyEvaluatable(evalable[i]);
		std::set<std::pair<bool, IRExpr *> > &actuallyEvalHere((*this)[i]);
		std::set<Instruction<ThreadRip> *> &predecessors(pred[i]);
		std::set<Instruction<ThreadRip> *> *orderingPredecessors;

		if (happensBefore.happensBefore.count(i))
			orderingPredecessors = &happensBefore.happensBefore[i];
		for (std::set<std::pair<bool, IRExpr *> >::iterator it2 = theoreticallyEvaluatable.begin();
		     it2 != theoreticallyEvaluatable.end();
		     it2++) {
			bool takeIt = false;
			for (std::set<Instruction<ThreadRip> *>::iterator it3 = predecessors.begin();
			     !takeIt && it3 != predecessors.end();
			     it3++) {
				Instruction<ThreadRip> *predecessor = *it3;
				if (!evalable[predecessor].count(*it2))
					takeIt = true;
			}
			/* If it's evaluatable at *any* happens-before
			   predecessor then we don't want to take it,
			   because happens-before edges are always
			   satisfied and it's therefore certain that
			   it will have already been evaluated. */
			if (takeIt && orderingPredecessors) {
				for (std::set<Instruction<ThreadRip> *>::iterator it3 = orderingPredecessors->begin();
				     takeIt && it3 != orderingPredecessors->end();
				     it3++) {
					if (evalable[*it3].count(*it2))
						takeIt = false;
				}
			}
			if (takeIt) {
				printf("Eval ");
				ppIRExpr(it2->second, stdout);
				printf(" at %d:%lx\n", i->rip.thread, i->rip.rip);
				actuallyEvalHere.insert(*it2);
			}
		}
	}
}

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
	static unsigned next_msg_id;

public:
	StateMachineSideEffectMemoryAccess *before;
	StateMachineSideEffectMemoryAccess *after;
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
		printf("HBE %d:%lx -> %d:%lx\n",
		       before->rip.thread,
		       before->rip.rip,
		       after->rip.thread,
		       after->rip.rip);
		std::set<Instruction<ThreadRip> *> &liveInstructions(
			idom[cfg->ripToInstr->get(hb.before->rip)]);
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
unsigned happensBeforeEdge::next_msg_id = 0xaabb;

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

class expressionEvalMapT : public std::map<unsigned long, std::set<exprEvalPoint> > {
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
};

class simulationSlotT {
public:
	int idx;
	simulationSlotT(int _idx) : idx(_idx) {}
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
					mk_slot(hb->after->rip.thread, hb->content[x]);
			}
		}
	}
};

class ClientRip {
public:
	unsigned long rip;
	std::set<unsigned> threads;

	ClientRip(unsigned long _rip)
		: rip(_rip)
	{}
	ClientRip()
		: rip(0)
	{}
	ClientRip(unsigned long _rip, const std::set<unsigned> &_threads)
		: rip(_rip), threads(_threads)
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
};

EnforceCrashPatchFragment::jcc_code EnforceCrashPatchFragment::jcc_code::zero(0x84);
EnforceCrashPatchFragment::jcc_code EnforceCrashPatchFragment::jcc_code::nonzero(0x85);

/* Is this opcode byte a prefix opcode? */
static bool
isPrefix(unsigned char opcode)
{
	return ((opcode >= 0x40 && opcode <= 0x4f) ||
		(opcode == 0x26) ||
		(opcode == 0x2E) ||
		(opcode == 0x36) ||
		(opcode == 0x3D) ||
		(opcode >= 64 && opcode <= 0x67) ||
		(opcode == 0xF0) ||
		(opcode == 0xF2) ||
		(opcode == 0xF3));
}

static unsigned
instrOpcode(Instruction<ClientRip> *i)
{
	unsigned j;
	j = 0;
	/* Skip prefixes */
	while (j < i->len && isPrefix(i->content[j]))
		j++;
	assert(j < i->len);
	if (i->content[j] == 0x0F) {
		/* Two-byte opcode */
		assert(j+1 < i->len);
		return 0x0F00 | i->content[j+1];
	} else {
		return i->content[j];
	}
}

EnforceCrashPatchFragment::RegisterIdx
EnforceCrashPatchFragment::instrModrmReg(Instruction<ClientRip> *i)
{
	unsigned j;
	bool extend;

	j = 0;
	extend = false;

	/* Skip prefixes */
	while (j < i->len && isPrefix(i->content[j])) {
		if (i->content[j] >= 0x40 && i->content[j] <= 0x4f)
			if (i->content[j] & 4)
				extend = true;
		j++;
	}
	assert(j < i->len);
	/* Skip opcode */
	if (i->content[j] == 0x0F)
		j++;
	j++;
	assert(j < i->len);
	/* Next one must be modrm */
	unsigned char modrm = i->content[j];
	unsigned res = (modrm >> 3) & 7;
	if (extend)
		res |= 8;
	RegisterIdx r = RegisterIdx::RAX;
	r.idx = res;
	return r;
}

void
EnforceCrashPatchFragment::emitMovRegToSlot(RegisterIdx offset, simulationSlotT slot)
{
	emitGsPrefix();
	emitMovRegisterToModrm(offset, modrmForSlot(slot));
}

void
EnforceCrashPatchFragment::emitMovSlotToReg(simulationSlotT slot, RegisterIdx offset)
{
	emitGsPrefix();
	emitMovModrmToRegister(modrmForSlot(slot), offset);
}

void
EnforceCrashPatchFragment::emitAddRegToSlot(RegisterIdx reg, simulationSlotT slot)
{
	emitGsPrefix();
	emitAddRegToModrm(reg, modrmForSlot(slot));
}

void
EnforceCrashPatchFragment::emitAddSlotToReg(simulationSlotT slot, RegisterIdx reg)
{
	emitGsPrefix();
	emitAddModrmToReg(modrmForSlot(slot), reg);
}

void
EnforceCrashPatchFragment::emitTestRegModrm(RegisterIdx reg, const ModRM &modrm)
{
	unsigned char rex = 0x48;
	if (reg.idx >= 8) {
		rex |= 4;
		reg.idx -= 8;
		assert(reg.idx < 8);
	}
	if (modrm.extendRm)
		rex |= 1;
	emitByte(rex);
	emitByte(0x85);
	emitModrm(modrm, reg);
}

void
EnforceCrashPatchFragment::emitJcc(ClientRip target, jcc_code branchType)
{
	emitByte(0x0F);
	emitByte(branchType.code);
	emitByte(0); /* Pad */
	emitByte(0); /* Pad */
	emitByte(0); /* Pad */
	emitByte(0); /* Pad */
	relocs.push_back(new RipRelativeBranchRelocation<ClientRip>(content.size() - 4,
								    4,
								    target));
}

simulationSlotT
EnforceCrashPatchFragment::emitSaveRflags()
{
	skipRedZone();
	emitPushf();
	simulationSlotT t = exprsToSlots.allocateSlot();
	emitMovRegToSlot(RegisterIdx::RAX, t);
	emitPopQ(RegisterIdx::RAX);
	restoreRedZone();
	simulationSlotT s = exprsToSlots.allocateSlot();
	emitMovRegToSlot(RegisterIdx::RAX, s);
	emitMovSlotToReg(t, RegisterIdx::RAX);

	return s;
}

void
EnforceCrashPatchFragment::emitRestoreRflags(simulationSlotT s)
{
	skipRedZone();
	simulationSlotT t = exprsToSlots.allocateSlot();
	emitMovRegToSlot(RegisterIdx::RAX, t);
	emitMovSlotToReg(s, RegisterIdx::RAX);
	emitPushQ(RegisterIdx::RAX);
	emitPopf();
	emitMovSlotToReg(t, RegisterIdx::RAX);
	restoreRedZone();
}

bool
EnforceCrashPatchFragment::emitEvalExpr(unsigned thread, IRExpr *e, RegisterIdx reg)
{
	{
		slotMapT::iterator it = exprsToSlots.find(std::pair<unsigned, IRExpr *>(thread, e));
		if (it != exprsToSlots.end()) {
			emitMovSlotToReg(it->second, reg);
			return true;
		}
	}

	switch (e->tag) {
	case Iex_Const:
		emitMovQ(reg, e->Iex.Const.con->Ico.U64);
		return true;

	case Iex_Unop:
		switch (e->Iex.Unop.op) {
		case Iop_Neg64:
			if (!emitEvalExpr(thread, e->Iex.Unop.arg, reg))
				return false;
			emitNegModrm(ModRM::directRegister(reg));
			return true;
		default:
			break;
		}
		break;

	case Iex_Binop:
		switch (e->Iex.Binop.op) {
		case Iop_CmpEQ64: {
			simulationSlotT old_rax = exprsToSlots.allocateSlot();
			if (!emitEvalExpr(thread, e->Iex.Binop.arg1, reg))
				return false;
			simulationSlotT t = exprsToSlots.allocateSlot();
			emitMovRegToSlot(reg, t);
			if (!emitEvalExpr(thread, e->Iex.Binop.arg2, reg))
				return false;
			emitGsPrefix();
			emitCmpRegModrm(reg, modrmForSlot(t));

			if (reg != RegisterIdx::RAX)
				emitMovRegToSlot(RegisterIdx::RAX, old_rax);
			/* Clear %rax */
			emitMovQ(RegisterIdx::RAX, 0);
			/* seteq al */
			emitByte(0x0F);
			emitByte(0x94);
			emitByte(0xC0); /* mod = 3, reg = 0, rm = 0 */
			if (reg != RegisterIdx::RAX) {
				emitMovRegisterToModrm(RegisterIdx::RAX, ModRM::directRegister(reg));
				emitMovSlotToReg(old_rax, RegisterIdx::RAX);
			}
			return true;
		}
		default:
			break;
		}
		break;
	case Iex_Associative:
		switch (e->Iex.Associative.op) {
		case Iop_Add64: {
			if (!emitEvalExpr(thread, e->Iex.Associative.contents[0], reg))
				return false;
			if (e->Iex.Associative.nr_arguments == 1)
				return true;
			simulationSlotT acc = exprsToSlots.allocateSlot();
			emitMovRegToSlot(reg, acc);
			for (int x = 1; x < e->Iex.Associative.nr_arguments - 1; x++) {
				if (!emitEvalExpr(thread, e->Iex.Associative.contents[x], reg))
					return false;
				emitAddRegToSlot(reg, acc);
			}
			if (!emitEvalExpr(thread, e->Iex.Associative.contents[e->Iex.Associative.nr_arguments - 1],
					  reg))
				return false;
			emitAddSlotToReg(acc, reg);
			return true;
		}
		default:
			break;
		}
		break;
	default:
		break;
	}

	fprintf(stderr, "WARNING: Cannot evaluate ");
	ppIRExpr(e, stderr);
	fprintf(stderr, "\n");
	dbg_break("Hello");
	return false;
}

bool
EnforceCrashPatchFragment::emitCompareExprToZero(unsigned thread, IRExpr *e)
{
	RegisterIdx reg = RegisterIdx::RAX;
	bool r;
	simulationSlotT spill = exprsToSlots.allocateSlot();
	emitMovRegToSlot(reg, spill);
	r = emitEvalExpr(thread, e, reg);
	if (r)
		emitTestRegModrm(reg, ModRM::directRegister(reg));
	emitMovSlotToReg(spill, reg);
	return r;
}

void
EnforceCrashPatchFragment::emitCheckExpressionOrEscape(const exprEvalPoint &e,
						       Instruction<ClientRip> *i)
{
	if (!i->rip.threads.count(e.thread))
		return;
	assert(!i->branchNext.rip);
	IRExpr *expr;
	expr = e.e;
	bool invert = e.invert;

	/* Special case: if the expression is already in the form x == 0
	   then we can just flip the invert flag and then evaluate x
	   directly. */
	if (expr->tag == Iex_Binop &&
	    expr->Iex.Binop.op == Iop_CmpEQ64 &&
	    expr->Iex.Binop.arg1->tag == Iex_Const &&
	    expr->Iex.Binop.arg1->Iex.Const.con->Ico.U64 == 0) {
		invert = !invert;
		expr = expr->Iex.Binop.arg2;
	}

	if (!emitCompareExprToZero(e.thread, expr))
		return;

	jcc_code branch_type = invert ? jcc_code::nonzero : jcc_code::zero;
	assert(i->defaultNextI);
	ClientRip n = i->defaultNextI->rip;
	n.threads.erase(e.thread);
	/* XXX several things wrong here:

	   -- Don't restore rflags if we branch
	   -- Don't evaluate expressions from target thread if we branch to an instruction
	      with additional expressions.
	*/
	emitJcc(n, branch_type);
}

void
EnforceCrashPatchFragment::emitLoadMessageToSlot(unsigned msg_id, unsigned msgslot, simulationSlotT simslot,
						 RegisterIdx spill)
{
	emitMovQ(spill, 0);
	addLateReloc(late_relocation(content.size() - 8,
				     8,
				     vex_asprintf("__msg_%d_slot_%d", msg_id, msgslot),
				     0,
				     false));
	emitMovModrmToRegister(ModRM::memAtRegister(spill), spill);
	emitMovRegToSlot(spill, simslot);
}

void
EnforceCrashPatchFragment::emitStoreSlotToMessage(unsigned msg_id, unsigned msgslot, simulationSlotT simslot,
						  RegisterIdx spill1, RegisterIdx spill2)
{
	emitMovQ(spill1, 0);
	addLateReloc(late_relocation(content.size() - 8,
				     8,
				     vex_asprintf("__msg_%d_slot_%d", msg_id, msgslot),
				     0,
				     false));
	emitMovSlotToReg(simslot, spill2);
	emitMovRegisterToModrm(spill2, ModRM::memAtRegister(spill1));
}

void
EnforceCrashPatchFragment::emitHappensBeforeEdgeAfter(const happensBeforeEdge *hb,
						      Instruction<ClientRip> *i)
{
	assert(!i->branchNextI);

	simulationSlotT rflags = emitSaveRflags();
	simulationSlotT rdi = exprsToSlots.allocateSlot();
	emitMovRegToSlot(RegisterIdx::RDI, rdi);
	emitMovQ(RegisterIdx::RDI, hb->msg_id);
	emitCallSequence("happensBeforeEdge__after", false);
	emitMovSlotToReg(rdi, RegisterIdx::RDI);

	emitTestRegModrm(RegisterIdx::RAX, ModRM::directRegister(RegisterIdx::RAX));
	/* XXX as usual, not quite right */
	ClientRip destinationIfThisFails = i->defaultNextI ? i->defaultNextI->rip : i->defaultNext;
	destinationIfThisFails.threads.erase(hb->after->rip.thread);
	emitJcc(destinationIfThisFails, jcc_code::zero);

	for (unsigned x = 0; x < hb->content.size(); x++) {
		simulationSlotT s = exprsToSlots(hb->after->rip.thread, hb->content[x]);
		emitLoadMessageToSlot(hb->msg_id, x, s, RegisterIdx::RDI);
	}
	emitMovSlotToReg(rdi, RegisterIdx::RDI);
	emitRestoreRflags(rflags);
}

void
EnforceCrashPatchFragment::emitHappensBeforeEdgeBefore(const happensBeforeEdge *hb)
{
	simulationSlotT rdi = exprsToSlots.allocateSlot();
	emitMovRegToSlot(RegisterIdx::RDI, rdi);
	simulationSlotT r13 = exprsToSlots.allocateSlot();
	emitMovRegToSlot(RegisterIdx::R13, r13);

	for (unsigned x = 0; x < hb->content.size(); x++) {
		simulationSlotT s = exprsToSlots(hb->before->rip.thread, hb->content[x]);
		emitStoreSlotToMessage(hb->msg_id, x, s, RegisterIdx::RDI, RegisterIdx::R13);
	}
	emitMovQ(RegisterIdx::RDI, hb->msg_id);
	emitCallSequence("happensBeforeEdge__before", false);
	emitMovSlotToReg(r13, RegisterIdx::R13);
	emitMovSlotToReg(rdi, RegisterIdx::RDI);
}

void
EnforceCrashPatchFragment::emitInstruction(Instruction<ClientRip> *i)
{
	if (i->rip.threads.empty()) {
		emitJmpToRipHost(i->rip.rip);
		return;
	}
	std::set<std::pair<unsigned, IRExpr *> > *neededExprs = NULL;
	if (neededExpressions.count(i->rip.rip)) {
		neededExprs = &neededExpressions[i->rip.rip];
		/* Need to emit gunk to store the appropriate
		   generated expression.  That'll either be a simple
		   register access or a memory load of some sort. */
		for (std::set<std::pair<unsigned, IRExpr *> >::iterator it = neededExprs->begin();
		     it != neededExprs->end();
		     it++) {
			if (!i->rip.threads.count(it->first))
				continue;
			IRExpr *e = it->second;
			if (e->tag == Iex_Get) {
				/* Easy case: just store the register in its slot */
				simulationSlotT s = exprsToSlots(it->first, e);
				emitMovRegToSlot(RegisterIdx::fromVexOffset(e->Iex.Get.offset), s);
			} else if (e->tag == Iex_ClientCall) {
				/* Do this after emitting the instruction */
			} else {
				assert(e->tag == Iex_Load);
				assert(neededExprs->size() == 1);
				/* Much more difficult case.  This
				   depends on the type of instruction
				   which we're looking at. */
				switch (instrOpcode(i)) {
				case 0x8b:
					/* Simple load from modrm to
					 * register.  Deal with it
					 * later. */
					break;
				default:
					abort();
				}
			}
		}
	}

	/* If this instruction is supposed to happen after some other
	 * instruction then we might want to insert a delay before
	 * running it. */
	std::set<happensBeforeEdge *> *hbEdges = NULL;
	if (happensBeforePoints.count(i->rip.rip)) {
		hbEdges = &happensBeforePoints[i->rip.rip];
		for (std::set<happensBeforeEdge *>::iterator it = hbEdges->begin();
		     it != hbEdges->end();
		     it++) {
			const happensBeforeEdge *hb = *it;
			assert(hb->after);
			if (hb->after->rip.rip == i->rip.rip &&
			    i->rip.threads.count(hb->after->rip.thread))
				emitHappensBeforeEdgeAfter(hb, i);
		}
	}

	PatchFragment<ClientRip>::emitInstruction(i);

	if (neededExprs) {
		for (std::set<std::pair<unsigned, IRExpr *> >::iterator it = neededExprs->begin();
		     it != neededExprs->end();
		     it++) {
			if (!i->rip.threads.count(it->first))
				continue;
			IRExpr *e = it->second;
			if (e->tag == Iex_Get) {
				/* Already handled */
			} else if (e->tag == Iex_ClientCall) {
				/* The result of the call should now be in %rax */
				simulationSlotT s = exprsToSlots(it->first, e);
				emitMovRegToSlot(RegisterIdx::RAX, s);
			} else {
				assert(e->tag == Iex_Load);
				switch (instrOpcode(i)) {
				case 0x8b: {
					/* Load from memory to modrm.
					 * Nice and easy. */
					simulationSlotT s = exprsToSlots(it->first, e);
					emitMovRegToSlot(instrModrmReg(i), s);
					break;
				}
				default:
					abort();
				}
			}
		}
	}

	if (expressionEvalPoints.count(i->rip.rip)) {
		std::set<exprEvalPoint> &expressionsToEval(expressionEvalPoints[i->rip.rip]);

		bool doit = false;
		for (std::set<exprEvalPoint>::iterator it = expressionsToEval.begin();
		     !doit && it != expressionsToEval.end();
		     it++)
			if (i->rip.threads.count(it->thread))
				doit = true;
		if (doit) {
			simulationSlotT rflags = emitSaveRflags();
			for (std::set<exprEvalPoint>::iterator it = expressionsToEval.begin();
			     it != expressionsToEval.end();
			     it++)
				emitCheckExpressionOrEscape(*it, i);
			emitRestoreRflags(rflags);
		}
	}

	/* Now look at the before end of happens before
	 * relationships. */
	if (hbEdges) {
		for (std::set<happensBeforeEdge *>::iterator it = hbEdges->begin();
		     it != hbEdges->end();
		     it++) {
			happensBeforeEdge *hb = *it;
			assert(hb->before);
			if (hb->before->rip.rip == i->rip.rip &&
			    i->rip.threads.count(hb->before->rip.thread))
				emitHappensBeforeEdgeBefore(hb);
		}
	}
}

ClientRip threadRipToClientRip(const ThreadRip &k)
{
	return ClientRip(k.rip);
}
unsigned long __trivial_hash_function(const ClientRip &k)
{
	return k.rip;
}

static EarlyRelocation<ClientRip> *
duplicateEarlyRelocAtNewThreadSet(EarlyRelocation<ClientRip> *er, const std::set<unsigned> &threads)
{
	if (RipRelativeRelocation<ClientRip> *rrr =
	    dynamic_cast<RipRelativeRelocation<ClientRip> *>(er)) {
		return new RipRelativeRelocation<ClientRip>(rrr->offset, rrr->size,
							    ClientRip(rrr->target.rip, threads),
							    rrr->nrImmediateBytes);
	} else if (RipRelativeBranchRelocation<ClientRip> *rrbr =
		   dynamic_cast<RipRelativeBranchRelocation<ClientRip> *>(er)) {
		return new RipRelativeBranchRelocation<ClientRip>(rrbr->offset, rrbr->size,
								  ClientRip(rrbr->target.rip, threads));

	} else {
		abort();
	}
}

template <typename k, typename v> void
mapKeys(std::set<k> &out, std::map<k, v> &m)
{
	for (typename std::map<k, v>::iterator it = m.begin();
	     it != m.end();
	     it++)
		out.insert(it->first);
}

template <typename t> void
powerSet(const std::set<t> &_in, std::set<std::set<t> > &out)
{
	/* It's useful to be able to refer to the elements of @_in by
	   index, which means we really want to put them in a
	   vector. */
	std::vector<t> in;
	in.reserve(_in.size());
	for (typename std::set<t>::iterator it = _in.begin();
	     it != _in.end();
	     it++)
		in.push_back(*it);
	/* @live tells you which elements of @in you want to include
	   in the next item.  It's pretty much the binary
	   representation of the number of items currently in @out,
	   and counts from 0 to 1111..., with an appropriate number of
	   ones, and hence covers every possible subvector of @in. */
	std::vector<bool> live;
	live.resize(in.size());
	while (1) {
		/* Insert new item */
		std::set<t> item;
		for (unsigned x = 0; x < live.size(); x++)
			if (live[x])
				item.insert(in[x]);
		out.insert(item);

		/* Advance @live.  This is just the add-one algorithm
		   in binary.  There might be a more efficient way to
		   do this. :) */
		unsigned x;
		for (x = 0; x < live.size(); x++) {
			if (live[x]) {
				live[x] = false;
			} else {
				live[x] = true;
				break;
			}
		}
		if (x == live.size())
			break;
	}
}

static void
duplicateCFGAtThreadSet(CFG<ClientRip> *cfg, std::set<unsigned long> &rips, const std::set<unsigned> &threads)
{
	std::map<Instruction<ClientRip> *, Instruction<ClientRip> *> m;

	for (std::set<unsigned long>::iterator it = rips.begin();
	     it != rips.end();
	     it++) {
		Instruction<ClientRip> *orig = cfg->ripToInstr->get(ClientRip(*it));
		ClientRip newRip(*it, threads);
		assert(!cfg->ripToInstr->hasKey(newRip));
		Instruction<ClientRip> *nr = new Instruction<ClientRip>(*orig);
		nr->rip = newRip;
		if (nr->defaultNext.rip)
			nr->defaultNext.threads = threads;
		if (nr->branchNext.rip)
			nr->branchNext.threads = threads;
		for (unsigned x = 0; x < nr->relocs.size(); x++)
			nr->relocs[x] = duplicateEarlyRelocAtNewThreadSet(nr->relocs[x], threads);
		cfg->ripToInstr->set(newRip, nr);
		m[orig] = nr;
	}

	for (std::set<unsigned long>::iterator it = rips.begin();
	     it != rips.end();
	     it++) {
		ClientRip newRip(*it, threads);
		Instruction<ClientRip> *n = cfg->ripToInstr->get(newRip);
		assert(n);
		if (n->defaultNextI) {
			n->defaultNextI = m[n->defaultNextI];
			assert(n->defaultNextI);
		}
		if (n->branchNextI) {
			n->branchNextI = m[n->branchNextI];
			assert(n->branchNextI);
		}
	}
}

static CFG<ClientRip> *
convertCFGFromThreadRipToClientRips(CFG<ThreadRip> *cfg,
				    std::set<unsigned> &neededThreads,
				    expressionDominatorMapT &exprDominatorMap)
{
	CFG<ClientRip> *degradedCfg = cfg->degrade<ClientRip, threadRipToClientRip>();

	/* And now expand it again so that we can do the power-set
	 * construction. */
	std::set<std::set<unsigned> > threadPower;
	{
		std::set<std::set<unsigned> > threadPower1;
		powerSet(neededThreads, threadPower1);
		for (std::set<std::set<unsigned> >::iterator it = threadPower1.begin();
		     it != threadPower1.end();
		     it++)
			threadPower.insert(*it);
	}
	printf("Power threads:\n");
	for (std::set<std::set<unsigned> >::iterator it = threadPower.begin();
	     it != threadPower.end();
	     it++) {
		printf("\t");
		for (std::set<unsigned>::const_iterator it2 = it->begin();
		     it2 != it->end();
		     it2++)
			printf("%d ", *it2);
		printf("\n");
	}
	std::set<unsigned long> rawRips;
	for (CFG<ClientRip>::ripToInstrT::iterator it = degradedCfg->ripToInstr->begin();
	     it != degradedCfg->ripToInstr->end();
	     it++)
		rawRips.insert(it.key().rip);
	for (std::set<std::set<unsigned> >::iterator it = threadPower.begin();
	     it != threadPower.end();
	     it++) {
		if (it->size() != 0)
			duplicateCFGAtThreadSet(degradedCfg, rawRips, *it);
	}

	return degradedCfg;
}

static void
partitionCrashCondition(DNF_Conjunction &c, FreeVariableMap &fv,
			std::map<unsigned, ThreadRip> &roots,
			AddressSpace *as)
{
	/* Figure out what we actually need to keep track of */
	std::set<IRExpr *> neededExpressions;
	for (unsigned x = 0; x < c.size(); x++)
		enumerateNeededExpressions(c[x].second, neededExpressions);

	/* and where the needed expressions are calculated */
	std::set<ThreadRip> neededRips;
	for (std::set<IRExpr *>::iterator it = neededExpressions.begin();
	     it != neededExpressions.end();
	     it++) {
		IRExpr *e = *it;
		if (e->tag == Iex_Get) {
			neededRips.insert(roots[e->Iex.Get.tid]);
		} else if (e->tag == Iex_ClientCall) {
			neededRips.insert(e->Iex.ClientCall.callSite);
		} else if (e->tag == Iex_Load) {
			neededRips.insert(e->Iex.Load.rip);
		} else if (e->tag == Iex_HappensBefore) {
			neededRips.insert(e->Iex.HappensBefore.before->rip);
			neededRips.insert(e->Iex.HappensBefore.after->rip);
		} else {
			abort();
		}
	}

	/* and which threads are relevant */
	std::set<unsigned> neededThreads;
	for (std::set<ThreadRip>::iterator it = neededRips.begin();
	     it != neededRips.end();
	     it++)
		neededThreads.insert(it->thread);

	/* Build the CFG */
	EnforceCrashCFG *cfg = new EnforceCrashCFG(as, neededRips);
	for (std::map<unsigned, ThreadRip>::iterator it = roots.begin();
	     it != roots.end();
	     it++) {
		printf("Root %d:%lx\n", it->second.thread, it->second.rip);
		cfg->add_root(it->second, 100);
	}
	cfg->doit();
	
	/* Figure out where the various expressions should be
	 * evaluated. */
	expressionDominatorMapT exprDominatorMap(c, cfg, neededRips);

	/* Figure out where we need to stash the various necessary
	 * expressions.  This is a map from RIPs to <thread,expr>
	 * pairs, where we need to stash @expr if we execute
	 * instruction @RIP in thread @thread. */
	expressionStashMapT exprStashPoints(neededExpressions, roots);

	/* And where we need to calculate them. */
	expressionEvalMapT exprEvalPoints(exprDominatorMap);

	/* Find out where the happens-before edges start and end. */
	std::map<unsigned long, std::set<happensBeforeEdge *> > happensBeforePoints;
	for (unsigned x = 0; x < c.size(); x++) {
		IRExpr *e = c[x].second;
		bool invert = c[x].first;
		if (e->tag == Iex_HappensBefore) {
			IRExpr::HappensBefore *hb = &e->Iex.HappensBefore;
			if (!hb->before || !hb->after)
				continue;
			happensBeforeEdge *hbe = new happensBeforeEdge(invert, *hb, exprDominatorMap.idom,
								       cfg, exprStashPoints);
			happensBeforePoints[hbe->before->rip.rip].insert(hbe);
			happensBeforePoints[hbe->after->rip.rip].insert(hbe);
		}
	}

	/* The patch needs to be built in direct RIP space, rather
	 * than in ThreadRip space.  That means we need to degrade the
	 * CFG. */
	CFG<ClientRip> *degradedCfg = convertCFGFromThreadRipToClientRips(cfg, neededThreads, exprDominatorMap);

	/* Figure out what slots to use for the various
	 * expressions. */
	slotMapT slotMap(exprStashPoints, happensBeforePoints);

	/* Now build the patch */
	EnforceCrashPatchFragment *pf = new EnforceCrashPatchFragment(slotMap, exprStashPoints, exprEvalPoints, happensBeforePoints);
	pf->fromCFG(degradedCfg);
	std::set<ClientRip> entryPoints;
	for (std::map<unsigned, ThreadRip>::iterator it = roots.begin();
	     it != roots.end();
	     it++)
		entryPoints.insert(ClientRip(it->second.rip, neededThreads));
	printf("Fragment: %s\n", pf->asC("ident", entryPoints));
}

static IRExpr *
zapFreeVariables(IRExpr *src, FreeVariableMap &fv)
{
	ShortCircuitFvTransformer trans(fv);
	return trans.transformIRExpr(src);
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);

	int fd = open(argv[4], O_RDONLY);
	if (fd < 0)
		err(1, "opening %s", argv[4]);
	VexPtr<CrashSummary, &ir_heap> summary(readCrashSummary(fd));
	close(fd);

	printf("Machines to enforce:\n");
	printCrashSummary(summary, stdout);

	IRExpr *requirement = findHappensBeforeRelations(summary, oracle, ALLOW_GC);
	fprintf(_logfile, "Crash requirement:\n");
	ppIRExpr(requirement, _logfile);
	fprintf(_logfile, "\n");

	std::map<unsigned, ThreadRip> roots;
	roots[summary->loadMachine->tid] = ThreadRip::mk(summary->loadMachine->tid, summary->loadMachine->origin);
	
	FreeVariableMap m(summary->loadMachine->freeVariables);
	zapBindersAndFreeVariables(m, summary->loadMachine);
	for (unsigned x = 0; x < summary->storeMachines.size(); x++) {
		FreeVariableMap n(summary->storeMachines[x]->machine->freeVariables);
		zapBindersAndFreeVariables(n, summary->storeMachines[x]->machine);
		m.merge(n);
		roots[summary->storeMachines[x]->machine->tid] =
			ThreadRip::mk(summary->storeMachines[x]->machine->tid,
				      summary->storeMachines[x]->machine->origin);
	}

	requirement = internIRExpr(zapFreeVariables(requirement, m));
	fprintf(_logfile, "After free variable removal:\n");
	ppIRExpr(requirement, _logfile);
	fprintf(_logfile, "\n");

	DNF_Disjunction d;
	if (TIMEOUT || !dnf(requirement, d)) {
		fprintf(_logfile, "failed to convert to DNF\n");
		return 1;
	}
	printDnf(d, _logfile);
       
	for (unsigned x = 0; x < d.size(); x++) {
		printf("Examine clause %d\n", x);
		partitionCrashCondition(d[x], m, roots, ms->addressSpace);
	}

	return 0;
}
