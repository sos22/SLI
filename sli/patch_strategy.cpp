#include <queue>

#include "sli.h"
#include "patch_strategy.hpp"
#include "oracle.hpp"
#include "crashcfg.hpp"

#ifndef NDEBUG
static bool debug_declobber_instructions = false;
#else
#define debug_declobber_instructions false
#endif


/* This function is responsible for setting up the patch point list
   and the force interpret list.  The preceding phases of the analysis
   have given us a set of instructions I and we must arrange that
   we're in the interpreter whenever the program executes an
   instruction from I.  The challenge is that the only way of gaining
   control is through a jump instruction, which is five bytes, and
   some of the instructions in I might themselves be smaller than five
   bytes, and so directly patching one of them might clobber something
   important.  That is itself fine *provided* that the program is
   definitely in the interpreter when it executes the instruction
   which you clobbered, which might then require us to add new entry
   points.

   Define some notation first:

   -- MustInterpret(X) means that we must be in the interpreter when we
   run instruction X.
   -- DoesInterpret(X) means that the patched program definitely will
   be in the interpreter when in runs X.
   -- Clobber(X, Y) means that trying to patch X into an entry point
   will clobber Y.
   -- Patch(X) means that we're going to replace X with an entry point.
   -- Cont(X) means that if the interpreter hits X it should continue
   interpreting.
   -- Predecessor(X, Y) is true precisely when there's some control-flow
   edge from Y to X i.e. when Y is a predecessor of X.
   -- External(X) is true if there might be some control-flow edge which
   we don't know about which ends at X.

   We control Patch and Cont; everything else is set for us in advance
   by the oracle and the CED.

   Assumptions:

   Patch(X) => DoesInterpret(X)
   !External(X) && Cont(X) && forall Y.(Predecessor(X, Y) => DoesInterpret(Y)) => DoesInterpret(X)

   In the final configuration, we need:

   Patch(X) => Cont(X)
   MustInterpret(X) => DoesInterpret(X)
   Patch(X) && Clobber(X, Y) => DoesInterpret(Y)
   Patch(X) && Clobber(X, Y) => !External(Y)

   For performance reasons, we'd also like to minimise the size of the
   Cont set.

   We treat this as an exhaustive search problem, using two possible
   maneuvers:

   -- Create a new patch point at X.  That's only valid if doing so
      wouldn't clobber an external function.  Doing this then moves
      you to a new state in which MustInterpret() contains all of the
      instructions which are clobbered by X.
   -- Use a continue point instead: set Cont(X) and then set
      MustInterpret for all of X's predecessors.
*/

struct patchStrategy {
	std::set<unsigned long> MustInterpret;
	std::set<unsigned long> Patch;
	std::set<unsigned long> Cont;
	unsigned size() const {
		return MustInterpret.size() + Cont.size();
	}
	class priorityOrder {
	public:
		bool operator ()(const patchStrategy &a, const patchStrategy &b) const {
			if (a.size() > b.size())
				return true;
			if (a.size() < b.size())
				return false;
			return a < b;
		}
	};
	bool operator<(const patchStrategy &o) const {
		if (MustInterpret < o.MustInterpret)
			return true;
		if (MustInterpret > o.MustInterpret)
			return false;
		if (Patch < o.Patch)
			return true;
		if (Patch > o.Patch)
			return false;
		return Cont < o.Cont;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "MI: {");
		for (auto it = MustInterpret.begin(); it != MustInterpret.end(); it++) {
			if (it != MustInterpret.begin())
				fprintf(f, ",");
			fprintf(f, "0x%lx", *it);
		}
		fprintf(f, "}; P {");
		for (auto it = Patch.begin(); it != Patch.end(); it++) {
			if (it != Patch.begin())
				fprintf(f, ",");
			fprintf(f, "0x%lx", *it);
		}
		fprintf(f, "}; C {");
		for (auto it = Cont.begin(); it != Cont.end(); it++) {
			if (it != Cont.begin())
				fprintf(f, ",");
			fprintf(f, "0x%lx", *it);
		}
		fprintf(f, "}\n");
	}
};

typedef std::priority_queue<patchStrategy, std::vector<patchStrategy>, patchStrategy::priorityOrder> patchQueueT;

static bool
patchSearch(Oracle *oracle,
	    const patchStrategy &input,
	    patchQueueT &thingsToTry)
{
	if (input.MustInterpret.empty())
		return true;

	if (debug_declobber_instructions)
		input.prettyPrint(stdout);
	unsigned long needed = *input.MustInterpret.begin();

	if (debug_declobber_instructions)
		printf("\tLook at %lx\n", needed);
	patchStrategy c(input);
	/* @needed is definitely going to be interpreted after
	 * this. */
	c.Cont.insert(needed);
	c.MustInterpret.erase(needed);

	/* Decide which maneuver to use here.  We need to either patch
	   @needed itself or bring all of its predecessors into the
	   patch. */

	/* Figure out which instructions might get clobbered by the
	 * patch */
	std::set<unsigned long> clobbered_by_patch;
	unsigned offset = 0;
	offset += getInstructionSize(oracle->ms->addressSpace, StaticRip(needed));
	while (offset < 5) {
		clobbered_by_patch.insert(needed + offset);
		offset += getInstructionSize(oracle->ms->addressSpace, StaticRip(needed + offset));
	}

	/* Can't use patch if that would clobber an external. */
	bool can_use_patch = true;
	for (auto it = clobbered_by_patch.begin(); can_use_patch && it != clobbered_by_patch.end(); it++) {
		if (oracle->isFunctionHead(StaticRip(*it)))
			can_use_patch = false;
	}
	/* Can't use patch if that would clobber/be clobbered by an
	   existing patch point. */
	for (auto it = input.Patch.begin(); can_use_patch && it != input.Patch.end(); it++) {
		if (needed > *it - 5 && needed < *it + 5)
			can_use_patch = false;
	}

	if (can_use_patch) {
		/* Try using a patch. */
		patchStrategy patched(c);
		patched.Patch.insert(needed);
		for (auto it = clobbered_by_patch.begin();
		     it != clobbered_by_patch.end();
		     it++) {
			std::set<unsigned long> predecessors;
			oracle->findPredecessors(*it, predecessors);
			for (unsigned long y = needed; y < *it; y++)
				predecessors.erase(y);
			patched.Cont.insert(*it);
			patched.MustInterpret.erase(*it);
			patched.MustInterpret.insert(predecessors.begin(), predecessors.end());
		}
		thingsToTry.push(patched);
		if (debug_declobber_instructions) {
			printf("Patch to: ");
			patched.prettyPrint(stdout);
		}
	}

	/* Try expanding to predecessors. */
	std::set<unsigned long> predecessors;
	oracle->findPredecessors(needed, predecessors);
	c.MustInterpret.insert(predecessors.begin(), predecessors.end());
	thingsToTry.push(c);
	if (debug_declobber_instructions) {
		printf("Unpatched: ");
		c.prettyPrint(stdout);
	}
	return false;
}

void
buildPatchStrategy(crashEnforcementRoots &roots,
		   CrashCfg &crashCfg,
		   Oracle *oracle,
		   std::set<unsigned long> &patchPoints,
		   std::set<unsigned long> &interpretInstrs)
{
	patchStrategy currentPs;

	for (auto it = roots.begin(); !it.finished(); it.advance()) {
		Instruction<ThreadCfgLabel> *instr = crashCfg.findInstr(it.threadCfgLabel());
		assert(instr);
		const AbstractThread &absThread(instr->rip.thread);
		ConcreteThread concThread(roots.lookupAbsThread(absThread));
		ConcreteCfgLabel concCfgLabel(concThread.summary(), instr->rip.label);
		const VexRip &vr(crashCfg.labelToRip(concCfgLabel));

		unsigned long r = vr.unwrap_vexrip();
		if (debug_declobber_instructions)
			printf("%lx is a root\n", r);
		if (currentPs.Cont.count(r)) {
			if (debug_declobber_instructions) {
				printf("... but it's already been handled elsewhere\n");
			}
			continue;
		}
		currentPs.MustInterpret.insert(r);
		std::set<patchStrategy> visited;
		patchQueueT pses;
		pses.push(currentPs);
		while (true) {
			if (pses.empty()) {
				errx(1, "cannot build patch strategy");
			}
			patchStrategy next(pses.top());
			pses.pop();
			if (!visited.insert(next).second)
				continue;
			if (patchSearch(oracle, next, pses)) {
				/* We have a solution for this entry
				 * point.  Update currentPs and move
				 * on. */
				currentPs = next;
				break;
			}
		}
	}

	patchPoints = currentPs.Patch;
	interpretInstrs = currentPs.Cont;

	/* Minor optimisation: anything within five bytes of a patch
	   point is implicitly cont, so remove them. */
	for (auto it = patchPoints.begin(); it != patchPoints.end(); it++) {
		for (unsigned x = 0; x < 5; x++) {
			interpretInstrs.erase(*it + x);
		}
	}
}
