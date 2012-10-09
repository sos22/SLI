/* Somewhat annoyingly, we actually need _GNU_SOURCE for correctness,
   because of the call to basename().  If it's not there then
   compilation will succeed but the resulting program will be
   buggy. */
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
/* Make sure this gets #include'd before libgen.h, including
   #include's from other headers, or you get the buggy version of
   basename() */
#include <string.h>

#include "sli.h"

#include "genfix.hpp"
#include "inferred_information.hpp"
#include "oracle.hpp"
#include "crashcfg.hpp"
#include "offline_analysis.hpp"

#include "cfgnode_tmpl.cpp"

#ifndef NDEBUG
static bool debug_find_dominator = false;
#else
#define debug_find_dominator false
#endif

template <typename t> static bool
operator &=(std::set<t> &a, const std::set<t> &b)
{
	bool res = false;
	for (auto it = a.begin(); it != a.end(); ) {
		if (!b.count(*it)) {
			a.erase(it++);
			res = true;
		} else {
			it++;
		}
	}
	return res;
}

static void
enumerateCFG(_CFGNode<StaticRip> *root, std::set<_CFGNode<StaticRip> *> &instrs)
{
	std::vector<_CFGNode<StaticRip> *> q;
	q.push_back(root);
	while (!q.empty()) {
		_CFGNode<StaticRip> *e = q.back();
		q.pop_back();
		if (instrs.insert(e).second) {
			for (auto it = e->successors.begin();
			     it != e->successors.end();
			     it++)
				if (it->instr)
					q.push_back(it->instr);
		}
	}
}

static VexRip
findDominator(Oracle *oracle, const std::set<VexRip> &neededInstrs, unsigned min_size)
{
	assert(!neededInstrs.empty());

	if (debug_find_dominator) {
		printf("findDominator({");
		for (auto it = neededInstrs.begin(); it != neededInstrs.end(); it++) {
			if (it != neededInstrs.begin())
				printf(", ");
			printf("%s", it->name());
		}
		printf("}, min_size = %d)\n", min_size);
	}

	/* First strip the needed instructions back so that they
	 * contain just the entry in the last common frame.  That
	 * means removing any common prefix of the stack, then mapping
	 * nested function calls to their call instructions. */
	std::vector<unsigned long> common_prefix;
	auto it = neededInstrs.begin();
	common_prefix = it->stack;
	it++;

	/* Never want to remove the bit of the stack which identifies
	   the actual instruction, only its context. */
	common_prefix.pop_back();

	while (it != neededInstrs.end()) {
		unsigned x;
		for (x = 0;
		     x < common_prefix.size() &&
			     x + 1 < it->stack.size() &&
			     it->stack[x] == common_prefix[x];
		     x++)
			;
		assert(x <= common_prefix.size());
		common_prefix.resize(x);
		it++;
	}
	if (debug_find_dominator) {
		printf("Common prefix: ");
		for (auto it = common_prefix.begin();
		     it != common_prefix.end();
		     it++) {
			if (it != common_prefix.begin())
				printf(", ");
			printf("0x%lx", *it);
		}
		printf("\n");
	}
	std::set<StaticRip> strippedInstrs;
	for (auto it = neededInstrs.begin(); it != neededInstrs.end(); it++) {
		assert(it->stack.size() > common_prefix.size());
		for (unsigned x = 0; x < common_prefix.size(); x++)
			assert(it->stack[x] == common_prefix[x]);

		/* This is the instruction in the common frame. */
		unsigned long r1 = it->stack[common_prefix.size()];

		if (it->stack.size() > common_prefix.size() + 1) {
			/* This instruction is the return point of a
			   call, and we need to get the call
			   instruction itself. */
			unsigned long r2 = oracle->findCallPredecessor(r1);
			if (r2 == 0) {
				printf("Huh?  %lx should be a call return, because %s is a valid rip, but oracle doesn't know about its call predecessor?\n",
				       r1, it->name());
				abort();
			}
			r1 = r2;
		} else {
			/* This is the instruction itself. */
		}
		strippedInstrs.insert(StaticRip(r1));
	}

	if (debug_find_dominator) {
		printf("Stripped instrs: {");
		for (auto it = strippedInstrs.begin();
		     it != strippedInstrs.end();
		     it++) {
			if (it != strippedInstrs.begin())
				printf(", ");
			printf("%s", it->name());
		}
		printf("}\n");
	}
			
	/* Now we need those to all be in the same function. */
	auto it2 = strippedInstrs.begin();
	StaticRip headRip(oracle->functionHeadForInstruction(*it2));
	for (it2++; it2 != strippedInstrs.end(); it2++) {
		StaticRip thisHead(oracle->functionHeadForInstruction(*it2));
		if (thisHead != headRip) {
			printf("Failed to find dominator: %s and %s are in different functions (%s vs %s)\n",
			       strippedInstrs.begin()->name(),
			       it->name(),
			       headRip.name(),
			       thisHead.name());
			return VexRip();
		}
	}

	if (debug_find_dominator)
		printf("headRip %s\n", headRip.name());

	/* So headRip is now definitely a valid dominator.  Build a
	 * CFG forwards from there and see if we can find anything
	 * better. */
	CfgLabelAllocator allocLabel;
	CfgSuccMap<StaticRip, StaticRip> succMap;
	std::map<_CFGNode<StaticRip> *, unsigned> sizeMap;
	std::map<StaticRip, _CFGNode<StaticRip> *> cfgNodes;
	std::vector<StaticRip> pending;
	pending.push_back(headRip);
	while (!pending.empty()) {
		StaticRip sr(pending.back());
		pending.pop_back();
		if (cfgNodes.count(sr))
			continue;
		_CFGNode<StaticRip> *n = CfgNodeForRip<StaticRip>(
			allocLabel(),
			oracle,
			VexRip::invent_vex_rip(sr.rip),
			sr,
			succMap,
			&sizeMap);
		if (!n) {
			printf("Warning: Cannot decode %s\n", sr.name());
			continue;
		}
		cfgNodes[sr] = n;
		assert(succMap.count(n));
		std::vector<CfgSuccessorT<StaticRip> > &succ(succMap[n]);
		for (auto it = succ.begin(); it != succ.end(); it++)
			pending.push_back(it->instr);
	}
	resolveReferences(succMap, cfgNodes);

	assert(cfgNodes.count(headRip));
	_CFGNode<StaticRip> *cfgRoot = cfgNodes[headRip];
	if (debug_find_dominator) {
		printf("CFG:\n");
		printCFG(cfgRoot, stdout);
	}

	std::set<_CFGNode<StaticRip> *> allInstrs;
	enumerateCFG(cfgRoot, allInstrs);

	/* So now we have the CFG.  Next step is to find the
	 * instructions in the CFG which dominate the instructions in
	 * strippedInstrs i.e. the set of instructions D such that
	 * every path from the root to any member of strippedInstrs
	 * passes through each member of D at least once.  Doing this
	 * properly requires a full dominator table, so build that
	 * instead.  When we're done, dominatorMap[x] is the set of
	 * instructions S such that every path to x passes through
	 * every member of S i.e. S is the set of dominators of x. */
	/* Need a predecessor map for this */
	std::map<_CFGNode<StaticRip> *, std::set<_CFGNode<StaticRip> *> > predecessors;
	for (auto it = allInstrs.begin(); it != allInstrs.end(); it++) {
		auto i = *it;
		for (auto it2 = i->successors.begin(); it2 != i->successors.end(); it2++) {
			if (it2->instr)
				predecessors[it2->instr].insert(i);
		}
	}
	predecessors[cfgRoot].clear();

	/* Start by assumming that everything dominates everything and
	 * then fix things up.  A dominates B if either A == B or A
	 * dominates every predecessor of B. */
	std::map<_CFGNode<StaticRip> *, std::set<_CFGNode<StaticRip> *> > dominatorMap;
	for (auto it = allInstrs.begin(); it != allInstrs.end(); it++)
		dominatorMap[*it] = allInstrs;
	dominatorMap[cfgRoot].clear();
	dominatorMap[cfgRoot].insert(cfgRoot);
	std::set<_CFGNode<StaticRip> *> need_recheck;
	need_recheck.insert(allInstrs.begin(), allInstrs.end());
	while (!need_recheck.empty()) {
		_CFGNode<StaticRip> *n = *need_recheck.begin();
		need_recheck.erase(n);
		assert(dominatorMap.count(n));
		assert(predecessors.count(n));
		const std::set<_CFGNode<StaticRip> *> &pred(predecessors[n]);
		auto it = pred.begin();
		std::set<_CFGNode<StaticRip> *> desiredDom;
		if (it != pred.end()) {
			assert(dominatorMap.count(*it));
			desiredDom = dominatorMap[*it];
			if (it != pred.end()) {
				for (it++; it != pred.end(); it++) {
					assert(dominatorMap.count(*it));
					desiredDom &= dominatorMap[*it];
				}
			}
		}
		desiredDom.insert(n);
		if (dominatorMap[n] &= desiredDom) {
			if (debug_find_dominator) {
				printf("Updated %s to {", n->rip.name());
				for (auto it = dominatorMap[n].begin();
				     it != dominatorMap[n].end();
				     it++) {
					if (it != dominatorMap[n].begin())
						printf(", ");
					printf("%s", (*it)->rip.name());
				}
				printf("}\n");
			}
			for (auto it = n->successors.begin();
			     it != n->successors.end();
			     it++)
				if (it->instr)
					need_recheck.insert(it->instr);
		}
	}

	if (debug_find_dominator) {
		printf("Dominator map:\n");
		for (auto it = dominatorMap.begin(); it != dominatorMap.end(); it++) {
			printf("%s -> {", it->first->rip.name());
			for (auto it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++) {
				if (it2 != it->second.begin())
					printf(", ");
				printf("%s", (*it2)->rip.name());
			}
			printf("}\n");
		}
	}

	/* Find all of the candidates.  These are instructions which
	   are of the minimum length and dominate all of the needed
	   instructions. */
	std::set<_CFGNode<StaticRip> *> candidates;
	for (auto it = strippedInstrs.begin(); it != strippedInstrs.end(); it++) {
		assert(cfgNodes.count(*it));
		_CFGNode<StaticRip> *n = cfgNodes[*it];
		assert(n);
		assert(dominatorMap.count(n));
		const std::set<_CFGNode<StaticRip> *> &dom(dominatorMap[n]);
		if (it == strippedInstrs.begin()) {
			for (auto it = dom.begin(); it != dom.end(); it++) {
				assert(sizeMap.count(*it));
				if (sizeMap[*it] >= min_size)
					candidates.insert(*it);
			}
		} else {
			candidates &= dom;
		}
	}

	if (debug_find_dominator) {
		printf("Candidates: {");
		for (auto it = candidates.begin();
		     it != candidates.end();
		     it++) {
			if (it != candidates.begin())
				printf(", ");
			printf("%s", (*it)->rip.name());
		}
		printf("}\n");
	}

	/* Anything in the candidates set would now be a correct
	 * choice.  For performance reasons, we want to pick the
	 * ``latest'' possible candidate, so as to keep the number of
	 * instructions in the patch down.  That means we don't want
	 * to pick anything which is dominated by another
	 * candidate. */
	bool progress = true;
	while (progress) {
		progress = false;
		for (auto it = candidates.begin(); !progress && it != candidates.end(); it++) {
			assert(dominatorMap.count(*it));
			const std::set<_CFGNode<StaticRip> *> &dominates(dominatorMap[*it]);
			for (auto it2 = dominates.begin(); it2 != dominates.end(); it2++) {
				if (*it2 != *it && candidates.count(*it2)) {
					candidates.erase(*it2);
					progress = true;
				}
			}
		}
	}

	if (debug_find_dominator) {
		printf("Optimal candidates: {");
		for (auto it = candidates.begin();
		     it != candidates.end();
		     it++) {
			if (it != candidates.begin())
				printf(", ");
			printf("%s", (*it)->rip.name());
		}
		printf("}\n");
	}

	/* There should now be precisely one valid answer. */
	assert(candidates.size() == 1);

	/* Take it. */
	std::vector<unsigned long> stack(common_prefix);
	stack.push_back((*candidates.begin())->rip.rip);
	return VexRip(stack);
}

class AddExitCallPatch : public PatchFragment<ThreadRip> {
protected:
	void generateEpilogue(const CfgLabel &l, ThreadRip exitRip);
	/* XXX should really override emitInstruction here to catch
	   indirect jmp and ret instructions; oh well. */
public:
	AddExitCallPatch(const std::set<ThreadRip> &roots)
		: PatchFragment<ThreadRip>(roots)
	{}
};


static void
trimCfg(StateMachine *machine, const std::set<std::pair<unsigned, CfgLabel> > &neededCfg)
{
	typedef std::pair<unsigned, const CFGNode *> elem;
	std::set<elem> neededNodes;
	std::set<elem> allNodes;

	std::vector<elem> q(machine->cfg_roots);
	while (!q.empty()) {
		if (!allNodes.insert(q.back()).second) {
			q.pop_back();
			continue;
		}
		unsigned tid = q.back().first;
		const CFGNode *n = q.back().second;
		if (neededCfg.count(std::pair<unsigned, CfgLabel>(tid, n->label)))
			neededNodes.insert(q.back());
		q.pop_back();
		for (auto it = n->successors.begin(); it != n->successors.end(); it++) {
			if (it->instr)
				q.push_back(elem(tid, it->instr));
		}
	}

	/* We need to preserve anything which can reach and be reached
	 * by some interesting node. */
	std::set<elem> reachInterestingNode(neededNodes);
	std::set<elem> reachedByInterestingNode(neededNodes);
	bool progress = true;
	while (progress) {
		progress = false;
		for (auto it = allNodes.begin(); it != allNodes.end(); it++) {
			if (!reachInterestingNode.count(*it)) {
				for (auto it2 = it->second->successors.begin();
				     it2 != it->second->successors.end();
				     it2++) {
					if (it2->instr &&
					    reachInterestingNode.count(elem(it->first, it2->instr))) {
						reachInterestingNode.insert(*it);
						progress = true;
						break;
					}
				}
			}
			if (reachedByInterestingNode.count(*it)) {
				for (auto it2 = it->second->successors.begin();
				     it2 != it->second->successors.end();
				     it2++) {
					if (it2->instr &&
					    reachedByInterestingNode.insert(elem(it->first, it2->instr)).second)
						progress = true;
				}
			}
		}
	}
	std::set<elem> desired;
	for (auto it = reachInterestingNode.begin();
	     it != reachInterestingNode.end();
	     it++) {
		if (reachedByInterestingNode.count(*it))
			desired.insert(*it);
	}

	/* Now we need to find a new root set for the machine, by
	   advancing the existing roots until they reach something in
	   desired. */
	std::set<elem> possibleRoots(machine->cfg_roots.begin(), machine->cfg_roots.end());
	std::set<elem> newRoots;
	while (!possibleRoots.empty()) {
		elem e = *possibleRoots.begin();
		possibleRoots.erase(e);
		if (desired.count(e)) {
			newRoots.insert(e);
		} else {
			for (auto it = e.second->successors.begin();
			     it != e.second->successors.end();
			     it++)
				if (it->instr)
					possibleRoots.insert(elem(e.first, it->instr));
		}
	}

	/* @newRoots is now the new root set.  Remove anything
	 * reachable which shouldn't be reachable. */
	std::vector<elem> pending;
	pending.insert(pending.begin(), newRoots.begin(), newRoots.end());
	while (!pending.empty()) {
		elem e = pending.back();
		pending.pop_back();
		for (auto it = ((CFGNode *)e.second)->successors.begin();
		     it != ((CFGNode *)e.second)->successors.end();
		     it++) {
			if (!it->instr)
				continue;
			if (desired.count(elem(e.first, it->instr)))
				pending.push_back(elem(e.first, it->instr));
			else
				it->instr = NULL;
		}
	}

	/* Done */
	machine->cfg_roots.clear();
	machine->cfg_roots.insert(machine->cfg_roots.begin(),
				  newRoots.begin(),
				  newRoots.end());
}

static void
avoidBranchToPatch(crashEnforcementRoots &cer,
		   CrashCfg &cfg,
		   std::map<VexRip, Instruction<ThreadCfgLabel> *> &cfgRoots,
		   CfgLabelAllocator &allocLabel,
		   Oracle *oracle)
{
	std::map<VexRip, std::set<Instruction<ThreadCfgLabel> *> > multiRoots;
	for (auto it = cer.content.begin(); it != cer.content.end(); it++) {
		AbstractThread tid(it->first);
		const std::set<CfgLabel> &pendingRoots(it->second);
		for (auto it2 = pendingRoots.begin(); it2 != pendingRoots.end(); it2++) {
			multiRoots[cfg.labelToRip(ConcreteCfgLabel(cer.lookupAbsThread(tid).summary_id, *it2))].
				insert(cfg.findInstr(ThreadCfgLabel(tid, *it2)));
		}
	}

	std::map<VexRip, std::set<Instruction<ThreadCfgLabel> *> > acceptedRoots;
	for (auto it = multiRoots.begin(); it != multiRoots.end(); it++) {
		const VexRip &inpRip(it->first);
		const std::set<Instruction<ThreadCfgLabel> *> &inpRoots(it->second);
		for (auto it = inpRoots.begin(); it != inpRoots.end(); it++) {
			std::set<std::pair<VexRip, Instruction<ThreadCfgLabel> *> > pendingRoots;
			pendingRoots.insert(std::pair<VexRip, Instruction<ThreadCfgLabel> *>(inpRip, *it));
			std::set<VexRip> alreadyCovered;
			while (!pendingRoots.empty()) {
				VexRip vr(pendingRoots.begin()->first);
				Instruction<ThreadCfgLabel> *node = pendingRoots.begin()->second;
				pendingRoots.erase(pendingRoots.begin());
				if (!alreadyCovered.insert(vr).second)
					continue;

				unsigned long e = vr.unwrap_vexrip();
				bool acceptAsRoot = true;
				for (unsigned x = 1; acceptAsRoot && x < 5; x++) {
					if (oracle->isFunctionHead(StaticRip(e + x))) {
						acceptAsRoot = false;
					} else {
						std::set<unsigned long> predecessors;
						oracle->findPredecessors(e + x, predecessors);
						for (unsigned y = 0; y < x; y++)
							predecessors.erase(e + y);
						if (!predecessors.empty())
							acceptAsRoot = false;
					}
				}
				if (acceptAsRoot) {
					acceptedRoots[vr].insert(node);
					continue;
				}

				/* Can't take this one as a root, so
				 * look at its predecessors. */
				std::set<unsigned long> predecessors;
				oracle->findPredecessors(e, predecessors);
				assert(!predecessors.empty());
				for (auto it = predecessors.begin(); it != predecessors.end(); it++) {
					auto pred = decode_instr(oracle->ms->addressSpace,
								 *it,
								 ThreadCfgLabel(node->rip.thread, allocLabel()),
								 true);
					pred->addDefault(node);
					VexRip pred_vr(vr);
					pred_vr.jump(*it);
					pendingRoots.insert(std::pair<VexRip, Instruction<ThreadCfgLabel> *>(pred_vr, pred));
				}
			}
		}
	}

	/* For now we assume that that only produces one CFG for each
	   potential entry point.  We will eventually need to support
	   a kind of cross-product operation to merge the CFGs. */
	for (auto it = multiRoots.begin(); it != multiRoots.end(); it++) {
		assert(it->second.size() == 1);
		cfgRoots[it->first] = *it->second.begin();
	}
}

class Relocation : public GarbageCollected<Relocation, &ir_heap> {
public:
	unsigned offset;
	unsigned size;
	unsigned addend;
	Instruction<ThreadCfgLabel> *target;
	unsigned long raw_target;
	bool generateEpilogue;
	bool relative;
	Relocation(unsigned _offset,
		   unsigned _size,
		   Instruction<ThreadCfgLabel> *_target,
		   bool _generateEpilogue,
		   bool _relative)
		: offset(_offset), size(_size), addend(0), target(_target),
		  raw_target(0), generateEpilogue(_generateEpilogue),
		  relative(_relative)
	{}
	Relocation(unsigned _offset,
		   unsigned _size,
		   unsigned long _raw_target,
		   bool _generateEpilogue,
		   bool _relative)
		: offset(_offset), size(_size), addend(0), target(NULL),
		  raw_target(_raw_target), generateEpilogue(_generateEpilogue),
		  relative(_relative)
	{}
	Relocation(EarlyRelocation<ThreadCfgLabel> *_base,
		   const SummaryId &summaryId,
		   const CrashCfg &cfg,
		   std::vector<Instruction<ThreadCfgLabel>::successor_t> &successors,
		   unsigned _offset)
		: offset(_offset + _base->offset),
		  size(_base->size)
	{
		if (auto rrr = dynamic_cast<RipRelativeRelocation<ThreadCfgLabel> *> (_base)) {
			addend = rrr->nrImmediateBytes;
			generateEpilogue = false;
			relative = true;
			target = NULL;
			for (auto it = successors.begin(); it != successors.end(); it++) {
				if (it->instr && it->instr->rip == rrr->target) {
					target = it->instr;
					break;
				}
			}
			if (!target) {
				generateEpilogue = true;
				raw_target = cfg.labelToRip(ConcreteCfgLabel(summaryId, rrr->target.label)).unwrap_vexrip();
			}
		} else if (auto rrdr = dynamic_cast<RipRelativeDataRelocation<ThreadCfgLabel> *>(_base)) {
			addend = rrdr->nrImmediateBytes;
			generateEpilogue = false;
			target = NULL;
			raw_target = rrdr->target;
			relative = true;
		} else if (auto rrbr = dynamic_cast<RipRelativeBranchRelocation<ThreadCfgLabel> *>(_base)) {
			addend = 0;
			generateEpilogue = false;
			relative = true;
			target = NULL;
			for (auto it = successors.begin(); it != successors.end(); it++) {
				if (it->instr && it->instr->rip == rrbr->target) {
					target = it->instr;
					break;
				}
			}
			if (!target) {
				generateEpilogue = true;
				raw_target = cfg.labelToRip(ConcreteCfgLabel(summaryId, rrbr->target.label)).unwrap_vexrip();
			}
		} else if (auto rrBr = dynamic_cast<RipRelativeBlindRelocation<ThreadCfgLabel> *>(_base)) {
			addend = 0;
			generateEpilogue = rrBr->is_branch;
			relative = true;
			target = NULL;
			raw_target = rrBr->target;
		} else {
			abort();
		}
	}

	void visit(HeapVisitor &hv) {
		hv(target);
	}
	NAMED_CLASS
};

asm (
	"__call_sequence_template_start:\n"
	"lea -128(%rsp), %rsp\n"
	"pushq %rsi\n"
	"__call_sequence_template_load_rsi:\n"
	"movq $0x1122334455667788, %rsi\n"
	"call *%rsi\n"
	"popq %rsi\n"
	"lea 128(%rsp), %rsp\n"
	"__call_sequence_template_end:\n"
	);

static void
emitCallSequence(std::vector<unsigned char> &content,
		 const char *target,
		 std::vector<LateRelocation *> &lateRelocs)
{
	extern const unsigned char
		__call_sequence_template_start[],
		__call_sequence_template_load_rsi[],
		__call_sequence_template_end[];

	unsigned start_sz = content.size();
	for (const unsigned char *cursor = __call_sequence_template_start;
	     cursor != __call_sequence_template_end;
	     cursor++)
		content.push_back(*cursor);

	lateRelocs.push_back(
		new LateRelocation(
			start_sz + __call_sequence_template_load_rsi - __call_sequence_template_start + 2,
			8,
			vex_asprintf("%s", target),
			0,
			false));
}

static void
stack_validation_table(std::vector<const char *> &fragments, Oracle *oracle, const VexRip &vr)
{
	unsigned offset = 0;
	for (unsigned x = 1; x < vr.stack.size(); x++) {
		offset += stack_offset(oracle, vr.stack[vr.stack.size() - x]);
		fragments.push_back(vex_asprintf("\t\t{ .offset = %d, .expected_value = 0x%lx },\n",
						 offset, vr.stack[vr.stack.size() - x - 1]));
	}
}

struct trans_table_entry {
	unsigned offset_in_patch;
	unsigned long rip;
	const char *debug_msg;
	trans_table_entry(unsigned _offset, unsigned long _rip,
			  const char *_msg)
		: offset_in_patch(_offset), rip(_rip),
		  debug_msg(_msg)
	{}
};

static char *
buildPatchForCrashSummary(Oracle *oracle,
			  const SummaryId &summaryId,
			  CrashSummary *summary,
			  const char *ident)
{
	ThreadAbstracter absThread;
	std::map<ConcreteThread, std::set<CfgLabel> > cfgRoots;
	for (auto it = summary->loadMachine->cfg_roots.begin();
	     it != summary->loadMachine->cfg_roots.end();
	     it++)
		cfgRoots[ConcreteThread(summaryId, it->first)].insert(it->second->label);
	for (auto it = summary->storeMachine->cfg_roots.begin();
	     it != summary->storeMachine->cfg_roots.end();
	     it++)
		cfgRoots[ConcreteThread(summaryId, it->first)].insert(it->second->label);
	crashEnforcementRoots cer(cfgRoots, absThread);
	CrashCfg cfg(cer, summaryId, summary, oracle->ms->addressSpace, true);

	cfg.prettyPrint(stdout, true);
	cer.prettyPrint(stdout);

	std::map<VexRip, Instruction<ThreadCfgLabel> *> cfgRoots2;
	CfgLabelAllocator allocLabel;
	avoidBranchToPatch(cer, cfg, cfgRoots2, allocLabel, oracle);
	
	for (auto it = cfgRoots2.begin(); it != cfgRoots2.end(); it++) {
		printf("Root %s:\n", it->first.name());
		std::vector<Instruction<ThreadCfgLabel> *> q;
		std::set<Instruction<ThreadCfgLabel> *> v;
		q.push_back(it->second);
		while (!q.empty()) {
			Instruction<ThreadCfgLabel> *a = q.back();
			q.pop_back();
			if (!v.insert(a).second)
				continue;
			a->prettyPrint(stdout);
			for (auto it2 = a->successors.begin(); it2 != a->successors.end(); it2++)
				q.push_back(it2->instr);
		}
	}

	/* Now go and flatten the CFG fragments into patches. */
	std::vector<unsigned char> patch_content;
	std::vector<LateRelocation *> lateRelocs;
	std::vector<std::pair<VexRip, unsigned> > entryOffsets;
	std::vector<trans_table_entry> transTable;
	for (auto it = cfgRoots2.begin(); it != cfgRoots2.end(); it++) {
		const VexRip &entryVr(it->first);
		std::vector<Instruction<ThreadCfgLabel> *> toEmit;
		std::map<Instruction<ThreadCfgLabel> *, unsigned> instrOffsets;
		std::vector<Relocation *> relocs;

		entryOffsets.push_back(std::pair<VexRip, unsigned>(entryVr, patch_content.size()));

		/* XXX need to do stack validation here */
		toEmit.push_back(it->second);
		while (!toEmit.empty()) {
			Instruction<ThreadCfgLabel> *node = toEmit.back();
			toEmit.pop_back();
			while (1) {
				auto it_did_insert = instrOffsets.insert(std::pair<Instruction<ThreadCfgLabel> *, unsigned>(node, patch_content.size()));
				auto did_insert = it_did_insert.second;
				if (!did_insert) {
					/* We already have something
					 * for this instruction, so
					 * just insert a branch. */
					patch_content.push_back(0xe9);
					patch_content.push_back(0);
					patch_content.push_back(0);
					patch_content.push_back(0);
					patch_content.push_back(0);
					relocs.push_back(
						new Relocation(
							patch_content.size() - 4,
							4,
							node,
							false,
							true));
					break;
				}
				VexRip vr(
					cfg.labelToRip(
						ConcreteCfgLabel(
							summaryId,
							node->label)));
				transTable.push_back(
					trans_table_entry(
						patch_content.size(),
						vr.unwrap_vexrip(),
						vex_asprintf("CFG node %s, vexrip %s, for entry point %s",
							     node->rip.name(),
							     vr.name(),
							     entryVr.name())));
				for (auto it = node->relocs.begin();
				     it != node->relocs.end();
				     it++)
					relocs.push_back(new Relocation(*it, summaryId, cfg, node->successors, patch_content.size()));
				for (auto it = node->lateRelocs.begin();
				     it != node->lateRelocs.end();
				     it++) {
					LateRelocation *lr = *it;
					assert(lr->nrImmediateBytes != 4);
					lateRelocs.push_back(
						new LateRelocation(
							lr->offset + patch_content.size(),
							lr->size,
							lr->target,
							lr->nrImmediateBytes,
							lr->relative));
				}
				for (unsigned x = 0; x < node->len; x++)
					patch_content.push_back(node->content[x]);
				if (node->successors.empty()) {
					patch_content.push_back(0xe9);
					patch_content.push_back(0);
					patch_content.push_back(0);
					patch_content.push_back(0);
					patch_content.push_back(0);
					relocs.push_back(
						new Relocation(
							patch_content.size() - 4,
							4,
							vr.unwrap_vexrip() + node->len,
							true,
							true));
				}
				Instruction<ThreadCfgLabel> *next = NULL;
				for (auto it = node->successors.begin(); it != node->successors.end(); it++) {
					if (!it->instr)
						continue;
					if (next)
						toEmit.push_back(it->instr);
					else
						next = it->instr;
				}
				if (!next)
					break;
				node = next;
			}
		}

		for (auto it = relocs.begin(); it != relocs.end(); it++) {
			Relocation *reloc = *it;
			if (reloc->target || reloc->generateEpilogue) {
				unsigned offset;
				if (reloc->target) {
					assert(instrOffsets.count(reloc->target));
					offset = instrOffsets[reloc->target];
				} else {
					offset = patch_content.size();
					emitCallSequence(patch_content, "(unsigned long)release_lock", lateRelocs);
					patch_content.push_back(0xe9);
					patch_content.push_back(0);
					patch_content.push_back(0);
					patch_content.push_back(0);
					patch_content.push_back(0);
					lateRelocs.push_back(
						new LateRelocation(
							patch_content.size() - 4,
							4,
							vex_asprintf("0x%lx", reloc->raw_target),
							0,
							true));
				}
				long delta = offset - reloc->offset + reloc->addend - 4;
				patch_content[reloc->offset  ] = delta;
				patch_content[reloc->offset+1] = delta >> 8;
				patch_content[reloc->offset+2] = delta >> 16;
				patch_content[reloc->offset+3] = delta >> 24;
			} else {
				lateRelocs.push_back(
					new LateRelocation(
						reloc->offset,
						4,
						vex_asprintf("0x%lx", reloc->raw_target),
						reloc->addend,
						reloc->relative));
			}
		}
	}

	std::vector<const char *> fragments;
	fragments.push_back("static const unsigned char patch_content[] = \"");
	for (auto it = patch_content.begin(); it != patch_content.end(); it++)
		fragments.push_back(vex_asprintf("\\x%02x", *it));
	fragments.push_back("\";\n\n");
	fragments.push_back("static const struct relocation relocations[] = {\n");
	for (auto it = lateRelocs.begin(); it != lateRelocs.end(); it++)
		fragments.push_back(vex_asprintf("\t%s,\n", (*it)->asC()));
	fragments.push_back("};\n\n");
	fragments.push_back("static const struct trans_table_entry trans_table[] = {\n");
	for (auto it = transTable.begin(); it != transTable.end(); it++)
		fragments.push_back(vex_asprintf("\t{.rip = 0x%lx, .offset = %d} /* %s */,\n",
						 it->rip,
						 it->offset_in_patch,
						 it->debug_msg));
	fragments.push_back("};\n\n");
	/* XXX this will need to change slightly once we have the
	 * stack validation stuff in. */
	fragments.push_back("static const struct entry_context entry_points[] = {\n");
	for (auto it = entryOffsets.begin(); it != entryOffsets.end(); it++)
		fragments.push_back(
			vex_asprintf(
				"\t{ .offset = %d, .rip = 0x%lx},\n",
				it->second,
				it->first.unwrap_vexrip()));
	fragments.push_back("};\n\n");

	fragments.push_back("static const struct patch patch = {\n");
	fragments.push_back("\t.content = patch_content,\n");
	fragments.push_back("\t.content_sz = sizeof(patch_content),\n");
	fragments.push_back("\t.relocations = relocations,\n");
	fragments.push_back("\t.nr_relocations = sizeof(relocations)/sizeof(relocations[0]),\n");
	fragments.push_back("\t.trans_table = trans_table,\n");
	fragments.push_back("\t.nr_trans_table_entries = sizeof(trans_table)/sizeof(trans_table[0]),\n");
	fragments.push_back("\t.entry_points = entry_points,\n");
	fragments.push_back("\t.nr_entry_points = sizeof(entry_points)/sizeof(entry_points[0]),\n");
	fragments.push_back("};\n");
	return flattenStringFragmentsMalloc(fragments, "", "", "");
}

static void
findRelevantMais(IRExpr *iex, std::set<MemoryAccessIdentifier> &out)
{
	struct : public IRExprTransformer {
		std::set<MemoryAccessIdentifier> *out;
		IRExpr *transformIex(IRExprHappensBefore *hb) {
			out->insert(hb->before);
			out->insert(hb->after);
			return hb;
		}
	} doit;
	doit.out = &out;
	doit.doit(iex);
}

static void
findRelevantCfgs(MaiMap *mai,
		 const std::set<MemoryAccessIdentifier> &neededMais,
		 std::set<std::pair<unsigned, CfgLabel> > &out)
{
	for (auto it = neededMais.begin(); it != neededMais.end(); it++) {
		for (auto it2 = mai->begin(*it); !it2.finished(); it2.advance())
			out.insert(std::pair<unsigned, CfgLabel>(it->tid, it2.label()));
	}
}

int
main(int argc, char *argv[])
{
	if (argc != 6)
		errx(1, "need four arguments: binary, types table, callgraph, summary, and output filename");

	const char *binary = argv[1];
	const char *types_table = argv[2];
	const char *callgraph = argv[3];
	const char *summary_fname = argv[4];
	const char *output_fname = argv[5];

	init_sli();

	VexPtr<Oracle> oracle;
	{
		MachineState *ms = MachineState::readELFExec(binary);
		Thread *thr = ms->findThread(ThreadId(1));
		oracle = new Oracle(ms, thr, types_table);
	}
	oracle->loadCallGraph(oracle, callgraph, ALLOW_GC);

	VexPtr<CrashSummary, &ir_heap> summary(readBugReport(summary_fname, NULL));
	SummaryId summaryId(1); /* Only have one summary here */
	std::set<MemoryAccessIdentifier> relevant_mais;
	findRelevantMais(summary->verificationCondition, relevant_mais);
	std::set<std::pair<unsigned, CfgLabel> > relevant_cfgs;
	findRelevantCfgs(summary->mai, relevant_mais, relevant_cfgs);

	trimCfg(summary->loadMachine, relevant_cfgs);
	trimCfg(summary->storeMachine, relevant_cfgs);

	char *patch = buildPatchForCrashSummary(oracle, summaryId, summary, "patch");
	printf("Patch is:\n%s\n", patch);

	FILE *output = fopen(output_fname, "w");
	fprintf(output, "/* SLI fix generated for %s */\n", binary);
	fprintf(output,
		"/* Compile as gcc -Wall -g -shared -fPIC -Isli %s -o %s.so */\n",
		output_fname, binary);
	fprintf(output, "/* Crash summary:\n");
	printCrashSummary(summary, output);
	fprintf(output, "*/\n");
	fprintf(output, "#define BINARY_PATCH_FOR \"%s\"\n",
		basename(binary));
	fprintf(output, "#include \"patch_head.h\"\n\n");
	fprintf(output, "%s\n\n", patch);
	fprintf(output, "#include \"patch_skeleton_jump.c\"\n");
	if (fclose(output) == EOF)
		err(1, "writing output");
	return 0;
}
