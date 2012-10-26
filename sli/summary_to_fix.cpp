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
	"__call_sequence_template_done_redzone:\n"
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
		 std::vector<LateRelocation *> &lateRelocs,
		 bool already_done_redzone)
{
	extern const unsigned char
		__call_sequence_template_start[],
		__call_sequence_template_done_redzone[],
		__call_sequence_template_load_rsi[],
		__call_sequence_template_end[];
	unsigned start_sz = content.size();
	const unsigned char *start;
	if (already_done_redzone)
		start = __call_sequence_template_done_redzone;
	else
		start = __call_sequence_template_start;
	for (const unsigned char *cursor = start;
	     cursor != __call_sequence_template_end;
	     cursor++)
		content.push_back(*cursor);

	lateRelocs.push_back(
		new LateRelocation(
			start_sz + __call_sequence_template_load_rsi - start + 2,
			8,
			vex_asprintf("%s", target),
			0,
			false));
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

static void
segregateRoots(const std::map<VexRip, Instruction<ThreadCfgLabel> *> &inp,
	       std::map<unsigned long, std::map<VexRip, Instruction<ThreadCfgLabel> *> > &out)
{
	for (auto it = inp.begin(); it != inp.end(); it++)
		out[it->first.unwrap_vexrip()].insert(*it);
}

static void
emitOneInstruction(const VexRip &vr,
		   const VexRip &entryVr,
		   Instruction<ThreadCfgLabel> *node,
		   const SummaryId &summaryId,
		   const CrashCfg &cfg,
		   std::vector<unsigned char> &patch_content,
		   std::vector<Relocation *> &relocs,
		   std::vector<LateRelocation *> &lateRelocs,
		   std::vector<trans_table_entry> &transTable)
{

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

	if (node->len == 1 && node->content[0] == 0xc3) {
		/* Special case for ret instructions.  These are in
		   theory redundant because of the stack context
		   validation logic, so all we need to do is adjust
		   the stack pointer.  Use an lea to do so. */
		patch_content.push_back(0x48);
		patch_content.push_back(0x8d);
		patch_content.push_back(0x64);
		patch_content.push_back(0x24);
		patch_content.push_back(0x08);
	} else {
		for (unsigned x = 0; x < node->len; x++)
			patch_content.push_back(node->content[x]);
	}
}

static void
validateStackContext(Oracle *oracle,
		     const SummaryId &summaryId,
		     const CrashCfg &cfg,
		     const std::map<VexRip, Instruction<ThreadCfgLabel> *> &cfgRoots2,
		     std::vector<std::pair<VexRip, unsigned> > &branchesToEntryPoints,
		     std::vector<unsigned char> &content,
		     std::vector<LateRelocation *> &lateRelocs,
		     std::vector<trans_table_entry> &transTable)
{
	unsigned offset = 136;

	std::vector<VexRip> rips;
	for (auto it = cfgRoots2.begin(); it != cfgRoots2.end(); it++)
		rips.push_back(it->first);

	std::vector<unsigned> branchesToEscape;

	for (unsigned idx = 0; idx < rips.size(); idx++) {
		const VexRip vr(rips[idx]);
		assert(vr.stack.size() > 1);
		std::vector<unsigned> branchesToNextValidate;
		/* This generates a series of stack validators, each
		   of which is structured like this:

		   cmp stack_value_1, off1(%rsp)
		   jne next_validator
		   cmp stack_value_2, off2(%rsp)
		   jne next_validator
		   ...
		   cmp stack_value_N, offN(%rsp)
		   je start_of_actual_machine
		   next_validator:
		   ...

		   If this is the last validator then next_validator
		   instead branches back to the original program. */
		for (unsigned x = 1; x < vr.stack.size(); x++) {
			offset += stack_offset(oracle, vr.stack[vr.stack.size() - x]);
			unsigned long expected = vr.stack[vr.stack.size() - x - 1];
			if (expected < 0x100000000ul) {
				/* cmpq imm32, offset(%rsp) */
				content.push_back(0x48);
				content.push_back(0x81);
				content.push_back(0xbc);
				content.push_back(0x24);
				content.push_back(offset);
				content.push_back(offset >> 8);
				content.push_back(offset >> 16);
				content.push_back(offset >> 24);
				content.push_back(expected);
				content.push_back(expected >> 8);
				content.push_back(expected >> 16);
				content.push_back(expected >> 24);
				/* jne rel32 or je rel32. */
				content.push_back(0x0f);
				if (idx == rips.size() - 1)
					content.push_back(0x84);
				else
					content.push_back(0x85);
				content.push_back(0);
				content.push_back(0);
				content.push_back(0);
				content.push_back(0);
				if (idx == rips.size() - 1)
					branchesToEntryPoints.push_back(std::pair<VexRip, unsigned>(vr, content.size() - 4));
				else
					branchesToNextValidate.push_back(content.size() - 4);
			} else {
				/* Can't check these ones yet. */
				abort();
			}
		}

		if (idx < rips.size() - 1) {
			for (auto it = branchesToNextValidate.begin();
			     it != branchesToNextValidate.end();
			     it++) {
				/* Fix up the branch */
				long delta = content.size() - *it - 4;
				content[*it] = delta;
				content[*it + 1] = delta >> 8;
				content[*it + 2] = delta >> 16;
				content[*it + 3] = delta >> 24;
			}
		} else {
			branchesToEscape = branchesToNextValidate;
		}
	}

	/* None of the stacks match, so go back to the original
	 * program. */

	/* Where are we actually going? */
	unsigned long targ = rips[0].unwrap_vexrip();
	for (unsigned x = 1; x < rips.size(); x++)
		assert(targ == rips[x].unwrap_vexrip());

	/* popf */
	content.push_back(0x9d);
	/* Restore red zone with lea 0x80(%rsp), %rsp */
	content.push_back(0x48);
	content.push_back(0x8d);
	content.push_back(0xa4);
	content.push_back(0x24);
	content.push_back(0x80);
	content.push_back(0x00);
	content.push_back(0x00);
	content.push_back(0x00);
	/* Emit the instruction which we clobbered to set up the
	 * patch. */
	std::vector<Relocation *> relocs;
	emitOneInstruction(rips[0],
			   VexRip(),
			   cfgRoots2.begin()->second,
			   summaryId,
			   cfg,
			   content,
			   relocs,
			   lateRelocs,
			   transTable);
	/* If that generated any further early relocs then we're
	   screwed, because we won't be able to resolve them.  Late
	   relocs are okay, though. */
	for (auto it = relocs.begin(); it != relocs.end(); it++) {
		Relocation *reloc = *it;
		assert(!reloc->target && !reloc->generateEpilogue);
		lateRelocs.push_back(
			new LateRelocation(
				reloc->offset,
				4,
				vex_asprintf("0x%lx", reloc->raw_target),
				reloc->addend,
				reloc->relative));
	}

	/* jmp rel32 */
	content.push_back(0xe9);
	content.push_back(0);
	content.push_back(0);
	content.push_back(0);
	content.push_back(0);

	targ += getInstructionSize(oracle->ms->addressSpace, StaticRip(targ));
	lateRelocs.push_back(
		new LateRelocation(
			content.size() - 4,
			4,
			vex_asprintf("0x%lxul", targ),
			0,
			true));
}

static void
emitInternalJump(unsigned to_offset,
		 std::vector<unsigned char> &patch_content)
{
	long delta = to_offset - patch_content.size();
	/* Try with an 8-bit jump */
	if (delta >= -126 && delta < 130) {
		patch_content.push_back(0xeb);
		patch_content.push_back(delta - 2);
	} else {
		/* Use a 32 bit one */
		patch_content.push_back(0xe9);
		delta -= 5;
		patch_content.push_back(delta & 0xff);
		patch_content.push_back((delta >> 8) & 0xff);
		patch_content.push_back((delta >> 16) & 0xff);
		patch_content.push_back((delta >> 24) & 0xff);
	}
}

static void
emitExitSequence(unsigned long exit_to,
		 std::vector<unsigned char> &patch_content,
		 std::vector<Relocation *> &relocs,
		 std::vector<LateRelocation *> &lateRelocs,
		 std::vector<trans_table_entry> &transTable,
		 const std::set<unsigned long> &clobberedInstructions,
		 std::map<unsigned long, unsigned> &exitSequences,
		 const SummaryId &summaryId,
		 const CrashCfg &cfg,
		 AddressSpace *as)
{
top:
	if (!clobberedInstructions.count(exit_to)) {
		/* Easy case: just branch to the original program
		 * instruction. */
		patch_content.push_back(0xe9);
		patch_content.push_back(0);
		patch_content.push_back(0);
		patch_content.push_back(0);
		patch_content.push_back(0);
		lateRelocs.push_back(
			new LateRelocation(
				patch_content.size() - 4,
				4,
				vex_asprintf("0x%lx", exit_to),
				0,
				true));
		return;
	}
	/* We're trying to exit to an instruction which was clobbered
	   by one of our patch points.  That's a little more
	   tricky. */
	if (exitSequences.count(exit_to)) {
		/* Reuse existing sequence */
		emitInternalJump(exitSequences[exit_to], patch_content);
		return;
	}

	/* Generate a new exit sequence */
	exitSequences[exit_to] = patch_content.size();

	Instruction<ThreadCfgLabel> *newInstr =
		decode_instr(as, exit_to, ThreadCfgLabel(AbstractThread::uninitialised(), CfgLabel(-1)), true);
	if (!newInstr)
		errx(1, "need to decode instruction at %lx, but decoder failed!", exit_to);
	emitOneInstruction(VexRip::invent_vex_rip(exit_to),
			   VexRip::invent_vex_rip(exit_to),
			   newInstr,
			   summaryId,
			   cfg,
			   patch_content,
			   relocs,
			   lateRelocs,
			   transTable);
	exit_to += newInstr->len;
	goto top;
}

static void
emitReleaseSequence(unsigned long exit_to,
		    std::map<unsigned long, unsigned> &releaseSequences,
		    std::vector<unsigned char> &patch_content,
		    std::vector<Relocation *> &relocs,
		    std::vector<LateRelocation *> &lateRelocs,
		    std::vector<trans_table_entry> &transTable,
		    const std::set<unsigned long> &clobberedInstructions,
		    std::map<unsigned long, unsigned> &exitSequences,
		    const SummaryId &summaryId,
		    const CrashCfg &cfg,
		    AddressSpace *as)
{
	if (releaseSequences.count(exit_to)) {
		/* Already have a release sequence here, branch to
		   it. */
		emitInternalJump(releaseSequences[exit_to], patch_content);
	} else {
		/* Generate a new release sequence here */
		unsigned offset = patch_content.size();
		releaseSequences[exit_to] = offset;
		emitCallSequence(patch_content, "(unsigned long)release_lock", lateRelocs, false);
		emitExitSequence(exit_to,
				 patch_content,
				 relocs,
				 lateRelocs,
				 transTable,
				 clobberedInstructions,
				 exitSequences,
				 summaryId,
				 cfg,
				 as);
	}
}

static unsigned
genCodeForEntryPoint(const std::set<unsigned long> &clobberedInstructions,
		     std::vector<unsigned char> &patch_content,
		     std::vector<LateRelocation *> &lateRelocs,
		     std::vector<trans_table_entry> &transTable,
		     const CrashCfg &cfg,
		     const SummaryId &summaryId,
		     Oracle *oracle,
		     const std::map<VexRip, Instruction<ThreadCfgLabel> *> &cfgRoots2)
{
	unsigned result = patch_content.size();
	bool have_entry_validate;
	assert(cfgRoots2.size() > 0);

	/* First thing we do is get out of the red zone. */
	patch_content.push_back(0x48);
	patch_content.push_back(0x8d);
	patch_content.push_back(0x64);
	patch_content.push_back(0x24);
	patch_content.push_back(0x80);

	/* Start by doing something to check all of the stack
	 * contexts. */
	std::vector<std::pair<VexRip, unsigned> > branchesToEntryPoints;
	if (cfgRoots2.size() > 1 || cfgRoots2.begin()->first.stack.size() > 1) {
		/* pushf */
		patch_content.push_back(0x9c);

		validateStackContext(oracle, summaryId, cfg, cfgRoots2,
				     branchesToEntryPoints,
				     patch_content, lateRelocs,
				     transTable);
		have_entry_validate = true;
	} else {
		have_entry_validate = false;
	}

	std::map<VexRip, unsigned> entryMap;
	std::map<unsigned long, unsigned> releaseSequences;
	std::map<unsigned long, unsigned> exitSequences;
	for (auto it = cfgRoots2.begin(); it != cfgRoots2.end(); it++) {
		const VexRip &entryVr(it->first);
		std::vector<Instruction<ThreadCfgLabel> *> toEmit;
		std::map<Instruction<ThreadCfgLabel> *, unsigned> instrOffsets;
		std::vector<Relocation *> relocs;

		assert(!entryMap.count(entryVr));
		entryMap[entryVr] = patch_content.size();

		if (have_entry_validate) {
			/* popf, to match the pushf in entry point
			 * validation. */
			patch_content.push_back(0x9d);
		}

		emitCallSequence(patch_content, "(unsigned long)acquire_lock", lateRelocs, true);

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
				emitOneInstruction(vr, entryVr, node,
						   summaryId, cfg,
						   patch_content,
						   relocs,
						   lateRelocs,
						   transTable);
				if (node->successors.empty())
					emitReleaseSequence(vr.unwrap_vexrip() + node->len,
							    releaseSequences,
							    patch_content,
							    relocs,
							    lateRelocs,
							    transTable,
							    clobberedInstructions,
							    exitSequences,
							    summaryId,
							    cfg,
							    oracle->ms->addressSpace);
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
					emitReleaseSequence(reloc->raw_target,
							    releaseSequences,
							    patch_content,
							    relocs,
							    lateRelocs,
							    transTable,
							    clobberedInstructions,
							    exitSequences,
							    summaryId,
							    cfg,
							    oracle->ms->addressSpace);
				}
				long delta = offset - reloc->offset + reloc->addend - 4;
				patch_content[reloc->offset  ] = delta;
				patch_content[reloc->offset+1] = delta >> 8;
				patch_content[reloc->offset+2] = delta >> 16;
				patch_content[reloc->offset+3] = delta >> 24;
			} else {
				if (clobberedInstructions.count(reloc->raw_target)) {
					unsigned offset = patch_content.size();
					emitExitSequence(reloc->raw_target,
							 patch_content,
							 relocs,
							 lateRelocs,
							 transTable,
							 clobberedInstructions,
							 exitSequences,
							 summaryId,
							 cfg,
							 oracle->ms->addressSpace);
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
	}

	for (auto it = branchesToEntryPoints.begin();
	     it != branchesToEntryPoints.end();
	     it++) {
		assert(entryMap.count(it->first));
		unsigned targ = entryMap[it->first];
		unsigned o = it->second;
		long delta = targ - o - 4;
		assert(delta == (int)delta);
		patch_content[o] = delta;
		patch_content[o + 1] = delta >> 8;
		patch_content[o + 2] = delta >> 16;
		patch_content[o + 3] = delta >> 24;
	}

	return result;
}

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
	std::set<unsigned long> clobberedInstructions;
	for (auto it = cfgRoots2.begin(); it != cfgRoots2.end(); it++) {
		for (unsigned x = 1; x < 5; x++)
			clobberedInstructions.insert(it->first.unwrap_vexrip() + x);
	}

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

	/* Classify the entry points according to their actual RIP, so
	   that we can do stack validation a bit more sensibly. */
	std::map<unsigned long, std::map<VexRip, Instruction<ThreadCfgLabel> * > > segregatedRoots;
	segregateRoots(cfgRoots2, segregatedRoots);

	/* Now go and flatten the CFG fragments into patches. */
	std::vector<unsigned char> patch_content;
	std::vector<LateRelocation *> lateRelocs;
	std::map<unsigned long, unsigned> entryPoints;
	std::vector<trans_table_entry> transTable;
	for (auto it = segregatedRoots.begin(); it != segregatedRoots.end(); it++)
		entryPoints[it->first] = genCodeForEntryPoint(
			clobberedInstructions,
			patch_content,
			lateRelocs,
			transTable,
			cfg,
			summaryId,
			oracle,
			it->second);

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
	for (auto it = entryPoints.begin(); it != entryPoints.end(); it++)
		fragments.push_back(
			vex_asprintf(
				"\t{ .offset = %d, .rip = 0x%lx},\n",
				it->second,
				it->first));
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
