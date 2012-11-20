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
#include "visitor.hpp"

#include "cfgnode_tmpl.cpp"

#ifndef NDEBUG
static bool debug_gen_patch = false;
static bool debug_stack_validation = false;
#else
#define debug_gen_patch false
#define debug_stack_validation false
#endif

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

class InstructionLabel : public Named {
public:
	class entry : public Named {
		char *mkName() const {
			return my_asprintf("%s:%d:%s", summary.name(), tid, node->label.name());
		}
	public:
		SummaryId summary;
		unsigned tid;
		const CFGNode *node;
		entry(const SummaryId &_summary,
		      unsigned _tid,
		      const CFGNode *_node)
			: summary(_summary), tid(_tid), node(_node)
		{}
		bool operator<(const entry &o) const {
			if (summary < o.summary)
				return true;
			else if (o.summary < summary)
				return false;
			else if (tid < o.tid)
				return true;
			else if (tid > o.tid)
				return false;
			else
				return node->label < o.node->label;
		}
		bool operator==(const entry &o) const {
			return summary == o.summary &&
				tid == o.tid &&
				node->label == o.node->label;
		}
	};

	enum {
		fl_locked,
		fl_unlocked,
		fl_bad,
	} flavour;
	/* For locked instructions */
	std::set<entry> content;
	bool restoreRedzone;
	unsigned long finishCallSequence;
	/* For unlocked instructions */
	unsigned long rip;
	/* For both */
	bool checkForEntry;
	bool locked;
private:
	char *mkName() const {
		switch (flavour) {
		case fl_locked: {
			std::vector<const char *> fragments;
			for (auto it = content.begin(); it != content.end(); it++)
				fragments.push_back(it->name());
			const char *suffix;
			if (!restoreRedzone &&
			    checkForEntry &&
			    locked &&
			    !finishCallSequence)
				suffix = ")";
			else
				suffix = vex_asprintf(
					"){%s%s%s%s%s%s%s}",
					(restoreRedzone ? "redzone" : ""),
					(restoreRedzone && (!checkForEntry || !locked || finishCallSequence) ? "," : ""),
					(checkForEntry ? "" : "non-entry"),
					(!checkForEntry && (!locked || finishCallSequence) ? "," : ""),
					(locked ? "" : "unlocked"),
					((locked && finishCallSequence) ? "," : ""),
					(finishCallSequence ? vex_asprintf("call{%lx}", finishCallSequence) : ""));
			return flattenStringFragmentsMalloc(fragments, ";",
							    "L(",
							    suffix);
		}
		case fl_unlocked:
			return my_asprintf("raw:0x%lx%s", rip,
					   checkForEntry ?
					   (locked ? "{locked}" : "") :
					   (locked ? "{non-entry,locked}" : "{non-entry}"));
		case fl_bad:
			return strdup("<bad>");
		}
		abort();
	}
public:
	InstructionLabel() : flavour(fl_bad) {}
	static InstructionLabel raw(unsigned long _rip, bool locked)
	{
		InstructionLabel res;
		res.flavour = fl_unlocked;
		res.rip = _rip;
		res.checkForEntry = true;
		res.locked = locked;
		return res;
	}
	static InstructionLabel rawDoneEntryCheck(unsigned long _rip, bool locked)
	{
		InstructionLabel res;
		res.flavour = fl_unlocked;
		res.rip = _rip;
		res.checkForEntry = false;
		res.locked = locked;
		return res;
	}
	static InstructionLabel compound(const std::set<entry> &_content, bool locked)
	{
		InstructionLabel res;
		res.flavour = fl_locked;
		res.content = _content;
		res.restoreRedzone = false;
		res.checkForEntry = true;
		res.locked = locked;
		res.finishCallSequence = 0;
		return res;
	}
	static InstructionLabel compoundRestoreRedZone(const std::set<entry> &_content, bool locked)
	{
		InstructionLabel res;
		res.flavour = fl_locked;
		res.content = _content;
		res.restoreRedzone = true;
		res.checkForEntry = true;
		res.locked = locked;
		return res;
	}
	static InstructionLabel compoundRestoreRedZoneSkipEntry(const std::set<entry> &_content, bool locked)
	{
		InstructionLabel res;
		res.flavour = fl_locked;
		res.content = _content;
		res.restoreRedzone = true;
		res.checkForEntry = false;
		res.locked = locked;
		res.finishCallSequence = 0;
		return res;
	}
	static InstructionLabel compoundSkipEntry(const std::set<entry> &_content, bool locked)
	{
		InstructionLabel res;
		res.flavour = fl_locked;
		res.content = _content;
		res.restoreRedzone = false;
		res.checkForEntry = false;
		res.locked = locked;
		res.finishCallSequence = 0;
		return res;
	}
	static InstructionLabel simple(const entry &_content, bool locked)
	{
		std::set<entry> content;
		content.insert(_content);
		return compound(content, locked);
	}

	InstructionLabel clearRestoreRedZone() const {
		InstructionLabel res = *this;
		res.restoreRedzone = false;
		res.clearName();
		return res;
	}
	InstructionLabel clearFinishCallSequence() const {
		InstructionLabel res = *this;
		res.finishCallSequence = false;
		assert(!res.restoreRedzone);
		res.clearName();
		return res;
	}

	InstructionLabel acquiredLock() const {
		InstructionLabel res = *this;
		res.locked = true;
		res.clearName();
		return res;
	}
	InstructionLabel releasedLock() const {
		InstructionLabel res = *this;
		res.locked = false;
		res.clearName();
		return res;
	}

	unsigned long getRip() const {
		switch (flavour) {
		case fl_locked: {
			if (content.empty())
				abort();
			unsigned long res = 0xf001; /* shut compiler up */
			for (auto it = content.begin(); it != content.end(); it++) {
				if (it == content.begin())
					res = it->node->rip.unwrap_vexrip();
				else
					assert(res == it->node->rip.unwrap_vexrip());
			}
			return res;
		}
		case fl_unlocked:
			return rip;
		case fl_bad:
			abort();
		}
		abort();
	}

	bool operator != (const InstructionLabel &o) const {
		return *this < o || o < *this;
	}
	bool operator<(const InstructionLabel &o) const {
		if (flavour < o.flavour)
			return true;
		if (flavour > o.flavour)
			return false;
		if (flavour == fl_bad)
			return false;
		if (checkForEntry < o.checkForEntry)
			return true;
		if (checkForEntry > o.checkForEntry)
			return false;
		if (locked < o.locked)
			return true;
		if (locked > o.locked)
			return false;
		switch (flavour) {
		case fl_locked:
			if (content < o.content)
				return true;
			if (content > o.content)
				return false;
			if (restoreRedzone < o.restoreRedzone)
				return true;
			if (restoreRedzone > o.restoreRedzone)
				return true;
			return finishCallSequence < o.finishCallSequence;
		case fl_unlocked:
			return rip < o.rip;
		case fl_bad:
			abort();
		}
		abort();
	}
};

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

class Relocation : public GarbageCollected<Relocation, &ir_heap> {
public:
	unsigned offset;
	InstructionLabel target;

	Relocation(unsigned _offset, const InstructionLabel &_target)
		: offset(_offset), target(_target)
	{}
	void visit(HeapVisitor &) {
	}
	NAMED_CLASS
};

class patch {
public:
	std::vector<unsigned char> content;
	std::map<InstructionLabel, unsigned> offsets;
	std::vector<trans_table_entry> transTable;
	std::vector<Relocation *> relocs;
	std::vector<LateRelocation *> lateRelocs;
};

static void
exitRedZone(patch &p)
{
	p.content.push_back(0x48);
	p.content.push_back(0x8d);
	p.content.push_back(0x64);
	p.content.push_back(0x24);
	p.content.push_back(0x80);	
}
static void
restoreRedZone(patch &p)
{
	p.content.push_back(0x48);
	p.content.push_back(0x8d);
	p.content.push_back(0xa4);
	p.content.push_back(0x24);
	p.content.push_back(0x80);
	p.content.push_back(0x00);
	p.content.push_back(0x00);
	p.content.push_back(0x00);
}

static void
emitBranchToHost(patch &p, unsigned long rip)
{
	p.content.push_back(0xe9);
	p.content.push_back(0);
	p.content.push_back(0);
	p.content.push_back(0);
	p.content.push_back(0);
	p.lateRelocs.push_back(
		new LateRelocation(
			p.content.size() - 4,
			4,
			vex_asprintf("0x%lx", rip),
			0,
			true));
}


class stack_context : public Named {
	char *mkName() const {
		std::vector<const char *> fragments;
		for (auto it = context.begin();
		     it != context.end();
		     it++)
			fragments.push_back(my_asprintf("%d -> %lx", it->first, it->second));
		char *res = flattenStringFragmentsMalloc(fragments, ", ", "StackContext(", ")");
		for (auto it = fragments.begin();
		     it != fragments.end();
		     it++)
			free((void *)*it);
		return res;
	}
public:
	std::vector<std::pair<int, unsigned long> > context;
	stack_context stripOne() const {
		assert(!context.empty());
		stack_context res(*this);
		res.context.pop_back();
		res.clearName();
		return res;
	}
	bool operator<(const stack_context &o) const {
		return context < o.context;
	}
};

struct validation_machine {
	std::set<std::pair<stack_context, InstructionLabel::entry> > toValidate;
	std::set<InstructionLabel::entry> accepted;
	bool operator<(const validation_machine &o) const {
		if (toValidate < o.toValidate)
			return true;
		if (toValidate > o.toValidate)
			return false;
		return accepted < o.accepted;
	}
	void prettyPrint(FILE *f, const char *prefix) const {
		fprintf(f, "%stoValidate:\n", prefix);
		for (auto it = toValidate.begin();
		     it != toValidate.end();
		     it++)
			fprintf(f, "%s\t%s -> %s\n", prefix, it->first.name(), it->second.name());
		fprintf(f, "%sAccepted:\n", prefix);
		for (auto it = accepted.begin();
		     it != accepted.end();
		     it++)
			fprintf(f, "%s\t%s\n", prefix, it->name());
	}
};

static void
emitInternalJump(patch &p, unsigned to)
{
	long delta = to - p.content.size();
	/* Try with an 8-bit jump */
	if (delta >= -126 && delta < 130) {
		p.content.push_back(0xeb);
		p.content.push_back(delta - 2);
	} else {
		/* Use a 32 bit one */
		p.content.push_back(0xe9);
		delta -= 5;
		p.content.push_back(delta & 0xff);
		p.content.push_back((delta >> 8) & 0xff);
		p.content.push_back((delta >> 16) & 0xff);
		p.content.push_back((delta >> 24) & 0xff);
	}
}

static void
emitInternalJump(patch &p, const InstructionLabel &to)
{
	if (p.offsets.count(to)) {
		emitInternalJump(p, p.offsets[to]);
	} else {
		p.content.push_back(0xe9);
		p.content.push_back(0);
		p.content.push_back(0);
		p.content.push_back(0);
		p.content.push_back(0);
		p.relocs.push_back(new Relocation(
					   p.content.size() - 4,
					   to));
	}
}

struct validater_context {
	std::vector<std::pair<unsigned, validation_machine> > relocs;
	std::map<validation_machine, unsigned> offsets;
	std::vector<validation_machine> pending;
	void flush(patch &p) {
		for (auto it = relocs.begin(); it != relocs.end(); ) {
			if (debug_stack_validation) {
				if (debug_stack_validation)
					printf("Process validation reloc, offset %d ->\n",
					       it->first);
				it->second.prettyPrint(stdout, "");
			}
			if (offsets.count(it->second)) {
				if (debug_stack_validation)
					printf("Ready to process\n");
				unsigned reloc_offset = it->first;
				unsigned res_offset = offsets[it->second];
				int delta = res_offset - reloc_offset;
				p.content[reloc_offset - 4] = delta;
				p.content[reloc_offset - 3] = delta >> 8;
				p.content[reloc_offset - 2] = delta >> 16;
				p.content[reloc_offset - 1] = delta >> 24;
				it = relocs.erase(it);
			} else {
				if (debug_stack_validation)
					printf("Still pending\n");
				pending.push_back(it->second);
				it++;
			}
		}
		for (auto it = pending.begin(); it != pending.end(); ) {
			if (offsets.count(*it)) {
				it = pending.erase(it);
			} else {
				it++;
			}
		}
 	}
};

static void
emitValidater(patch &p,
	      unsigned long rip,
	      struct validater_context &ctxt,
	      bool locked,
	      validation_machine machine)
{
	if (debug_stack_validation) {
		printf("emitValidater: rip = %lx, machine =\n", rip);
		machine.prettyPrint(stdout, "\t");
	}
	/* Anything with a now-empty context is accepted */
	for (auto it = machine.toValidate.begin();
	     it != machine.toValidate.end();
		) {
		if (it->first.context.empty()) {
			machine.accepted.insert(it->second);
			machine.toValidate.erase(it++);
		} else {
			it++;
		}
	}
	if (machine.toValidate.empty()) {
		/* We're done */
		if (debug_stack_validation)
			printf("\t-> all done\n");
		emitInternalJump(p, InstructionLabel::compoundRestoreRedZoneSkipEntry(machine.accepted, locked));
		return;
	}
	/* Otherwise, need to do some more validation.  Always pick
	 * the nearest (i.e. lowest offset) entry in the stack
	 * context. */
	int nearest_offset = -1;
	for (auto it = machine.toValidate.begin();
	     it != machine.toValidate.end();
	     it++) {
		if (it->first.context[0].first > nearest_offset)
			nearest_offset = it->first.context[0].first;
	}
	assert(nearest_offset != -1);
	if (debug_stack_validation)
		printf("\tSplit on offset %d\n", nearest_offset);
	/* Now split based on that offset */
	std::map<unsigned long, validation_machine> split;
	std::set<std::pair<stack_context, InstructionLabel::entry> > unsplit;
	for (auto it = machine.toValidate.begin(); it != machine.toValidate.end(); it++) {
		if (it->first.context[0].first == nearest_offset) {
			split[it->first.context[0].second].toValidate.insert(
				std::pair<stack_context, InstructionLabel::entry>(
					it->first.stripOne(),
					it->second));
		} else {
			unsplit.insert(*it);
		}
	}
	for (auto it = split.begin();
	     it != split.end();
	     it++) {
		it->second.accepted = machine.accepted;
		it->second.toValidate |= unsplit;
	}
	/* Now emit the validater */

	if (debug_stack_validation) {
		printf("\tSplit validaters:\n");
		for (auto it = split.begin();
		     it != split.end();
		     it++) {
			printf("\t\t%lx ->\n", it->first);
			it->second.prettyPrint(stdout, "\t\t\t");
		}
	}
	/* 136 to get past red zone and save rflags */
	int offset = 136 + nearest_offset;
	for (auto it = split.begin(); it != split.end(); it++) {
		unsigned long expected = it->first;
		if (expected >= 0x100000000ul) {
			/* Can't handle this case yet */
			abort();
		}
		/* cmpq imm32, offset(%rsp) */
		p.content.push_back(0x48);
		p.content.push_back(0x81);
		p.content.push_back(0xbc);
		p.content.push_back(0x24);
		p.content.push_back(offset);
		p.content.push_back(offset >> 8);
		p.content.push_back(offset >> 16);
		p.content.push_back(offset >> 24);
		p.content.push_back(expected);
		p.content.push_back(expected >> 8);
		p.content.push_back(expected >> 16);
		p.content.push_back(expected >> 24);
		/* je rel32 */
		p.content.push_back(0x0f);
		p.content.push_back(0x84);
		p.content.push_back(1);
		p.content.push_back(2);
		p.content.push_back(3);
		p.content.push_back(4);
		ctxt.relocs.push_back(
			std::pair<unsigned, validation_machine>(p.content.size(), it->second));
	}

	/* None of the validaters fired.  Take what we have. */
	if (!machine.accepted.empty()) {
		emitInternalJump(p, InstructionLabel::compoundRestoreRedZoneSkipEntry(machine.accepted, locked));
		ctxt.flush(p);
		if (debug_stack_validation) {
			printf("\tFall back to {");
			for (auto it = machine.accepted.begin(); it != machine.accepted.end(); it++) {
				if (it != machine.accepted.begin())
					printf(", ");
				printf("%s", it->name());
			}
			printf("}\n");
		}
		return;
	}

	/* Don't have anything -> get out */

	/* popf */
	p.content.push_back(0x9d);
	/* Restore red zone */
	p.content.push_back(0x48);
	p.content.push_back(0x8d);
	p.content.push_back(0xa4);
	p.content.push_back(0x24);
	p.content.push_back(0x80);
	p.content.push_back(0x00);
	p.content.push_back(0x00);
	p.content.push_back(0x00);

	ctxt.flush(p);
	if (!ctxt.pending.empty()) {
		if (debug_stack_validation)
			printf("\tFall back to raw %lx\n", rip);
		emitInternalJump(p, InstructionLabel::rawDoneEntryCheck(rip, locked));
	} else {
		if (debug_stack_validation)
			printf("No epilogue\n");
		assert(ctxt.relocs.empty());
	}
}

static stack_context
ripToStackContext(Oracle *oracle, const VexRip &vr)
{
	unsigned offset = 0;
	stack_context res;
	for (unsigned x = 1; x < vr.stack.size(); x++) {
		offset += stack_offset(oracle, vr.stack[vr.stack.size() - x ]);
		res.context.push_back(
			std::pair<int, unsigned long>(
				offset, vr.stack[vr.stack.size() - x - 1]));
	}
	return res;
}

static void
stackValidatedEntryPoints(Oracle *oracle,
			  patch &p,
			  const InstructionLabel &start,
			  const std::set<InstructionLabel::entry> &entries,
			  bool locked)
{
	if (debug_stack_validation) {
		printf("Stack validated entry point at %s\n", start.name());
		printf("Options:\n");
		for (auto it = entries.begin(); it != entries.end(); it++)
			printf("\t%s\n", it->name());
	}

	/* Get out of the red zone. */
	exitRedZone(p);
	/* pushf */
	p.content.push_back(0x9c);

	validation_machine validater;
	validater.accepted.insert(start.content.begin(), start.content.end());
	for (auto it = entries.begin(); it != entries.end(); it++)
		validater.toValidate.insert(
			std::pair<stack_context, InstructionLabel::entry>
			(ripToStackContext(oracle, it->node->rip), *it));
	if (debug_stack_validation) {
		printf("Initial validater:\n");
		validater.prettyPrint(stdout, "");
	}
	struct validater_context ctxt;
	ctxt.pending.push_back(validater);
	while (!ctxt.pending.empty()) {
		validation_machine m(ctxt.pending.back());
		ctxt.pending.pop_back();
		if (ctxt.offsets.count(m))
			continue;
		ctxt.offsets[m] = p.content.size();
		emitValidater(p, start.getRip(), ctxt, locked, m);
		ctxt.flush(p);
	}
	assert(ctxt.relocs.empty());
}

typedef std::map<SummaryId, std::vector<std::pair<unsigned, const CFGNode *> > > summaryRootsT;
static void
findEntryLabels(unsigned long rip,
		std::set<InstructionLabel::entry> &entryPoints,
		const summaryRootsT &summaryRoots)
{
	for (auto it = summaryRoots.begin(); it != summaryRoots.end(); it++) {
		SummaryId summary(it->first);
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			unsigned thread = it2->first;
			const CFGNode *n = it2->second;
			if (n->rip.unwrap_vexrip() == rip)
				entryPoints.insert(
					InstructionLabel::entry(summary,
								thread,
								n));
		}
	}
}

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
emitCallSequence(patch &p, const char *target)
{
	extern const unsigned char
		__call_sequence_template_start[],
		__call_sequence_template_load_rsi[],
		__call_sequence_template_end[];
	unsigned start_sz = p.content.size();
	for (const unsigned char *cursor = __call_sequence_template_start;
	     cursor != __call_sequence_template_end;
	     cursor++)
		p.content.push_back(*cursor);

	p.lateRelocs.push_back(
		new LateRelocation(
			start_sz + __call_sequence_template_load_rsi - __call_sequence_template_start + 2,
			8,
			vex_asprintf("%s", target),
			0,
			false));
}

static Maybe<InstructionLabel>
emitUnlockedInstruction(const InstructionLabel &rip,
			const std::set<unsigned long> &clobbered,
			const summaryRootsT &summaryRoots,
			Oracle *oracle,
			patch &p)
{
	if (rip.locked) {
		emitCallSequence(p, "(unsigned long)release_lock");
		return Maybe<InstructionLabel>::just(rip.releasedLock());
	}
	if (rip.checkForEntry) {
		/* Do we need to move to locked mode? */
		std::set<InstructionLabel::entry> entries;
		findEntryLabels(rip.getRip(), entries, summaryRoots);
		if (!entries.empty()) {
			if (entries.size() == 1 &&
			    entries.begin()->node->rip.stack.size() == 1) {
				/* Easy case: there is only one entrypoint
				   here, and it has no stack context, so just
				   switch unconditionally. */
				return Maybe<InstructionLabel>::just(InstructionLabel::simple(*entries.begin(), false));
			}
			bool allContextFree = true;
			for (auto it = entries.begin();
			     allContextFree && it != entries.end();
			     it++)
				allContextFree &= it->node->rip.stack.size() == 1;
			if (allContextFree) {
				/* Multiple entry points, but none require
				   stack validation -> still pretty easy. */
				return Maybe<InstructionLabel>::just(InstructionLabel::compound(entries, false));
			}

			/* Okay, we need to do stack validation.  That
			 * complicates things a bit. */
			stackValidatedEntryPoints(oracle, p, rip, entries, false);
			/* Fall through if stack validation fails. */
		}
	}

	if (!clobbered.count(rip.getRip())) {
		emitBranchToHost(p, rip.getRip());
		return Maybe<InstructionLabel>::nothing();
	}

	unsigned len = 99;
	Instruction<ThreadCfgLabel> *newInstr =
		decode_instr(oracle->ms->addressSpace,
			     rip.getRip(),
			     ThreadCfgLabel(
				     AbstractThread::uninitialised(),
				     CfgLabel(-1)),
			     &len,
			     true);
	assert(len != 99);
	if (!newInstr)
		errx(1, "need to decode instruction at %lx, but decoder failed!", rip.getRip());
	for (auto it = newInstr->relocs.begin();
	     it != newInstr->relocs.end();
	     it++) {
		RipRelativeBlindRelocation<ThreadCfgLabel> *r = 
			dynamic_cast<RipRelativeBlindRelocation<ThreadCfgLabel> *>(*it);
		assert(r);
		if (r->is_branch) {
			p.relocs.push_back(
				new Relocation(
					r->offset + p.content.size(),
					InstructionLabel::raw(r->target, false)));
		} else {
			p.lateRelocs.push_back(
				new LateRelocation(
					r->offset + p.content.size(),
					4,
					vex_asprintf("0x%lx", r->target),
					0,
					true));
		}
	}
	assert(newInstr->lateRelocs.empty());
	for (unsigned x = 0; x < newInstr->len; x++)
		p.content.push_back(newInstr->content[x]);

	/* Figure out whether we have a fall-through successor.
	   Assuming we have a fallthrough when we don't is safe but
	   inefficient; assuming we don't have one when we do is
	   dangerous. */
	bool hasFallThrough = true;
	if (newInstr->content[0] == 0xc3 /* ret */ ||
	    newInstr->content[0] == 0xeb /* jmp 8 bit */ ||
	    newInstr->content[0] == 0xe9 /* jmp 32 bit */)
		hasFallThrough = false;
	if (hasFallThrough)
		return Maybe<InstructionLabel>::just(InstructionLabel::raw(rip.getRip() + len, false));
	else
		return Maybe<InstructionLabel>::nothing();
}

static InstructionLabel
succRipToLabel(unsigned long nextRip, const InstructionLabel &start)
{
	InstructionLabel nextLabel(InstructionLabel::compound(std::set<InstructionLabel::entry>(), start.locked));
	for (auto it = start.content.begin();
	     it != start.content.end();
	     it++) {
		const CFGNode *currentNode = it->node;
		for (auto it2 = currentNode->successors.begin();
		     it2 != currentNode->successors.end();
		     it2++) {
			const CFGNode *potentialSuccessor = it2->instr;
			if (!potentialSuccessor)
				continue;
			if (potentialSuccessor->rip.unwrap_vexrip() != nextRip)
				continue;
			/* Take this successor */
			nextLabel.content.insert(
				InstructionLabel::entry(
					it->summary,
					it->tid,
					potentialSuccessor));
		}
	}
	if (nextLabel.content.empty())
		return InstructionLabel::raw(nextRip, start.locked);
	nextLabel.clearName();
	return nextLabel;
}

static Maybe<InstructionLabel>
handleIndirectCall(patch &p,
		   const InstructionLabel &start,
		   unsigned len,
		   Instruction<ThreadCfgLabel> *instr)
{
	unsigned long rip = start.getRip();
	unsigned long next_rip = rip + len;
	InstructionLabel emptyLabel(InstructionLabel::compound(std::set<InstructionLabel::entry>(), start.locked));
	emptyLabel.finishCallSequence = next_rip;
	emptyLabel.clearName();

	/* Where might we be going next? */
	std::map<unsigned long, InstructionLabel> whereToNext;
	for (auto it = start.content.begin();
	     it != start.content.end();
	     it++) {
		const CFGNode *currentNode = it->node;
		for (auto it2 = currentNode->successors.begin();
		     it2 != currentNode->successors.end();
		     it2++) {
			const CFGNode *potentialSuccessor = it2->instr;
			if (!potentialSuccessor)
				continue;
			unsigned long rip = potentialSuccessor->rip.unwrap_vexrip();
			auto it3_did_insert = whereToNext.insert(
				std::pair<unsigned long, InstructionLabel>(
					rip,
					emptyLabel));
			InstructionLabel &nextLabel(it3_did_insert.first->second);
			nextLabel.content.insert(
				InstructionLabel::entry(
					it->summary,
					it->tid,
					potentialSuccessor));
		}
	}

	exitRedZone(p);
	p.content.push_back(0x57); /* push rdi */
	p.content.push_back(0x9c); /* pushf */

	/* The instruction is call modrm.  We want to turn it into mov
	   modrm, rdi so that we can do the validation. */
	int skip = 0;
	if (instr->content[0] >= 0x40 && instr->content[0] <= 0x4f) {
		/* Preserve REX prefix, except for the R bit, and set
		   W bit. */
		p.content.push_back((instr->content[0] & ~4) | 8);
		skip = 1;
	} else {
		/* Need a REX prefix with the W bit set */
		p.content.push_back(0x48);
	}
	/* opcode */
	p.content.push_back(0x8b);
	/* modrm.  Take the original one, but replace the reg field with
	   7 (== rdi) */
	p.content.push_back(instr->content[1 + skip] | (7 << 3));
	/* Transfer the rest of the modrm */
	for (unsigned i = skip + 2; i < instr->len; i++)
		p.content.push_back(instr->content[i]);

	/* Now emit the validation stuff */
	for (auto it = whereToNext.begin(); it != whereToNext.end(); it++) {
		assert(it->first < 0x100000000ul);
		/* cmpq $imm32, %rdi */
		p.content.push_back(0x48);
		p.content.push_back(0x81);
		p.content.push_back(0xff);
		p.content.push_back(it->first);
		p.content.push_back(it->first >> 8);
		p.content.push_back(it->first >> 16);
		p.content.push_back(it->first >> 32);
		/* je rel32 */
		p.content.push_back(0x0f);
		p.content.push_back(0x84);
		p.content.push_back(1);
		p.content.push_back(2);
		p.content.push_back(3);
		p.content.push_back(4);
		p.relocs.push_back(
			new Relocation(
				p.content.size() - 4,
				it->second));
	}

	/* If we get here then none of the successors matched, so we
	   need to get out of the patch. */
	/* Tricky part: can't re-evaluate the successor, because that
	   would introduce a race, so have to emulate the call
	   manually. */
	if (start.locked)
		emitCallSequence(p, "(unsigned long)release_lock");
	/* movq imm32, 0x88(%rsp) -- save the return address */
	assert(next_rip <= 0x100000000ul);
	p.content.push_back(0x48);
	p.content.push_back(0xc7);
	p.content.push_back(0x84);
	p.content.push_back(0x24);
	p.content.push_back(0x88);
	p.content.push_back(0x00);
	p.content.push_back(0x00);
	p.content.push_back(0x00);
	p.content.push_back(next_rip);
	p.content.push_back(next_rip >> 8);
	p.content.push_back(next_rip >> 16);
	p.content.push_back(next_rip >> 24);
	/* popf */
	p.content.push_back(0x9d);
	/* xchg %rdi, (%rsp) -- restores rdi and pushes the address we want to go to next. */
	p.content.push_back(0x48);
	p.content.push_back(0x87);
	p.content.push_back(0x3c);
	p.content.push_back(0x24);
	/* ret $0x78 -- restore redzone.  Note that we don't restore
	   the whole thing, because the return address of the function
	   we're calling is effectively the first 8 bytes of the
	   redzone. */
	p.content.push_back(0xc2);
	p.content.push_back(0x78);
	p.content.push_back(0x00);
	/* Well, that was fun. */
	return Maybe<InstructionLabel>::nothing();
}

static Maybe<InstructionLabel>
handleReturnInstr(patch &p, const InstructionLabel &start)
{
	/* If we're in a locked fragment then returns are pointless,
	   because the return structure is already incorporated into
	   the control structure of the patch via implicit inlining.
	   All we need to do is calculate the successor and adjust the
	   stack. */
	InstructionLabel nextLabel(InstructionLabel::compound(std::set<InstructionLabel::entry>(), start.locked));
	for (auto it = start.content.begin();
	     it != start.content.end();
	     it++) {
		const CFGNode *currentNode = it->node;
		for (auto it2 = currentNode->successors.begin();
		     it2 != currentNode->successors.end();
		     it2++) {
			const CFGNode *potentialSuccessor = it2->instr;
			if (!potentialSuccessor)
				continue;
			nextLabel.content.insert(
				InstructionLabel::entry(
					it->summary,
					it->tid,
					potentialSuccessor));
		}
	}
	nextLabel.clearName();
	assert(!nextLabel.content.empty());
	/* Restore stack pointer with an lea. */
	p.content.push_back(0x48);
	p.content.push_back(0x8d);
	p.content.push_back(0x64);
	p.content.push_back(0x24);
	p.content.push_back(0x08);
	/* Go wherever we need to go next */
	return Maybe<InstructionLabel>::just(nextLabel);
}

static Maybe<InstructionLabel>
emitLockedInstruction(const InstructionLabel &start,
		      const summaryRootsT &summaryRoots,
		      Oracle *oracle,
		      patch &p)
{
	unsigned long rip = start.getRip();

	if (start.finishCallSequence) {
		/* popf */
		p.content.push_back(0x9d);
		/* pop rdi */
		p.content.push_back(0x5f);
		/* restore red zone */
		restoreRedZone(p);
		/* pushq $imm64 */
		assert(start.finishCallSequence < 0x100000000ul);
		p.content.push_back(0x68);
		p.content.push_back(start.finishCallSequence);
		p.content.push_back(start.finishCallSequence >> 8);
		p.content.push_back(start.finishCallSequence >> 16);
		p.content.push_back(start.finishCallSequence >> 24);
		return Maybe<InstructionLabel>::just(start.clearFinishCallSequence());
	}
	if (start.restoreRedzone) {
		/* popf */
		p.content.push_back(0x9d);
		restoreRedZone(p);
		return Maybe<InstructionLabel>::just(start.clearRestoreRedZone());
	}

	if (!start.locked) {
		emitCallSequence(p, "(unsigned long)acquire_lock");
		return Maybe<InstructionLabel>::just(start.acquiredLock());
	}
	if (start.checkForEntry) {
		/* Do we need to start any more CFG fragments? */
		std::set<InstructionLabel::entry> entries;
		findEntryLabels(rip, entries, summaryRoots);
		if (!entries.empty()) {
			InstructionLabel newStart(start);
			if (entries.size() == 1 &&
			    entries.begin()->node->rip.stack.size() == 1) {
				newStart.content.insert(*entries.begin());
				if (newStart != start) {
					newStart.clearName();
					return Maybe<InstructionLabel>::just(newStart);
				}
			} else {
				bool allContextFree = true;
				for (auto it = entries.begin();
				     allContextFree && it != entries.end();
				     it++)
					allContextFree &= it->node->rip.stack.size() == 1;
				if (allContextFree) {
					/* Multiple entry points, but
					   none require stack
					   validation -> still pretty
					   easy. */
					newStart.content.insert(entries.begin(), entries.end());
					if (newStart != start) {
						newStart.clearName();
						return Maybe<InstructionLabel>::just(newStart);
					}
				} else {
					/* Okay, we need to do stack
					 * validation.  That
					 * complicates things a
					 * bit. */
					stackValidatedEntryPoints(oracle, p, start, entries, true);
				}
			}
		}
	}

	if (start.content.empty()) {
		/* Fell off the locked CFG -> move to unlocked mode */
		return Maybe<InstructionLabel>::just(InstructionLabel::raw(rip, true));
	}
	unsigned len = 99;
	Instruction<ThreadCfgLabel> *newInstr =
		decode_instr(oracle->ms->addressSpace,
			     rip,
			     ThreadCfgLabel(AbstractThread::uninitialised(), CfgLabel(-1)),
			     &len,
			     true);
	assert(len != 99);
	if (!newInstr)
		errx(1, "need to decode instruction at %lx, but decoder failed!", rip);

	if (newInstr->content[0] == 0xff &&
	    ((newInstr->content[1] >> 3) & 7) == 2) {
		/* Indirect call instructions need special handling. */
		return handleIndirectCall(p, start, len, newInstr);
	}
	if (newInstr->content[0] == 0xc3) {
		/* Also need special handling for ret instructions. */
		return handleReturnInstr(p, start);
	}

	std::vector<unsigned long> succInstructions;
	for (auto it = newInstr->relocs.begin();
	     it != newInstr->relocs.end();
	     it++) {
		RipRelativeBlindRelocation<ThreadCfgLabel> *r = 
			dynamic_cast<RipRelativeBlindRelocation<ThreadCfgLabel> *>(*it);
		assert(r);
		if (!r->is_branch) {
			p.lateRelocs.push_back(
				new LateRelocation(
					r->offset + p.content.size(),
					4,
					vex_asprintf("0x%lx", r->target),
					0,
					true));
			continue;
		}
		
		/* The decoder has told us what RIP this instruction
		   might branch to.  Figure out what label that
		   corresponds to. */
		InstructionLabel nextLabel = succRipToLabel(r->target, start);
		/* Emit an appropriate reloc */
		p.relocs.push_back(
			new Relocation(
				r->offset + p.content.size(),
				nextLabel));
	}
	assert(newInstr->lateRelocs.empty());
	for (unsigned x = 0; x < newInstr->len; x++)
		p.content.push_back(newInstr->content[x]);

	/* Figure out whether we have a fall-through successor.
	   Assuming we have a fallthrough when we don't is safe but
	   inefficient; assuming we don't have one when we do is
	   dangerous. */
	bool hasFallThrough = true;
	if (newInstr->content[0] == 0xeb /* jmp 8 bit */ ||
	    newInstr->content[0] == 0xe9 /* jmp 32 bit */)
		hasFallThrough = false;
	if (hasFallThrough)
		return Maybe<InstructionLabel>::just(succRipToLabel(rip + len, start));
	else
		return Maybe<InstructionLabel>::nothing();
	
}

static void
flushRelocations(patch &p, std::vector<InstructionLabel> &needed)
{
	for (auto it = p.relocs.begin();
	     it != p.relocs.end();
		) {
		Relocation *r = *it;
		if (p.offsets.count(r->target)) {
			long delta = (long)p.offsets[r->target] - (long)r->offset - 4;
			assert(delta == (int)delta);
			p.content[r->offset] = delta;
			p.content[r->offset+1] = delta >> 8;
			p.content[r->offset+2] = delta >> 16;
			p.content[r->offset+3] = delta >> 24;
			it = p.relocs.erase(it);
		} else {
			needed.push_back(r->target);
			it++;
		}
	}
}

static void
buildPatch(patch &p,
	   const std::set<unsigned long> &patchPoints,
	   const std::set<unsigned long> &clobbered,
	   const summaryRootsT &summaryRoots,
	   Oracle *oracle)
{
	std::vector<InstructionLabel> needed;
	for (auto it = patchPoints.begin();
	     it != patchPoints.end();
	     it++)
		needed.push_back(InstructionLabel::raw(*it, false));

	while (!needed.empty()) {
		InstructionLabel n(needed.back());
		needed.pop_back();

		if (p.offsets.count(n))
			continue;
		while (1) {
			if (debug_gen_patch)
				printf("Extend patch with %s at offset 0x%zx\n",
				       n.name(), p.content.size());
			assert(!p.offsets.count(n));
			p.offsets[n] = p.content.size();
			p.transTable.push_back(
				trans_table_entry(
					p.content.size(),
					n.getRip(),
					strdup(n.name())));
			Maybe<InstructionLabel> next(Maybe<InstructionLabel>::nothing());
			switch (n.flavour) {
			case InstructionLabel::fl_locked:
				next = emitLockedInstruction(n, summaryRoots, oracle, p);
				break;
			case InstructionLabel::fl_unlocked:
				next = emitUnlockedInstruction(n, clobbered, summaryRoots, oracle, p);
				break;
			case InstructionLabel::fl_bad:
				abort();
			}
			if (!next.valid)
				break;
			if (p.offsets.count(next.content)) {
				emitInternalJump(p, p.offsets[next.content]);
				break;
			}
			n = next.content;
		}
		flushRelocations(p, needed);
	}
}

static void
findRelevantMais(const IRExpr *iex, std::set<MemoryAccessIdentifier> &out)
{
	struct {
		static visit_result HappensBefore(
			std::set<MemoryAccessIdentifier> *out,
			const IRExprHappensBefore *hb) {
			out->insert(hb->before);
			out->insert(hb->after);
			return visit_continue;
		}
	} foo;
	static irexpr_visitor<std::set<MemoryAccessIdentifier> > visitor;
	visitor.HappensBefore = foo.HappensBefore;
	visit_irexpr(&out, &visitor, iex);
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

struct patchStrategy {
	std::set<unsigned long> MustInterpret;
	std::set<unsigned long> Patch;
	std::set<unsigned long> Cont;
	unsigned size() const {
		return MustInterpret.size() + Cont.size();
	}
	bool operator<(const patchStrategy &o) const {
		return size() > o.size();
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

static bool
patchSearch(Oracle *oracle,
	    const patchStrategy &input,
	    std::priority_queue<patchStrategy> &thingsToTry)
{
	if (input.MustInterpret.empty())
		return true;

	input.prettyPrint(stdout);
	unsigned long needed = *input.MustInterpret.begin();

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
		printf("Patch to: ");
		patched.prettyPrint(stdout);
	}

	/* Try expanding to predecessors. */
	std::set<unsigned long> predecessors;
	oracle->findPredecessors(needed, predecessors);
	c.MustInterpret.insert(predecessors.begin(), predecessors.end());
	thingsToTry.push(c);
	printf("Unpatched: ");
	c.prettyPrint(stdout);
	return false;
}

static void
buildPatchStrategy(Oracle *oracle,
		   crashEnforcementRoots &roots,
		   CrashCfg &cfg,
		   std::set<unsigned long> &patchPoints,
		   std::set<unsigned long> &clobbered)
{
	patchStrategy initPs;

	for (auto it = roots.begin(); !it.finished(); it.advance()) {
		Instruction<ThreadCfgLabel> *instr = cfg.findInstr(it.get());
		assert(instr);
		const AbstractThread &absThread(instr->rip.thread);
		ConcreteThread concThread(roots.lookupAbsThread(absThread));
		ConcreteCfgLabel concCfgLabel(concThread.summary(), instr->rip.label);
		const VexRip &vr(cfg.labelToRip(concCfgLabel));

		unsigned long r = vr.unwrap_vexrip();
		initPs.MustInterpret.insert(r);
	}

	std::priority_queue<patchStrategy> pses;
	pses.push(initPs);
	while (!pses.empty()) {
		patchStrategy next(pses.top());
		pses.pop();
		if (patchSearch(oracle, next, pses)) {
			/* We have a solution. */
			printf("Patch solution:\n");
			next.prettyPrint(stdout);
			patchPoints = next.Patch;
			clobbered = next.Cont;
			return;
		}
	}
	errx(1, "Cannot solve patch problem");
}

static char *
buildPatchForCrashSummary(Oracle *oracle,
			  const std::map<SummaryId, CrashSummary *> &summaries)
{
	std::set<unsigned long> patchPoints;
	std::set<unsigned long> clobbered;
	summaryRootsT summaryRoots;
	{
		ThreadAbstracter absThread;
		std::map<ConcreteThread, std::set<CfgLabel> > cfgRoots;
		for (auto it = summaries.begin();
		     it != summaries.end();
		     it++) {
			CrashSummary *summary = it->second;
			const SummaryId &summaryId(it->first);

			std::set<MemoryAccessIdentifier> relevant_mais;
			findRelevantMais(summary->verificationCondition, relevant_mais);
			std::set<std::pair<unsigned, CfgLabel> > relevant_cfgs;
			findRelevantCfgs(summary->mai, relevant_mais, relevant_cfgs);

			trimCfg(summary->loadMachine, relevant_cfgs);
			trimCfg(summary->storeMachine, relevant_cfgs);

			for (auto it = summary->loadMachine->cfg_roots.begin();
			     it != summary->loadMachine->cfg_roots.end();
			     it++)
				cfgRoots[ConcreteThread(summaryId, it->first)].insert(it->second->label);
			for (auto it = summary->storeMachine->cfg_roots.begin();
			     it != summary->storeMachine->cfg_roots.end();
			     it++)
				cfgRoots[ConcreteThread(summaryId, it->first)].insert(it->second->label);

			summaryRoots[summaryId] = summary->loadMachine->cfg_roots;
			summaryRoots[summaryId].insert(
				summaryRoots[summaryId].end(),
				summary->storeMachine->cfg_roots.begin(),
				summary->storeMachine->cfg_roots.end());
		}
		crashEnforcementRoots cer(cfgRoots, absThread);
		CrashCfg cfg(cer, summaries, oracle->ms->addressSpace, true, absThread);
		buildPatchStrategy(oracle, cer, cfg, patchPoints, clobbered);
	}

	/* Now go and flatten the CFG fragments into patches. */
	patch p;
	buildPatch(p, patchPoints, clobbered, summaryRoots,oracle);

	std::vector<const char *> fragments;
	fragments.push_back("static const unsigned char patch_content[] = \"");
	for (auto it = p.content.begin(); it != p.content.end(); it++)
		fragments.push_back(vex_asprintf("\\x%02x", *it));
	fragments.push_back("\";\n\n");
	fragments.push_back("static const struct relocation relocations[] = {\n");
	for (auto it = p.lateRelocs.begin(); it != p.lateRelocs.end(); it++)
		fragments.push_back(vex_asprintf("\t%s,\n", (*it)->asC()));
	fragments.push_back("};\n\n");
	fragments.push_back("static const struct trans_table_entry trans_table[] = {\n");
	for (auto it = p.transTable.begin(); it != p.transTable.end(); it++)
		fragments.push_back(vex_asprintf("\t{.rip = 0x%lx, .offset = %d} /* %s */,\n",
						 it->rip,
						 it->offset_in_patch,
						 it->debug_msg));
	fragments.push_back("};\n\n");

	fragments.push_back("static const struct entry_context entry_points[] = {\n");
	for (auto it = patchPoints.begin(); it != patchPoints.end(); it++) {
		assert(p.offsets.count(InstructionLabel::raw(*it, false)));
		fragments.push_back(
			vex_asprintf(
				"\t{ .offset = %d, .rip = 0x%lx},\n",
				p.offsets[InstructionLabel::raw(*it, false)],
				*it));
	}
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

int
main(int argc, char *const argv[])
{
	if (argc < 7)
		errx(1, "need at least six arguments: binary, types table, callgraph, static db, output filename, and at least one summary");

	const char *binary = argv[1];
	const char *types_table = argv[2];
	const char *callgraph = argv[3];
	const char *staticdb = argv[4];
	const char *output_fname = argv[5];
	const char *const *summary_fnames = argv + 6;
	int nr_summaries = argc - 6;

	init_sli();

	VexPtr<Oracle> oracle;
	{
		MachineState *ms = MachineState::readELFExec(binary);
		Thread *thr = ms->findThread(ThreadId(1));
		oracle = new Oracle(ms, thr, types_table);
	}
	oracle->loadCallGraph(oracle, callgraph, staticdb, ALLOW_GC);

	std::map<SummaryId, CrashSummary *> summaries;
	for (int i = 0; i < nr_summaries; i++) {
		SMScopes scopes;
		summaries[SummaryId(i + 1)] = readBugReport(&scopes, summary_fnames[i], NULL);
	}

	char *patch = buildPatchForCrashSummary(oracle, summaries);
	printf("Patch is:\n%s\n", patch);

	FILE *output = fopen(output_fname, "w");
	fprintf(output, "/* SLI fix generated for %s */\n", binary);
	fprintf(output,
		"/* Compile as gcc -Wall -g -shared -fPIC -Isli %s -o %s.so */\n",
		output_fname, binary);
	fprintf(output, "/* Crash summaries:\n");
	for (auto it = summaries.begin(); it != summaries.end(); it++) {
		fprintf(output, "  Summary %s:\n", it->first.name());
		printCrashSummary(it->second, output);
		fprintf(output, "\n\n\n");
	}
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
