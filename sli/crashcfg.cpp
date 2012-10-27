#include "sli.h"
#include "crashcfg.hpp"
#include "alloc_mai.hpp"

#include "x86_opcodes.c"

/* Cut-down version of x86_emulate which just does enough to find the
 * size of the instruction. */
Instruction<ThreadCfgLabel> *
decode_instr(AddressSpace *as, unsigned long ptr, const ThreadCfgLabel &label,
	     unsigned *true_size, bool generate_relocs)
{
	const unsigned long init_ptr = ptr;
	uint16_t b;
	uint8_t d, rex_prefix = 0;
	uint8_t modrm = 0;
	unsigned int op_bytes;

	struct {
		std::vector<EarlyRelocation<ThreadCfgLabel> *> r;
		void operator()(unsigned long offset,
				unsigned long value,
				unsigned sz,
				bool is_branch) {
			r.push_back(new RipRelativeBlindRelocation<ThreadCfgLabel>(
					    offset,
					    sz,
					    value,
					    is_branch));
		}
	} emit_reloc;

	op_bytes = 4;

#define insn_fetch_type(ty) ({ty res = as->fetch<ty>(ptr, NULL); ptr += sizeof(ty); res; })

	/* Prefix bytes. */
	while (1) {
		b = insn_fetch_type(uint8_t);
		switch (b) {
		case 0x66:
			op_bytes = 2;
			break;
		case 0x64: /* FS override */
		case 0x65: /* GS override */
		case 0xf0: /* LOCK */
		case 0xf2: /* REPNE/REPNZ */
		case 0xf3: /* REP/REPE/REPZ */
			break;
		case 0x40 ... 0x4f: /* REX */
			rex_prefix = b;
			continue;
		default:
			goto done_prefixes;
		}

		/* Any legacy prefix after a REX prefix nullifies its effect. */
		rex_prefix = 0;
	}
done_prefixes:

	if ( rex_prefix & 8 ) /* REX.W */
		op_bytes = 8;

	/* Opcode byte(s). */
	d = opcode_table[b];
	if ( d == 0 )
	{
		/* Two-byte opcode? */
		if ( b == 0x0f )
		{
			b = insn_fetch_type(uint8_t);
			d = twobyte_table[b];
			b |= 0x0f00;
		}

		/* Unrecognised? */
		if ( d == 0 )
			abort();
	}

	/* ModRM and SIB bytes. */
	if ( d & ModRM )
	{
		modrm = insn_fetch_type(uint8_t);
		unsigned char modrm_mod = (modrm & 0xc0) >> 6;
		unsigned char modrm_reg = (modrm & 0x38) >> 3;
		unsigned char modrm_rm  = modrm & 0x07;

		if ( modrm_mod == 3 )
		{
			modrm_rm |= (rex_prefix & 1) << 3;
		}
		else
		{
			/* 32/64-bit ModR/M decode. */
			if ( modrm_rm == 4 )
			{
				unsigned char sib,  sib_base;
				sib = insn_fetch_type(uint8_t);
				sib_base  = (sib & 7) | ((rex_prefix << 3) & 8);
				if ( (modrm_mod == 0) && ((sib_base & 7) == 5) )
					ptr += 4;
			}
			else
			{
				modrm_rm |= (rex_prefix & 1) << 3;
			}
			switch ( modrm_mod )
			{
			case 0:
				if ( (modrm_rm & 7) != 5 )
					break;
				if (generate_relocs) {
					/* Relative to RIP of next instruction. Argh! */
					unsigned long target = insn_fetch_type(int32_t) + ptr;
					unsigned long delta = 0;
					if ( (d & SrcMask) == SrcImm )
						delta = (d & ByteOp) ? 1 :
							((op_bytes == 8) ? 4 : op_bytes);
					else if ( (d & SrcMask) == SrcImmByte )
						delta = 1;
					else if ( (b & ~1) == 0xf6 &&
						  ((modrm_reg & 7) <= 1) )
						/* Special case in Grp3: test has immediate operand. */
						delta = (d & ByteOp) ? 1
							: ((op_bytes == 8) ? 4 : op_bytes);
					else if ( (b & 0xfff7) == 0xfa4 )
						/* SHLD/SHRD with immediate byte third operand. */
						delta = 1;
					emit_reloc(ptr - 4 - init_ptr, target, 4, false);
				} else {
					ptr += 4;
				}
				break;
			case 1:
				ptr++;
				break;
			case 2:
				ptr += 4;
				break;
			}
		}
	}

	/* Immediate operands */
	switch ( d & SrcMask )
	{
	case SrcImm:
		if (d & ByteOp) {
			ptr++;
		} else if (op_bytes == 2) {
			ptr += 2;
		} else {
			ptr += 4;
		}
		break;
	case SrcImmByte:
		ptr++;
		break;
	}

	/* And now a whole bunch of special cases */
	switch ( b )
	{
	case 0x68: /* push imm{16,32,64} */
		if (op_bytes == 2)
			ptr += 2;
		else
			ptr += 4;
		break;

	case 0x6a: /* push imm8 */
	case 0xcd: /* int imm8 */
	case 0xe4: /* in imm8,%al */
	case 0xe5: /* in imm8,%eax */
	case 0xe6: /* out %al,imm8 */
	case 0xe7: /* out %eax,imm8 */
		ptr++;
		break;

	case 0xa0 ... 0xa1: /* mov mem.offs,{%al,%ax,%eax,%rax} */
	case 0xa2 ... 0xa3: /* mov {%al,%ax,%eax,%rax},mem.offs */
		ptr += 8;
		break;

	case 0xb8 ... 0xbf: /* mov imm{16,32,64},r{16,32,64} */
		if ( op_bytes == 8 ) /* Fetch more bytes to obtain imm64 */
			ptr += 4;
		break;

	case 0xc2: /* ret imm16 (near) */
	case 0xca: /* ret imm16 (far) */
		ptr += 2;
		break;

	case 0xc8: /* enter imm16,imm8 */
		ptr += 3;
		break;


	case 0xf6 ... 0xf7: /* Grp3 */
		if ( (modrm & 7) == 0 || (modrm & 7) == 1) {
			/* Special case in Grp3: test has an immediate source operand. */
			if (d & ByteOp)
				ptr++;
			else if (op_bytes == 2)
				ptr += 2;
			else 
				ptr += 4;
			break;
		}
		break;

	case 0xe8: /* call (near) */
	case 0xe9: /* jmp (near) */
	case 0x0f80 ... 0x0f8f: /* 32-bit jcc */
	{
		assert(op_bytes == 4);
		int delta = op_bytes == 4 ? insn_fetch_type(int) : insn_fetch_type(short);
		unsigned long target = ptr + delta;
		emit_reloc(ptr - 4 - init_ptr, target, 4, true);
		break;
	}
	case 0xeb: /* jmp rel 8 bit. */
		if (generate_relocs) {
			/* Can't cope with 8 bit relocs, so convert to
			 * a 32 bit jump. */
			Instruction<ThreadCfgLabel> *work = new Instruction<ThreadCfgLabel>(-1, label.label);
			int delta = insn_fetch_type(char);
			unsigned long target = ptr + delta;
			work->rip = label;
			work->len = 5;
			work->content[0] = 0xe9;
			work->relocs.push_back(
				new RipRelativeBlindRelocation<ThreadCfgLabel>(
					1, 4, target, true));
			if (true_size)
				*true_size = 2;
			return work;
		} else {
			ptr++;
		}
		break;
	case 0x70 ... 0x7f: /* jcc 8 bit */
		if (generate_relocs) {
			Instruction<ThreadCfgLabel> *work = new Instruction<ThreadCfgLabel>(-1, label.label);
			int delta = insn_fetch_type(char);
			unsigned long target = ptr + delta;
			work->rip = label;
			work->len = 6;
			work->content[0] = 0x0f;
			work->content[1] = b + 0x80 - 0x70;
			work->relocs.push_back(
				new RipRelativeBlindRelocation<ThreadCfgLabel>(
					2, 4, target, true));
			if (true_size)
				*true_size = 2;
			return work;
		} else {
			ptr++;
		}
		break;
	case 0xe0 ... 0xe3: {
		/* Can't generate correct relocs for these! */
		if (generate_relocs)
			abort();
		ptr++;
		break;
	}

	}

#undef insn_fetch_type

	/* Finished parsing, build and return result */

	Instruction<ThreadCfgLabel> *work = new Instruction<ThreadCfgLabel>(-1, label.label);
	work->rip = label;
	work->len = ptr - init_ptr;
	for (unsigned x = 0; x < work->len; x++)
		work->content[x] = as->fetch<unsigned char>(init_ptr + x, NULL);
	work->relocs = emit_reloc.r;
	if (true_size)
		*true_size = work->len;
	return work;
}

bool
CrashCfg::parse(crashEnforcementRoots &roots, AddressSpace *as,
		bool generateRelocs, const char *str, const char **suffix)
{
	if (!parseThisString("CFG:\n", str, &str))
		return false;
	const char *cursor = str;
	std::map<ThreadCfgLabel, std::pair<ThreadCfgLabel, std::vector<CfgLabel> > > content;
	while (1) {
		ThreadCfgLabel label;
		std::pair<ThreadCfgLabel, std::vector<CfgLabel> > value;
		if (!label.parse(cursor, &cursor) ||
		    !parseThisString(": ", cursor, &cursor) ||
		    !value.first.parse(cursor, &cursor) ||
		    !parseThisString(" {", cursor, &cursor))
			break;
		while (1) {
			CfgLabel target(CfgLabel::uninitialised());
			if (!target.parse(cursor, &cursor))
				break;
			parseThisString(", ", cursor, &cursor);
			value.second.push_back(target);
		}
		if (!parseThisString("}\n", cursor, &cursor))
			break;
		content[label] = value;
	}
	if (!parseThisString("Label to RIP table:\n", cursor, &cursor))
		return false;
	while (1) {
		ConcreteCfgLabel cfg;
		VexRip vr;
		if (!cfg.parse(cursor, &cursor))
			break;
		if (!parseThisString(" -> ", cursor, &cursor) ||
		    !parseVexRip(&vr, cursor, &cursor) ||
		    !parseThisChar('\n', cursor, &cursor))
			return false;
		if (rips.count(cfg))
			return false;
		rips[cfg] = vr;
	}
	
	/* Decode instructions */
	for (auto it = content.begin(); it != content.end(); it++) {
		const AbstractThread &absThread(it->second.first.thread);
		ConcreteThread concThread(roots.lookupAbsThread(absThread));
		ConcreteCfgLabel clabel(concThread.summary(), it->second.first.label);
		Instruction<ThreadCfgLabel> *instr =
			decode_instr(as, rips[clabel].unwrap_vexrip(), it->first, NULL, generateRelocs);
		assert(instr->len != 0);
		this->content[it->first] = instr;
	}
	/* Resolve successor pointers */
	for (auto it = content.begin(); it != content.end(); it++) {
		Instruction<ThreadCfgLabel> *instr = this->content[it->first];
		assert(instr != NULL);
		const AbstractThread &thread(it->first.thread);

		const std::vector<CfgLabel> &desiredSuccessors(it->second.second);
		std::vector<Instruction<ThreadCfgLabel>::successor_t> resSuccessors;
		for (auto it = desiredSuccessors.begin();
		     it != desiredSuccessors.end();
		     it++) {
			auto it3 = this->content.find(ThreadCfgLabel(thread, *it));
			if (it3 == this->content.end())
				return false;
			Instruction<ThreadCfgLabel> *desiredTarget = it3->second;
			assert(desiredTarget != NULL);
			resSuccessors.push_back(
				Instruction<ThreadCfgLabel>::successor_t::dflt(desiredTarget));
		}

		instr->successors = resSuccessors;
	}

	*suffix = cursor;
	return true;
}

void
CrashCfg::removeAllBut(const std::set<Instruction<ThreadCfgLabel> *> &retain)
{
	for (auto it = content.begin(); it != content.end(); ) {
		if (!retain.count(it->second))
			content.erase(it++);
		else
			it++;
	}
}

const VexRip &
CrashCfg::labelToRip(const ConcreteCfgLabel &l) const
{
	auto it = rips.find(l);
	assert(it != rips.end());
	return it->second;
}

void
CrashCfg::prettyPrint(FILE *f, bool verbose)
{
	fprintf(f, "\tCFG:\n");
	for (auto it = content.begin(); it != content.end(); it++) {
		auto *instr = it->second;
		fprintf(f, "\t\t%s: %s {", it->first.name(), instr->rip.name());
		bool done_one = false;
		for (auto it2 = instr->successors.begin();
		     it2 != instr->successors.end();
		     it2++) {
			if (!it2->instr)
				continue;
			if (done_one)
				fprintf(f, ", ");
			fprintf(f, "%s", it2->instr->label.name());
			done_one = true;
		}
		fprintf(f, "}");
		if (verbose) {
			fprintf(f, " [");
			for (unsigned x = 0; x < instr->len; x++) {
				if (x != 0)
					fprintf(f, " ");
				fprintf(f, "%02x", instr->content[x]);
			}
			fprintf(f, "]");
			if (instr->relocs.size() != 0) {
				fprintf(f, " relocs = [");
				for (auto it = instr->relocs.begin();
				     it != instr->relocs.end();
				     it++) {
					if (it != instr->relocs.begin())
						fprintf(f, ", ");
					if (auto rrr = dynamic_cast<RipRelativeRelocation<VexRip> *>(*it)) {
						fprintf(f, "rrr(at=%d, size=%d, target=%s, nr_imm=%d)",
							rrr->offset,
							rrr->size,
							rrr->target.name(),
							rrr->nrImmediateBytes);
					} else if (auto rrbr = dynamic_cast<RipRelativeBranchRelocation<VexRip> *>(*it)) {
						fprintf(f, "rrbr(at=%d, size=%d, target=%s)",
							rrbr->offset,
							rrbr->size,
							rrbr->target.name());
					} else {
						fprintf(f, "<bad reloc>");
					}
				}
				fprintf(f, "]");
			}
			if (instr->lateRelocs.size() != 0) {
				fprintf(f, " lateRelocs = [");
				for (auto it = instr->lateRelocs.begin();
				     it != instr->lateRelocs.end();
				     it++) {
					if (it != instr->lateRelocs.begin())
						fprintf(f, ", ");
					fprintf(f, "r(at=%d, size=%d, target=%s, nrImmediate=%d, %s)",
						(*it)->offset,
						(*it)->size,
						(*it)->target,
						(*it)->nrImmediateBytes,
						(*it)->relative ? "relative" : "absolute");
				}
				fprintf(f, "]");
			}
				
		}
		fprintf(f, "\n");
	}
	fprintf(f, "\tLabel to RIP table:\n");
	for (auto it = rips.begin(); it != rips.end(); it++)
		fprintf(f, "\t\t%s -> %s\n", it->first.name(), it->second.name());
}

CrashCfg::CrashCfg(crashEnforcementRoots &roots,
		   const SummaryId &summaryId,
		   CrashSummary *summary,
		   AddressSpace *as,
		   bool need_relocs,
		   const ThreadAbstracter &abs)
{
	std::map<SummaryId, CrashSummary *> c;
	c[summaryId] = summary;
	init(roots, c, as, need_relocs, abs);
}

CrashCfg::CrashCfg(crashEnforcementRoots &roots,
		   const std::map<SummaryId, CrashSummary *> &summaries,
		   AddressSpace *as, bool need_relocs,
		   const ThreadAbstracter &abs)
{
	init(roots, summaries, as, need_relocs, abs);
}
void
CrashCfg::init(crashEnforcementRoots &roots,
	       const std::map<SummaryId, CrashSummary *> &summaries,
	       AddressSpace *as,
	       bool need_relocs,
	       const ThreadAbstracter &abs)
{
	typedef std::pair<SummaryId, CfgLabel> slabel;
	std::map<slabel, const CFGNode *> labelToNode;

	for (auto it = summaries.begin(); it != summaries.end(); it++) {
		const SummaryId &summaryId(it->first);
		CrashSummary *summary = it->second;
		std::vector<const CFGNode *> nodesToExplore;
		for (auto it = summary->loadMachine->cfg_roots.begin();
		     it != summary->loadMachine->cfg_roots.end();
		     it++)
			nodesToExplore.push_back(it->second);
		for (auto it = summary->storeMachine->cfg_roots.begin();
		     it != summary->storeMachine->cfg_roots.end();
		     it++)
			nodesToExplore.push_back(it->second);
		while (!nodesToExplore.empty()) {
			const CFGNode *n = nodesToExplore.back();
			nodesToExplore.pop_back();
			if (labelToNode.count(slabel(summaryId, n->label))) {
				assert(labelToNode[slabel(summaryId, n->label)] == n);
				continue;
			}
			rips[ConcreteCfgLabel(summaryId, n->label)] = n->rip;
			labelToNode[slabel(summaryId, n->label)] = n;
			for (auto it = n->successors.begin(); it != n->successors.end(); it++) {
				if (it->instr)
					nodesToExplore.push_back(it->instr);
			}
		}
	}

	std::vector<ThreadCfgLabel> pending;
	for (auto it = roots.begin(); !it.finished(); it.advance())
		pending.push_back(it.get());

	while (!pending.empty()) {
		ThreadCfgLabel label(pending.back());
		pending.pop_back();
		SummaryId summary(abs.lookup(label.thread).summary_id);
		const CFGNode *node = labelToNode[slabel(summary, label.label)];
		assert(node != NULL);
		Instruction<ThreadCfgLabel> *newInstr =
			decode_instr(as, node->rip.unwrap_vexrip(), label, NULL, need_relocs);
		auto it_did_insert = content.insert(
				std::pair<ThreadCfgLabel, Instruction<ThreadCfgLabel> *>(
					label, newInstr));
		auto did_insert = it_did_insert.second;
		if (did_insert) {
			for (auto it = node->successors.begin();
			     it != node->successors.end();
			     it++) {
				if (it->instr)
					pending.push_back(ThreadCfgLabel(label.thread, it->instr->label));
			}
		}
	}

	for (auto it = content.begin(); it != content.end(); it++) {
		Instruction<ThreadCfgLabel> *instr = it->second;
		SummaryId summary(abs.lookup(instr->rip.thread).summary_id);
		const CFGNode *old = labelToNode[slabel(summary, instr->rip.label)];
		for (auto it = old->successors.begin();
		     it != old->successors.end();
		     it++) {
			const CFGNode::successor_t &srcSucc(*it);
			if (!srcSucc.instr)
				continue;
			ThreadCfgLabel succLabel(instr->rip.thread, srcSucc.instr->label);
			assert(content.count(succLabel));
			Instruction<ThreadCfgLabel>::successor_t destSucc(
				srcSucc.type,
				succLabel,
				content[succLabel],
				srcSucc.calledFunction);
			instr->successors.push_back(destSucc);
		}
		for (auto it2 = instr->relocs.begin();
		     it2 != instr->relocs.end();
		     it2++) {
			RipRelativeBlindRelocation<ThreadCfgLabel> *reloc =
				dynamic_cast<RipRelativeBlindRelocation<ThreadCfgLabel> *>(*it2);
			assert(reloc);
			Instruction<ThreadCfgLabel> *targetInstr = NULL;
			for (auto it3 = instr->successors.begin(); it3 != instr->successors.end(); it3++) {
				Instruction<ThreadCfgLabel>::successor_t &succ(*it3);
				VexRip succRip(labelToRip(ConcreteCfgLabel(roots.lookupAbsThread(succ.rip.thread).summary_id, succ.rip.label)));
				if (succRip.unwrap_vexrip() == reloc->target) {
					targetInstr = succ.instr;
					break;
				}
			}
			if (targetInstr) {
				*it2 = new RipRelativeBranchRelocation<ThreadCfgLabel>(
					reloc->offset,
					reloc->size,
					targetInstr->rip);
			}
		}
	}
}
