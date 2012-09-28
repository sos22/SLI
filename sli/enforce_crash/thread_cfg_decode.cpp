#include "sli.h"
#include "enforce_crash.hpp"

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
	fprintf(f, "Label to RIP table:\n");
	for (auto it = rips.begin(); it != rips.end(); it++)
		fprintf(f, "\t%s -> %s\n", it->first.name(), it->second.name());
}

#include "x86_opcodes.c"

/* Cut-down version of x86_emulate which just does enough to find the
 * size of the instruction. */
static Instruction<ThreadCfgLabel> *
decode_instr(AddressSpace *as, unsigned long ptr, const ThreadCfgLabel &label)
{
	const unsigned long init_ptr = ptr;
	uint16_t b;
	uint8_t d, rex_prefix = 0;
	uint8_t modrm = 0;
	unsigned int op_bytes;
	
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
				ptr += 4;
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
	case 0xe8: /* call (near) */
	case 0xe9: /* jmp (near) */
	case 0x0f80 ... 0x0f8f: /* jcc (near) */
		if (op_bytes == 2)
			ptr += 2;
		else
			ptr += 4;
		break;

	case 0x6a: /* push imm8 */
	case 0x70 ... 0x7f: /* jcc (short) */
	case 0xcd: /* int imm8 */
	case 0xe0 ... 0xe2: /* loop{,z,nz} */
	case 0xe3: /* jcxz/jecxz (short) */
	case 0xe4: /* in imm8,%al */
	case 0xe5: /* in imm8,%eax */
	case 0xe6: /* out %al,imm8 */
	case 0xe7: /* out %eax,imm8 */
	case 0xeb: /* jmp (short) */
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
	}

#undef insn_fetch_type

	/* Finished parsing, build and return result */

	Instruction<ThreadCfgLabel> *work = new Instruction<ThreadCfgLabel>(-1, label.label);
	work->rip = label;
	work->len = ptr - init_ptr;
	for (unsigned x = 0; x < work->len; x++)
		work->content[x] = as->fetch<unsigned char>(init_ptr + x, NULL);
	return work;
}

bool
CrashCfg::parse(AddressSpace *as, const char *str, const char **suffix)
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
		CfgLabel cfg(CfgLabel::uninitialised());
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
		assert(rips.count(it->second.first.label));
		Instruction<ThreadCfgLabel> *instr =
			decode_instr(as, rips[it->second.first.label].unwrap_vexrip(), it->first);
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

Instruction<ThreadCfgLabel> *
ThreadAbstracter::instr_iterator::get() const
{
	return cfg.findInstr(underlying.get());
}

const VexRip &
CrashCfg::labelToRip(const CfgLabel &l) const
{
	auto it = rips.find(l);
	assert(it != rips.end());
	return it->second;
}

CrashCfg::CrashCfg(crashEnforcementRoots &roots, CrashSummary *summary, AddressSpace *as)
{
	std::map<CfgLabel, const CFGNode *> labelToNode;

	{
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
			if (labelToNode.count(n->label)) {
				assert(labelToNode[n->label] == n);
				assert(rips.count(n->label));
				continue;
			}
			rips[n->label] = n->rip;
			labelToNode[n->label] = n;
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
		const CFGNode *node = labelToNode[label.label];
		assert(node != NULL);
		Instruction<ThreadCfgLabel> *newInstr =
			decode_instr(as, node->rip.unwrap_vexrip(), label);
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
		const CFGNode *old = labelToNode[instr->rip.label];
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
	}
}

predecessorMapT::predecessorMapT(CrashCfg &cfg)
{
	for (auto it = cfg.begin(); !it.finished(); it.advance()) {
		auto v = it.instr();
		if (!count(v))
			(*this)[v];
		for (auto it2 = v->successors.begin(); it2 != v->successors.end(); it2++)
			if (it2->instr)
				(*this)[it2->instr].insert(v);
	}
}

happensBeforeEdge *
happensBeforeEdge::parse(CrashCfg &cfg, const char *str, const char **suffix)
{
	ThreadCfgLabel before;
	ThreadCfgLabel after;
	unsigned msg_id;
	if (!parseDecimalUInt(&msg_id, str, &str) ||
	    !parseThisString(": ", str, &str) ||
	    !before.parse(str, &str) ||
	    !parseThisString(" <-< ", str, &str) ||
	    !after.parse(str, &str) ||
	    !parseThisString(" {", str, &str))
		return NULL;
	std::vector<IRExprGet *> content;
	while (1) {
		IRExpr *a;
		if (!parseIRExpr(&a, str, &str))
			break;
		if (!parseThisString(", ", str, &str))
			return NULL;
		if (a->tag != Iex_Get)
			return NULL;
		content.push_back((IRExprGet *)a);
	}
	if (!parseThisChar('}', str, &str))
		return NULL;
	*suffix = str;
	return new happensBeforeEdge(cfg.findInstr(before), cfg.findInstr(after), content, msg_id);
}
