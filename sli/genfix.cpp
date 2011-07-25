#include <map>
#include <set>

#include "sli.h"
#include "genfix.hpp"
#include "oracle.hpp"
#include "inferred_information.hpp"

typedef unsigned char Byte;

class PatchFragment;

/* There are two types of relocation, early and late.  Early
   relocations are done statically while building the patch.  Late
   relocations are done afterwards, when the patch is loaded. */
class EarlyRelocation : public GarbageCollected<EarlyRelocation> {
public:
	unsigned offset;
	unsigned size;
	EarlyRelocation(unsigned _offset, unsigned _size)
		: offset(_offset), size(_size) {}
	virtual void doit(PatchFragment *pf) = 0;
	void visit(HeapVisitor &hv) {}
	void destruct() {}
	NAMED_CLASS
};

static LateRelocation
late_relocation(unsigned offset, unsigned size,
		const char *target, unsigned nrImmediateBytes,
		bool relative)
{
	return vex_asprintf("{%d, %d, %d, %d, %s}",
			    offset, size,
			    relative ? -nrImmediateBytes - size : 0,
			    relative, target);
}

void
Instruction::emit(Byte b)
{
	assert(len < MAX_INSTRUCTION_SIZE);
	content[len] = b;
	len++;
}

Byte
Instruction::byte()
{
	unsigned long t;
	t = 0;
	as->readMemory(rip + len, 1, &t, false, NULL);
	Byte b = t;
	emit(b);
	return b;
}

int
Instruction::int32()
{
	unsigned long t[4];
	as->readMemory(rip + len, 4, t, false, NULL);
	emit(t[0]);
	emit(t[1]);
	emit(t[2]);
	emit(t[3]);
	return t[0] | (t[1] << 8) | (t[2] << 16) | (t[3] << 24);
}

void
Instruction::immediate(unsigned size)
{
	for (unsigned x = 0; x < size; x++)
		byte();
}

int
Instruction::modrmExtension(void)
{
	Byte b = byte();
	len--;
	return (b >> 3) & 7;
}

class RipRelativeRelocation : public EarlyRelocation {
	unsigned long target;
	unsigned nrImmediateBytes;
public:
	void doit(PatchFragment *pf);

	RipRelativeRelocation(unsigned _offset,
			      unsigned _size,
			      unsigned long _target,
			      unsigned _nrImmediateBytes)
		: EarlyRelocation(_offset, _size),
		  target(_target),
		  nrImmediateBytes(_nrImmediateBytes)
	{
	}
};

class RipRelativeBranchRelocation : public EarlyRelocation {
	unsigned long target;
public:
	void doit(PatchFragment *pf);
	RipRelativeBranchRelocation(unsigned _offset,
				    unsigned _size,
				    unsigned long _target)
		: EarlyRelocation(_offset, _size),
		  target(_target)
	{
	}
};

void
Instruction::modrm(unsigned nrImmediates)
{
	Byte modrm = byte();
	unsigned rm = modrm & 7;
	unsigned mod = modrm >> 6;

	if (mod == 3) {
		/* No further data */
		return;
	}
	if (mod == 0 && rm == 5) {
		/* RIP-relative mode.  The one-byte modrm is followed
		   by four bytes of signed displacement, plus
		   immediates if appropriate. */
		immediate(4);
		int delta = *(int *)(content + len - 4);
		relocs.push_back(new RipRelativeRelocation(len - 4,
							   4,
							   delta + rip + len + nrImmediates,
							   nrImmediates));
		return;
	}
	unsigned dispBytes;
	dispBytes = 0;
	if (rm == 4) {
		/* SIB byte */
		Byte sib = byte();
		if ((sib & 7) == 5)
			dispBytes = 4;
	}
	if (mod == 1)
		dispBytes = 1;
	else if (mod == 2)
		dispBytes = 4;
	immediate(dispBytes);
}

Instruction *
Instruction::pseudo(unsigned long rip)
{
	Instruction *i = new Instruction();
	i->rip = rip;
	return i;
}

Instruction *
Instruction::decode(AddressSpace *as,
		    unsigned long start,
		    CFG *cfg)
{
	Instruction *i = new Instruction();
	i->rip = start;
	i->as = as;
	Byte b;
	while (1) {
		b = i->byte();
		if (b < 0x40 || b > 0x4f)
			break;
		i->pfx.rexByte(b);
		i->nr_prefixes++;
	}
	bool fallsThrough = true;
	char delta;
	int delta32;

top:
	switch (b) {
	case 0x00 ... 0x3f:
		if (b != 0x0f) {
			switch (b & 7) {
			case 0 ... 3:
				i->modrm(0);
				break;
			case 4:
				i->immediate(1);
				break;
			case 5:
				i->immediate(4);
				break;
			case 6:
				b = i->byte();
				goto top;
			case 7:
				/* Not allowed in 64-bit mode */
				fail("Instruction %02x is not allowed in 64 bit code\n",
				     b);
			}
			break;
		}
		/* Two-byte instructions */
		b = i->byte();
		switch (b) {
		case 0x80 ... 0x8f: /* 32 bit conditional jumps. */
			delta32 = i->int32();
			i->branchNext = i->rip + i->len + delta32;
			i->relocs.push_back(new RipRelativeBranchRelocation(i->len - 4, 4, i->branchNext));
			/* Unlike 8 bit jumps, we don't need to set
			   fallsThrough here, because the normal
			   defaultNext calculation will do the right
			   thing, because the output instruction is
			   the same size as the input one. */
			break;

		case 0x40 ... 0x4f: /* CMOVcc Gv,Ev */
		case 0x90 ... 0x9f: /* setcc Eb */
		case 0xaf: /* imul Gv, Ev */
		case 0xb6: /* movzx Gv, Eb */
		case 0xb7: /* movzw Gv, Ew */
			i->modrm(0);
			break;
		default:
			throw NotImplementedException("cannot decode instruction starting 0x0f 0x%02x at %lx\n",
						      b, i->rip);
		}
		break;

	case 0x40 ... 0x5f:
		break;

	case 0x64: /* FS prefix.  Pass it through verbatim. */
		b = i->byte();
		goto top;

	case 0x70 ... 0x7f:
		/* 8 bit conditional jumps are handled specially, by
		   turning them into 32 conditional jumps, because
		   that simplifies a lot of relocation-related
		   stuff. */
		/* Decode the instruction... */
		delta = i->byte();
		i->branchNext = i->rip + i->len + delta;
		i->defaultNext = i->rip + i->len;

		/* Now rewind and emit the 32 bit version. */
		i->len = 0;
		i->emit(0x0f);
		i->emit(b + 0x10);
		i->relocs.push_back(new RipRelativeBranchRelocation(i->len, 4, i->branchNext));
		i->len += 4;

		/* Don't let the tail update defaultNext */
		fallsThrough = false;
		break;

	case 0x80:
	case 0x82:
	case 0x83:
		i->modrm(1);
		i->immediate(1);
		break;
	case 0x81:
		i->modrm(4);
		i->immediate(4);
		break;

	case 0x84 ... 0x8e:
		i->modrm(0);
		break;

	case 0x90 ... 0x9f:
		break;

	case 0xb0 ... 0xb7:
		i->immediate(1);
		break;
	case 0xb8 ... 0xbf:
		if (i->pfx.rex_w) {
			i->immediate(8);
		} else {
			i->immediate(4);
		}
		break;
	case 0xc0:
	case 0xc1: /* Shift group 2 with an Ib */
		i->modrm(1);
		i->immediate(1);
		break;

	case 0xc3:
		fallsThrough = false;
		break;
	case 0xc6:
		i->modrm(1);
		i->immediate(1);
		break;
	case 0xc7:
		i->modrm(4);
		i->immediate(4);
		break;
	case 0xcc:
		/* Really int3, but we treat it as a no-op because
		   it's used in our infrastructure for triggering
		   bugs. */
		break;
	case 0xc9:
		break;
	case 0xd0 ... 0xd3: /* Shift group 2*/
		i->modrm(0);
		break;
	case 0xe8: { /* Call instruction. */
		i->immediate(4);
		/* We don't emit epilogues for the target of a call
		   instruction, because we assume that we'll come back
		   here as soon as the call is done. */
		/* XXX this is unsafe: we have no idea what the call
		   does, so can't just assume that it'll cope without
		   an epilogue. XXX */
		int delta = *(int *)(i->content + i->len - 4);
		unsigned long target = i->rip + i->len + delta;
		i->relocs.push_back(new RipRelativeRelocation(i->len - 4,
							      4,
							      target,
							      0));
		if (cfg->exploreFunction(target))
			i->branchNext = target;
		break;
	}
	case 0xeb: /* jmp rel8 */
		delta = i->byte();
		i->defaultNext = i->rip + i->len + delta;

		/* Don't emit this instruction at all; if it's useful,
		 * we'll synthesise an appropriate jump later on.
		 * Otherwise, we'll eliminate it with jump
		 * threading. */
		i->len = 0;

		/* Don't let the tail update defaultNext */
		fallsThrough = false;
		break;

	case 0xe9: /* jmp rel32 */
		delta32 = i->int32();
		i->defaultNext = i->rip + i->len + delta32;
		i->len = 0;
		fallsThrough = false;
		break;

	case 0xf7: /* Unary group 3 Ev */
		if (i->modrmExtension() == 0) {
			i->modrm(4);
			i->immediate(4);
		} else {
			i->modrm(0);
		}
		break;

	case 0xff:
		i->modrm(0);
		break;
	default:
		throw NotImplementedException("cannot decode instruction starting %x at %lx\n",
					      b, i->rip);
	}

	if (fallsThrough)
		i->defaultNext = i->rip + i->len;

	return i;
}

void
CFG::decodeInstruction(unsigned long rip, unsigned max_depth)
{
	if (!max_depth)
		return;
	Instruction *i = Instruction::decode(as, rip, this);
	if (!i)
		return;
	assert(i->rip == rip);
	registerInstruction(i);
	if (exploreInstruction(i)) {
		if (i->branchNext)
			pendingRips.push_back(std::pair<unsigned long, unsigned>(
						      i->branchNext, max_depth - 1));
		if (i->defaultNext)
			pendingRips.push_back(std::pair<unsigned long, unsigned>(
						      i->defaultNext, max_depth - 1));
	}
}

void
CFG::doit()
{
	while (!pendingRips.empty()) {
		std::pair<unsigned long, unsigned> p = pendingRips.back();
		pendingRips.pop_back();
		if (!ripToInstr->hasKey(p.first))
			decodeInstruction(p.first, p.second);
	}

	for (ripToInstrT::iterator it = ripToInstr->begin();
	     it != ripToInstr->end();
	     it++) {
		Instruction *ins = it.value();
		ins->useful = instructionUseful(ins);
		if (ins->defaultNext && ripToInstr->hasKey(ins->defaultNext)) {
			Instruction *dn = (*ripToInstr)[ins->defaultNext];
			ins->defaultNext = 0;
			ins->defaultNextI = dn;
			if (dn->useful)
				ins->useful = true;
		}
		if (ins->branchNext && ripToInstr->hasKey(ins->branchNext)) {
			Instruction *bn = (*ripToInstr)[ins->branchNext];
			ins->branchNext = 0;
			ins->branchNextI = bn;
			if (bn->useful)
				bn->useful = true;
		}
	}

	bool progress;
	do {
		progress = false;
		for (ripToInstrT::iterator it = ripToInstr->begin();
		     it != ripToInstr->end();
		     it++) {
			Instruction *i = it.value();
			if (i->useful)
				continue;
			if (i->defaultNextI && i->defaultNextI->useful) {
				i->useful = true;
				progress = true;
			}
			if (i->branchNextI && i->branchNextI->useful) {
				i->useful = true;
				progress = true;
			}
		}
	} while (progress);

	/* Rewrite every instruction so that non-useful next
	   instructions get turned back into RIPs, and remove the
	   non-useful instructions. */
	for (ripToInstrT::iterator it = ripToInstr->begin();
	     it != ripToInstr->end();
		) {
		Instruction *i = it.value();

		if (i->useful) {
			if (i->defaultNextI && !i->defaultNextI->useful) {
				i->defaultNext = i->defaultNextI->rip;
				i->defaultNextI = NULL;
			}
			if (i->branchNextI && !i->branchNextI->useful) {
				i->branchNext = i->branchNextI->rip;
				i->branchNextI = NULL;
			}
			it++;
		} else {
			it = ripToInstr->erase(it);
		}
	}
}

void
RipRelativeRelocation::doit(PatchFragment *pf)
{
	unsigned targetOffset;
	if (pf->ripToOffset(target, &targetOffset)) {
		long delta = targetOffset - offset - nrImmediateBytes - size;
		pf->writeBytes(&delta, size, offset);
	} else {
		pf->addLateReloc(late_relocation(offset, size,
						 vex_asprintf("0x%lx",target),
						 nrImmediateBytes, true));
	}
}

void
RipRelativeBranchRelocation::doit(PatchFragment *pf)
{
	unsigned targetOffset;
	if (!pf->ripToOffset(target, &targetOffset))
		pf->generateEpilogue(target);
	if (!pf->ripToOffset(target, &targetOffset))
		fail("Failed to generate epilogue for %lx\n", target);
	int delta = targetOffset - offset - size;
	pf->writeBytes(&delta, size, offset);
}

Instruction *
PatchFragment::nextInstr(CFG *cfg)
{
	/* Decide what to emit next */
	std::map<Instruction *, bool> pendingInstructions;
	for (CFG::ripToInstrT::iterator it = cfg->ripToInstr->begin();
	     it != cfg->ripToInstr->end();
	     it++) {
		if (!it.value()->presentInPatch)
			pendingInstructions[it.value()] = true;
	}
	if (pendingInstructions.empty())
		return NULL;

	/* Pick something which isn't the default next instruction for
	   some other instruction, so as to avoid introducing extra
	   jumps.  There should always be such an instruction, because
	   otherwise we must have a cycle in the default next chain,
	   which is impossible. */
	for (std::map<Instruction *, bool>::iterator it = pendingInstructions.begin();
	     it != pendingInstructions.end();
	     it++) {
		if (it->first->defaultNextI)
			pendingInstructions[it->first->defaultNextI] = false;
	}
	for (std::map<Instruction *, bool>::iterator it = pendingInstructions.begin();
	     it != pendingInstructions.end();
	     it++)
		if (it->second)
			return it->first;

	/* Yurk.  Everything is part of a cycle.  Just pick the
	 * instruction with the numerically smallest address. */
	std::set<std::pair<unsigned long, Instruction *> > instrs;
	for (std::map<Instruction *, bool>::iterator it = pendingInstructions.begin();
	     it != pendingInstructions.end();
	     it++)
		instrs.insert(std::pair<unsigned long, Instruction *>(it->first->rip, it->first));
	/* The set will sort on the first item in the pair, so this
	   gives us the first instruction. */
	assert(instrs.begin() != instrs.end());
	return instrs.begin()->second;
}

bool
PatchFragment::ripToOffset(unsigned long rip, unsigned *res)
{
	*res = 0;
	if (!cfg->ripToInstr->hasKey(rip))
		return false;
	Instruction *i = (*cfg->ripToInstr)[rip];
	if (!i->presentInPatch)
		return false;
	*res = i->offsetInPatch;
	return true;
}

void
PatchFragment::writeBytes(const void *_bytes, unsigned size, unsigned offset)
{
	const Byte *bytes = (const Byte *)_bytes;
	for (unsigned x = 0; x < size; x++)
		content[offset + x] = bytes[x];
}

void
PatchFragment::fromCFG(CFG *_cfg)
{
	cfg = _cfg;
	while (1) {
		Instruction *i = nextInstr(cfg);
		if (!i)
			break;
		emitStraightLine(i);
	}

	while (!relocs.empty()) {
		EarlyRelocation *r = relocs.back();
		relocs.pop_back();
		assert(r);
		assert(r->offset + r->size <= content.size());

		r->doit(this);
	}
}

void
PatchFragment::emitInstruction(Instruction *i)
{
	unsigned offset = content.size();
	for (unsigned x = 0; x < i->len; x++)
		content.push_back(i->content[x]);
	for (std::vector<EarlyRelocation *>::iterator it = i->relocs.begin();
	     it != i->relocs.end();
	     it++) {
		(*it)->offset += offset;
		relocs.push_back(*it);
	}
}

void
PatchFragment::emitJmpToOffset(unsigned target_offset)
{
	unsigned starting_offset = content.size();
	content.push_back(0xe9);
	union {
		int delta_word;
		Byte delta_bytes[4];
	};
	delta_word = target_offset - starting_offset - 5;
	for (unsigned x = 0; x < 4; x++)
		content.push_back(delta_bytes[x]);
}

void
PatchFragment::emitJmpToRipClient(unsigned long rip)
{
	emitJmpToOffset(0);
	relocs.push_back(new RipRelativeBranchRelocation(content.size() - 4, 4, rip));
}

void
PatchFragment::emitJmpToRipHost(unsigned long rip)
{
	emitJmpToOffset(0);
	lateRelocs.push_back(late_relocation(content.size() - 4, 4,
					     vex_asprintf("0x%lx", rip),
					     0,
					     true));
}

void
PatchFragment::skipRedZone()
{
	/* lea -128(%rsp), %rsp */
	content.push_back(0x48);
	content.push_back(0x8d);
	content.push_back(0x64);
	content.push_back(0x24);
	content.push_back(0x80);
}

void
PatchFragment::restoreRedZone()
{
	/* lea 128(%rsp), %rsp */
	content.push_back(0x48);
	content.push_back(0x8d);
	content.push_back(0xa4);
	content.push_back(0x24);
	content.push_back(0x80);
	content.push_back(0x00);
	content.push_back(0x00);
	content.push_back(0x00);
}

void
PatchFragment::emitPushQ(unsigned reg)
{
	if (reg >= 8) {
		content.push_back(0x41);
		reg -= 8;
	}
	assert(reg < 8);
	content.push_back(0x50 + reg);
}

void
PatchFragment::emitPopQ(unsigned reg)
{
	if (reg >= 8) {
		content.push_back(0x41);
		reg -= 8;
	}
	assert(reg < 8);
	content.push_back(0x58 + reg);
}

void
PatchFragment::emitMovQ(unsigned reg, unsigned long val)
{
	if (reg < 8) {
		content.push_back(0x48);
	} else {
		content.push_back(0x49);
		reg -= 8;
	}
	assert(reg < 8);
	content.push_back(0xb8 + reg);
	union {
		unsigned long asLong;
		Byte asBytes[8];
	};
	asLong = val;
	for (unsigned x = 0; x < 8; x++)
		content.push_back(asBytes[x]);
}

void
PatchFragment::emitCallReg(unsigned reg)
{
	if (reg >= 8) {
		content.push_back(0x41);
		reg -= 8;
	}
	content.push_back(0xff);
	content.push_back(0xd0 + reg);
}

static char *
vg_strdup(const char *s)
{
	return vex_asprintf("%s", s);
}

void
PatchFragment::emitCallSequence(const char *target, bool allowRedirection)
{
	skipRedZone();

	emitPushQ(6);
	emitMovQ(6, 0);
	lateRelocs.push_back(late_relocation(content.size() - 8,
					     8,
					     vg_strdup(target),
					     0,
					     false));
	emitCallReg(6);
	emitPopQ(6);
	
	restoreRedZone();
}

void
PatchFragment::emitStraightLine(Instruction *i)
{
	assert(i);
	while (1) {
		unsigned offset = content.size();

		if (i->presentInPatch) {
			/* This instruction has already been emitted.
			   Rather than duplicating it, emit an
			   unconditional branch to the existing
			   location. */
			emitJmpToOffset(i->offsetInPatch);

			/* Don't try to reassemble any further. */
/**/			return;
		}

		registerInstruction(i, offset);

		emitInstruction(i);
			
		if (!i->defaultNextI) {
			/* Hit end of block, and don't want to go any
			 * further.  Return to the original code. */
			if (i->defaultNext) {
				emitJmpToRipClient(i->defaultNext);
			} else {
				/* Last instruction in the block was
				   an unpredictable branch, which
				   we'll just have emitted verbatim,
				   so we don't need to do any more. */
			}
			return;
		}

		i = i->defaultNextI;
	}
}

char *
PatchFragment::asC(const char *ident, char **relocs_name, char **trans_name, char **content_name) const
{
	char *content_buf = (char *)LibVEX_Alloc_Bytes(content.size() * 4 + 1);
	for (unsigned x = 0; x < content.size(); x++)
		sprintf(content_buf + x * 4, "\\x%02x", content[x]);
	*relocs_name = vex_asprintf("__%s_reloc", ident);
	*content_name = vex_asprintf("__%s_patch_content", ident);
	char *content = vex_asprintf("static const unsigned char %s[] = \"%s\";\n\n"
				     "static const struct relocation %s[] = {\n",
				     *content_name,
				     content_buf,
				     *relocs_name);
	for (std::vector<LateRelocation>::const_iterator it = lateRelocs.begin();
	     it != lateRelocs.end();
	     it++)
		content = vex_asprintf("%s\t%s,\n",
				       content, *it);

	*trans_name = vex_asprintf("__%s__trans_table", ident);
	content = vex_asprintf("%s};\n\nstatic const struct trans_table_entry %s[] = {\n",
			       content, *trans_name);
	for (std::vector<Instruction *>::const_iterator it = registeredInstrs.begin();
	     it != registeredInstrs.end();
	     it++)
		content = vex_asprintf("%s\t{0x%lx, %d},\n",
				       content,
				       (*it)->rip,
				       (*it)->offsetInPatch);
	return vex_asprintf("%s};\n", content);
}

void
PatchFragment::generateEpilogue(unsigned long exitRip)
{
	Instruction *i = Instruction::pseudo(exitRip);
	cfg->registerInstruction(i);
	registerInstruction(i, content.size());
	emitJmpToRipHost(exitRip);
}

class DcdCFG : public CFG {
	std::set<unsigned long> &neededInstructions;
public:
	bool instructionUseful(Instruction *i) { return neededInstructions.count(i->rip) != 0; }
	DcdCFG(AddressSpace *as, std::set<unsigned long> &ni)
		: CFG(as), neededInstructions(ni)
	{}
};

static void
add_array_summary(std::vector<const char *> &out,
		  const char *t_ptr,
		  const char *nr_entries,
		  const char *table)
{
	out.push_back(
		vex_asprintf(
			"\t.%s = %s, .%s = sizeof(%s)/sizeof(%s[0]),\n",
			t_ptr,
			table,
			nr_entries,
			table,
			table));
}

char *
buildPatchForCrashSummary(Oracle *oracle, CrashSummary *summary, const char *ident)
{
	VexPtr<AddressSpace> as(oracle->ms->addressSpace);

	/* What instructions do we need to cover? */
	std::set<unsigned long> neededInstructions;
	summary->loadMachine->root->enumerateMentionedMemoryAccesses(neededInstructions);
	/* 5 bytes is the size of a 32-bit relative jump. */
	unsigned long root = oracle->dominator(neededInstructions, as, 5);
	if (!root) {
		fprintf(_logfile, "Patch generation fails because we can't find an appropriate dominating instruction for load machine.\n");
		return NULL;
	}
	for (std::vector<CrashSummary::StoreMachineData *>::iterator it = summary->storeMachines.begin();
	     it != summary->storeMachines.end();
	     it++)
		(*it)->machine->root->enumerateMentionedMemoryAccesses(neededInstructions);

	DcdCFG *cfg = new DcdCFG(as, neededInstructions);

	std::vector<unsigned long> roots;
	/* What are the entry points of the patch? */
	cfg->add_root(root, 100);
	roots.push_back(root);
	for (std::vector<CrashSummary::StoreMachineData *>::iterator it = summary->storeMachines.begin();
	     it != summary->storeMachines.end();
	     it++) {
		std::set<unsigned long> instrs;
		(*it)->machine->root->enumerateMentionedMemoryAccesses(instrs);
		unsigned long r = oracle->dominator(instrs, as, 5);
		if (!r) {
			fprintf(_logfile, "Patch generation fails because we can't find an appropriate dominator instruction for one of the store machines.\n");
			return NULL;
		}
		cfg->add_root(r, 100);
		roots.push_back(r);
	}
	try {
		cfg->doit();
	} catch (NotImplementedException &e) {
		/* This means that there's some instruction we can't
		   decode.  Dump a diagnostic and just continue on. */
		fprintf(_logfile,
			"Cannot build patch for crash summary.  Instruction decoder said %s\n",
			e.what());
		return NULL;
	}
	PatchFragment *pf = new PatchFragment();
	pf->fromCFG(cfg);

	std::vector<const char *> fragments;
	char *relocs_name;
	char *trans_name;
	char *content_name;
	char *entry_table_name;
	fragments.push_back(pf->asC(ident, &relocs_name, &trans_name, &content_name));
	entry_table_name = vex_asprintf("__%s_entry_points", ident);
	fragments.push_back("static unsigned long ");
	fragments.push_back(entry_table_name);
	fragments.push_back("[] = {\n");
	for (unsigned x = 0; x < roots.size(); x++)
		fragments.push_back(vex_asprintf("\t0x%lx,\n", roots[x]));
	fragments.push_back("};\n\nstatic struct patch ");
	fragments.push_back(ident);
	fragments.push_back(" = {\n");

	add_array_summary(fragments, "relocations", "nr_relocations", relocs_name);
	add_array_summary(fragments, "trans_table", "nr_translations", trans_name);
	add_array_summary(fragments, "entry_points", "nr_entry_points", entry_table_name);
	add_array_summary(fragments, "content", "content_size", content_name);
	fragments.push_back("};\n");

	size_t sz = 1;
	for (unsigned x = 0; x < fragments.size(); x++)
		sz += strlen(fragments[x]);
	char *res = (char *)LibVEX_Alloc_Bytes(sz);
	char *cursor = res;
	for (unsigned x = 0; x < fragments.size(); x++) {
		memcpy(cursor, fragments[x], strlen(fragments[x]));
		cursor += strlen(fragments[x]);
	}
	*cursor = 0;
	assert(cursor == res + sz-1);
	return res;
}
