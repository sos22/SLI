#include <sys/types.h>
#include <sys/fcntl.h>
#include <err.h>
#include <errno.h>
#include <unistd.h>
#include <wait.h>

#include <map>

#include "sli.h"

#define MAX_INSTRUCTION_SIZE 15

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

typedef char *LateRelocation;

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

class Prefixes {
public:
	bool rex_w, rex_r, rex_x, rex_b;
	Prefixes() : rex_w(false),
		     rex_r(false),
		     rex_x(false),
		     rex_b(false)
	{
	}
	void rexByte(Byte b) {
		assert(b >= 0x40);
		assert(b < 0x50);
		rex_b = !!(b & 1);
		rex_x = !!(b & 2);
		rex_r = !!(b & 4);
		rex_w = !!(b & 8);
	}
};

class CFG;

class Instruction : public GarbageCollected<Instruction > {
	Byte byte();
	void emit(Byte);
	void modrm(unsigned nrImmediates);
	void immediate(unsigned size);
public:
	unsigned long rip;

	unsigned long defaultNext;
	Instruction *defaultNextI;
	unsigned long branchNext;
	Instruction *branchNextI;

	/* Doesn't really belong here, but it'll do for now. */
	unsigned offsetInPatch;
	bool presentInPatch;

	Byte content[MAX_INSTRUCTION_SIZE];
	unsigned len;
	Prefixes pfx;
	unsigned nr_prefixes;
	std::vector<EarlyRelocation *> relocs;

	AddressSpace<unsigned long> *as;

	bool useful;

	static Instruction *decode(AddressSpace<unsigned long> *as,
				   unsigned long rip,
				   CFG *cfg);
	static Instruction *pseudo(unsigned long rip);

	void visit(HeapVisitor &hv) {
		visit_container(relocs, hv);
		hv(as);
		hv(defaultNextI);
		hv(branchNextI);
	}
	void destruct() { this->~Instruction(); }
	NAMED_CLASS
};

class CFG : public GarbageCollected<CFG> {
	AddressSpace<unsigned long> *as;
public:
	static unsigned long __trivial_hash_function(const unsigned long &k) { return k; }
	typedef gc_map<unsigned long, Instruction *, __trivial_hash_function,
		       __default_eq_function, __visit_function_heap> ripToInstrT;
	ripToInstrT *ripToInstr;
private:
	std::vector<std::pair<unsigned long, unsigned> > pendingRips;
	std::vector<unsigned long> neededRips;
	void decodeInstruction(unsigned long rip, unsigned max_depth);
public:
	CFG(AddressSpace<unsigned long> *_as) : as(_as), ripToInstr(new ripToInstrT()) {}
	void add_root(unsigned long root, unsigned max_depth)
	{
		pendingRips.push_back(std::pair<unsigned long, unsigned>(root, max_depth));
	}
	void doit();
	void visit(HeapVisitor &hv) {
		hv(ripToInstr);
		hv(as);
	}
	void registerInstruction(Instruction *i) { (*ripToInstr)[i->rip] = i; }
	virtual void destruct() { this->~CFG(); }
	NAMED_CLASS

	/* These can be overriden by derived classes to change the
	 * behaviour a bit. */

	/* Should we bother to explore instructions which follow this
	 * one?  If this returns true, direct followers of this
	 * instruction will be explored; indirect ones will not be
	 * (i.e. we only consider branches whose target is statically
	 * constant). */
	virtual bool exploreInstruction(Instruction *i) { return true; }
	/* We've discovered a direct-called function.  Should we
	 * explore the callee?  Indirect calls are never explored. */
	virtual bool exploreFunction(unsigned long rip) { return false; }
	/* Is this instruction useful?  Once the CFG is built, we do a
	 * post-pass which walks the list of instructions, and uses
	 * this to decide whether instructions are useful.  We then
	 * walk backwards through the CFG and mark any instruction
	 * which can reach a useful instruction as being useful
	 * itself.  Finally, any non-useful instructions are replaced
	 * with branches back into the original code.
	 */
	virtual bool instructionUseful(Instruction *i) { return true; }
};

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

void
Instruction::immediate(unsigned size)
{
	for (unsigned x = 0; x < size; x++)
		byte();
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
	if (rm == 4) {
		/* SIB byte */
		byte();
	}
	unsigned dispBytes;
	if (mod == 0)
		dispBytes = 0;
	else if (mod == 1)
		dispBytes = 1;
	else
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
Instruction::decode(AddressSpace<unsigned long> *as,
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

	switch (b) {
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
/**/		return i;
	case 0x83:
		i->modrm(1);
		i->immediate(1);
		break;
	case 0x85:
	case 0x89:
	case 0x8b:
		i->modrm(0);
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
	case 0xc3:
		fallsThrough = false;
		break;
	case 0xc7:
		i->modrm(4);
		i->immediate(4);
		break;
	case 0xc9:
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


class PatchFragment : public GarbageCollected<PatchFragment> {
	std::vector<EarlyRelocation *> relocs;
	std::vector<LateRelocation> lateRelocs;
	std::vector<Instruction *> registeredInstrs;

protected:
	CFG *cfg;
	std::vector<Byte> content;

private:
	Instruction *nextInstr(CFG *cfg);
	void emitStraightLine(Instruction *i);

protected:
	/* Emit a jump to an offset in the current fragment. */
	void emitJmpToOffset(unsigned offset);
	void emitJmpToRipClient(unsigned long rip);
	void emitJmpToRipHost(unsigned long rip);
	void emitCallSequence(const char *target, bool allowRedirection);
	void skipRedZone();
	void restoreRedZone();
	void emitPushQ(unsigned);
	void emitPopQ(unsigned);
	void emitMovQ(unsigned, unsigned long);
	void emitCallReg(unsigned);
public:
	void fromCFG(CFG *cfg);
	char *asC() const;

	bool ripToOffset(unsigned long rip, unsigned *res);
	void writeBytes(const void *bytes, unsigned size, unsigned offset);
	void addLateReloc(LateRelocation m) { lateRelocs.push_back(m); }

	void visit(HeapVisitor &hv) {
		visit_container(relocs, hv);
	}
	void destruct() { this->~PatchFragment(); }
	NAMED_CLASS

	/* Can be overridden by derived classes which need to do
	 * something special when we return to untranslated code.
	 * This is only invoked for statically constant branches; if
	 * you want to do anything with non-constant branches then
	 * you'll need to override emitInstruction() as well.
	 */
	virtual bool generateEpilogue(unsigned long exitRip) { return false; }

protected:

	/* Emit a single instruction.  The instruction passed in is as
	 * it was in the original program.  The derived class is at
	 * liberty to generate as many or as few output instructions
	 * as it desires. */
	virtual void emitInstruction(Instruction *i);

	void registerInstruction(Instruction *i, unsigned offset) {
		assert(!i->presentInPatch);
		i->offsetInPatch = offset;
		i->presentInPatch = true;
		registeredInstrs.push_back(i);
	}
};

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
		abort();
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

	abort();
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
PatchFragment::asC() const
{
	char *content_buf = (char *)LibVEX_Alloc_Bytes(content.size() * 4 + 1);
	for (unsigned x = 0; x < content.size(); x++)
		sprintf(content_buf + x * 4, "\\x%02x", content[x]);
	char *content = vex_asprintf("static const unsigned char patch_content[] = \"%s\";\n\n"
				     "static const struct relocation reloc[] = {\n",
				     content_buf);
	for (std::vector<LateRelocation>::const_iterator it = lateRelocs.begin();
	     it != lateRelocs.end();
	     it++)
		content = vex_asprintf("%s\t%s,\n",
				       content, *it);

	content = vex_asprintf("%s};\n\nstatic const struct trans_table_entry trans_table[] = {\n",
			       content);
	for (std::vector<Instruction *>::const_iterator it = registeredInstrs.begin();
	     it != registeredInstrs.end();
	     it++)
		content = vex_asprintf("%s\t{0x%lx, %d},\n",
				       content,
				       (*it)->rip,
				       (*it)->offsetInPatch);
	return vex_asprintf("%s};\n", content);
}

class SourceSinkCFG : public CFG {
	static unsigned long __trivial_hash_function(const unsigned long &k) { return k; }	
	gc_map<unsigned long, bool, __trivial_hash_function> *sinkInstructions;
public:
	void add_sink(unsigned long rip) { (*sinkInstructions)[rip] = true; }
	void destruct() { this->~SourceSinkCFG(); }

	bool exploreInstruction(Instruction *i) { return !(*sinkInstructions)[i->rip]; }
	bool instructionUseful(Instruction *i) { return (*sinkInstructions)[i->rip]; }

	SourceSinkCFG(AddressSpace<unsigned long> *as)
		: CFG(as)
	{
		sinkInstructions = new gc_map<unsigned long, bool, __trivial_hash_function>();
	}
	void visit(HeapVisitor &hv) {
		CFG::visit(hv);
		hv(sinkInstructions);
	}
};

class AddExitCallPatch : public PatchFragment {
protected:
	bool generateEpilogue(unsigned long exitRip);
	/* XXX should really override emitInstruction here to catch
	   indirect jmp and ret instructions; oh well. */
};

bool
AddExitCallPatch::generateEpilogue(unsigned long exitRip)
{
	Instruction *i = Instruction::pseudo(exitRip);

	cfg->registerInstruction(i);
	registerInstruction(i, content.size());

	emitCallSequence("(unsigned long)release_lock", true);
	emitJmpToRipHost(exitRip);

	return true;
}

struct CriticalSection {
	unsigned long entry;
	unsigned long exit;
};

static char *
mkPatch(AddressSpace<unsigned long> *as, struct CriticalSection *csects, unsigned nr_csects)
{
	SourceSinkCFG *cfg = new SourceSinkCFG(as);
	for (unsigned x = 0; x < nr_csects; x++) {
		cfg->add_root(csects[x].entry, 50);
		cfg->add_sink(csects[x].exit);
	}
	cfg->doit();

	PatchFragment *pf = new AddExitCallPatch();
	pf->fromCFG(cfg);

	char *res = pf->asC();
	res = vex_asprintf("#include \"patch_head.h\"\n\n%s\nstatic unsigned long entry_points[] = {\n",
			   res);
	for (unsigned x = 0; x < nr_csects; x++)
		res = vex_asprintf("%s\t0x%lx,\n", res, csects[x].entry);
	return vex_asprintf("%s};\n\n#include \"patch_skeleton.c\"\n", res);
}

static void
safeWrite(int fd, const void *buf, size_t buf_size)
{
	unsigned written;
	int this_time;

	for (written = 0; written < buf_size; written += this_time) {
		this_time = write(fd, (const char*)buf + written, buf_size - written);
		if (this_time < 0)
			err(1, "writing to output file");
		if (this_time == 0)
			errx(1, "cannot write to output file");
	}
}

class DeleteOnDeath {
	char *path;
public:
	DeleteOnDeath(char *_path) : path(strdup(_path)) {}
	~DeleteOnDeath() { unlink(path); free(path); }
};

static int
spawn(const char *path, ...)
{
	va_list args;
	unsigned nr_args;
	const char *arg;
	const char **argv;

	va_start(args, path);
	nr_args = 2; /* Include argv[0] and the NULL terminator */
	while (1) {
		arg = va_arg(args, const char *);
		if (!arg)
			break;
		nr_args++;
	}
	va_end(args);

	argv = (const char **)malloc(sizeof(argv[0]) * nr_args);
	argv[0] = path;
	va_start(args, path);
	unsigned argc = 1;
	while (1) {
		argv[argc] = va_arg(args, const char *);
		if (argv[argc] == NULL)
			break;
		argc++;		
	}
	va_end(args);

	pid_t child = fork();
	if (child == 0) {
		execv(path, (char *const*)argv);
		err(1, "cannot exec %s", path);
	}
	if (child == -1)
		err(1, "cannot fork");

	int status;
	pid_t r = waitpid(child, &status, 0);
	if (r < 0)
		err(1, "waiting for child");
	assert(r == child);
	if (WIFEXITED(status))
		return WEXITSTATUS(status);
	if (WIFSIGNALED(status))
		return -WTERMSIG(status);
	abort();
}

int
main(int argc, char *argv[])
{
	if (argc < 4 || argc % 2)
		errx(1, "expected at least one critical section, and for each section to have two rips, plus the logfile");

	init_sli();

	/* The only thing we care about in the log file is the initial
	   memory layout.  We should arguably fast-forward it to the
	   point for which the patch was created, so that we can
	   handle e.g. self-modifying code, but that's a pain, and
	   there are so many other things which go wrong when code
	   changes while you're trying to fix it that it's not worth
	   it. */
	LogReaderPtr ptr;
	VexPtr<LogReader<unsigned long> > lf(LogFile::open(argv[1], &ptr));
	if (!lf)
		err(1, "opening %s", argv[1]);
	MachineState<unsigned long> *ms = MachineState<unsigned long>::initialMachineState(lf, ptr, &ptr, ALLOW_GC);
	AddressSpace<unsigned long> *as = ms->addressSpace;

	CriticalSection *csects = (CriticalSection *)malloc(sizeof(CriticalSection) * (argc - 2) / 2);
	for (int x = 0; x < (argc - 2) / 2; x++) {
		csects[x].entry = strtol(argv[x * 2 + 2], NULL, 16);
		csects[x].exit = strtol(argv[x * 2 + 3], NULL, 16);
	}

	char *patchFragment = mkPatch(as, csects, (argc - 2) / 2);

	char *tmpPath;
	int tmpFd;
	while (1) {
		tmpPath = tempnam(NULL, NULL);
		tmpFd = open(tmpPath, O_WRONLY|O_CREAT|O_EXCL|O_APPEND, 0600);
		if (tmpFd >= 0)
			break;
		if (errno != EEXIST)
			err(1, "creating temporary file");
		free(tmpPath);
	}
	DeleteOnDeath dod(tmpPath);
	safeWrite(tmpFd, patchFragment, strlen(patchFragment));

	int r = spawn("/usr/bin/gcc",
		      "-Wall",
		      "-shared",
		      "-fPIC",
		      "-I",
		      "sli",
		      "-x"
		      "c",
		      tmpPath,
		      "-o",
		      "patch1.so",
		      NULL);

	printf("gcc said %d\n", r);

	return 0;
}
