#include <err.h>

#include "sli.h"

#define MAX_INSTRUCTION_SIZE 15

template <typename p>
class VexPtr {
	p *content;
	VexGcRoot root;
public:
	VexPtr(p *_content) : content(_content), root((void **)&content, "VexPtr") {}
	VexPtr(VexPtr<p> &c) : content(c.content), root((void **)&content, "VexPtr") {}
	const VexPtr<p> &operator=(VexPtr<p> &x) { content = x.content; return *this; }
	p &operator*() { return *content; }
	p *operator->() { return content; }
	operator p*() { return content; }
};

typedef unsigned char Byte;

/* A relocation represents any kind of reference inside the patch
   which can't be resolved immediately.  The targets can include:

   -- Client code
   -- Another bit in the patch
   -- Host code
   -- Client data
   -- A host symbol

   We determine the actual target like this:

   -- If a host symbol is set, use that as the target.

   -- If allowRedirection is clear, the target is just @target.

   -- Otherwise, guess that the target is client code.  If there
      is a patch instruction for it, use that.

   -- Otherwise, if needsEpilogue is set, generate a new
      pseudo-instruction for the target, set up a redirection from
      the target to the pseudo, and then use the pseudo.

   -- Otherwise, treat the target as data as use it directly.
*/
class Relocation : public GarbageCollected<Relocation> {
public:
	unsigned int offset;
	unsigned long target;
	long addend;
	bool needsEpilogue;
	bool allowRedirection;
	char *symbol;
	Relocation(unsigned _offset, unsigned long _target, long _addend, bool _needsEpilogue,
		   bool _allowRedirection)
		: offset(_offset),
		  target(_target),
		  addend(_addend),
		  needsEpilogue(_needsEpilogue),
		  allowRedirection(_allowRedirection),
		  symbol(NULL)
	{}
	Relocation(unsigned _offset, long _addend, char *_symbol)
		: offset(_offset),
		  addend(_addend),
		  symbol(_symbol)
	{
	}
	void visit(HeapVisitor &hv) const { hv(symbol); }
	void destruct() { this->~Relocation(); }
	NAMED_CLASS
};

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
	void justEmittedRipRel32(unsigned long target, long addend, bool needsEpilogue);
	void justEmittedRipRel32(unsigned immediates, bool needsEpilogue);
public:
	unsigned long rip;

	unsigned long defaultNext;
	Instruction *defaultNextI;
	unsigned long branchNext;
	Instruction *branchNextI;

	Byte content[MAX_INSTRUCTION_SIZE];
	unsigned len;
	Prefixes pfx;
	unsigned nr_prefixes;
	std::vector<Relocation *> relocs;

	AddressSpace<unsigned long> *as;

	bool useful;

	static Instruction *decode(AddressSpace<unsigned long> *as,
				   unsigned long rip,
				   CFG *cfg);
	static Instruction *pseudo(unsigned long rip);

	void visit(HeapVisitor &hv) const {
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
	std::map<unsigned long, Instruction *> ripToInstr;
private:
	std::vector<std::pair<unsigned long, unsigned> > pendingRips;
	std::vector<unsigned long> neededRips;
	void decodeInstruction(unsigned long rip, unsigned max_depth);
public:
	CFG(AddressSpace<unsigned long> *_as) : as(_as) {}
	void add_root(unsigned long root, unsigned max_depth)
	{
		pendingRips.push_back(std::pair<unsigned long, unsigned>(root, max_depth));
	}
	void doit();
	void visit(HeapVisitor &hv) const {
		for (std::map<unsigned long, Instruction *>::const_iterator it = ripToInstr.begin();
		     it != ripToInstr.end();
		     it++)
			hv(it->second);
		hv(as);
	}
	void registerInstruction(Instruction *i) { ripToInstr[i->rip] = i; }
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
	as->readMemory(rip + len, 1, &t);
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

void
Instruction::justEmittedRipRel32(unsigned long target, long addend, bool needsEpilogue)
{
	relocs.push_back(new Relocation(len - 4, target, addend, needsEpilogue, true));
}

void
Instruction::justEmittedRipRel32(unsigned immediates, bool needsEpilogue)
{
	int delta = *(int *)(content + len - 4);
	justEmittedRipRel32(delta + rip + len + immediates, -4 - immediates, needsEpilogue);
}

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
		justEmittedRipRel32(nrImmediates, false);
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
	printf("Pseudo(%lx)\n", rip);
	Instruction *i = new Instruction();
	i->rip = rip;
	return i;
}

Instruction *
Instruction::decode(AddressSpace<unsigned long> *as,
		    unsigned long start,
		    CFG *cfg)
{
	printf("Decode %lx\n", start);
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
		i->len += 4;
		i->justEmittedRipRel32(i->branchNext, -4, true);
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
		i->justEmittedRipRel32(0, false);
		int delta = *(int *)(i->content + i->len - 4);
		unsigned long target = i->rip + i->len + delta;
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
		if (ripToInstr.find(p.first) == ripToInstr.end())
			decodeInstruction(p.first, p.second);
	}

	for (std::map<unsigned long, Instruction *>::iterator it = ripToInstr.begin();
	     it != ripToInstr.end();
	     it++) {
		std::map<unsigned long, Instruction *>::iterator probe;
		it->second->useful = instructionUseful(it->second);
		if (it->second->defaultNext) {
			probe = ripToInstr.find(it->second->defaultNext);
			if (probe != ripToInstr.end()) {
				it->second->defaultNext = 0;
				it->second->defaultNextI = probe->second;
				if (probe->second->useful)
					it->second->useful = true;
			}
		}
		if (it->second->branchNext) {
			probe = ripToInstr.find(it->second->branchNext);
			if (probe != ripToInstr.end()) {
				it->second->branchNext = 0;
				it->second->branchNextI = probe->second;
				if (probe->second->useful)
					it->second->useful = true;
			}
		}
	}

	bool progress;
	do {
		progress = false;
		for (std::map<unsigned long, Instruction *>::iterator it = ripToInstr.begin();
		     it != ripToInstr.end();
		     it++) {
			Instruction *i = it->second;
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
	for (std::map<unsigned long, Instruction *>::iterator it = ripToInstr.begin();
	     it != ripToInstr.end();
		) {
		Instruction *i = it->second;

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
			ripToInstr.erase(it++);
		}
	}
}


class PatchFragment : public GarbageCollected<PatchFragment> {
	std::map<Instruction *, unsigned> instrToOffset;
	std::vector<Relocation *> relocs;
	std::vector<Relocation *> symbolRelocs;
protected:
	std::vector<Byte> content;

private:
	Instruction *nextInstr(CFG *cfg);
	void emitStraightLine(Instruction *i);

protected:
	/* Emit a jump to an offset in the current fragment. */
	void emitJmpToOffset(unsigned offset);
	void emitJmpToRip(unsigned long rip, bool needsEpilogue, bool allowRedirection);
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

	void visit(HeapVisitor &hv) const {
		for (std::map<Instruction*, unsigned>::const_iterator it = instrToOffset.begin();
		     it != instrToOffset.end();
		     it++)
			hv(it->first);
		visit_container(relocs, hv);
	}
	void destruct() { this->~PatchFragment(); }
	NAMED_CLASS

protected:

	/* Can be overridden by derived classes which need to do
	 * something special when we return to untranslated code.
	 * This is only invoked for statically constant branches; if
	 * you want to do anything with non-constant branches then
	 * you'll need to override emitInstruction() as well.
	 */
	virtual bool generateEpilogue(unsigned long exitRip, CFG *cfg) { return false; }

	/* Emit a single instruction.  The instruction passed in is as
	 * it was in the original program.  The derived class is at
	 * liberty to generate as many or as few output instructions
	 * as it desires. */
	virtual void emitInstruction(Instruction *i);

	void registerInstruction(Instruction *i, unsigned offset) {
		instrToOffset[i] = offset;
	}
};

Instruction *
PatchFragment::nextInstr(CFG *cfg)
{
	/* Decide what to emit next */
	std::map<Instruction *, bool> pendingInstructions;
	for (std::map<unsigned long, Instruction *>::iterator it = cfg->ripToInstr.begin();
	     it != cfg->ripToInstr.end();
	     it++) {
		if (instrToOffset.find(it->second) == instrToOffset.end())
			pendingInstructions[it->second] = true;
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

void
PatchFragment::fromCFG(CFG *cfg)
{
	while (1) {
		Instruction *i = nextInstr(cfg);
		if (!i)
			break;
		emitStraightLine(i);
	}

	bool expectTargetPresent = false;
	while (!relocs.empty()) {
		Relocation *r = relocs.back();
		relocs.pop_back();
		assert(r);
		assert(r->offset < content.size());

		if (r->symbol) {
			/* These need to be deferred until we're in C
			 * again. */
			symbolRelocs.push_back(r);
/**/			continue;
		}
		union {
			unsigned delta;
			Byte deltaBytes[4];
		};
		if (r->allowRedirection) {
			std::map<unsigned long, Instruction *>::iterator probe =
				cfg->ripToInstr.find(r->target);
			if (probe == cfg->ripToInstr.end()) {
				assert(!expectTargetPresent);
				if (r->needsEpilogue) {
					/* This relocation represents
					 * a branch out of translated
					 * code.  That may require
					 * epilogue generation.
					 */
					if (generateEpilogue(r->target, cfg)) {
						/* Yes.  There should
						   now be an epilogue
						   instruction for the
						   target, so try it
						   again. */
						relocs.push_back(r);
						
						/* Next time around,
						   the target of the
						   relocation should
						   definitely be
						   present, or we'll
						   get an infinite
						   loop. */
						expectTargetPresent = true;

/**/						continue;
					}
				}
				delta = r->target - (unsigned long)&content[r->offset] + r->addend;
			} else {
				unsigned targetOffset = instrToOffset[probe->second];
				delta = targetOffset - r->offset + r->addend;
			}
		} else {
			delta = r->target - (unsigned long)&content[r->offset] + r->addend;
		}
		for (unsigned x = 0; x < 4; x++)
			content[x + r->offset] = deltaBytes[x];
		expectTargetPresent = false;
	}
}

void
PatchFragment::emitInstruction(Instruction *i)
{
	unsigned offset = content.size();
	for (unsigned x = 0; x < i->len; x++)
		content.push_back(i->content[x]);
	for (std::vector<Relocation *>::iterator it = i->relocs.begin();
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
PatchFragment::emitJmpToRip(unsigned long rip, bool needsEpilogue, bool allowRedirection)
{
	/* Emit a jmp32. */
	content.push_back(0xe9);

	/* Fill in offset later. */
	content.push_back(0);
	content.push_back(0);
	content.push_back(0);
	content.push_back(0);

	relocs.push_back(new Relocation(content.size() - 4, rip, -4, needsEpilogue, allowRedirection));
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

	/* Emit a call instruction */
	content.push_back(0xe8);
	content.push_back(0);
	content.push_back(0);
	content.push_back(0);
	content.push_back(0);
	relocs.push_back(new Relocation(content.size() - 4,
					-4,
					vg_strdup(target)));
	
	restoreRedZone();
}

void
PatchFragment::emitStraightLine(Instruction *i)
{
	assert(i);
	while (1) {
		unsigned offset = content.size();
		unsigned existing_offset = instrToOffset[i];

		if (existing_offset) {
			/* This instruction has already been emitted.
			   Rather than duplicating it, emit an
			   unconditional branch to the existing
			   location. */
			emitJmpToOffset(existing_offset);

			/* Don't try to reassemble any further. */
/**/			return;
		}

		instrToOffset[i] = offset;

		emitInstruction(i);
			
		if (!i->defaultNextI) {
			/* Hit end of block, and don't want to go any
			 * further.  Return to the original code. */
			if (i->defaultNext) {
				emitJmpToRip(i->defaultNext, true, true);
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
	char *content = vex_asprintf("const unsigned char patch_content[] = \"%s\";\n\n"
				     "struct relocation reloc[] = {\n",
				     content_buf);
	for (std::vector<Relocation *>::const_iterator it = symbolRelocs.begin();
	     it != symbolRelocs.end();
	     it++)
		content = vex_asprintf("%s{%d, %ld, %s},\n",
				       content,
				       (*it)->offset,
				       (*it)->addend,
				       (*it)->symbol);
	return vex_asprintf("%s};\n", content);
}

class SourceSinkCFG : public CFG {
	std::map<unsigned long, bool> sinkInstructions;
public:
	void add_sink(unsigned long rip) { sinkInstructions[rip] = true; }
	void destruct() { this->~SourceSinkCFG(); }

	bool exploreInstruction(Instruction *i) { return !sinkInstructions[i->rip]; }
	bool instructionUseful(Instruction *i) { return sinkInstructions[i->rip]; }

	SourceSinkCFG(AddressSpace<unsigned long> *as)
		: CFG(as)
	{
	}
};

class AddExitCallPatch : public PatchFragment {
protected:
	bool generateEpilogue(unsigned long exitRip, CFG *cfg);
	/* XXX should really override emitInstruction here to catch
	   indirect jmp and ret instructions; oh well. */
};

bool
AddExitCallPatch::generateEpilogue(unsigned long exitRip,
				   CFG *cfg)
{
	Instruction *i = Instruction::pseudo(exitRip);

	cfg->registerInstruction(i);
	registerInstruction(i, content.size());

	emitCallSequence("release_lock", true);
	emitJmpToRip(exitRip, false, false);

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

	return pf->asC();
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
	LogFile *lf;
	LogReaderPtr ptr;
	lf = LogFile::open(argv[1], &ptr);
	if (!lf)
		err(1, "opening %s", argv[1]);
	MachineState<unsigned long> *ms = MachineState<unsigned long>::initialMachineState(lf, ptr, &ptr);
	VexPtr<AddressSpace<unsigned long> > as(ms->addressSpace);

	CriticalSection *csects = (CriticalSection *)malloc(sizeof(CriticalSection) * (argc - 2) / 2);
	for (int x = 0; x < (argc - 2) / 2; x++) {
		csects[x].entry = strtol(argv[x * 2 + 2], NULL, 16);
		csects[x].exit = strtol(argv[x * 2 + 3], NULL, 16);
	}

	printf("%s\n", mkPatch(as, csects, (argc - 2) / 2));

	return 0;
}
