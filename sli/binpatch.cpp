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

class Relocation : public GarbageCollected<Relocation> {
public:
	Relocation(unsigned _offset) : offset(_offset) {}
	unsigned offset;
	void visit(HeapVisitor &hv) const {};
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

/* A relocation which says that there's a 32 bit value at @offset
 * which is RIP relative and should be tweaked so that it points at
 * the same absolute address after relocation. */
class RelocationRipRel32 : public Relocation {
public:
	unsigned long target;
	long addend;
	RelocationRipRel32(unsigned _offset, unsigned long _target,
			   long _addend)
		: Relocation(_offset),
		  target(_target),
		  addend(_addend)
	{
	}
};

class CFG;

class Instruction : public GarbageCollected<Instruction > {
	Byte byte();
	void emit(Byte);
	void modrm(unsigned nrImmediates);
	void immediate(unsigned size);
	void justEmittedRipRel32(unsigned long target, long addend);
	void justEmittedRipRel32(unsigned immediates = 0);
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
Instruction::justEmittedRipRel32(unsigned long target, long addend)
{
	relocs.push_back(new RelocationRipRel32(len - 4, target, addend));
}

void
Instruction::justEmittedRipRel32(unsigned immediates)
{
	int delta = *(int *)(content + len - 4);
	justEmittedRipRel32(delta + rip + len + immediates, -4 - immediates);
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
		justEmittedRipRel32(nrImmediates);
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
		i->justEmittedRipRel32(i->branchNext, -4);
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
		i->justEmittedRipRel32();
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
	ripToInstr[rip] = i;
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
	std::vector<Byte> content;

	Instruction *nextInstr(CFG *cfg);
	void emitStraightLine(Instruction *i);
public:
	static PatchFragment *fromCFG(CFG *cfg);

	void visit(HeapVisitor &hv) const {
		for (std::map<Instruction*, unsigned>::const_iterator it = instrToOffset.begin();
		     it != instrToOffset.end();
		     it++)
			hv(it->first);
		visit_container(relocs, hv);
	}
	void destruct() { this->~PatchFragment(); }
	NAMED_CLASS
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

PatchFragment *
PatchFragment::fromCFG(CFG *cfg)
{
	PatchFragment *work = new PatchFragment();

	while (1) {
		Instruction *i = work->nextInstr(cfg);
		if (!i)
			break;
		work->emitStraightLine(i);
	}

	for (std::vector<Relocation *>::iterator it = work->relocs.begin();
	     it != work->relocs.end();
	     it++) {
		RelocationRipRel32 *rrr32 =
			dynamic_cast<RelocationRipRel32 *>(*it);
		assert(rrr32);
		assert(rrr32->offset < work->content.size());

		std::map<unsigned long, Instruction *>::iterator probe =
			cfg->ripToInstr.find(rrr32->target);
		union {
			unsigned delta;
			Byte deltaBytes[4];
		};
		if (probe == cfg->ripToInstr.end()) {
			delta = rrr32->target - (unsigned long)&work->content[rrr32->offset] + rrr32->addend;
		} else {
			unsigned targetOffset = work->instrToOffset[probe->second];
			delta = targetOffset - rrr32->offset + rrr32->addend;
		}
		for (unsigned x = 0; x < 4; x++)
			work->content[x + rrr32->offset] = deltaBytes[x];
	}
	return work;
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
			content.push_back(0xe9);
			union {
				int delta_word;
				Byte delta_bytes[4];
			};
			delta_word = existing_offset - offset - 5;
			for (unsigned x = 0; x < 4; x++)
				content.push_back(delta_bytes[x]);

			/* Don't try to reassemble any further. */
/**/			return;
		}

		instrToOffset[i] = offset;
		for (unsigned x = 0; x < i->len; x++)
			content.push_back(i->content[x]);

		for (std::vector<Relocation *>::iterator it = i->relocs.begin();
		     it != i->relocs.end();
		     it++) {
			(*it)->offset += offset;
			relocs.push_back(*it);
		}
			
		if (!i->defaultNextI) {
			/* Hit end of block, and don't want to go any
			 * further.  Return to the original code. */
			if (!i->defaultNext) {
				/* Last instruction in the block was
				   an unpredictable branch, which
				   we'll just have emitted verbatim,
				   so we don't need to do any more. */
				return;
			}

			/* Emit a jmp32. */
			content.push_back(0xe9);

			/* Fill in offset later. */
			content.push_back(0);
			content.push_back(0);
			content.push_back(0);
			content.push_back(0);

			relocs.push_back(new RelocationRipRel32(content.size() - 4,
								i->defaultNext,
								-4));
			return;
		}

		i = i->defaultNextI;
	}
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

	SourceSinkCFG *cfg = new SourceSinkCFG(as);
	for (int x = 2; x < argc; x += 2) {
		cfg->add_root(strtol(argv[x], NULL, 16), 50);
		cfg->add_sink(strtol(argv[x+1], NULL, 16));
	}
	cfg->doit();

	PatchFragment *pf = PatchFragment::fromCFG(cfg);

	return 0;
}
