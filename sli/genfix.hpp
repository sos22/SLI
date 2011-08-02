#ifndef GENFIX_H__
#define GENFIX_H__

#define MAX_INSTRUCTION_SIZE 15

#include "libvex_ir.h"
#include <set>
#include <map>

template <typename ripType> class CFG;
template <typename ripType> class EarlyRelocation;
typedef unsigned char Byte;

class Prefixes {
public:
	bool rex_w, rex_r, rex_x, rex_b;
	Prefixes() : rex_w(false),
		     rex_r(false),
		     rex_x(false),
		     rex_b(false)
	{
	}
	void rexByte(unsigned char b) {
		assert(b >= 0x40);
		assert(b < 0x50);
		rex_b = !!(b & 1);
		rex_x = !!(b & 2);
		rex_r = !!(b & 4);
		rex_w = !!(b & 8);
	}
};

template <typename ripType>
class Instruction : public GarbageCollected<Instruction<ripType> > {
	unsigned char byte();
	int int32();
	void emit(unsigned char);
	void modrm(unsigned nrImmediates);
	void immediate(unsigned size);
	int modrmExtension(void);
public:
	ripType rip;

	ripType defaultNext;
	Instruction *defaultNextI;
	ripType branchNext;
	Instruction *branchNextI;

	/* Doesn't really belong here, but it'll do for now. */
	unsigned offsetInPatch;
	bool presentInPatch;

	unsigned char content[MAX_INSTRUCTION_SIZE];
	unsigned len;
	Prefixes pfx;
	unsigned nr_prefixes;
	std::vector<EarlyRelocation<ripType> *> relocs;

	AddressSpace *as;

	bool useful;

	static Instruction<ripType> *decode(AddressSpace *as,
					    ripType rip,
					    CFG<ripType> *cfg);
	static Instruction<ripType> *pseudo(ripType rip);

	template <typename targetType, targetType degrader(const ripType &)> Instruction<targetType> *degrade();

	void visit(HeapVisitor &hv) {
		visit_container(relocs, hv);
		hv(as);
		hv(defaultNextI);
		hv(branchNextI);
	}
	void destruct() { this->~Instruction(); }
	NAMED_CLASS
};

class ClientRip;

unsigned long __trivial_hash_function(const ThreadRip &k);
unsigned long __trivial_hash_function(const unsigned long &k);
unsigned long __trivial_hash_function(const ClientRip &k);

template <typename ripType>
class CFG : public GarbageCollected<CFG<ripType> > {
	AddressSpace *as;
public:
	typedef gc_map<ripType, Instruction<ripType> *, __trivial_hash_function,
		       __default_eq_function, __visit_function_heap> ripToInstrT;
	ripToInstrT *ripToInstr;
private:
	std::vector<std::pair<ripType, unsigned> > pendingRips;
	std::vector<ripType> neededRips;
	void decodeInstruction(ripType rip, unsigned max_depth);
public:
	CFG(AddressSpace *_as) : as(_as), ripToInstr(new ripToInstrT()) {}
	void add_root(ripType root, unsigned max_depth)
	{
		pendingRips.push_back(std::pair<ripType, unsigned>(root, max_depth));
	}
	void doit();
	void visit(HeapVisitor &hv) {
		hv(ripToInstr);
		hv(as);
	}
	void registerInstruction(Instruction<ripType> *i) { (*ripToInstr)[i->rip] = i; }

	void print(FILE *logfile);

	virtual void destruct() { this->~CFG(); }
	NAMED_CLASS

	/* Switch from one ripType to a less fine-grained one
	 * e.g. from a ThreadRip to an unsigned long rip */
	template <typename target, target degrader(const ripType &)> CFG<target> *degrade();

	/* These can be overriden by derived classes to change the
	 * behaviour a bit. */

	/* Should we bother to explore instructions which follow this
	 * one?  If this returns true, direct followers of this
	 * instruction will be explored; indirect ones will not be
	 * (i.e. we only consider branches whose target is statically
	 * constant). */
	virtual bool exploreInstruction(Instruction<ripType> *i) { return true; }
	/* We've discovered a direct-called function.  Should we
	 * explore the callee?  Indirect calls are never explored. */
	virtual bool exploreFunction(ripType rip) { return false; }
	/* Is this instruction useful?  Once the CFG is built, we do a
	 * post-pass which walks the list of instructions, and uses
	 * this to decide whether instructions are useful.  We then
	 * walk backwards through the CFG and mark any instruction
	 * which can reach a useful instruction as being useful
	 * itself.  Finally, any non-useful instructions are replaced
	 * with branches back into the original code.
	 */
	virtual bool instructionUseful(Instruction<ripType> *i) { return true; }
};

typedef char *LateRelocation;

template <typename ripType>
class PatchFragment : public GarbageCollected<PatchFragment<ripType> > {
	std::vector<Instruction<ripType> *> registeredInstrs;

protected:
	std::vector<EarlyRelocation<ripType> *> relocs;
	std::vector<LateRelocation> lateRelocs;
	CFG<ripType> *cfg;
	std::vector<unsigned char> content;

private:
	Instruction<ripType> *nextInstr(CFG<ripType> *cfg);
	void emitStraightLine(Instruction<ripType> *i);

protected:
	class ModRM {
		ModRM() : extendRm(false) {}
	public:
		std::vector<unsigned char> content;
		bool extendRm;
		/* Access memory at address @reg + offset, where reg
		   is a register index and offset is a constant. */
		static ModRM memAtRegisterPlusOffset(unsigned reg, int offset);
		/* Access register @reg directly, not going through
		 * memory. */
		static ModRM directRegister(unsigned reg);
		/* Access memory at a fixed 32 bit signed address */
		static ModRM absoluteAddress(int address);
	};

	void emitByte(unsigned char b) { content.push_back(b); }
	void emitQword(unsigned long val);

	void emitModrm(const ModRM &mrm, unsigned reg);

	/* Emit a jump to an offset in the current fragment. */
	void emitJmpToOffset(unsigned offset);
	void emitJmpToRipClient(ripType rip);
	void emitJmpToRipHost(unsigned long rip);

	/* Emit a simple opcode which uses a modrm but no immediates
	 * and is 64 bits.  This corresponds to the Ev,Gv and Gv,Ev
	 * encodings in the architecture manual. */
	void emitNoImmediatesModrmOpcode(unsigned opcode, unsigned reg, const ModRM &rm);

	/* Store a register to a modrm. */
	void emitMovRegisterToModrm(unsigned reg, const ModRM &rm);
	/* Load a register from a modrm */
	void emitMovModrmToRegister(const ModRM &rm, unsigned reg);
	/* Add a register to a modrm */
	void emitAddRegToModrm(unsigned reg, const ModRM &rm);
	/* Compare a register to a modrm */
	void emitCmpRegModrm(unsigned reg, const ModRM &rm);
	/* Negate a modrm */
	void emitNegModrm(const ModRM &rm);

	void emitLea(const ModRM &modrm, unsigned reg);

	void emitCallSequence(const char *target, bool allowRedirection);
	void skipRedZone();
	void restoreRedZone();
	void emitPushQ(unsigned);
	void emitPopQ(unsigned);
	void emitMovQ(unsigned, unsigned long);
	void emitCallReg(unsigned);
public:
	void fromCFG(CFG<ripType> *cfg);

	bool ripToOffset(ripType rip, unsigned *res);
	void writeBytes(const void *bytes, unsigned size, unsigned offset);
	void addLateReloc(LateRelocation m) { lateRelocs.push_back(m); }

	/* Just the core patch itself, not including the metdata tables. */
	char *asC(const char *ident, char **relocs_name, char **trans_name, char **content_name) const;
	/* The whole patch, including metadata tables. */
	char *asC(const char *ident, const std::set<ripType> &entryPoints) const;

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
	virtual void generateEpilogue(ripType exitRip);

protected:

	/* Emit a single instruction.  The instruction passed in is as
	 * it was in the original program.  The derived class is at
	 * liberty to generate as many or as few output instructions
	 * as it desires. */
	virtual void emitInstruction(Instruction<ripType> *i);

	void registerInstruction(Instruction<ripType> *i, unsigned offset) {
		assert(!i->presentInPatch);
		i->offsetInPatch = offset;
		i->presentInPatch = true;
		registeredInstrs.push_back(i);
	}
};

/* There are two types of relocation, early and late.  Early
   relocations are done statically while building the patch.  Late
   relocations are done afterwards, when the patch is loaded. */
template <typename ripType>
class EarlyRelocation : public GarbageCollected<EarlyRelocation<ripType> > {
public:
	unsigned offset;
	unsigned size;
	EarlyRelocation(unsigned _offset, unsigned _size)
		: offset(_offset), size(_size) {}
	virtual void doit(PatchFragment<ripType> *pf) = 0;
	template <typename targetType, targetType degrader(const ripType &)> EarlyRelocation<targetType> *degrade();
	void visit(HeapVisitor &hv) {}
	void destruct() {}
	NAMED_CLASS
};

LateRelocation late_relocation(unsigned offset, unsigned size,
			       const char *target, unsigned nrImmediateBytes,
			       bool relative);

template <typename r> void
Instruction<r>::emit(Byte b)
{
	assert(len < MAX_INSTRUCTION_SIZE);
	content[len] = b;
	len++;
}

template <typename r> Byte
Instruction<r>::byte()
{
	unsigned long t;
	t = 0;
	as->readMemory(rip.rip + len, 1, &t, false, NULL);
	Byte b = t;
	emit(b);
	return b;
}

template <typename r> int
Instruction<r>::int32()
{
	unsigned long t[4];
	as->readMemory(rip.rip + len, 4, t, false, NULL);
	emit(t[0]);
	emit(t[1]);
	emit(t[2]);
	emit(t[3]);
	return t[0] | (t[1] << 8) | (t[2] << 16) | (t[3] << 24);
}

template <typename r> void
Instruction<r>::immediate(unsigned size)
{
	for (unsigned x = 0; x < size; x++)
		byte();
}

template <typename r> int
Instruction<r>::modrmExtension(void)
{
	Byte b = byte();
	len--;
	return (b >> 3) & 7;
}

template <typename r>
class RipRelativeRelocation : public EarlyRelocation<r> {
public:
	r target;
	unsigned nrImmediateBytes;

	void doit(PatchFragment<r> *pf);

	RipRelativeRelocation(unsigned _offset,
			      unsigned _size,
			      r _target,
			      unsigned _nrImmediateBytes)
		: EarlyRelocation<r>(_offset, _size),
		  target(_target),
		  nrImmediateBytes(_nrImmediateBytes)
	{
	}
	template <typename targetT, targetT degrader(const r &)> RipRelativeRelocation<targetT> *degrade()
	{
		return new RipRelativeRelocation<targetT>(
			this->offset,
			this->size,
			degrader(target),
			nrImmediateBytes);
	}
};

template <typename r>
class RipRelativeBranchRelocation : public EarlyRelocation<r> {
public:
	r target;
	void doit(PatchFragment<r> *pf);
	RipRelativeBranchRelocation(unsigned _offset,
				    unsigned _size,
				    r _target)
		: EarlyRelocation<r>(_offset, _size),
		  target(_target)
	{
	}
	template <typename targetT, targetT degrader(const r &)> RipRelativeBranchRelocation<targetT> *degrade()
	{
		return new RipRelativeBranchRelocation<targetT>(
			this->offset,
			this->size,
			degrader(target));
	}
};

template <typename r> void
Instruction<r>::modrm(unsigned nrImmediates)
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
		relocs.push_back(new RipRelativeRelocation<r>(len - 4,
							      4,
							      rip + delta + len + nrImmediates,
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

template <typename r> Instruction<r> *
Instruction<r>::pseudo(r rip)
{
	Instruction<r> *i = new Instruction<r>();
	i->rip = rip;
	return i;
}

template <typename r> Instruction<r> *
Instruction<r>::decode(AddressSpace *as,
		       r start,
		       CFG<r> *cfg)
{
	Instruction<r> *i = new Instruction<r>();
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
	bool opsize = false;

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
				if (opsize)
					i->immediate(2);
				else
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
			i->relocs.push_back(new RipRelativeBranchRelocation<r>(i->len - 4, 4, i->branchNext));
			/* Unlike 8 bit jumps, we don't need to set
			   fallsThrough here, because the normal
			   defaultNext calculation will do the right
			   thing, because the output instruction is
			   the same size as the input one. */
			break;

		case 0x1f: /* nop Ev */
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

	case 0x66: /* opsize prefix */
		opsize = !opsize;
		b = i->byte();
		goto top;

	case 0x70 ... 0x7f:
		/* 8 bit conditional jumps are handled specially, by
		   turning them into 32 conditional jumps, because
		   that simplifies a lot of relocation-related
		   stuff. */
		/* Decode the instruction... */
		delta = i->byte();
		i->defaultNext = i->rip + i->len;
		i->branchNext = i->defaultNext + delta;

		/* Now rewind and emit the 32 bit version. */
		i->len = 0;
		i->emit(0x0f);
		i->emit(b + 0x10);
		i->relocs.push_back(new RipRelativeBranchRelocation<r>(i->len, 4, i->branchNext));
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
		if (opsize) {
			i->modrm(2);
			i->immediate(2);
		} else {
			i->modrm(4);
			i->immediate(4);
		}
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
		} else if (opsize) {
			i->immediate(2);
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
		if (opsize) {
			i->modrm(2);
			i->immediate(2);
		} else {
			i->modrm(4);
			i->immediate(4);
		}
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
		r target = i->rip + i->len + delta;
		i->relocs.push_back(new RipRelativeRelocation<r>(i->len - 4,
								 4,
								 target,
								 0));
		if (cfg->exploreFunction(target))
			i->branchNext = target;
		break;
	}
	case 0xeb: /* jmp rel8 */
		delta = i->byte();
		i->defaultNext = ThreadRip::mk(i->rip.thread, i->rip.rip + i->len + delta);

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
		i->defaultNext = ThreadRip::mk(i->rip.thread, i->rip.rip + i->len + delta32);
		i->len = 0;
		fallsThrough = false;
		break;

	case 0xf7: /* Unary group 3 Ev */
		if (i->modrmExtension() == 0) {
			if (opsize) {
				i->modrm(2);
				i->immediate(2);
			} else {
				i->modrm(4);
				i->immediate(4);
			}
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
		i->defaultNext = ThreadRip::mk(i->rip.thread, i->rip.rip + i->len);

	return i;
}

template <typename r> void
CFG<r>::decodeInstruction(r rip, unsigned max_depth)
{
	if (!max_depth)
		return;
	Instruction<r> *i = Instruction<r>::decode(as, rip, this);
	if (!i)
		return;
	assert(i->rip == rip);
	registerInstruction(i);
	if (exploreInstruction(i)) {
		if (i->branchNext.rip)
			pendingRips.push_back(std::pair<r, unsigned>(
						      i->branchNext, max_depth - 1));
		if (i->defaultNext.rip)
			pendingRips.push_back(std::pair<r, unsigned>(
						      i->defaultNext, max_depth - 1));
	}
}

template <typename r> void
CFG<r>::doit()
{
	while (!pendingRips.empty()) {
		std::pair<r, unsigned> p = pendingRips.back();
		pendingRips.pop_back();
		if (!ripToInstr->hasKey(p.first))
			decodeInstruction(p.first, p.second);
	}

	for (typename ripToInstrT::iterator it = ripToInstr->begin();
	     it != ripToInstr->end();
	     it++) {
		Instruction<r> *ins = it.value();
		ins->useful = instructionUseful(ins);
		if (ins->defaultNext.rip && ripToInstr->hasKey(ins->defaultNext)) {
			Instruction<r> *dn = (*ripToInstr)[ins->defaultNext];
			ins->defaultNext.rip = 0;
			ins->defaultNextI = dn;
			if (dn->useful)
				ins->useful = true;
		}
		if (ins->branchNext.rip && ripToInstr->hasKey(ins->branchNext)) {
			Instruction<r> *bn = (*ripToInstr)[ins->branchNext];
			ins->branchNext.rip = 0;
			ins->branchNextI = bn;
			if (bn->useful)
				bn->useful = true;
		}
	}

	bool progress;
	do {
		progress = false;
		for (typename ripToInstrT::iterator it = ripToInstr->begin();
		     it != ripToInstr->end();
		     it++) {
			Instruction<r> *i = it.value();
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
	for (typename ripToInstrT::iterator it = ripToInstr->begin();
	     it != ripToInstr->end();
		) {
		Instruction<r> *i = it.value();

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

template <typename r> void
RipRelativeRelocation<r>::doit(PatchFragment<r> *pf)
{
	unsigned targetOffset;
	if (pf->ripToOffset(target, &targetOffset)) {
		long delta = targetOffset - this->offset - nrImmediateBytes - this->size;
		pf->writeBytes(&delta, this->size, this->offset);
	} else {
		pf->addLateReloc(late_relocation(this->offset, this->size,
						 vex_asprintf("0x%lx",target.rip),
						 nrImmediateBytes, true));
	}
}

template <typename r> void
RipRelativeBranchRelocation<r>::doit(PatchFragment<r> *pf)
{
	unsigned targetOffset;
	if (!pf->ripToOffset(target, &targetOffset))
		pf->generateEpilogue(target);
	if (!pf->ripToOffset(target, &targetOffset))
		fail("Failed to generate epilogue for %lx\n", target.rip);
	int delta = targetOffset - this->offset - this->size;
	pf->writeBytes(&delta, this->size, this->offset);
}

template <typename r> Instruction<r> *
PatchFragment<r>::nextInstr(CFG<r> *cfg)
{
	/* Decide what to emit next */
	std::map<Instruction<r> *, bool> pendingInstructions;
	for (typename CFG<r>::ripToInstrT::iterator it = cfg->ripToInstr->begin();
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
	for (typename std::map<Instruction<r> *, bool>::iterator it = pendingInstructions.begin();
	     it != pendingInstructions.end();
	     it++) {
		if (it->first->defaultNextI)
			pendingInstructions[it->first->defaultNextI] = false;
	}
	for (typename std::map<Instruction<r> *, bool>::iterator it = pendingInstructions.begin();
	     it != pendingInstructions.end();
	     it++)
		if (it->second)
			return it->first;

	/* Yurk.  Everything is part of a cycle.  Just pick the
	 * instruction with the numerically smallest address. */
	std::set<std::pair<r, Instruction<r> *> > instrs;
	for (typename std::map<Instruction<r> *, bool>::iterator it = pendingInstructions.begin();
	     it != pendingInstructions.end();
	     it++)
		instrs.insert(std::pair<r, Instruction<r> *>(it->first->rip, it->first));
	/* The set will sort on the first item in the pair, so this
	   gives us the first instruction. */
	assert(instrs.begin() != instrs.end());
	return instrs.begin()->second;
}

template <typename r> bool
PatchFragment<r>::ripToOffset(r rip, unsigned *res)
{
	*res = 0;
	if (!cfg->ripToInstr->hasKey(rip))
		return false;
	Instruction<r> *i = (*cfg->ripToInstr)[rip];
	if (!i->presentInPatch)
		return false;
	*res = i->offsetInPatch;
	return true;
}

template <typename r> void
PatchFragment<r>::writeBytes(const void *_bytes, unsigned size, unsigned offset)
{
	const Byte *bytes = (const Byte *)_bytes;
	for (unsigned x = 0; x < size; x++)
		content[offset + x] = bytes[x];
}

template <typename r> void
PatchFragment<r>::fromCFG(CFG<r> *_cfg)
{
	cfg = _cfg;
	while (1) {
		Instruction<r> *i = nextInstr(cfg);
		if (!i)
			break;
		emitStraightLine(i);
	}

	while (!relocs.empty()) {
		EarlyRelocation<r> *re = relocs.back();
		relocs.pop_back();
		assert(re);
		assert(re->offset + re->size <= content.size());

		re->doit(this);
	}
}

template <typename r> void
PatchFragment<r>::emitInstruction(Instruction<r> *i)
{
	unsigned offset = content.size();
	for (unsigned x = 0; x < i->len; x++)
		emitByte(i->content[x]);
	for (typename std::vector<EarlyRelocation<r> *>::iterator it = i->relocs.begin();
	     it != i->relocs.end();
	     it++) {
		(*it)->offset += offset;
		relocs.push_back(*it);
	}
}

/* Convert an int to its constituent bytes, in little-endian order. */
/* For some reason gcc flags a warning if you use this construct from
 * in a template; meh. */
static inline void
toBytes(int i, unsigned char b[4])
{
	union {
		unsigned char asBytes[4];
		int j;
	};
	j = i;
	b[0] = asBytes[0];
	b[1] = asBytes[1];
	b[2] = asBytes[2];
	b[3] = asBytes[3];
}

template <typename r> void
PatchFragment<r>::emitJmpToOffset(unsigned target_offset)
{
	unsigned starting_offset = content.size();
	emitByte(0xe9);
	Byte delta_bytes[4];
	toBytes((int)(target_offset - starting_offset - 5), delta_bytes);
	for (unsigned x = 0; x < 4; x++)
		emitByte(delta_bytes[x]);
}

template <typename r> void
PatchFragment<r>::emitJmpToRipClient(r rip)
{
	emitJmpToOffset(0);
	relocs.push_back(new RipRelativeBranchRelocation<r>(content.size() - 4, 4, rip));
}

template <typename r> void
PatchFragment<r>::emitJmpToRipHost(unsigned long rip)
{
	emitJmpToOffset(0);
	lateRelocs.push_back(late_relocation(content.size() - 4, 4,
					     vex_asprintf("0x%lx", rip),
					     0,
					     true));
}

template <typename r> void
PatchFragment<r>::emitLea(const ModRM &modrm, unsigned reg)
{
	if (reg >= 8) {
		emitByte(0x49);
		reg -= 8;
	} else {
		emitByte(0x48);
	}
	emitByte(0x8d);
	emitModrm(modrm, reg);
}

template <typename r> void
PatchFragment<r>::skipRedZone()
{
	emitLea(ModRM::memAtRegisterPlusOffset(4, -128), 4);
}

template <typename r> void
PatchFragment<r>::restoreRedZone()
{
	emitLea(ModRM::memAtRegisterPlusOffset(4, 128), 4);
}

template <typename r> void
PatchFragment<r>::emitPushQ(unsigned reg)
{
	if (reg >= 8) {
		emitByte(0x41);
		reg -= 8;
	}
	assert(reg < 8);
	emitByte(0x50 + reg);
}

template <typename r> void
PatchFragment<r>::emitPopQ(unsigned reg)
{
	if (reg >= 8) {
		emitByte(0x41);
		reg -= 8;
	}
	assert(reg < 8);
	emitByte(0x58 + reg);
}

/* For some reason gcc produces an unused variable warning if you use
   an anonymous union in a template.  Fix by splitting this into two
   functions. */
static inline void
__emitQword_toBytes(long x, Byte b[8])
{
	union {
		unsigned long asLong;
		Byte asBytes[8];
	};
	asLong = x;
	memcpy(b, asBytes, 8);
}
template <typename r> void
PatchFragment<r>::emitQword(unsigned long val)
{
	Byte asBytes[8];
	__emitQword_toBytes(val, asBytes);
	for (unsigned x = 0; x < 8; x++)
		emitByte(asBytes[x]);
}

/* Move immediate 64 bit to register. */
template <typename r> void
PatchFragment<r>::emitMovQ(unsigned reg, unsigned long val)
{
	if (reg < 8) {
		emitByte(0x48);
	} else {
		emitByte(0x49);
		reg -= 8;
	}
	assert(reg < 8);
	emitByte(0xb8 + reg);
	emitQword(val);
}

template <typename r> void
PatchFragment<r>::emitModrm(const ModRM &rm, unsigned reg)
{
	assert(reg < 8);
	emitByte(rm.content[0] | (reg << 3));
	for (unsigned x = 1; x < rm.content.size(); x++)
		emitByte(rm.content[x]);
}

template <typename r> typename PatchFragment<r>::ModRM
PatchFragment<r>::ModRM::absoluteAddress(int address)
{
	ModRM res;
	/* modrm byte: mod = 0, rm = 4 */
	res.content.push_back(4);
	/* SIB byte.  base = 5, scale = 0, index = 4 */
	res.content.push_back(0x25);
	/* Displacement */
	unsigned char asBytes[4];
	toBytes(address, asBytes);
	for (unsigned x = 0; x < 4; x++)
		res.content.push_back(asBytes[x]);
	return res;
}

template <typename r> typename PatchFragment<r>::ModRM
PatchFragment<r>::ModRM::memAtRegisterPlusOffset(unsigned reg, int offset)
{
	ModRM res;
	if (reg >= 8) {
		res.extendRm = true;
		reg -= 8;
	} else {
		res.extendRm = false;
	}

	if (offset == 0) {
		switch (reg) {
		case 0: case 1: case 2: case 3: case 6: case 7:
			/* mod = 0, rm = register */
			res.content.push_back(reg);
			break;
		case 4: 
			/* Use a SIB */
			res.content.push_back(0x04);
			/* base = 4, scale = 0, index = 4. */
			res.content.push_back(0x24);
			break;
		case 5:
			goto encode_8bit_offset;
		default:
			abort();
		}
	} else if (offset >= -0x80 && offset < 0x80) {
	encode_8bit_offset:
		switch (reg) {
		case 0: case 1: case 2: case 3: case 5: case 6: case 7:
			/* mod = 1, rm = register */
			res.content.push_back(reg | 0x40);
			break;
		case 4:
			/* mod = 1, rm = 4 */
			res.content.push_back(0x44);
			/* SIB byte, base = 4, scale = 0, index = 4 */
			res.content.push_back(0x24);
			break;
		default:
			abort();
		}
		/* 8 bit displacement */
		res.content.push_back(offset);
	} else {
		switch (reg) {
		case 0: case 1: case 2: case 3: case 5: case 6: case 7:
			/* mod = 2, rm = register */
			res.content.push_back(reg | 0x80);
			break;
		case 4:
			/* mod = 2, rm = 4 */
			res.content.push_back(0x84);
			/* SIB byte, base = 4, scale = 0, index = 4 */
			res.content.push_back(0x24);
			break;
		default:
			abort();
		}
		unsigned char asBytes[4];
		toBytes(offset, asBytes);
		for (unsigned x = 0; x < 4; x++)
			res.content.push_back(asBytes[x]);
	}
	return res;
}

template <typename r> typename PatchFragment<r>::ModRM
PatchFragment<r>::ModRM::directRegister(unsigned reg)
{
	ModRM res;
	if (reg >= 8) {
		res.extendRm = true;
		reg -= 8;
	} else {
		res.extendRm = false;
	}
	assert(reg < 8);
	/* mod = 3, rm = register */
	res.content.push_back(0xc0 | reg);
	return res;
}

template <typename r> void
PatchFragment<r>::emitNoImmediatesModrmOpcode(unsigned opcode, unsigned reg, const ModRM &rm)
{
	unsigned char rex = 0x48;
	if (reg >= 8) {
		rex |= 4;
		reg -= 8;
	}
	if (rm.extendRm)
		rex |= 1;
	emitByte(rex);
	assert(reg < 8);
	if (opcode >= 0x100) {
		assert((opcode & 0xff00) == 0x0f00);
		emitByte(0x0f);
		emitByte(opcode & 0xff);
	} else {
		emitByte(opcode);
	}
	emitModrm(rm, reg);
}

template <typename r> void
PatchFragment<r>::emitMovRegisterToModrm(unsigned reg, const ModRM &rm)
{
	emitNoImmediatesModrmOpcode(0x89, reg, rm);
}

template <typename r> void
PatchFragment<r>::emitMovModrmToRegister(const ModRM &rm, unsigned reg)
{
	emitNoImmediatesModrmOpcode(0x8B, reg, rm);
}

template <typename r> void
PatchFragment<r>::emitAddRegToModrm(unsigned reg, const ModRM &rm)
{
	emitNoImmediatesModrmOpcode(0x01, reg, rm);
}

template <typename r> void
PatchFragment<r>::emitCmpRegModrm(unsigned reg, const ModRM &rm)
{
	emitNoImmediatesModrmOpcode(0x3B, reg, rm);
}

template <typename r> void
PatchFragment<r>::emitNegModrm(const ModRM &rm)
{
	emitNoImmediatesModrmOpcode(0xF7, 3, rm);
}

template <typename r> void
PatchFragment<r>::emitCallReg(unsigned reg)
{
	if (reg >= 8) {
		emitByte(0x41);
		reg -= 8;
	}
	emitByte(0xff);
	emitModrm(ModRM::directRegister(reg), 2);
}

template <typename r> void
PatchFragment<r>::emitCallSequence(const char *target, bool allowRedirection)
{
	skipRedZone();

	emitPushQ(6);
	emitMovQ(6, 0);
	lateRelocs.push_back(late_relocation(content.size() - 8,
					     8,
					     vex_asprintf("%s", target),
					     0,
					     false));
	emitCallReg(6);
	emitPopQ(6);
	
	restoreRedZone();
}

template <typename r> void
PatchFragment<r>::emitStraightLine(Instruction<r> *i)
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
			if (i->defaultNext.rip) {
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

template <typename r> char *
PatchFragment<r>::asC(const char *ident, char **relocs_name, char **trans_name, char **content_name) const
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
	for (typename std::vector<Instruction<r> *>::const_iterator it = registeredInstrs.begin();
	     it != registeredInstrs.end();
	     it++)
		content = vex_asprintf("%s\t{0x%lx, %d},\n",
				       content,
				       (*it)->rip.rip,
				       (*it)->offsetInPatch);
	return vex_asprintf("%s};\n", content);
}

template <typename r> void
PatchFragment<r>::generateEpilogue(r exitRip)
{
	Instruction<r> *i = Instruction<r>::pseudo(exitRip);
	cfg->registerInstruction(i);
	registerInstruction(i, content.size());
	emitJmpToRipHost(exitRip.rip);
}

void __genfix_add_array_summary(std::vector<const char *> &out,
				const char *t_ptr,
				const char *nr_entries,
				const char *table);

template <typename r> char *
PatchFragment<r>::asC(const char *ident, const std::set<r> &entryPoints) const
{
	std::vector<const char *> fragments;
	char *relocs_name;
	char *trans_name;
	char *content_name;
	char *entry_table_name;
	fragments.push_back(asC(ident, &relocs_name, &trans_name, &content_name));
	entry_table_name = vex_asprintf("__%s_entry_points", ident);
	fragments.push_back("static unsigned long ");
	fragments.push_back(entry_table_name);
	fragments.push_back("[] = {\n");
	for (typename std::set<r>::iterator it = entryPoints.begin();
	     it != entryPoints.end();
	     it++)
		fragments.push_back(vex_asprintf("\t0x%lx,\n", it->rip));
	fragments.push_back("};\n\nstatic struct patch ");
	fragments.push_back(ident);
	fragments.push_back(" = {\n");

	__genfix_add_array_summary(fragments, "relocations", "nr_relocations", relocs_name);
	__genfix_add_array_summary(fragments, "trans_table", "nr_translations", trans_name);
	__genfix_add_array_summary(fragments, "entry_points", "nr_entry_points", entry_table_name);
	__genfix_add_array_summary(fragments, "content", "content_size", content_name);
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

template <typename r> void
CFG<r>::print(FILE *f)
{
	for (typename ripToInstrT::iterator it = ripToInstr->begin();
	     it != ripToInstr->end();
	     it++) {
		fprintf(f, "%d:%lx[%p] -> %d:%lx[%p], %d:%lx[%p]\n",
			it.key().thread,
			it.key().rip,
			it.value(),
			it.value()->defaultNext.thread,
			it.value()->defaultNext.rip,
			it.value()->defaultNextI,
			it.value()->branchNext.thread,
			it.value()->branchNext.rip,
			it.value()->branchNextI);
	}
}

template <typename ripType> template <typename targetType, targetType degrader(const ripType &)> EarlyRelocation<targetType> *
EarlyRelocation<ripType>::degrade()
{
	if (RipRelativeRelocation<ripType> *rrr =
	    dynamic_cast<RipRelativeRelocation<ripType> *>(this))
		return rrr->degrade<targetType, degrader>();
	else if (RipRelativeBranchRelocation<ripType> *rrbr =
		 dynamic_cast<RipRelativeBranchRelocation<ripType> *>(this))
		return rrbr->degrade<targetType, degrader>();
	else
		abort();
}

template <typename ripType> template <typename targetType, targetType degrader(const ripType &)> Instruction<targetType> *
Instruction<ripType>::degrade()
{
	Instruction<targetType> *work = new Instruction<targetType>();

	work->rip = degrader(rip);
	work->defaultNext = degrader(defaultNext);
	work->branchNext = degrader(branchNext);

	work->offsetInPatch = offsetInPatch;
	work->presentInPatch = presentInPatch;

	memcpy(work->content, content, len);
	work->len = len;
	work->pfx = pfx;
	work->nr_prefixes = nr_prefixes;

	work->relocs.resize(relocs.size());
	for (unsigned x = 0; x < relocs.size(); x++)
		work->relocs[x] = relocs[x]->degrade<targetType, degrader>();

	work->as = as;
	work->useful = useful;

	return work;
}

template <typename ripType> template <typename targetType, targetType degrader(const ripType &)> CFG<targetType> *
CFG<ripType>::degrade()
{
	std::map<Instruction<ripType> *, Instruction<targetType> *> trans;
	CFG<targetType> *work = new CFG<targetType>(as);

	for (typename ripToInstrT::iterator it = ripToInstr->begin();
	     it != ripToInstr->end();
	     it++) {
		ripType srcRip = it.key();
		Instruction<ripType> *src = it.value();
		Instruction<targetType> *dest;
		targetType destRip = degrader(srcRip);
		if (work->ripToInstr->hasKey(destRip)) {
			dest = work->ripToInstr->get(destRip);
		} else {
			dest = src->degrade<targetType, degrader>();
			work->ripToInstr->set(destRip, dest);
		}
		trans[src] = dest;
	}
	for (typename ripToInstrT::iterator it = ripToInstr->begin();
	     it != ripToInstr->end();
	     it++) {
		ripType srcRip = it.key();
		Instruction<ripType> *src = it.value();
		Instruction<targetType> *dest = work->ripToInstr->get(degrader(srcRip));
		assert(dest);

		Instruction<targetType> *d;
		if (src->branchNextI) {
			d = trans[src->branchNextI];
			assert(d);
			if (dest->branchNextI)
				assert(d == dest->branchNextI);
			else
				dest->branchNextI = d;
		}
		if (src->defaultNextI) {
			d = trans[src->defaultNextI];
			assert(d);
			if (dest->defaultNextI)
				assert(d == dest->defaultNextI);
			else
				dest->defaultNextI = d;
		}
	}
	return work;
}

#endif /* !GENFIX_H__ */
