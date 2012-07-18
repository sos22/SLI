#ifndef GENFIX_H__
#define GENFIX_H__

#define MAX_INSTRUCTION_SIZE 15

#include "libvex_ir.h"
#include "libvex_guest_offsets.h"
#include "library.hpp"

#include <set>
#include <map>

template <typename ripType> class CFG;
template <typename ripType> class EarlyRelocation;
class LateRelocation;
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
	static Prefixes rex_wide() {
		Prefixes r;
		r.rex_w = true;
		return r;
	}
	void rexByte(unsigned char b) {
		assert(b >= 0x40);
		assert(b < 0x50);
		rex_b = !!(b & 1);
		rex_x = !!(b & 2);
		rex_r = !!(b & 4);
		rex_w = !!(b & 8);
	}
	bool anything_set() const {
		return rex_w || rex_r || rex_x || rex_b;
	}
	unsigned char asByte() const {
		unsigned char res = 0x40;
		if (rex_w)
			res |= 8;
		if (rex_r)
			res |= 4;
		if (rex_x)
			res |= 2;
		if (rex_b)
			res |= 1;
		return res;
	}
};

class RegisterIdx {
	friend class RegisterOrOpcodeExtension;
	RegisterIdx() : idx(999) {}
	RegisterIdx(unsigned i) : idx(i) {}
public:
	unsigned idx;
	static const RegisterIdx RAX;
	static const RegisterIdx RCX;
	static const RegisterIdx RDX;
	static const RegisterIdx RBX;
	static const RegisterIdx RSP;
	static const RegisterIdx RBP;
	static const RegisterIdx RSI;
	static const RegisterIdx RDI;
	static const RegisterIdx R8;
	static const RegisterIdx R9;
	static const RegisterIdx R10;
	static const RegisterIdx R11;
	static const RegisterIdx R12;
	static const RegisterIdx R13;
	static const RegisterIdx R14;
	static const RegisterIdx R15;
	static RegisterIdx fromVexOffset(unsigned offset);
	static RegisterIdx fromRaw(unsigned offset) { return RegisterIdx(offset); }
	bool operator !=(const RegisterIdx &k) const { return idx != k.idx; }
	bool operator <(const RegisterIdx &o) const { return idx < o.idx; }
};

class RegisterOrOpcodeExtension {
	RegisterOrOpcodeExtension(unsigned k)
		: isOpcodeExtension(true), opcodeExtension(k)
	{}
public:
	RegisterOrOpcodeExtension(RegisterIdx &k)
		: isOpcodeExtension(false), idx(k)
	{}
	bool isOpcodeExtension;
	RegisterIdx idx;
	unsigned opcodeExtension;
	
	static RegisterOrOpcodeExtension opcode(unsigned k)
	{
		return RegisterOrOpcodeExtension(k);
	}
};

class ModRM {
	ModRM() : extendRm(false), extendIndex(false) {}
public:
	std::vector<unsigned char> content;
	bool extendRm;
	bool extendIndex;
	/* Access memory at address @reg + offset, where reg
	   is a register index and offset is a constant. */
	static ModRM memAtRegisterPlusOffset(RegisterIdx reg, int offset);
	/* Access memory at *(@reg) */
	static ModRM memAtRegister(RegisterIdx reg) { return memAtRegisterPlusOffset(reg, 0); }
	/* Access register @reg directly, not going through
	 * memory. */
	static ModRM directRegister(RegisterIdx reg);
	/* Access memory at a fixed 32 bit signed address */
	static ModRM absoluteAddress(int address);

	static ModRM fromBytes(const unsigned char *content);

	bool isRegister() const;
	RegisterIdx getRegister() const;
	RegisterIdx selectNonConflictingRegister() const;
};

template <typename ripType>
class Instruction : public GarbageCollected<Instruction<ripType>, &ir_heap > {
	unsigned char byte(AddressSpace *as);
	int int32(AddressSpace *as);
	void _modrm(unsigned nrImmediates, AddressSpace *as);
	void immediate(unsigned size, AddressSpace *as);
	int modrmExtension(AddressSpace *as);
	Instruction(const CfgLabel &_label)
		: label(_label), modrm_start(-1)
	{}
public:
	void addBranch(const ripType &r) {
		successors.push_back(successor_t::branch(r));
	}
	void addCall(const ripType &r) {
		successors.push_back(successor_t::call(r));
	}
	void addCall(Instruction *r) {
		successors.push_back(successor_t::call(r));
	}
	void addDefault(const ripType &r, LibraryFunctionType t = LibraryFunctionTemplate::none) {
		assert(!getDefault());
		successors.push_back(successor_t::dflt(r, t));
	}
	Instruction *addDefault(Instruction *r) {
		assert(!getDefault());
		successors.push_back(successor_t::dflt(r));
		return r;
	}
	Instruction *addBranch(Instruction *r) {
		successors.push_back(successor_t::branch(r));
		return r;
	}
	Instruction(int _modrm_start, const CfgLabel &_label)
		: label(_label),
		  modrm_start(_modrm_start)
	{ successors.reserve(2); }
	ripType rip;
	CfgLabel label;

	class successor_t {
	public:
		enum succ_type { succ_default, succ_branch, succ_call, succ_unroll };
	private:
		successor_t(succ_type _type,
			    const ripType &_rip,
			    Instruction *_instr,
			    LibraryFunctionType _calledFunction)
			: type(_type), rip(_rip), instr(_instr),
			  calledFunction(_calledFunction)
		{}
	public:
		succ_type type;
		ripType rip;
		Instruction *instr;
		LibraryFunctionType calledFunction;
		bool operator==(const successor_t &o) const {
			return type == o.type && rip == o.rip &&
				instr == o.instr && calledFunction == o.calledFunction;
		}
		successor_t() : type((succ_type)-1) {}
		static successor_t call(const ripType _rip)
		{
			return successor_t(succ_call, _rip,
					   NULL, LibraryFunctionTemplate::none);
		}
		static successor_t call(Instruction *i)
		{
			return successor_t(succ_call, ripType(), i, LibraryFunctionTemplate::none);
		}
		static successor_t branch(const ripType _rip)
		{
			return successor_t(succ_branch, _rip, NULL,
					   LibraryFunctionTemplate::none);
		}
		static successor_t branch(Instruction *i)
		{
			return successor_t(succ_branch, ripType(), i,
					   LibraryFunctionTemplate::none);
		}
		static successor_t dflt(const ripType _rip, LibraryFunctionType _calledFunction = LibraryFunctionTemplate::none)
		{
			return successor_t(succ_default, _rip, NULL,
					   _calledFunction);
		}
		static successor_t dflt(Instruction *i)
		{
			return successor_t(succ_default, ripType(), i,
					   LibraryFunctionTemplate::none);
		}
		static successor_t unroll(Instruction *i)
		{
			return successor_t(succ_unroll, ripType(), i,
					   LibraryFunctionTemplate::none);
		}
		static successor_t unroll(const ripType &_rip)
		{
			return successor_t(succ_unroll, _rip, NULL,
					   LibraryFunctionTemplate::none);
		}
	};
	std::vector<successor_t> successors;

	successor_t *getDefault() {
		successor_t *res = NULL;
		for (auto it = successors.begin(); it != successors.end(); it++) {
			if (it->type == successor_t::succ_default) {
				assert(!res);
				res = &*it;
			}
		}
		return res;
	}
	/* Doesn't really belong here, but it'll do for now. */
	unsigned offsetInPatch;
	bool presentInPatch;

	unsigned char content[MAX_INSTRUCTION_SIZE];
	unsigned len;
	Prefixes pfx;
	unsigned nr_prefixes;
	int modrm_start; /* or -1 if there's no modrm */
	std::vector<EarlyRelocation<ripType> *> relocs;
	std::vector<LateRelocation *> lateRelocs;

	bool useful;

	Instruction *dupe(const CfgLabel &l)
	{
		Instruction *w = new Instruction(l);
		*w = *this;
		w->label = l;
		return w;
	}
	static Instruction<ripType> *decode(const CfgLabel &label,
					    AddressSpace *as,
					    ripType rip,
					    CFG<ripType> *cfg);
	static Instruction<ripType> *pseudo(const CfgLabel &label, ripType rip);

	void emit(unsigned char);
	void emitDword(unsigned);
	void emitQword(unsigned long);
	void emitModrm(const ModRM &mrm, RegisterOrOpcodeExtension reg);

	void prettyPrint(FILE *f) const;

	void visit(HeapVisitor &hv) {
		visit_container(relocs, hv);
		visit_container(lateRelocs, hv);
		for (auto it = successors.begin(); it != successors.end(); it++)
			hv(it->instr);
	}
	void destruct() { this->~Instruction(); }
	NAMED_CLASS
};

class ClientRip;

unsigned long __trivial_hash_function(const ThreadRip &k);
struct DirectRip;
unsigned long __trivial_hash_function(const DirectRip &k);
unsigned long __trivial_hash_function(const ClientRip &k);
unsigned long __trivial_hash_function(const VexRip &k);
struct ThreadCfgLabel;
unsigned long __trivial_hash_function(const ThreadCfgLabel &x);
class C2PRip;
unsigned long __trivial_hash_function(const C2PRip &x);

template <typename ripType>
class CFG : public GarbageCollected<CFG<ripType>, &ir_heap > {
public:
	AddressSpace *as;
	/* Bad things happen if NULL gets into ripToInstr maps, so in
	   DEBUG builds assert that that doesn't happen. */
#ifdef NDEBUG
	typedef gc_map<ripType, Instruction<ripType> *, __trivial_hash_function,
		       __default_eq_function, __visit_function_heap, &ir_heap> ripToInstrT;
#else
	class ripToInstrT : public GarbageCollected<ripToInstrT, &ir_heap> {
		typedef gc_map<ripType, Instruction<ripType> *, __trivial_hash_function,
			       __default_eq_function, __visit_function_heap, &ir_heap> contentT;
		contentT *content;
	public:
		class iterator {
		public:
			class contentT::iterator content;
			iterator(class contentT::iterator _content)
				: content(_content)
			{}
			bool operator!=(const iterator &other) const {
				return content != other.content;
			}
			void operator++(int) {
				content++;
			}
			Instruction<ripType> *value() const { return content.value(); }
			ripType key() const { return content.key(); }
		};
		ripToInstrT() : content(new contentT()) {}
		void visit(HeapVisitor &hv) {
			hv(content);
		}

		Instruction<ripType> *get(const ripType &idx) {
			assert(content->hasKey(idx));
			return content->get(idx);
		}
		void set(const ripType &idx, Instruction<ripType> *const&r) {
			assert(r != NULL);
			content->set(idx, r);
		}
		bool hasKey(const ripType &k) { return content->hasKey(k); }
		iterator begin() const { return iterator(content->begin()); }
		iterator end() const { return iterator(content->end()); }
		iterator erase(const iterator &i) { return iterator(content->erase(i.content)); }
		size_t size() const { return content->size(); }
		NAMED_CLASS
	};
#endif
	ripToInstrT *ripToInstr;
private:
	std::vector<std::pair<ripType, unsigned> > pendingRips;
	std::vector<ripType> neededRips;
	void decodeInstruction(const CfgLabel &l, ripType rip, unsigned max_depth);
public:
	CFG(AddressSpace *_as) : as(_as), ripToInstr(new ripToInstrT()) {}
	void add_root(ripType root, unsigned max_depth)
	{
		pendingRips.push_back(std::pair<ripType, unsigned>(root, max_depth));
	}
	void doit(CfgLabelAllocator &);
	void visit(HeapVisitor &hv) {
		hv(ripToInstr);
		hv(as);
	}
	void registerInstruction(Instruction<ripType> *i) { ripToInstr->set(i->rip, i); }

	void print(FILE *logfile);

	virtual void destruct() { this->~CFG(); }
	NAMED_CLASS

	/* These can be overriden by derived classes to change the
	 * behaviour a bit. */

	/* Should we bother to explore instructions which follow this
	 * one?  If this returns true, direct followers of this
	 * instruction will be explored; indirect ones will not be
	 * (i.e. we only consider branches whose target is statically
	 * constant). */
	virtual bool exploreInstruction(Instruction<ripType> *) { return true; }
	/* We've discovered a direct-called function.  Should we
	 * explore the callee?  Indirect calls are never explored. */
	virtual bool exploreFunction(ripType ) { return false; }
	/* Is this instruction useful?  Once the CFG is built, we do a
	 * post-pass which walks the list of instructions, and uses
	 * this to decide whether instructions are useful.  We then
	 * walk backwards through the CFG and mark any instruction
	 * which can reach a useful instruction as being useful
	 * itself.  Finally, any non-useful instructions are replaced
	 * with branches back into the original code.
	 */
	virtual bool instructionUseful(Instruction<ripType> *) { return true; }
};

template <typename ripType>
class PatchFragment : public GarbageCollected<PatchFragment<ripType>, &ir_heap > {
	std::vector<Instruction<ripType> *> registeredInstrs;
	std::set<ripType> entryPoints;

protected:
	std::vector<EarlyRelocation<ripType> *> relocs;
	std::vector<LateRelocation *> lateRelocs;
	CFG<ripType> *cfg;
	std::vector<unsigned char> content;

private:
	Instruction<ripType> *nextInstr(CFG<ripType> *cfg);
	void emitStraightLine(Instruction<ripType> *i);

protected:

	void emitByte(unsigned char b) { content.push_back(b); }
	void emitDword(unsigned val);
	void emitQword(unsigned long val);

	void emitModrm(const ModRM &mrm, RegisterOrOpcodeExtension reg);

	/* Emit a jump to an offset in the current fragment. */
	void emitJmpToOffset(unsigned offset);
	void emitJmpToRipClient(ripType rip);
	void emitJmpToRipHost(unsigned long rip);

	/* Emit a simple opcode which uses a modrm but no immediates
	 * and is 64 bits.  This corresponds to the Ev,Gv and Gv,Ev
	 * encodings in the architecture manual. */
	void emitNoImmediatesModrmOpcode(unsigned opcode, RegisterOrOpcodeExtension reg, const ModRM &rm);

	/* Store a register to a modrm. */
	void emitMovRegisterToModrm(RegisterIdx reg, const ModRM &rm);
	/* Load a register from a modrm */
	void emitMovModrmToRegister(const ModRM &rm, RegisterIdx reg);
	/* Add a register to a modrm */
	void emitAddRegToModrm(RegisterIdx reg, const ModRM &rm);
	/* Add a modrm to a register */
	void emitAddModrmToReg(const ModRM &rm, RegisterIdx reg);
	/* Compare a register to a modrm */
	void emitCmpRegModrm(RegisterIdx reg, const ModRM &rm);
	/* Negate a modrm */
	void emitNegModrm(const ModRM &rm);

	void emitLea(const ModRM &modrm, RegisterIdx reg);

	void emitCallSequence(const char *target);
	void skipRedZone();
	void restoreRedZone();
	void emitPushQ(RegisterIdx);
	void emitPushImm32(int what);
	void emitPopQ(RegisterIdx);
	void emitMovQ(RegisterIdx, unsigned long);
	void emitCallReg(RegisterIdx);
public:
	PatchFragment(const std::set<ripType> &_entryPoints)
		: entryPoints(_entryPoints)
	{}

	void fromCFG(CfgLabelAllocator &, CFG<ripType> *cfg);

	bool ripToOffset(ripType rip, unsigned *res);
	void writeBytes(const void *bytes, unsigned size, unsigned offset);
	void addLateReloc(LateRelocation *m) { lateRelocs.push_back(m); }

	/* Just the core patch itself, not including the metdata tables. */
	char *asC(const char *ident, char **relocs_name, char **trans_name, char **content_name) const;
	/* The whole patch, including metadata tables. */
	char *asC(const char *ident) const;

	void visit(HeapVisitor &hv) {
		visit_container(relocs, hv);
		visit_container(lateRelocs, hv);
	}
	void destruct() { this->~PatchFragment(); }
	NAMED_CLASS

	/* Can be overridden by derived classes which need to do
	 * something special when we return to untranslated code.
	 * This is only invoked for statically constant branches; if
	 * you want to do anything with non-constant branches then
	 * you'll need to override emitInstruction() as well.
	 */
	virtual void generateEpilogue(const CfgLabel &l, ripType exitRip);

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
class EarlyRelocation : public GarbageCollected<EarlyRelocation<ripType>, &ir_heap >,
			public Named {
public:
	unsigned offset;
	unsigned size;
	EarlyRelocation(unsigned _offset, unsigned _size)
		: offset(_offset), size(_size) {}
	virtual void doit(CfgLabelAllocator &, PatchFragment<ripType> *pf) = 0;
	void visit(HeapVisitor &) {}
	void destruct() {}
	NAMED_CLASS
};

class LateRelocation : public GarbageCollected<LateRelocation, &ir_heap>,
		       public Named {
	char *mkName() const {
		return my_asprintf("lr(offset = %d, size = %d, target = %s, nrImmediate = %d, %s)",
				   offset,
				   size,
				   target,
				   nrImmediateBytes,
				   relative ? "relative" : "absolute");
	}
public:
	unsigned offset;
	unsigned size;
	const char *target;
	unsigned nrImmediateBytes;
	bool relative;

	LateRelocation(unsigned _offset, unsigned _size,
		       const char *_target, unsigned _nrImmediateBytes,
		       bool _relative)
		: offset(_offset), size(_size), target(_target),
		  nrImmediateBytes(_nrImmediateBytes),
		  relative(_relative)
	{}

	char *asC() const {
		return vex_asprintf("{0x%x, 0x%x, %d, %d, %s}",
				    offset, size,
				    relative ? -nrImmediateBytes - size : 0,
				    relative, target);
	}

	void visit(HeapVisitor &hv) { hv(target); }
	NAMED_CLASS
};

template <typename r> void
Instruction<r>::emit(Byte b)
{
	assert(len < MAX_INSTRUCTION_SIZE);
	content[len] = b;
	len++;
}

template <typename r> void
Instruction<r>::emitQword(unsigned long v)
{
	union {
		Byte bytes[8];
		unsigned long v;
	} u;

	u.v = v;
	memcpy(content + len, u.bytes, 8);
	len += 8;
	assert(len <= MAX_INSTRUCTION_SIZE);
}

template <typename r> void
Instruction<r>::emitDword(unsigned v)
{
	union {
		Byte bytes[4];
		unsigned long v;
	} u;

	u.v = v;
	memcpy(content + len, u.bytes, 4);
	len += 4;
	assert(len <= MAX_INSTRUCTION_SIZE);
}

template <typename r> void
Instruction<r>::emitModrm(const ModRM &rm, RegisterOrOpcodeExtension reg)
{
	if (reg.isOpcodeExtension) {
		assert(reg.opcodeExtension < 8);
		emit(rm.content[0] | (reg.opcodeExtension << 3));
	} else {
		assert(reg.idx.idx < 8);
		emit(rm.content[0] | (reg.idx.idx << 3));
	}
	for (unsigned x = 1; x < rm.content.size(); x++)
		emit(rm.content[x]);
}

template <typename r> Byte
Instruction<r>::byte(AddressSpace *as)
{
	unsigned long t;
	t = 0;
	as->readMemory(rip.unwrap_vexrip() + len, 1, &t, false, NULL);
	Byte b = t;
	emit(b);
	return b;
}

template <typename r> int
Instruction<r>::int32(AddressSpace *as)
{
	unsigned long t[4];
	as->readMemory(rip.unwrap_vexrip() + len, 4, t, false, NULL);
	emit(t[0]);
	emit(t[1]);
	emit(t[2]);
	emit(t[3]);
	return t[0] | (t[1] << 8) | (t[2] << 16) | (t[3] << 24);
}

template <typename r> void
Instruction<r>::immediate(unsigned size, AddressSpace *as)
{
	for (unsigned x = 0; x < size; x++)
		byte(as);
}

template <typename r> int
Instruction<r>::modrmExtension(AddressSpace *as)
{
	Byte b = byte(as);
	len--;
	return (b >> 3) & 7;
}

template <typename r>
class RipRelativeRelocation : public EarlyRelocation<r> {
	char *mkName() const {
		return my_asprintf("rrr(offset = %d, size = %d, target = %s, nrImmediate = %d)",
				   this->offset,
				   this->size,
				   target.name(),
				   nrImmediateBytes);
	}
public:
	r target;
	unsigned nrImmediateBytes;

	void doit(CfgLabelAllocator &, PatchFragment<r> *pf);

	RipRelativeRelocation(unsigned _offset,
			      unsigned _size,
			      r _target,
			      unsigned _nrImmediateBytes)
		: EarlyRelocation<r>(_offset, _size),
		  target(_target),
		  nrImmediateBytes(_nrImmediateBytes)
	{
	}
};

template <typename r>
class RipRelativeDataRelocation : public EarlyRelocation<r> {
	char *mkName() const {
		return my_asprintf("rrdr(offset = %d, size = %d, target = 0x%lx, nrImmediate = %d)",
				   this->offset,
				   this->size,
				   target,
				   nrImmediateBytes);
	}
public:
	unsigned long target;
	unsigned nrImmediateBytes;
	void doit(CfgLabelAllocator &, PatchFragment<r> *pf);
	RipRelativeDataRelocation(unsigned _offset,
				  unsigned _size,
				  unsigned long _target,
				  unsigned _nrImmediateBytes)
		: EarlyRelocation<r>(_offset, _size),
		  target(_target),
		  nrImmediateBytes(_nrImmediateBytes)
	{
	}
};

template <typename r>
class RipRelativeBranchRelocation : public EarlyRelocation<r> {
	char *mkName() const {
		return my_asprintf("rrbr(offset = %d, size = %d, target = %s)",
				   this->offset,
				   this->size,
				   target.name());
	}
public:
	r target;
	void doit(CfgLabelAllocator &, PatchFragment<r> *pf);
	RipRelativeBranchRelocation(unsigned _offset,
				    unsigned _size,
				    r _target)
		: EarlyRelocation<r>(_offset, _size),
		  target(_target)
	{
	}
};

template <typename r> void
Instruction<r>::_modrm(unsigned nrImmediates, AddressSpace *as)
{
	modrm_start = len;

	Byte modrm = byte(as);
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
		immediate(4, as);
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
		Byte sib = byte(as);
		if ((sib & 7) == 5)
			dispBytes = 4;
	}
	if (mod == 1)
		dispBytes = 1;
	else if (mod == 2)
		dispBytes = 4;
	immediate(dispBytes, as);
}

template <typename r> Instruction<r> *
Instruction<r>::pseudo(const CfgLabel &label, r rip)
{
	Instruction<r> *i = new Instruction<r>(label);
	i->rip = rip;
	return i;
}

template <typename r> Instruction<r> *
Instruction<r>::decode(const CfgLabel &label,
		       AddressSpace *as,
		       r start,
		       CFG<r> *cfg)
{
	Instruction<r> *i = new Instruction<r>(label);
	i->rip = start;
	Byte b;
	while (1) {
		b = i->byte(as);
		if (b < 0x40 || b > 0x4f)
			break;
		i->pfx.rexByte(b);
		i->nr_prefixes++;
	}
	bool fallsThrough = true;
	char delta;
	int delta32;
	bool opsize = false;
	bool repne = false;
	bool repe = false;

top:
	switch (b) {
	case 0x00 ... 0x3f:
		if (b != 0x0f) {
			switch (b & 7) {
			case 0 ... 3:
				i->_modrm(0, as);
				break;
			case 4:
				i->immediate(1, as);
				break;
			case 5:
				if (opsize)
					i->immediate(2, as);
				else
					i->immediate(4, as);
				break;
			case 6:
				b = i->byte(as);
				goto top;
			case 7:
				/* Not allowed in 64-bit mode */
				fail("Instruction %02x is not allowed in 64 bit code\n",
				     b);
			}
			break;
		}
		/* Two-byte instructions */
		b = i->byte(as);
		switch (b) {
		case 0x80 ... 0x8f: { /* 32 bit conditional jumps. */
			delta32 = i->int32(as);
			r target = i->rip + i->len + delta32;
			i->addBranch(target);
			i->relocs.push_back(new RipRelativeBranchRelocation<r>(i->len - 4, 4, target));
			/* Unlike 8 bit jumps, we don't need to set
			   fallsThrough here, because the normal
			   defaultNext calculation will do the right
			   thing, because the output instruction is
			   the same size as the input one. */
			break;
		}

		case 0x30 ... 0x3f: /* wrmsr, rdmsr, sysenter, etc.
				     * An opcode with no operands. */
			break;

		case 0x10 ... 0x17: /* Various flavours of mov */
		case 0x18: /* prefetch, in its multitudinous forms */
		case 0x19 ... 0x1f: /* nop Ev */
		case 0x20 ... 0x27: /* move to and from control and debug registers */
		case 0x28 ... 0x2f: /* various xmm instructions which take a simple modrm */
		case 0x40 ... 0x4f: /* CMOVcc Gv,Ev */
		case 0x50 ... 0x6f: /* Yet more xmm instructions using a simple modrm */
		case 0x90 ... 0x9f: /* setcc Eb */
		case 0xaf: /* imul Gv, Ev */
		case 0xb0: /* cmpxchg Eb, Gb  */
		case 0xb1: /* cmpxchg Ev, Gv  */
		case 0xb6: /* movzx Gv, Eb */
		case 0xb7: /* movzw Gv, Ew */
		case 0xbe: /* movsb Gv, Eb */
		case 0xbf: /* movsb Gv, Ew */
		case 0xc0: /* xadd Eb, Gb */
		case 0xc1: /* xadd Ev, Gv */
			i->_modrm(0, as);
			break;
		default:
			throw NotImplementedException("cannot decode instruction starting 0x0f 0x%02x at %s\n",
						      b, i->rip.name());
		}
		break;

	case 0x40 ... 0x5f:
	case 0xa4 ... 0xa7: /* movs, cmps. */
	case 0xaa ... 0xaf: /* stos, lods, scas */
	case 0xcc:
	case 0xc9:
	case 0x90 ... 0x9f:
		break;

	case 0x64: /* FS prefix.  Pass it through verbatim. */
	case 0xf0: /* Lock prefix.  Pass it through verbatim.  At this
		      stage, we're only really interested in
		      instruction size and control flow, so LOCKs
		      don't matter. */
		b = i->byte(as);
		goto top;

	case 0xd0 ... 0xd3: /* Shift group 2*/
	case 0x84 ... 0x8e:
	case 0x63: /* Move with sign extend. */
		i->_modrm(0, as);
		break;

	case 0xff: /* Group 5 */
		if (i->modrmExtension(as) == 2) {
			i->successors.push_back(
				Instruction<r>::successor_t::call(r()));
		}
		i->_modrm(0, as);
		break;

	case 0x66: /* opsize prefix */
		opsize = !opsize;
		b = i->byte(as);
		goto top;

	case 0x68: /* push Iz */
		if (opsize)
			i->immediate(2, as);
		else
			i->immediate(4, as);
		break;

	case 0x70 ... 0x7f: {
		/* 8 bit conditional jumps are handled specially, by
		   turning them into 32-bit conditional jumps, because
		   that simplifies a lot of relocation-related
		   stuff. */
		/* Decode the instruction... */
		delta = i->byte(as);
		r fallThrough = i->rip + i->len;
		r target = fallThrough + delta;
		i->addDefault(fallThrough);
		i->addBranch(target);

		/* Now rewind and emit the 32 bit version. */
		i->len = 0;
		i->emit(0x0f);
		i->emit(b + 0x10);
		i->relocs.push_back(new RipRelativeBranchRelocation<r>(i->len, 4, target));
		i->len += 4;

		/* Don't let the tail update defaultNext */
		fallsThrough = false;
		break;
	}
	case 0x69: /* imul gv,ev,iz */
	case 0x81:
	case 0xc7:
		if (opsize) {
			i->_modrm(2, as);
			i->immediate(2, as);
		} else {
			i->_modrm(4, as);
			i->immediate(4, as);
		}
		break;

	case 0xb0 ... 0xb7:
		i->immediate(1, as);
		break;

	case 0xb8 ... 0xbf:
		if (i->pfx.rex_w) {
			i->immediate(8, as);
		} else if (opsize) {
			i->immediate(2, as);
		} else {
			i->immediate(4, as);
		}
		break;

	case 0x6b: /* imul gv, ev, ib */
	case 0x80:
	case 0x82:
	case 0x83:
	case 0xc0:
	case 0xc1: /* Shift group 2 with an Ib */
	case 0xc6:
		i->_modrm(1, as);
		i->immediate(1, as);
		break;

	case 0xc3:
		fallsThrough = false;
		break;

	case 0xe8: { /* Call instruction. */
		i->immediate(4, as);
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
		if (cfg && cfg->exploreFunction(target))
			i->addCall(target);
		break;
	}
	case 0xe9: /* jmp rel32 */
		delta32 = i->int32(as);
		i->addDefault(i->rip + i->len + delta32);
		i->len = 0;
		fallsThrough = false;
		break;

	case 0xeb: /* jmp rel8 */
		delta = i->byte(as);
		i->addDefault(i->rip + i->len + delta);

		/* Don't emit this instruction at all; if it's useful,
		 * we'll synthesise an appropriate jump later on.
		 * Otherwise, we'll eliminate it with jump
		 * threading. */
		i->len = 0;

		/* Don't let the tail update defaultNext */
		fallsThrough = false;
		break;

	case 0xf2:
		repne = true;
		b = i->byte(as);
		goto top;

	case 0xf3:
		repe = true;
		b = i->byte(as);
		goto top;

	case 0xf7: /* Unary group 3 Ev */
		if (i->modrmExtension(as) == 0) {
			if (opsize) {
				i->_modrm(2, as);
				i->immediate(2, as);
			} else {
				i->_modrm(4, as);
				i->immediate(4, as);
			}
		} else {
			i->_modrm(0, as);
		}
		break;

	default:
		throw NotImplementedException("cannot decode instruction starting %x at %s\n",
					      b, i->rip.name());
	}

	if (fallsThrough)
		i->addDefault(i->rip + i->len);

	return i;
}

template <typename r> void
CFG<r>::decodeInstruction(const CfgLabel &l, r rip, unsigned max_depth)
{
	if (!max_depth)
		return;
	Instruction<r> *i = Instruction<r>::decode(l, as, rip, this);
	if (!i)
		return;
	assert(i->rip == rip);
	registerInstruction(i);
	if (exploreInstruction(i)) {
		for (auto it = i->successors.begin(); it != i->successors.end(); it++)
			pendingRips.push_back(std::pair<r, unsigned>(
						      it->rip, max_depth - 1));
	}
}

template <typename r> void
CFG<r>::doit(CfgLabelAllocator &allocLabel)
{
	while (!pendingRips.empty()) {
		std::pair<r, unsigned> p = pendingRips.back();
		pendingRips.pop_back();
		if (!ripToInstr->hasKey(p.first))
			decodeInstruction(allocLabel(), p.first, p.second);
	}

	for (typename ripToInstrT::iterator it = ripToInstr->begin();
	     it != ripToInstr->end();
	     it++) {
		Instruction<r> *ins = it.value();
		ins->useful = instructionUseful(ins);
		for (auto it2 = ins->successors.begin(); it2 != ins->successors.end(); it2++) {
			if (ripToInstr->hasKey(it2->rip)) {
				Instruction<r> *dn = ripToInstr->get(it2->rip);
				it2->rip = r();
				it2->instr = dn;
				if (dn->useful)
					ins->useful = true;
			}
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
			for (auto it2 = i->successors.begin(); it2 != i->successors.end(); it2++) {
				if (it2->instr && it2->instr->useful) {
					i->useful = true;
					progress = true;
				}
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
			for (auto it2 = i->successors.begin(); it2 != i->successors.end(); it2++) {
				if (it2->instr && !it2->instr->useful) {
					it2->rip = it2->instr->rip;
					it2->instr = NULL;
				}
			}
			it++;
		} else {
			it = ripToInstr->erase(it);
		}
	}
}

template <typename r> void
RipRelativeRelocation<r>::doit(CfgLabelAllocator &, PatchFragment<r> *pf)
{
	unsigned targetOffset;
	if (pf->ripToOffset(target, &targetOffset)) {
		long delta = targetOffset - this->offset - nrImmediateBytes - this->size;
		pf->writeBytes(&delta, this->size, this->offset);
	} else {
		pf->addLateReloc(new LateRelocation(this->offset, this->size,
						    vex_asprintf("0x%lx",target.unwrap_vexrip()),
						    nrImmediateBytes, true));
	}
}

template <typename r> void
RipRelativeDataRelocation<r>::doit(CfgLabelAllocator &, PatchFragment<r> *pf)
{
	pf->addLateReloc(new LateRelocation(this->offset,
					    this->size,
					    vex_asprintf("0x%lx",target),
					    nrImmediateBytes,
					    true));
}

template <typename r> void
RipRelativeBranchRelocation<r>::doit(CfgLabelAllocator &allocLabel, PatchFragment<r> *pf)
{
	unsigned targetOffset;
	if (!pf->ripToOffset(target, &targetOffset))
		pf->generateEpilogue(allocLabel(), target);
	if (!pf->ripToOffset(target, &targetOffset))
		fail("Failed to generate epilogue for %s\n", target.name());
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
		for (auto it2 = it->first->successors.begin(); it2 != it->first->successors.end(); it2++) {
			if (it2->type == Instruction<r>::successor_t::succ_default &&
			    it2->instr) {
				pendingInstructions[it2->instr] = false;
				break;
			}
		}
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
	Instruction<r> *i = cfg->ripToInstr->get(rip);
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
PatchFragment<r>::fromCFG(CfgLabelAllocator &allocLabel, CFG<r> *_cfg)
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

		re->doit(allocLabel, this);
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
	for (auto it = i->lateRelocs.begin();
	     it != i->lateRelocs.end();
	     it++) {
		(*it)->offset += offset;
		lateRelocs.push_back(*it);
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
	lateRelocs.push_back(new LateRelocation(content.size() - 4, 4,
						vex_asprintf("0x%lx", rip),
						0,
						true));
}

template <typename r> void
PatchFragment<r>::emitLea(const ModRM &modrm, RegisterIdx reg)
{
	if (reg.idx >= 8) {
		emitByte(0x49);
		reg.idx -= 8;
	} else {
		emitByte(0x48);
	}
	emitByte(0x8d);
	emitModrm(modrm, reg);
}

template <typename r> void
PatchFragment<r>::skipRedZone()
{
	emitLea(ModRM::memAtRegisterPlusOffset(RegisterIdx::RSP, -128),
		RegisterIdx::RSP);
}

template <typename r> void
PatchFragment<r>::restoreRedZone()
{
	emitLea(ModRM::memAtRegisterPlusOffset(RegisterIdx::RSP, 128),
		RegisterIdx::RSP);
}

template <typename r> void
PatchFragment<r>::emitPushQ(RegisterIdx reg)
{
	if (reg.idx >= 8) {
		emitByte(0x41);
		reg.idx -= 8;
	}
	assert(reg.idx < 8);
	emitByte(0x50 + reg.idx);
}

template <typename r> void
PatchFragment<r>::emitPushImm32(int val)
{
	emitByte(0x68);
	emitDword(val);
}

template <typename r> void
PatchFragment<r>::emitPopQ(RegisterIdx reg)
{
	if (reg.idx >= 8) {
		emitByte(0x41);
		reg.idx -= 8;
	}
	assert(reg.idx < 8);
	emitByte(0x58 + reg.idx);
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

static inline void
__emitDword_toBytes(unsigned x, Byte b[4])
{
	union {
		unsigned asUint;
		Byte asBytes[4];
	};
	asUint = x;
	memcpy(b, asBytes, 4);
}
template <typename r> void
PatchFragment<r>::emitDword(unsigned val)
{
	Byte asBytes[4];
	__emitDword_toBytes(val, asBytes);
	for (unsigned x = 0; x < 4; x++)
		emitByte(asBytes[x]);
}

/* Move immediate 64 bit to register. */
template <typename r> void
PatchFragment<r>::emitMovQ(RegisterIdx reg, unsigned long val)
{
	if (reg.idx < 8) {
		emitByte(0x48);
	} else {
		emitByte(0x49);
		reg.idx -= 8;
	}
	assert(reg.idx < 8);
	emitByte(0xb8 + reg.idx);
	emitQword(val);
}

template <typename r> void
PatchFragment<r>::emitModrm(const ModRM &rm, RegisterOrOpcodeExtension reg)
{
	if (reg.isOpcodeExtension) {
		assert(reg.opcodeExtension < 8);
		emitByte(rm.content[0] | (reg.opcodeExtension << 3));
	} else {
		assert(reg.idx.idx < 8);
		emitByte(rm.content[0] | (reg.idx.idx << 3));
	}
	for (unsigned x = 1; x < rm.content.size(); x++)
		emitByte(rm.content[x]);
}

template <typename r> void
PatchFragment<r>::emitNoImmediatesModrmOpcode(unsigned opcode, RegisterOrOpcodeExtension reg, const ModRM &rm)
{
	unsigned char rex = 0x48;
	if (!reg.isOpcodeExtension && reg.idx.idx >= 8) {
		rex |= 4;
		reg.idx.idx -= 8;
		assert(reg.idx.idx < 8);
	}
	if (rm.extendRm)
		rex |= 1;
	emitByte(rex);
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
PatchFragment<r>::emitMovRegisterToModrm(RegisterIdx reg, const ModRM &rm)
{
	emitNoImmediatesModrmOpcode(0x89, reg, rm);
}

template <typename r> void
PatchFragment<r>::emitMovModrmToRegister(const ModRM &rm, RegisterIdx reg)
{
	emitNoImmediatesModrmOpcode(0x8B, reg, rm);
}

template <typename r> void
PatchFragment<r>::emitAddRegToModrm(RegisterIdx reg, const ModRM &rm)
{
	emitNoImmediatesModrmOpcode(0x01, reg, rm);
}

template <typename r> void
PatchFragment<r>::emitAddModrmToReg(const ModRM &rm, RegisterIdx reg)
{
	emitNoImmediatesModrmOpcode(0x03, reg, rm);
}

template <typename r> void
PatchFragment<r>::emitCmpRegModrm(RegisterIdx reg, const ModRM &rm)
{
	emitNoImmediatesModrmOpcode(0x3B, reg, rm);
}

template <typename r> void
PatchFragment<r>::emitNegModrm(const ModRM &rm)
{
	emitNoImmediatesModrmOpcode(0xF7, RegisterOrOpcodeExtension::opcode(3), rm);
}

template <typename r> void
PatchFragment<r>::emitCallReg(RegisterIdx reg)
{
	if (reg.idx >= 8) {
		emitByte(0x41);
		reg.idx -= 8;
	}
	emitByte(0xff);
	emitModrm(ModRM::directRegister(reg), RegisterOrOpcodeExtension::opcode(2));
}

template <typename r> void
PatchFragment<r>::emitCallSequence(const char *target)
{
	skipRedZone();

	emitPushQ(RegisterIdx::RSI);
	emitMovQ(RegisterIdx::RSI, 0);
	lateRelocs.push_back(new LateRelocation(content.size() - 8,
						8,
						vex_asprintf("%s", target),
						0,
						false));
	emitCallReg(RegisterIdx::RSI);
	emitPopQ(RegisterIdx::RSI);
	
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
		
		typename Instruction<r>::successor_t *next = NULL;
		for (auto it = i->successors.begin(); it != i->successors.end(); it++) {
			if (it->type == Instruction<r>::successor_t::succ_default) {
				assert(!next);
				next = &*it;
			}
		}
		if (!next || !next->instr) {
			/* Hit end of block, and don't want to go any
			 * further.  Return to the original code. */
			if (next && next->rip.isValid()) {
				emitJmpToRipClient(next->rip);
			} else {
				/* Last instruction in the block was
				   an unpredictable branch, which
				   we'll just have emitted verbatim,
				   so we don't need to do any more. */
			}
			return;
		}

		i = next->instr;
	}
}

char *flattenStringFragments(std::vector<const char *> fragments);

template <typename r> char *
PatchFragment<r>::asC(const char *ident, char **relocs_name, char **trans_name, char **content_name) const
{
	std::vector<const char *> fragments;
	char *content_buf = (char *)LibVEX_Alloc_Bytes(content.size() * 4 + 1);
	for (unsigned x = 0; x < content.size(); x++)
		sprintf(content_buf + x * 4, "\\x%02x", content[x]);
	*relocs_name = vex_asprintf("__%s_reloc", ident);
	*content_name = vex_asprintf("__%s_patch_content", ident);
	fragments.push_back(vex_asprintf("static const unsigned char %s[] = \"%s\";\n\n"
					 "static const struct relocation %s[] = {\n",
					 *content_name,
					 content_buf,
					 *relocs_name));
	for (auto it = lateRelocs.begin(); it != lateRelocs.end(); it++)
		fragments.push_back(vex_asprintf("\t%s,\n", (*it)->asC()));

	*trans_name = vex_asprintf("__%s__trans_table", ident);
	fragments.push_back(vex_asprintf("};\n\nstatic const struct trans_table_entry %s[] = {\n",
					 *trans_name));
	for (typename std::vector<Instruction<r> *>::const_iterator it = registeredInstrs.begin();
	     it != registeredInstrs.end();
	     it++)
		fragments.push_back(vex_asprintf("\t{0x%lx, 0x%x}, /* %s */\n",
						 (*it)->rip.unwrap_vexrip(),
						 (*it)->offsetInPatch,
						 (*it)->rip.name()));
	fragments.push_back("};\n");
	return flattenStringFragments(fragments);
}

template <typename r> void
PatchFragment<r>::generateEpilogue(const CfgLabel &l, r exitRip)
{
	Instruction<r> *i = Instruction<r>::pseudo(l, exitRip);
	cfg->registerInstruction(i);
	registerInstruction(i, content.size());
	emitJmpToRipHost(exitRip.unwrap_vexrip());
}

void __genfix_add_array_summary(std::vector<const char *> &out,
				const char *t_ptr,
				const char *nr_entries,
				const char *table);

template <typename r> char *
PatchFragment<r>::asC(const char *ident) const
{
	std::vector<const char *> fragments;
	char *relocs_name;
	char *trans_name;
	char *content_name;
	char *entry_table_name;
	fragments.push_back(asC(ident, &relocs_name, &trans_name, &content_name));
	entry_table_name = vex_asprintf("__%s_entry_points", ident);
	fragments.push_back("static struct patch_entry_point ");
	fragments.push_back(entry_table_name);
	fragments.push_back("[] = {\n");
	for (typename std::set<r>::iterator it = entryPoints.begin();
	     it != entryPoints.end();
	     it++) {
		Instruction<r> *i = cfg->ripToInstr->get(*it);
		assert(i);
		fragments.push_back(vex_asprintf("\t{0x%lx, %d},\n", it->rip.unwrap_vexrip(), i->offsetInPatch));
	}
	fragments.push_back("};\n\nstatic struct patch ");
	fragments.push_back(ident);
	fragments.push_back(" = {\n");

	__genfix_add_array_summary(fragments, "relocations", "nr_relocations", relocs_name);
	__genfix_add_array_summary(fragments, "trans_table", "nr_translations", trans_name);
	__genfix_add_array_summary(fragments, "entry_points", "nr_entry_points", entry_table_name);
	__genfix_add_array_summary(fragments, "content", "content_size", content_name);
	fragments.push_back("};\n");

	return flattenStringFragments(fragments);
}

template <typename r> void
CFG<r>::print(FILE *f)
{
	for (typename ripToInstrT::iterator it = ripToInstr->begin();
	     it != ripToInstr->end();
	     it++) {
		fprintf(f, "%s[%p] -> ",
			it.key().name(),
			it.value());
		for (auto it2 = it.value()->successors.begin();
		     it2 != it.value()->successors.end();
		     it2++) {
			const char *t = NULL;
			switch (it2->type) {
			case Instruction<r>::successor_t::succ_default:
				t = "default";
				break;
			case Instruction<r>::successor_t::succ_branch:
				t = "branch";
				break;
			case Instruction<r>::successor_t::succ_call:
				t = "call";
				break;
			case Instruction<r>::successor_t::succ_unroll:
				t = "unroll";
				break;
			}
			if (t == NULL)
				t = "BAD";
			if (it2 != it.value()->successors.begin())
				fprintf(f, ", ");
			fprintf(f, "%s:%s[%p]", t, it2->rip.name(), it2->instr);
		}
		fprintf(f, "\n");
	}
}

template <typename r> void
Instruction<r>::prettyPrint(FILE *f) const
{
	fprintf(f, "instr(%s, %s, %d bytes content, %s, %s, successors = {",
		label.name(),
		rip.name(),
		len,
		useful ? "useful" : "useless",
		presentInPatch ? "in patch" : "not in patch");
	for (auto it = successors.begin();
	     it != successors.end();
	     it++) {
		if (it != successors.begin())
			fprintf(f, ", ");
		const char *t = NULL;
		switch (it->type) {
		case successor_t::succ_default:
			t = "default";
			break;
		case successor_t::succ_branch:
			t = "branch";
			break;
		case successor_t::succ_call:
			t = "call";
			break;
		case successor_t::succ_unroll:
			t = "unroll";
			break;
		}
		fprintf(f, "%s:%s:%p", it->instr ? it->instr->label.name() : "<null>", t, it->instr);
		if (it->calledFunction != LibraryFunctionTemplate::none)
			LibraryFunctionTemplate::pp(it->calledFunction, f);
	}
	fprintf(f, "}\n");
}

#endif /* !GENFIX_H__ */
