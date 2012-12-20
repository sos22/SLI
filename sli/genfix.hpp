#ifndef GENFIX_H__
#define GENFIX_H__

#define MAX_INSTRUCTION_SIZE 15

#include "libvex_ir.h"
#include "libvex_guest_offsets.h"
#include "library.hpp"
#include "cfgnode.hpp"
#include "map.h"

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
	/* Access register @reg directly, not going through
	 * memory. */
	static ModRM directRegister(RegisterIdx reg);
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
	Instruction(int _modrm_start, const CfgLabel &_label)
		: label(_label),
		  modrm_start(_modrm_start)
	{ successors.reserve(2); }
	ripType rip;
	CfgLabel label;

	class successor_t {
	public:
		successor_t(CfgSuccessorType _type,
			    const ripType &_rip,
			    Instruction *_instr,
			    LibraryFunctionType _calledFunction)
			: type(_type), rip(_rip), instr(_instr),
			  calledFunction(_calledFunction)
		{}
		CfgSuccessorType type;
		ripType rip;
		Instruction *instr;
		LibraryFunctionType calledFunction;
		successor_t() : type((CfgSuccessorType)-1) {}
		static successor_t dflt(Instruction *i)
		{
			return successor_t(succ_default, ripType(), i,
					   LibraryFunctionTemplate::none);
		}
	};
	std::vector<successor_t> successors;

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

	static Instruction<ripType> *pseudo(const CfgLabel &label, ripType rip);

	void visit(HeapVisitor &hv) {
		visit_container(relocs, hv);
		visit_container(lateRelocs, hv);
		for (auto it = successors.begin(); it != successors.end(); it++)
			hv(it->instr);
	}
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
public:
	CFG(AddressSpace *_as) : as(_as), ripToInstr(new ripToInstrT()) {}
	void visit(HeapVisitor &hv) {
		hv(ripToInstr);
		hv(as);
	}
	NAMED_CLASS
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

public:
	PatchFragment(const std::set<ripType> &_entryPoints)
		: entryPoints(_entryPoints)
	{}

	void visit(HeapVisitor &hv) {
		visit_container(relocs, hv);
		visit_container(lateRelocs, hv);
	}
	NAMED_CLASS
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
	{
	}

	char *asC() const {
		return vex_asprintf("{0x%x, 0x%x, %d, %d, %s}",
				    offset, size,
				    relative ? -nrImmediateBytes - size : 0,
				    relative, target);
	}

	void visit(HeapVisitor &hv) { hv(target); }
	NAMED_CLASS
};

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

template <typename r>
class RipRelativeBlindRelocation : public EarlyRelocation<r> {
	char *mkName() const {
		return my_asprintf("rrbr(offset = %d, size = %d, target = %lx, is_branch = %s)",
				   this->offset,
				   this->size,
				   target,
				   is_branch ? "true" : "false");
	}
public:
	unsigned long target;
	bool is_branch;

	void doit(CfgLabelAllocator &, PatchFragment<r> *) { abort(); }

	RipRelativeBlindRelocation(unsigned _offset,
				   unsigned _size,
				   unsigned long _target,
				   bool _is_branch)
		: EarlyRelocation<r>(_offset, _size),
		  target(_target),
		  is_branch(_is_branch)
	{
		assert((int)this->offset >= 0);
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
RipRelativeBranchRelocation<r>::doit(CfgLabelAllocator &, PatchFragment<r> *)
{
	abort();
}

void __genfix_add_array_summary(std::vector<const char *> &out,
				const char *t_ptr,
				const char *nr_entries,
				const char *table);
#endif /* !GENFIX_H__ */
