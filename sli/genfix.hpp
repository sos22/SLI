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

template <typename ripType>
class Instruction : public GarbageCollected<Instruction<ripType>, &ir_heap > {
public:
	Instruction(const CfgLabel &_label)
		: label(_label)
	{ successors.reserve(2); }
	ripType rip;
	CfgLabel label;

	class successor_t {
	public:
		successor_t(const ripType &_rip, Instruction *_instr)
			  : rip(_rip), instr(_instr)
		{}
		ripType rip;
		Instruction *instr;
		successor_t() {}
		static successor_t dflt(Instruction *i)
		{
			return successor_t(ripType(), i);
		}
	};
	std::vector<successor_t> successors;
	unsigned char content[MAX_INSTRUCTION_SIZE];
	unsigned len;
	std::vector<EarlyRelocation<ripType> *> relocs;
	std::vector<LateRelocation *> lateRelocs;

	static Instruction<ripType> *pseudo(const CfgLabel &label, ripType rip);

	void visit(HeapVisitor &hv) {
		visit_container(relocs, hv);
		visit_container(lateRelocs, hv);
		for (auto it = successors.begin(); it != successors.end(); it++)
			hv(it->instr);
	}
	NAMED_CLASS
};

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
public:
	CFG(AddressSpace *_as) : as(_as), ripToInstr(new ripToInstrT()) {}
	void visit(HeapVisitor &hv) {
		hv(ripToInstr);
		hv(as);
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
class RipRelativeBranchRelocation : public EarlyRelocation<r> {
	char *mkName() const {
		return my_asprintf("rrbr(offset = %d, size = %d, target = %s)",
				   this->offset,
				   this->size,
				   target.name());
	}
public:
	r target;
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

#endif /* !GENFIX_H__ */
