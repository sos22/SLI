#ifndef SLI_H__
#define SLI_H__

#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <algorithm>
#include <map>

#include "libvex_guest_amd64.h"
#include "libvex_ir.h"
#include "libvex.h"

#include "exceptions.h"

#include "map.h"
#include "ring_buffer.h"

FILE *fopenf(const char *mode, const char *fmt, ...) __attribute__((__format__ (__printf__, 2, 3)));

char *readfile(int fd);

class ThreadId {
	unsigned tid;
public:
	static const ThreadId invalidTid;
	bool valid() const { return tid != 0xf001beef && tid != 0xa1b2c3d4 && tid != 0xaabbccdd; }
	ThreadId(unsigned _tid) : tid(_tid) {}
	ThreadId() : tid(0xf001beef) {}
	bool operator==(const ThreadId &b) const { return b.tid == tid; }
	bool operator!=(const ThreadId &b) const { return b.tid != tid; }
	bool operator<(const ThreadId &b) const { return tid < b.tid; }
	bool operator>(const ThreadId &b) const { return tid > b.tid; }
	ThreadId operator++() {
		tid++;
		return *this;
	}
	const unsigned _tid() const { return tid; }
	unsigned long hash() const { return tid; }
};

class PhysicalAddress {
public:
	unsigned long _pa;
	PhysicalAddress() : _pa(0) {}
	bool operator<(PhysicalAddress b) const { return _pa < b._pa; }
	bool operator>=(PhysicalAddress b) const { return _pa >= b._pa; }
	bool operator!=(PhysicalAddress b) const { return _pa != b._pa; }
	bool operator==(PhysicalAddress b) const { return _pa == b._pa; }
	PhysicalAddress operator+(unsigned long x) const
	{
		PhysicalAddress r;
		r._pa = _pa + x;
		return r;
	}
	PhysicalAddress operator-(unsigned long x) const
	{
		PhysicalAddress r;
		r._pa = _pa - x;
		return r;
	}
	unsigned long operator-(PhysicalAddress b) { return _pa - b._pa; }
};

struct expression_result : public Named {
protected:
	char *mkName() const {
		return my_asprintf("{%lx, %lx}", lo, hi);
	}
public:
	unsigned long lo;
	unsigned long hi;
	expression_result() : Named(), lo(0), hi(0) {}
};

class RegisterSet {
public:
	static const unsigned NR_REGS = sizeof(VexGuestAMD64State) / 8;
#define REGISTER_IDX(x) (offsetof(VexGuestAMD64State, guest_ ## x) / 8)
	unsigned long registers[NR_REGS];
	RegisterSet(const VexGuestAMD64State &r);
	RegisterSet() {};
	unsigned long &get_reg(unsigned idx) { assert(idx < NR_REGS); return registers[idx]; }
	const unsigned long &get_reg(unsigned idx) const { assert(idx < NR_REGS); return registers[idx]; }
	void set_reg(unsigned idx, unsigned long val)
	{
		assert(idx < NR_REGS);
		registers[idx] = val;
	}
	unsigned long &rip() { return get_reg(REGISTER_IDX(RIP)); }
	unsigned long &rsp() { return get_reg(REGISTER_IDX(RSP)); }

	void pretty_print() const {
		for (unsigned x = 0; x < NR_REGS; x++)
			printf("\treg%d: %lx\n", x, registers[x]);
	}
};

class MachineState;
class AddressSpace;
class PMap;
class ThreadEvent;

class Thread : public GarbageCollected<Thread> {
public:

	ThreadId tid;
	RegisterSet regs;
	bool crashed;

	void pretty_print() const;

	void visit(HeapVisitor &) {}

	NAMED_CLASS
};

class VAMap : public GarbageCollected<VAMap> {
public:
	class VAMapEntry {
	public:
		VAMapEntry *prev;
		VAMapEntry *succ;
		unsigned long start; /* Inclusive */
		unsigned long end; /* Exclusive */
		PhysicalAddress *pa;
		static VAMapEntry *alloc(unsigned long start,
					 unsigned long end,
					 PhysicalAddress *pa);
		void split(unsigned long where);
		static void visit(VAMapEntry *&ref, PMap *pmap, HeapVisitor &hv);
		VAMapEntry *dupeSelf() const;
	};

private:
	/* Mutable because we splay the tree on lookup */
	mutable VAMapEntry *root;

	VAMap *parent;

	void forceCOW();
public:
	bool translate(unsigned long va,
		       PhysicalAddress *pa = NULL) const;
	void addTranslation(unsigned long va,
			    PhysicalAddress pa);

	static VAMap *empty();
	VAMap *dupeSelf();
	static void visit(VAMap *&ref, HeapVisitor &hv, PMap *pmap);
	void visit(HeapVisitor &hv);

	NAMED_CLASS
};

#define MEMORY_CHUNK_SIZE 4096

class MemoryChunk : public GarbageCollected<MemoryChunk> {
public:
	static const unsigned long size = MEMORY_CHUNK_SIZE;

	void write(unsigned offset, const unsigned long *source, unsigned nr_bytes);
	void read(unsigned offset, unsigned long *dest, unsigned nr_bytes) const;

	MemoryChunk *dupeSelf() const;

	PhysicalAddress base;
	void visit(HeapVisitor &) {}

	NAMED_CLASS

private:
	unsigned char content[size];
};

/* A PMap is a mapping from physical addresses to memory chunks.  It's
   pretty much just a simple hash table; nothing clever here.  There are
   two main oddities:

   -- Physical addresses are divided into two parts, a chunk number
      and a chunk offset, and when you do a PA -> chunk translation
      you get back the chunk offset as well as the chunk itself.

   -- The references from the PMap to the memory chunks are weak.  If
      you want to stop them from disappearing, something else needs to
      reference them.  The helper function visitPA is provided to help
      with this: it keeps both the mapping and the memory chunk live.
*/
class PMapEntry : public GarbageCollected<PMapEntry> {
public:
	PhysicalAddress pa;
	MemoryChunk *mc;
	PMapEntry *next;
	PMapEntry **pprev;
	bool readonly;
	static PMapEntry *alloc(PhysicalAddress pa, MemoryChunk *mc, bool readonly);
	void visit(HeapVisitor &hv) { hv(mc); }
	~PMapEntry() {
		*pprev = next;
		if (next)
			next->pprev = pprev;
	}
	void relocate(PMapEntry *target, size_t sz);
	NAMED_CLASS
};

class PMap : public GarbageCollected<PMap> {
public:
	static const unsigned nrHashBuckets = 1024;
	static unsigned paHash(PhysicalAddress pa);
	PhysicalAddress nextPa;
	/* mutable because we do pull-to-front in the lookup methods.
	 * The denotation of the mapping is unchanged, but its
	 * physical structure is. */
	mutable PMapEntry *heads[nrHashBuckets];
	PMap *parent;

private:
	PMapEntry *findPme(PhysicalAddress pa, unsigned h) const;
public:
	/* Look up the memory chunk for a physical address.  On
	   success, *mc_start is set to the offset of the address in
	   the chunk. */
	MemoryChunk *lookup(PhysicalAddress pa, unsigned long *mc_start);
	const MemoryChunk *lookupConst(PhysicalAddress pa, unsigned long *mc_start,
				       bool pull_up = true) const;

	/* Add a new chunk to the map, and return a newly-assigned
	   physical address for it. */
	PhysicalAddress introduce(MemoryChunk *mc);

	static PMap *empty();
	PMap *dupeSelf() const;

	void visitPA(PhysicalAddress pa, HeapVisitor &hv);
	void visit(HeapVisitor &hv);
	void relocate(PMap *target, size_t sz);

	NAMED_CLASS
};

class ElfData : public GarbageCollected<ElfData> {
public:
	unsigned long plt_start, plt_end;
	std::vector<std::pair<unsigned, char *> > plt_symbol_names;
	const char *lookupPltSymbol(unsigned idx) const;
	unsigned long getPltAddress(AddressSpace *as, const char *name) const;
	void visit(HeapVisitor &) {}
	NAMED_CLASS
};

class MachineState : public GarbageCollected<MachineState> {
public:
	std::vector<Thread *> threads;

	ThreadId nextTid;

	AddressSpace *addressSpace;
	ElfData *elfData;

	static MachineState *readCoredump(const char *fname);
	static MachineState *readELFExec(const char *fname);

	void registerThread(Thread *t) {
		ThreadId tid;
		tid = 1;
	top:
		for (unsigned x = 0; x < threads.size(); x++) {
			if (threads[x]->tid == tid) {
				++tid;
				goto top;
			}
		}
		t->tid = tid;
		threads.push_back(t);
	}
	Thread *findThread(ThreadId id, bool allow_failure = false) {
		unsigned x;
		for (x = 0; x < threads.size(); x++)
			if (threads[x]->tid == id)
				return threads[x];
		assert(allow_failure);
		return NULL;
	}
	const Thread *findThread(ThreadId id) const {
		unsigned x;
		for (x = 0; x < threads.size(); x++)
			if (threads[x]->tid == id)
				return threads[x];
		return NULL;
	}

	void visit(HeapVisitor &hv);

	NAMED_CLASS
};

template<typename t> void
visit_container(t &vector, HeapVisitor &hv)
{
	for (class t::iterator it = vector.begin();
	     it != vector.end();
	     it++)
		hv(*it);
}

class AddressSpace : public GarbageCollected<AddressSpace > {
public:
	VAMap *vamap;
	PMap *pmap;

	IRSB *getIRSBForAddress(const ThreadRip &rip, bool singleInstr);

	void allocateMemory(unsigned long start, unsigned long size);
	void writeMemory(unsigned long start, unsigned size,
			 const unsigned long *contents);
	bool copyToClient(unsigned long start, unsigned size, const void *source);
	template <typename t> const t fetch(unsigned long addr);
	void readMemory(unsigned long start, unsigned size,
			unsigned long *contents);
	bool isReadable(unsigned long start);

	static AddressSpace *initialAddressSpace();
	void visit(HeapVisitor &hv);

	NAMED_CLASS
};

void init_sli(void);

void dbg_break(const char *msg, ...);
void printIRExpr(IRExpr *e);

VexRip extract_call_follower(IRSB *irsb);
expression_result eval_expression(const RegisterSet *rs,
				  IRExpr *expr,
				  const std::vector<expression_result> &temporaries);
void put_stmt(RegisterSet *rs, unsigned put_offset, struct expression_result put_data, IRType put_type);

template <typename t> const t
AddressSpace::fetch(unsigned long start)
{
	unsigned long *res;

	res = (unsigned long *)malloc(sizeof(unsigned long) * sizeof(t));
	readMemory(start, sizeof(t), res);
	t tt;
	for (unsigned x = 0; x < sizeof(t); x++)
		((unsigned char *)&tt)[x] = res[x];
	free(res);
	return tt;
}

IRExpr *readIRExpr(int fd);

IRSB *instrument_func(unsigned tid,
		      void *closure,
		      IRSB *sb_in,
		      VexGuestLayout *layout,
		      VexGuestExtents *vge,
		      IRType gWordTy,
		      IRType hWordTy);

class internIRExprTable : public GcCallback<&ir_heap> {
	void runGc(HeapVisitor &hv);
protected:
	virtual void _runGc(HeapVisitor &) {}
public:
	static const int nr_entries = 17;
	std::map<IRExpr *, IRExpr *> lookups[nr_entries];
	internIRExprTable() : GcCallback<&ir_heap>(true) {};
};
IRExpr *internIRExpr(IRExpr *e, internIRExprTable &lookupTable);

char *nameIRExpr(IRExpr *a);
void my_system(const char *arg1, ...);
char *flattenStringFragmentsMalloc(std::vector<const char *> fragments, const char *sep = "",
				   const char *prefix = "", const char *suffix = "");

void warning(const char *fmt, ...) __attribute__((__format__(__printf__, 1, 2)));

void __fail(const char *file, unsigned line, const char *fmt, ...)
	__attribute__((noreturn, __format__(__printf__, 3, 4)));
#define fail(...) __fail(__FILE__, __LINE__, __VA_ARGS__)
#define abort() fail("aborted")

template <typename t> bool
operator |=(std::set<t> &a, const std::set<t> &b)
{
	bool res = false;
	for (auto it = b.begin(); it != b.end(); it++)
		res |= a.insert(*it).second;
	return res;
}

template <typename t> bool
operator &=(std::set<t> &a, const std::set<t> &b)
{
	bool res = false;
	for (auto it = a.begin(); it != a.end(); ) {
		if (b.count(*it)) {
			it++;
		} else {
			a.erase(it++);
			res = true;
		}
	}
	return res;
}

#endif /* !SLI_H__ */
