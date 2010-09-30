#ifndef SLI_H__
#define SLI_H__

#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <algorithm>

#include "libvex_guest_amd64.h"
#include "libvex_ir.h"
#include "libvex.h"

#include "exceptions.h"

#include "map.h"
#include "ring_buffer.h"

static inline char *my_asprintf(const char *fmt, ...)
{
	va_list args;
	char *r;
	va_start(args, fmt);
	int x = vasprintf(&r, fmt, args);
	(void)x;
	va_end(args);
	return r;
}
static char *my_asprintf(const char *fmt, ...) __attribute__((__format__ (__printf__, 1, 2)));

char *vex_asprintf(const char *fmt, ...) __attribute__((__format__ (__printf__, 1, 2)));
char *vex_vasprintf(const char *fmt, va_list args);
	
template <typename underlying> class PointerKeeper {
	underlying *x;
public:
	~PointerKeeper() { if (x) delete x; }
	PointerKeeper(underlying *y) : x(y) {}
	PointerKeeper() : x(NULL) {}
	void keep(underlying *y) { if (x) delete x; x = y; }
};

template <typename underlying>
class Maybe {
public:
	underlying value;
	bool full;
	Maybe(const underlying &x)
		: value(x),
		  full(true)
	{
	}
	Maybe() : full(false)
	{
	}		
};

class Named {
	mutable char *_name;
	mutable char *_name2;
protected:
	virtual char *mkName(void) const = 0;
	void clearName() const { assert(_name == _name2); free(_name); _name = NULL; _name2 = NULL; }
public:
	Named &operator=(const Named &src) {
		assert(src._name == src._name2);
		clearName();
		if (src._name)
			_name2 = _name = strdup(src._name);
		return *this;
	}
	Named() : _name(NULL), _name2(NULL) {}
	Named(const Named &b) {
		assert(b._name == b._name2);
		if (b._name)
			_name2 = _name = strdup(b._name);
		else
			_name2 = _name = NULL;
	}
	const char *name() const {
		if (!this)
			return NULL;
		assert(_name == _name2);
		if (!_name)
			_name2 = _name = mkName();
		return _name;
	}
	~Named() { clearName(); }
};

template <typename t, const char *(*get_name)(const void *) = get_name<t>, void (*visit)(void *, HeapVisitor &) = visit_object<t>, void (*destruct)(void *) = destruct_object<t> >
class VexAllocTypeWrapper {
public:
	VexAllocType type;
	VexAllocTypeWrapper() {
		type.nbytes = sizeof(t);
		type.gc_visit = visit;
		type.destruct = destruct;
		type.get_name = get_name;
	}
	t *alloc() {
		return (t *)__LibVEX_Alloc(&type);
	}
};

static inline void visit_aiv(unsigned long, HeapVisitor &)
{
}

static inline char *name_aiv(unsigned long x)
{
	return vex_asprintf("%lx", x);
}

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

class EventTimestamp {
public:
	EventTimestamp(ThreadId _tid, unsigned long _idx, unsigned long _total_timestamp,
		       unsigned long _rip)
		: tid(_tid), idx(_idx), total_timestamp(_total_timestamp),
		  rip(_rip)
	{}
	EventTimestamp() : tid(ThreadId::invalidTid), idx(0), total_timestamp(0) {}
	static const EventTimestamp invalid;
	ThreadId tid;
	unsigned long idx;

	/* Count of all events over every thread.  This could, in
	   principle, be derived from tid and idx, but doing so is
	   often difficult. */
	unsigned long total_timestamp;

	/* RIP when the event was generated.  Again, could be derived,
	   given the tid, idx, and context, but doing so is a pain. */
	unsigned long rip;

	bool operator ==(const EventTimestamp &b) const { return tid == b.tid && idx == b.idx; }
	bool operator !=(const EventTimestamp &b) const { return tid != b.tid || idx != b.idx; }

	bool operator >(const EventTimestamp &b) const { return total_timestamp > b.total_timestamp; }
	bool operator <(const EventTimestamp &b) const { return total_timestamp < b.total_timestamp; }

	unsigned hash() const { return total_timestamp; }
};

/* This is intended to be a measure of how ``relevant'' a given event
   is to some other event, and is used when deciding which branch of
   an expression to perform refinement on. */
class Relevance {
	/* Careful: This is a measure of the irrelevance of the
	   target, so has a backwards sense to the enclosing
	   structure.  0 is perfectly relevant, +ve numbers are
	   increasingly irrelevance, and -ve numbers aren't used. */
	long irrelevance;
	Relevance(long _irr) : irrelevance(_irr) {}
public:
	Relevance(Relevance a, Relevance b) {
		irrelevance = std::min<long>(a.irrelevance, b.irrelevance) + 1;
	}
	/* How relevant is @ev likely to be to an event at time
	 * @to? */
	Relevance(EventTimestamp ev, EventTimestamp to) {
		long delta = ev.total_timestamp - to.total_timestamp;
		if (delta > 0) {
			irrelevance = (delta * delta) / 10 + delta;
			if (irrelevance < 0)
				irrelevance = 0;
		} else {
			irrelevance = -delta;
		}
		if (ev.tid != to.tid)
			irrelevance += 100000;
	}

	/* These look backwards, because irrelevance is the opposite
	   of relevance. */
	bool operator>(const Relevance &r) const { return irrelevance < r.irrelevance; }
	bool operator>=(const Relevance &r) const { return irrelevance <= r.irrelevance; }
	bool operator<(const Relevance &r) const { return irrelevance > r.irrelevance; }
	bool operator<=(const Relevance &r) const { return irrelevance >= r.irrelevance; }

	Relevance operator-(long d) const { return Relevance(irrelevance + d); }
	Relevance operator+(long d) const { return Relevance(irrelevance - d); }

	static const Relevance irrelevant;
	static const Relevance perfect;
};

template <typename t> t min(const t &a, const t &b)
{
	if (a < b)
		return a;
	else
		return b;
}

template <typename t> t max(const t &a, const t &b)
{
	if (a > b)
		return a;
	else
		return b;
}

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

template<typename ait> ait load_ait(ait x, ait addr, EventTimestamp when, EventTimestamp store,
				    ait storeAddr, unsigned size);

template <typename ait> static inline ait mkConst(unsigned long x);

template <>
unsigned long mkConst(unsigned long x)
{
	return x;
}

template<typename abst_int_value>
struct expression_result : public Named {
protected:
	char *mkName() const {
		return my_asprintf("{%s, %s}",
				   name_aiv(lo), name_aiv(hi));
	}
public:
	abst_int_value lo;
	abst_int_value hi;
	expression_result() : Named() {}
	void visit(HeapVisitor &hv) { visit_aiv(lo, hv); visit_aiv(hi, hv); }
	
	template <typename new_type> void abstract(expression_result<new_type> *out) const
	{
		out->lo = mkConst<new_type>(lo);
		out->hi = mkConst<new_type>(hi);
	}
};

template <typename underlying>
class RegisterSet {
public:
	static const unsigned NR_REGS = sizeof(VexGuestAMD64State) / 8;
#define REGISTER_IDX(x) (offsetof(VexGuestAMD64State, guest_ ## x) / 8)
	underlying registers[NR_REGS];
	RegisterSet(const VexGuestAMD64State &r);
	RegisterSet() {};
	underlying &get_reg(unsigned idx) { assert(idx < NR_REGS); return registers[idx]; }
	void set_reg(unsigned idx, underlying val)
	{
		sanity_check_ait(val);
		assert(idx < NR_REGS);
		registers[idx] = val;
		if (idx == REGISTER_IDX(RSP))
			mark_as_stack(registers[idx]);
	}
	underlying &rip() { return get_reg(REGISTER_IDX(RIP)); }
	underlying &rsp() { return get_reg(REGISTER_IDX(RSP)); }

	template <typename new_type> void abstract(RegisterSet<new_type> *out) const;

	void visit(HeapVisitor &hv) {
		for (unsigned x = 0; x < NR_REGS; x++)
			visit_aiv(registers[x], hv);
	}

	void pretty_print() const {
		for (unsigned x = 0; x < NR_REGS; x++)
			printf("\treg%d: %s\n", x, name_aiv(registers[x]));
	}
};

template <typename ait> class AddressSpace;

template <typename ait>
class expression_result_array {
public:
	std::vector<expression_result<ait> > content;
	void setSize(unsigned new_size) {
		content.clear();
		content.resize(new_size);
	}
	expression_result<ait> &operator[](unsigned idx) { return content[idx]; }
	void visit(HeapVisitor &hv) {
		for (class std::vector<expression_result<ait> >::iterator it = content.begin();
		     it != content.end();
		     it++)
			it->visit(hv);

	}
	expression_result_array() :
		content()
	{
	}

	template <typename new_type> void abstract(expression_result_array<new_type> *out) const;

	void pretty_print() const {
		for (unsigned x = 0; x < content.size(); x++)
			printf("\tt%d: %s\n", x, content[x].name());
	}
};

template <typename ait> class ThreadEvent;
template <typename ait> class MachineState;
template <typename ait> class LogRecordInitialRegisters;
template <typename ait> class LogWriter;
template <typename ait> class LogRecordVexThreadState;

class LogReaderPtr {
public:
	unsigned char cls_data[32];
	LogReaderPtr() { memset(cls_data, 0, sizeof(cls_data)); }
};

template <typename abst_int_type>
class Thread : public GarbageCollected<Thread<abst_int_type> > {
	static void translateNextBlock(VexPtr<Thread<abst_int_type> > &ths,
				       VexPtr<AddressSpace<abst_int_type> > &addrSpace,
				       VexPtr<MachineState<abst_int_type> > &ms,
				       const LogReaderPtr &ptr,
				       abst_int_type rip,
				       GarbageCollectionToken t);
	struct expression_result<abst_int_type> eval_expression(IRExpr *expr);
	ThreadEvent<abst_int_type> *do_dirty_call(IRDirty *details, MachineState<abst_int_type> *ms);
	ThreadEvent<abst_int_type> *do_load(EventTimestamp when,
					    IRTemp tmp,
					    abst_int_type addr,
					    unsigned size,
					    MachineState<abst_int_type> *ms);
	expression_result<abst_int_type> do_ccall_calculate_condition(struct expression_result<abst_int_type> *args);
	expression_result<abst_int_type> do_ccall_calculate_rflags_c(expression_result<abst_int_type> *args);
	expression_result<abst_int_type> do_ccall_generic(IRCallee *cee, struct expression_result<abst_int_type> *rargs);
	expression_result<abst_int_type> do_ccall(IRCallee *cee, IRExpr **args);

	void amd64g_dirtyhelper_loadF80le(MachineState<abst_int_type> *, IRTemp tmp, abst_int_type addr);
	void amd64g_dirtyhelper_storeF80le(MachineState<abst_int_type> *, abst_int_type addr, abst_int_type _f64);

	void redirectGuest(abst_int_type rip);

public:
	std::vector<unsigned long> currentCallStack;

	unsigned decode_counter;
	EventTimestamp bumpEvent(MachineState<abst_int_type> *ms);
	ThreadId tid;
	unsigned pid;
	RegisterSet<abst_int_type> regs;
	abst_int_type clear_child_tid;
	abst_int_type robust_list;
	abst_int_type set_child_tid;
	abst_int_type futex_block_address;
	bool exitted;
	bool crashed;
	bool idle;

	bool cannot_make_progress;
	bool blocked;

	unsigned long nrAccesses;
	unsigned long nrEvents;

	IRSB *currentIRSB;
	abst_int_type currentIRSBRip;
	expression_result_array<abst_int_type> temporaries;
	int currentIRSBOffset;

	/* We maintain a log of the thread's recent control flow
	   activity.  This means that whenever we translate a new
	   IRSB, we record the address from which we obtained the old
	   one. */
	struct control_log_entry {
		unsigned long translated_rip;
		int exit_idx;
		control_log_entry(unsigned long _rip, int _idx)
			: translated_rip(_rip), exit_idx(_idx)
		{
		}
		control_log_entry()
			: translated_rip(0), exit_idx(-99)
		{
		}
	};
	ring_buffer<control_log_entry, 100> controlLog;
	struct snapshot_log_entry {
		MachineState<abst_int_type> *ms;
		LogReaderPtr ptr;
		snapshot_log_entry(MachineState<abst_int_type> *_ms,
				   const LogReaderPtr &_ptr)
			: ms(_ms), ptr(_ptr)
		{
		}
		snapshot_log_entry() : ms(NULL), ptr(LogReaderPtr())
		{
		}
	};
	/* mutable because we have to nuke it from dupeSelf. */
	mutable ring_buffer<snapshot_log_entry, 2> snapshotLog;

	abst_int_type currentControlCondition;

	EventTimestamp lastEvent;

	bool runnable() const { return !exitted && !crashed && !cannot_make_progress; }
	void futexBlock(abst_int_type fba) { blocked = true; futex_block_address = fba; }
	void futexUnblock() { blocked = false; }

	void pretty_print() const;
private:
	bool allowRipMismatch;
public:
	static ThreadEvent<abst_int_type> *runToEvent(VexPtr<Thread<abst_int_type> > &ths,
						      VexPtr<MachineState<abst_int_type> > &ms,
						      const LogReaderPtr &ptr,
						      GarbageCollectionToken t);

	static Thread<abst_int_type> *initialThread(const LogRecordInitialRegisters<abst_int_type> &initRegs);
	Thread<abst_int_type> *fork(unsigned newPid);
	Thread<abst_int_type> *dupeSelf() const;
	void dumpSnapshot(LogWriter<abst_int_type> *lw);

	static void imposeState(VexPtr<Thread<abst_int_type> > &thr,
				VexPtr<LogRecordVexThreadState<abst_int_type> > &rec,
				VexPtr<AddressSpace<abst_int_type> > &as,
				VexPtr<MachineState<abst_int_type> > &ms,
				const LogReaderPtr &ptr,
				GarbageCollectionToken t);

	void visit(HeapVisitor &hv);

	template <typename new_type> Thread<new_type> *abstract() const;

	void destruct() { temporaries.~expression_result_array<abst_int_type>(); }

	NAMED_CLASS
};

template <typename ait> class PMap;

class VAMap {
public:
	class Protection {
	public:
		bool readable;
		bool writable;
		bool executable;
		Protection(bool r, bool w, bool x) :
			readable(r),
			writable(w),
			executable(x)
		{
		}
		Protection(unsigned prot); /* PROT_* flags */
		bool operator==(const Protection &p) const {
			return readable == p.readable &&
				writable == p.writable &&
				executable == p.executable;
		}
		operator unsigned long() const;
	};
	class AllocFlags {
	public:
		bool expandsDown;
		AllocFlags(bool _e) :
			expandsDown(_e)
		{
		}
		AllocFlags(unsigned flags); /* MAP_* flags */
		bool operator==(const AllocFlags alf) const {
			return expandsDown == alf.expandsDown;
		}
		operator unsigned long() const;
	};
	static const AllocFlags defaultFlags;

	class VAMapEntry {
	public:
		VAMapEntry *prev;
		VAMapEntry *succ;
		unsigned long start; /* Inclusive */
		unsigned long end; /* Exclusive */
		PhysicalAddress *pa;
		Protection prot;
		AllocFlags alf;
		static VAMapEntry *alloc(unsigned long start,
					 unsigned long end,
					 PhysicalAddress *pa,
					 Protection prot,
					 AllocFlags alf);
		void split(unsigned long where);
		template <typename ait> static void visit(VAMapEntry *&ref, PMap<ait> *pmap, HeapVisitor &hv);
		VAMapEntry *promoteSmallest();
		VAMapEntry *dupeSelf() const;
		void sanityCheck(unsigned long max = 0,
				 bool have_max = false,
				 unsigned long min = 0,
				 bool have_min = false) const;
	};

	class iterator {
		VAMapEntry *current;
		VAMap *m;
	public:
		iterator(VAMap *_m);
		iterator(VAMap *_m, void *ign) : current(NULL), m(_m) {}
		const VAMapEntry &operator*() const { return *current; }
		const VAMapEntry *operator->() const { return current; }
		void operator++(int);
		bool operator==(const iterator &x) const { return current == x.current && m == x.m; }
		bool operator!=(const iterator &x) const { return !(x == *this); }
	};

	iterator begin() { return iterator(this); }
	iterator end() { return iterator(this, NULL); }

private:
	/* Mutable because we splay the tree on lookup */
	mutable VAMapEntry *root;

	VAMap *parent;

	void forceCOW();
public:
	bool translate(unsigned long va,
		       PhysicalAddress *pa = NULL,
		       Protection *prot = NULL,
		       AllocFlags *alf = NULL) const;
	bool findNextMapping(unsigned long from,
			     unsigned long *va = NULL,
			     PhysicalAddress *pa = NULL,
			     Protection *prot = NULL,
			     AllocFlags *alf = NULL) const;
	void addTranslation(unsigned long va,
			    PhysicalAddress pa,
			    Protection prot,
			    AllocFlags alf);
	bool protect(unsigned long start,
		     unsigned long size,
		     Protection prot);
	void unmap(unsigned long start, unsigned long size);

	static VAMap *empty();
	VAMap *dupeSelf();
	template <typename ait> static void visit(VAMap *&ref, HeapVisitor &hv, PMap<ait> *pmap);
	void visit(HeapVisitor &hv);

	void sanityCheck() const;
};

#define MEMORY_CHUNK_SIZE 4096

template <typename ait> class MemoryChunk;

template <>
class MemoryChunk<unsigned long> : public GarbageCollected<MemoryChunk<unsigned long> > {
public:
	static const unsigned long size = MEMORY_CHUNK_SIZE;
	static MemoryChunk<unsigned long> *allocate();

	void write(EventTimestamp, unsigned offset, const unsigned long *source, unsigned nr_bytes,
		   unsigned long sa);
	EventTimestamp read(unsigned offset, unsigned long *dest, unsigned nr_bytes,
			    unsigned long *sa = NULL) const;

	MemoryChunk<unsigned long> *dupeSelf() const;
	template <typename nt> MemoryChunk<nt> *abstract() const;

	PhysicalAddress base;
	unsigned serial;
	unsigned long checksum;
	void sanity_check(void) const;
	void visit(HeapVisitor &hv) { sanity_check(); }
	void destruct() {}

	NAMED_CLASS

private:
	static unsigned serial_start;
	mutable bool frozen;
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
template <typename ait>
class PMapEntry : public GarbageCollected<PMapEntry<ait> > {
public:
	PhysicalAddress pa;
	MemoryChunk<ait> *mc;
	PMapEntry<ait> *next;
	PMapEntry<ait> **pprev;
	bool readonly;
	static PMapEntry *alloc(PhysicalAddress pa, MemoryChunk<ait> *mc, bool readonly);
	void visit(HeapVisitor &hv) { hv(mc); }
	void destruct() {
		*pprev = next;
		if (next)
			next->pprev = pprev;
	}
	void relocate(PMapEntry<ait> *target, size_t sz);
	NAMED_CLASS
};

template <typename ait>
class PMap : public GarbageCollected<PMap<ait> > {
public:
	static const unsigned nrHashBuckets = 1024;
	static unsigned paHash(PhysicalAddress pa);
	PhysicalAddress nextPa;
	/* mutable because we do pull-to-front in the lookup methods.
	 * The denotation of the mapping is unchanged, but its
	 * physical structure is. */
	mutable PMapEntry<ait> *heads[nrHashBuckets];
	PMap<ait> *parent;

private:
	PMapEntry<ait> *findPme(PhysicalAddress pa, unsigned h) const;
public:
	/* Look up the memory chunk for a physical address.  On
	   success, *mc_start is set to the offset of the address in
	   the chunk. */
	MemoryChunk<ait> *lookup(PhysicalAddress pa, unsigned long *mc_start);
	const MemoryChunk<ait> *lookupConst(PhysicalAddress pa, unsigned long *mc_start,
					    bool pull_up = true) const;

	/* Add a new chunk to the map, and return a newly-assigned
	   physical address for it. */
	PhysicalAddress introduce(MemoryChunk<ait> *mc);

	static PMap<ait> *empty();
	PMap<ait> *dupeSelf() const;

	void visitPA(PhysicalAddress pa, HeapVisitor &hv);
	void visit(HeapVisitor &hv);
	void relocate(PMap<ait> *target, size_t sz);

	void destruct() {}

	template <typename newtype> PMap<newtype> *abstract() const;
	NAMED_CLASS
};

template <typename ait>
class LogRecord : public Named, public GarbageCollected<LogRecord<ait> > {
	ThreadId tid;
protected:
	void *marshal(unsigned cls, unsigned psize, unsigned *sz, void **r) const;
	LogRecord(ThreadId _tid) : tid(_tid) {}
public:
	ThreadId thread() const { return tid; }
	virtual unsigned marshal_size() const = 0;
	virtual void *marshal(unsigned *size) const = 0;
	virtual ~LogRecord() {};
	virtual void destruct() {}
	virtual void visit(HeapVisitor &hv) {}
	NAMED_CLASS
};

template <typename ait> class SignalHandlers;

template <typename ait>
class LogRecordInitialSighandlers : public LogRecord<ait> {
	friend class SignalHandlers<ait>;
	struct sigaction handlers[64];
protected:
	virtual char *mkName() const {
		return strdup("initial_sighandlers");
	}
public:
	LogRecordInitialSighandlers(ThreadId tid,
				    const struct sigaction *sa)
		: LogRecord<ait>(tid)
	{
		memcpy(handlers, sa, sizeof(*sa) * 64);
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
	template <typename outtype> LogRecordInitialSighandlers<outtype> *abstract() const
	{
		return new LogRecordInitialSighandlers<outtype>(this->thread(), handlers);
	}
};

template <typename ait>
class SignalHandlers {
public:
	struct sigaction handlers[64];
	SignalHandlers(const LogRecordInitialSighandlers<ait> &init) {
		memcpy(handlers, init.handlers, sizeof(init.handlers));
	}
	SignalHandlers() { memset(handlers, 0, sizeof(handlers)); }
	void dumpSnapshot(LogWriter<ait> *lw) const;
	template <typename new_type> void abstract(SignalHandlers<new_type> *out) const
	{
		memcpy(out->handlers, handlers, sizeof(handlers));
	}
};

template <typename ait>
class LogReader : public GarbageCollected<LogReader<ait> > {
public:
	virtual LogRecord<ait> *read(LogReaderPtr startPtr, LogReaderPtr *outPtr) const = 0;
	virtual ~LogReader() {}
	template <typename new_type> LogReader<new_type> *abstract() const;
	NAMED_CLASS
};

class LogFile : public LogReader<unsigned long> {
	int fd;
	struct _ptr {
		uint64_t off;
		unsigned record_nr;
		bool valid;
		_ptr() : off(0xcafebabe00000000ul), record_nr(0xbeeffeed), valid(false) {}
		bool operator>=(const _ptr &b) const { return off >= b.off; }
	};
	_ptr unwrapPtr(LogReaderPtr p) const {
		return *(_ptr *)p.cls_data;
	}
	_ptr forcedEof;

	ssize_t buffered_pread(void *output, size_t output_size, off_t start_offset) const;

	mutable unsigned char buffer[8192];
	mutable off_t buffer_start;
	mutable off_t buffer_end;

	LogFile() {}
public:
	LogReaderPtr mkPtr(uint64_t off, unsigned record_nr) const {
		LogReaderPtr w;
		_ptr *p = (_ptr *)w.cls_data;
		p->off = off;
		p->record_nr = record_nr;
		p->valid = true;
		return w;
	}
	virtual LogRecord<unsigned long> *read(LogReaderPtr startPtr, LogReaderPtr *outPtr) const;
	~LogFile();
	static LogFile *open(const char *path, LogReaderPtr *initial_ptr);
	LogFile *truncate(LogReaderPtr eof);
	void visit(HeapVisitor &hv){}
	void destruct() { this->~LogFile(); }
	NAMED_CLASS
};

template <typename abst_int_type>
class MachineState : public GarbageCollected<MachineState<abst_int_type> > {
public:
	LibvexVector<Thread<abst_int_type> > *threads;

	bool exitted;
	abst_int_type exit_status;
	ThreadId nextTid;

private:
	static MachineState *initialMachineState(AddressSpace<abst_int_type> *as,
						 const LogRecordInitialSighandlers<abst_int_type> &handlers);
public:
	AddressSpace<abst_int_type> *addressSpace;
	SignalHandlers<abst_int_type> signalHandlers;
	unsigned long nrEvents;
	static MachineState<abst_int_type> *initialMachineState(VexPtr<LogReader<abst_int_type> > &lf,
								LogReaderPtr startPtr,
								LogReaderPtr *endPtr,
								GarbageCollectionToken t);

	template <typename new_type> MachineState<new_type> *abstract() const;

	void registerThread(Thread<abst_int_type> *t) {
		ThreadId tid;
		tid = 1;
	top:
		for (unsigned x = 0; x < threads->size(); x++) {
			if (threads->index(x)->exitted) {
				t->tid = tid;
				threads->set(x, t);
				return;
			}
			if (threads->index(x)->tid == tid) {
				++tid;
				goto top;
			}
		}
		t->tid = tid;
		threads->push(t);
	}
	Thread<abst_int_type> *findThread(ThreadId id, bool allow_failure = false) {
		unsigned x;
		for (x = 0; x < threads->size(); x++)
			if (threads->index(x)->tid == id)
				return threads->index(x);
		assert(allow_failure);
		return NULL;
	}
	const Thread<abst_int_type> *findThread(ThreadId id) const {
		unsigned x;
		for (x = 0; x < threads->size(); x++)
			if (threads->index(x)->tid == id)
				return threads->index(x);
		return NULL;
	}
	void exitGroup(abst_int_type result) {
		exitted = true;
		exit_status = result;
	}
	bool crashed() const;
	
	unsigned futexWake(abst_int_type key, bool do_it) {
		unsigned cntr = 0;
		for (unsigned x = 0; x < threads->size(); x++)
			if (threads->index(x)->blocked &&
			    force(threads->index(x)->futex_block_address == key)) {
				cntr++;
				if (do_it)
					threads->index(x)->futexUnblock();
			}
		return cntr;
	}
	MachineState<abst_int_type> *dupeSelf() const;

	void dumpSnapshot(LogWriter<abst_int_type> *lw) const;

	void visit(HeapVisitor &hv);
	void sanityCheck() const;

	void destruct() {}

	NAMED_CLASS
};

template <typename ait> class LogRecordFootstep;

enum InterpretResult {
	InterpretResultContinue = 0xf001,
	InterpretResultExit,
	InterpretResultCrash,
	InterpretResultIncomplete,
	InterpretResultTimedOut
};

template <typename ait> class MemoryTrace;

template <typename ait>
class EventRecorder : public GarbageCollected<EventRecorder<ait> > {
protected:
	virtual ~EventRecorder() {}
	virtual void record(Thread<ait> *thr, ThreadEvent<ait> *evt) = 0;
public:
	virtual void record(Thread<ait> *thr, ThreadEvent<ait> *evt,
			    MachineState<ait> *ms)
	{
		record(thr, evt);
	}
	void destruct() { this->~EventRecorder(); }
	NAMED_CLASS
};

template<typename abst_int_type>
class Interpreter {
	void replayFootstep(const LogRecordFootstep<abst_int_type> &lrf,
			    const LogReader<abst_int_type> *lr,
			    LogReaderPtr startOffset,
			    LogReaderPtr *endOffset);

public:
	VexPtr<MachineState<abst_int_type> > currentState;
	Interpreter(MachineState<abst_int_type> *rootMachine) : currentState(rootMachine)
	{
	}
	void replayLogfile(VexPtr<LogReader<abst_int_type> > &lf,
			   LogReaderPtr startingPoint,
			   GarbageCollectionToken,
			   LogReaderPtr *endingPoint,
			   VexPtr<LogWriter<abst_int_type> > &log,
			   VexPtr<EventRecorder<abst_int_type> > &er,
			   EventTimestamp *lastEvent = NULL);
	void replayLogfile(VexPtr<LogReader<abst_int_type> > &lf,
			   LogReaderPtr startingPoint,
			   GarbageCollectionToken tok)
	{
		replayLogfile(lf, startingPoint, tok, NULL);
	}
	void replayLogfile(VexPtr<LogReader<abst_int_type> > &lf,
			   LogReaderPtr startingPoint,
			   GarbageCollectionToken tok,
			   LogReaderPtr *endingPoint)
	{
		VexPtr<LogWriter<abst_int_type> > l(NULL);
		replayLogfile(lf, startingPoint, tok, endingPoint, l);
	}
	void replayLogfile(VexPtr<LogReader<abst_int_type> > &lf,
			   LogReaderPtr startingPoint,
			   GarbageCollectionToken tok,
			   LogReaderPtr *endingPoint,
			   VexPtr<LogWriter<abst_int_type> > &log)
	{
		VexPtr<EventRecorder<abst_int_type> > er(NULL);
		replayLogfile(lf, startingPoint, tok, endingPoint, log, er);
	}

	InterpretResult getThreadMemoryTrace(ThreadId tid,
					     MemoryTrace<abst_int_type> **output,
					     unsigned max_events,
					     GarbageCollectionToken t);
	void runToAccessLoggingEvents(ThreadId tid, unsigned nr_accesses,
				      GarbageCollectionToken t,
				      VexPtr<LogWriter<abst_int_type> > &output);
	void runToFailure(ThreadId tid, VexPtr<LogWriter<abst_int_type> > &output,
			  GarbageCollectionToken t,
			  unsigned max_events = 0);
	void runToEvent(EventTimestamp evt,
			VexPtr<LogReader<abst_int_type> > &lf,
			LogReaderPtr startingPoint,
			GarbageCollectionToken t,
			LogReaderPtr *endPoint = NULL);
};

template <typename ait>
class LogWriter : public GarbageCollected<LogWriter<ait> > {
public:
	virtual void append(LogRecord<ait> *lr, unsigned long idx) = 0;
	virtual ~LogWriter() {}
	InterpretResult recordEvent(Thread<ait> *thr, MachineState<ait> *ms, ThreadEvent<ait> *evt);

	NAMED_CLASS
};

class LogFileWriter : public LogWriter<unsigned long> {
	int fd;
public:
	void append(LogRecord<unsigned long> *lr, unsigned long idx);
	static LogFileWriter *open(const char *fname);
	~LogFileWriter();
	void visit(HeapVisitor &hv) {}
	void destruct() { this->~LogFileWriter(); }
};

template <typename ait> void destroy_memlog(void *_ctxt);

template <typename ait>
class MemLog : public LogReader<ait> {
	std::vector<LogRecord<ait> *> *content;
	unsigned offset;
	const MemLog<ait> *parent;

	static unsigned unwrapPtr(LogReaderPtr p) {
		return *(unsigned *)p.cls_data;
	}
	static LogReaderPtr mkPtr(unsigned o) {
		LogReaderPtr p;
		*(unsigned *)p.cls_data = o;
		return p;
	}

	/* Special, need to use placement new.  Should only really be
	   invoked from emptyMemlog(). */
protected:
	MemLog();

public:
	/* Can't multiply inherit GarbageCollected, so use a proxy
	 * object. */
	class Writer : public LogWriter<ait> {
		MemLog<ait> *underlying;
	public:
		Writer(MemLog<ait> *_underlying) : underlying(_underlying) {}
		void append(LogRecord<ait> *lr, unsigned long idx) {
			underlying->append(lr, idx);
		}
		void visit(HeapVisitor &hv) { hv(underlying); }
		void destruct() {}
		NAMED_CLASS
	};
	Writer *writer;

	static MemLog *emptyMemlog();
	static LogReaderPtr startPtr() { return mkPtr(0); }
	MemLog<ait> *dupeSelf() const;
	LogRecord<ait> *read(LogReaderPtr startPtr, LogReaderPtr *outPtr) const;
	void dump() const;

	void append(LogRecord<ait> *lr, unsigned long idx);

	/* Should only be called by GC destruct routine */
	virtual void destruct();

	virtual void visit(HeapVisitor &hv);

	NAMED_CLASS
};

template <typename ait>
class ThreadEvent : public Named, public GarbageCollected<ThreadEvent<ait> > {
protected:
	ThreadEvent(EventTimestamp _when) : when(_when) {}
public:
	EventTimestamp when;
	/* Replay the event using information in the log record */
	virtual ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> **ms,
					 bool &consumedRecord, LogReaderPtr ptr) = 0;
	/* Try to ``replay'' the event without reference to a pre-existing logfile */
	virtual InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL) = 0;
	/* Use the logfile if it matches, and otherwise fake it.  This
	   can fast-forward through the log e.g. to find a matching
	   syscall. */
	virtual ThreadEvent<ait> *fuzzyReplay(VexPtr<MachineState<ait> > &ms,
					      VexPtr<LogReader<ait> > &lf,
					      LogReaderPtr startPtr,
					      LogReaderPtr *endPtr,
					      GarbageCollectionToken t)
	{
		fake(ms, NULL);
		return NULL;
	}

	/* This should really be DNI, but g++ doesn't let you inherit
	 * from a class which has a private destructor. */
	~ThreadEvent() { abort(); }

	virtual void visit(HeapVisitor &hv){};
	virtual void destruct() {}

	NAMED_CLASS
};

template <typename ait>
class UseFreeMemoryEvent : public ThreadEvent<ait> {
public:
	ait free_addr;
	ait use_addr;
	EventTimestamp whenFreed;
private:
	UseFreeMemoryEvent(EventTimestamp _when,
			   ait _use_addr,
			   ait _free_addr,
			   EventTimestamp _whenFreed)
		: ThreadEvent<ait>(_when),
		  free_addr(_free_addr),
		  use_addr(_use_addr),
		  whenFreed(_whenFreed)
	{
	}
protected:
	char *mkName() const { return my_asprintf("useFree(%d:%lx, %s==%s, %d:%lx)",
						  this->when.tid._tid(),
						  this->when.idx,
						  name_aiv(use_addr),
						  name_aiv(free_addr),
						  whenFreed.tid._tid(),
						  whenFreed.idx); }
public:
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> **ms,
				 bool &consumedRecord, LogReaderPtr);
	InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	static ThreadEvent<ait> *get(EventTimestamp when,
				     ait use_addr,
				     ait free_addr,
				     EventTimestamp whenFreed)
	{ return new UseFreeMemoryEvent<ait>(when, use_addr, free_addr, whenFreed); }
};

template <typename ait>
class RdtscEvent : public ThreadEvent<ait> {
	IRTemp tmp;
	RdtscEvent(EventTimestamp when, IRTemp _tmp) : ThreadEvent<ait>(when), tmp(_tmp) {};
protected:
	virtual char *mkName() const { return my_asprintf("rdtsc(%d)", tmp); }
public:
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> **ms,
				 bool &consumedRecord, LogReaderPtr);
	InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	ThreadEvent<ait> *fuzzyReplay(VexPtr<MachineState<ait> > &ms,
				      VexPtr<LogReader<ait> > &lf,
				      LogReaderPtr startPtr,
				      LogReaderPtr *endPtr,
				      GarbageCollectionToken);
	static ThreadEvent<ait> *get(EventTimestamp when, IRTemp temp)
	{ return new RdtscEvent<ait>(when, temp); }
	NAMED_CLASS
};

template <typename ait> class MemoryAccessLoad;
template <typename ait> class MemoryAccessStore;

template <typename ait>
class LoadEvent : public ThreadEvent<ait> {
	friend class MemoryAccessLoad<ait>;
	IRTemp tmp;
public:
	ait addr;
private:
	unsigned size;
	LoadEvent(EventTimestamp when, IRTemp _tmp, ait _addr, unsigned _size) :
		ThreadEvent<ait>(when),
		tmp(_tmp),
		addr(_addr),
		size(_size)
	{
	}
protected:
	virtual char *mkName() const { return my_asprintf("load(%s, %d, %d)", name_aiv(addr), tmp, size); }
public:
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> **ms,
				 bool &consumedRecord, LogReaderPtr);
	InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	static ThreadEvent<ait> *get(EventTimestamp when, IRTemp _tmp, ait _addr, unsigned _size)
	{
		return new LoadEvent<ait>(when, _tmp, _addr, _size);
	}
	void visit(HeapVisitor &hv){ visit_aiv(addr, hv); ThreadEvent<ait>::visit(hv); }
	NAMED_CLASS
};

template <typename ait>
class StoreEvent : public ThreadEvent<ait> {
	friend class MemoryAccessStore<ait>;
public:
	ait addr;
	unsigned size;
	expression_result<ait> data;
private:
	StoreEvent(EventTimestamp when, ait addr, unsigned size, expression_result<ait> data);
protected:
	virtual char *mkName() const { return my_asprintf("store(%d, %s, %s)", size, name_aiv(addr), data.name()); }
public:
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> **ms,
				 bool &consumedRecord, LogReaderPtr);
	InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	static ThreadEvent<ait> *get(EventTimestamp when, ait _addr, unsigned _size, expression_result<ait> data)
	{
		return new StoreEvent<ait>(when, _addr, _size, data);
	}

	void visit(HeapVisitor &hv){ visit_aiv(addr, hv); data.visit(hv); ThreadEvent<ait>::visit(hv); }
	void destruct() { data.~expression_result<ait>(); ThreadEvent<ait>::destruct(); }
	NAMED_CLASS
};

template <typename ait>
class InstructionEvent : public ThreadEvent<ait> {
public:
	ait rip;
	ait reg0;
	ait reg1;
	ait reg2;
	ait reg3;
	ait reg4;
	bool allowRipMismatch;
	InstructionEvent(EventTimestamp when, ait _rip, ait _reg0, ait _reg1,
			 ait _reg2, ait _reg3, ait _reg4, bool _allowRipMismatch) :
		ThreadEvent<ait>(when),
		rip(_rip),
		reg0(_reg0),
		reg1(_reg1),
		reg2(_reg2),
		reg3(_reg3),
		reg4(_reg4),
		allowRipMismatch(_allowRipMismatch)
	{
	}
protected:
	virtual char *mkName() const {
		return my_asprintf("footstep(%s)", name_aiv(rip));
	}
public:
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> **ms,
				 bool &consumedRecord, LogReaderPtr);
	InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	static InstructionEvent<ait> *get(EventTimestamp when, ait _rip, ait _reg0, ait _reg1,
					  ait _reg2, ait _reg3, ait _reg4, bool _allowRipMismatch)
	{
		return new InstructionEvent<ait>(when, _rip, _reg0, _reg1, _reg2, _reg3, _reg4,
						 _allowRipMismatch);
	}

	void visit(HeapVisitor &hv)
	{
		visit_aiv(rip, hv);
		visit_aiv(reg0, hv);
		visit_aiv(reg1, hv);
		visit_aiv(reg2, hv);
		visit_aiv(reg3, hv);
		visit_aiv(reg4, hv);
		ThreadEvent<ait>::visit(hv);
	}
	NAMED_CLASS
};

template <typename ait>
class CasEvent : public ThreadEvent<ait> {
	IRTemp dest;
	expression_result<ait> addr;
	expression_result<ait> data;
	expression_result<ait> expected;
	unsigned size;
	CasEvent(EventTimestamp when,
		 IRTemp _dest,
		 expression_result<ait> _addr,
		 expression_result<ait> _data,
		 expression_result<ait> _expected,
		 unsigned _size) :
		ThreadEvent<ait>(when),
		dest(_dest),
		addr(_addr),
		data(_data),
		expected(_expected),
		size(_size)
	{
	}
protected:
	virtual char *mkName() const {
		return my_asprintf("cas(%s:%s -> %s; dest %d, size %d)",
				   addr.name(), expected.name(), data.name(),
				   dest, size);
	}
public:
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> **ms,
				 bool &consumedRecord, LogReaderPtr);
	virtual InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	virtual InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL,
				     LogRecord<ait> **lr2 = NULL);
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> *ms,
				 const LogReader<ait> *lf, LogReaderPtr ptr,
				 LogReaderPtr *outPtr, LogWriter<ait> *lw);
	ThreadEvent<ait> *fuzzyReplay(VexPtr<MachineState<ait> > &ms,
				      VexPtr<LogReader<ait> > &lf,
				      LogReaderPtr startPtr,
				      LogReaderPtr *endPtr,
				      GarbageCollectionToken);

	static ThreadEvent<ait> *get(EventTimestamp when,
				     IRTemp _dest,
				     expression_result<ait> _addr,
				     expression_result<ait> _data,
				     expression_result<ait> _expected,
				     unsigned _size)
	{
		return new CasEvent<ait>(when, _dest, _addr, _data, _expected, _size);
	}

	void visit(HeapVisitor &hv)
	{
		addr.visit(hv);
		data.visit(hv);
		expected.visit(hv);
		ThreadEvent<ait>::visit(hv);
	}
	void destruct()
	{
		addr.~expression_result<ait>();
		data.~expression_result<ait>();
		expected.~expression_result<ait>();
		ThreadEvent<ait>::destruct();
	}
	NAMED_CLASS
};

template <typename ait>
class SyscallEvent : public ThreadEvent<ait> {
protected:
	virtual char *mkName() const {
		return my_asprintf("syscall");
	}
	SyscallEvent(EventTimestamp when) : ThreadEvent<ait>(when) {}
public:
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> **ms,
				 bool &consumedRecord, LogReaderPtr ptr);
	InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	ThreadEvent<ait> *fuzzyReplay(VexPtr<MachineState<ait> > &ms,
				      VexPtr<LogReader<ait> > &lf,
				      LogReaderPtr startPtr,
				      LogReaderPtr *endPtr,
				      GarbageCollectionToken);
	static ThreadEvent<ait> *get(EventTimestamp when)
	{ return new SyscallEvent(when); }
	NAMED_CLASS
};

template <typename ait>
class SignalEvent : public ThreadEvent<ait> {
public:
	unsigned signr;
	ait virtaddr;
	SignalEvent(EventTimestamp when, unsigned _signr, ait _va) :
		ThreadEvent<ait>(when),
		signr(_signr),
		virtaddr(_va)
	{
	}
protected:
	virtual char *mkName() const {
		return my_asprintf("signal(nr = %d)", signr);
	}
public:
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> **ms,
				 bool &consumedRecord, LogReaderPtr);
	InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	static ThreadEvent<ait> *get(EventTimestamp when, unsigned _signr, ait _virtaddr)
	{
		return new SignalEvent<ait>(when, _signr, _virtaddr);
	}

	void visit(HeapVisitor &hv)
	{
		visit_aiv(virtaddr, hv);
		ThreadEvent<ait>::visit(hv);
	}
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

template <typename ait>
class MemoryAccess : public GarbageCollected<MemoryAccess<ait> >, public Named {
public:
	EventTimestamp when;
	ait addr;
	unsigned size;
	MemoryAccess(EventTimestamp _when, ait _addr, unsigned _size)
		: when(_when),
		  addr(_addr),
		  size(_size)
	{
		assert_gc_allocated(this);
	}
	virtual bool isLoad() = 0;
	void dump() const { printf("%s\n", name()); }
	void visit(HeapVisitor &hv){ visit_aiv(addr, hv); }
	void destruct() {}
	NAMED_CLASS
};

template <typename ait>
class LogRecordLoad : public LogRecord<ait> {
	friend class LoadEvent<ait>;
	friend class CasEvent<ait>;
	friend class MemoryAccessLoad<ait>;
	unsigned size;
public:
	ait ptr;
private:
	expression_result<ait> value;
protected:
	char *mkName() const {
		return my_asprintf("load(%x)", size);
	}
public:
	LogRecordLoad(ThreadId _tid,
		      unsigned _size,
		      ait _ptr,
		      expression_result<ait> _value) :
		LogRecord<ait>(_tid),
		size(_size),
		ptr(_ptr),
		value(_value)
	{
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
	template <typename outtype> LogRecordLoad<outtype> *abstract() const
	{
		expression_result<outtype> nvalue;
		value.abstract(&nvalue);
		return new LogRecordLoad<outtype>(this->thread(),
						  size,
						  mkConst<outtype>(ptr),
						  nvalue);
	}
	void visit(HeapVisitor &hv){ value.visit(hv); visit_aiv(ptr, hv); }
};

template <typename ait>
class MemoryAccessLoad : public MemoryAccess<ait> {
protected:
	virtual char *mkName() const {
		return my_asprintf("%d: Load(%x)", this->when.tid._tid(),
				   this->size);
	}
public:
	MemoryAccessLoad(const class LoadEvent<ait> &evt)
		: MemoryAccess<ait>(evt.when, evt.addr, evt.size)
	{
	}
	virtual bool isLoad() { return true; }
};

template <typename ait>
class LogRecordStore : public LogRecord<ait> {
	friend class StoreEvent<ait>;
	friend class CasEvent<ait>;
	friend class MemoryAccessStore<ait>;
	unsigned size;
public:
	ait ptr;
private:
	expression_result<ait> value;
protected:
	virtual char *mkName() const {
		return my_asprintf("store(%x,%s)", size, name_aiv(ptr));
	}
public:
	LogRecordStore(ThreadId _tid,
		       unsigned _size,
		       ait _ptr,
		       expression_result<ait> _value) :
		LogRecord<ait>(_tid),
		size(_size),
		ptr(_ptr),
		value(_value)
	{
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
	template <typename outtype> LogRecordStore<outtype> *abstract() const
	{
		expression_result<outtype> res;
		value.abstract(&res);
		return new LogRecordStore<outtype>(this->thread(),
						   size,
						   mkConst<outtype>(ptr),
						   res);
	}
	void visit(HeapVisitor &hv){ value.visit(hv); visit_aiv(ptr, hv); }
};

template <typename ait>
class MemoryAccessStore : public MemoryAccess<ait> {
protected:
	virtual char *mkName() const {
		return my_asprintf("%d: Store(%x)",
				   this->when.tid._tid(),
				   this->size);
	}
public:
	MemoryAccessStore(const class StoreEvent<ait> &evt)
		: MemoryAccess<ait>(evt.when, evt.addr, evt.size)
	{
	}
	virtual bool isLoad() { return false; }
};

/* Essentially a thin wrapper around std::vector */
template <typename ait>
class MemoryTrace : public GarbageCollected<MemoryTrace<ait> > {
public:
	std::vector<MemoryAccess<ait> *> content;
	static MemoryTrace<ait> *get(VexPtr<MachineState<ait> > &,
				     VexPtr<LogReader<ait> > &,
				     LogReaderPtr,
				     GarbageCollectionToken);
	size_t size() const { return content.size(); }
	MemoryAccess<ait> *&operator[](unsigned idx) { return content[idx]; }
	void push_back(MemoryAccess<ait> *x) { content.push_back(x); }
	MemoryTrace() : content() {}
	void dump() const;
	void visit(HeapVisitor &hv){ visit_container(content, hv); }
	void destruct() { this->~MemoryTrace<ait>(); }
	NAMED_CLASS
};

template <typename ait> void
visit_memory_trace_fn(MemoryTrace<ait> *&h, HeapVisitor &hv)
{
	hv(h);
}

template <typename ait>
class MemTracePool : public GarbageCollected<MemTracePool<ait> > {
	typedef gc_map<ThreadId, MemoryTrace<ait> *, __default_hash_function, __default_eq_function,
		       visit_memory_trace_fn<ait> > contentT;
	contentT *content;
public:
	static MemTracePool<ait> *get(VexPtr<MachineState<ait> > &base_state, ThreadId ignoredThread, GarbageCollectionToken t);
	gc_map<ThreadId, Maybe<unsigned> > *firstRacingAccessMap();
	void visit(HeapVisitor &hv);
	void destruct() { }
	NAMED_CLASS
};

template <typename ait>
class LogRecordFootstep : public LogRecord<ait> {
protected:
	virtual char *mkName() const {
		return my_asprintf("footstep()");
	}
public:
	ait rip;
	ait reg0;
	ait reg1;
	ait reg2;
	ait reg3;
	ait reg4;
	LogRecordFootstep(ThreadId _tid,
			  ait _rip,
			  ait _reg0,
			  ait _reg1,
			  ait _reg2,
			  ait _reg3,
			  ait _reg4) :
		LogRecord<ait>(_tid),
		rip(_rip),
		reg0(_reg0),
		reg1(_reg1),
		reg2(_reg2),
		reg3(_reg3),
		reg4(_reg4)
	{
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
	template <typename outtype> LogRecordFootstep<outtype> *abstract() const
	{
		return new LogRecordFootstep<outtype>(this->thread(),
						      mkConst<outtype>(rip),
						      mkConst<outtype>(reg0),
						      mkConst<outtype>(reg1),
						      mkConst<outtype>(reg2),
						      mkConst<outtype>(reg3),
						      mkConst<outtype>(reg4));
	}
	void visit(HeapVisitor &hv)
	{
		visit_aiv(rip, hv);
		visit_aiv(reg0, hv);
		visit_aiv(reg1, hv);
		visit_aiv(reg2, hv);
		visit_aiv(reg3, hv);
		visit_aiv(reg4, hv);
	}
};

template <typename ait>
class LogRecordSyscall : public LogRecord<ait> {
protected:
	virtual char *mkName() const {
		return my_asprintf("syscall()");
	}
public:
	ait sysnr, res, arg1, arg2, arg3;
	LogRecordSyscall(ThreadId _tid,
			 ait _sysnr,
			 ait _res,
			 ait _arg1,
			 ait _arg2,
			 ait _arg3) :
		LogRecord<ait>(_tid),
		sysnr(_sysnr),
		res(_res),
		arg1(_arg1),
		arg2(_arg2),
		arg3(_arg3)
	{
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
	template <typename outtype> LogRecordSyscall<outtype> *abstract() const
	{
		return new LogRecordSyscall<outtype>(this->thread(),
						     mkConst<outtype>(sysnr),
						     mkConst<outtype>(res),
						     mkConst<outtype>(arg1),
						     mkConst<outtype>(arg2),
						     mkConst<outtype>(arg3));
	}
	void visit(HeapVisitor &hv)
	{
		visit_aiv(sysnr, hv);
		visit_aiv(res, hv);
		visit_aiv(arg1, hv);
		visit_aiv(arg2, hv);
		visit_aiv(arg3, hv);
	}
};

template <typename ait>
class LogRecordMemory : public LogRecord<ait> {
protected:
	char *mkName() const {
		return my_asprintf("memory(%x)", size);
	}
	LogRecordMemory(const LogRecordMemory &); /* DNI */
	void operator=(const LogRecordMemory &); /* DNI */
public:
	unsigned size;
	ait start;
	const ait *contents;
	LogRecordMemory(ThreadId _tid,
			unsigned _size,
			ait _start,
			const ait *_contents) :
		LogRecord<ait>(_tid),
		size(_size),
		start(_start),
		contents(_contents)
	{
	}
	~LogRecordMemory()
	{ 
		free((void *)contents);
	}
	void destruct() { this->~LogRecordMemory(); }
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
	template <typename outtype> LogRecordMemory<outtype> *abstract() const
	{
		outtype *b = (outtype *)malloc(size * sizeof(outtype));
		for (unsigned x = 0; x < size; x++)
			b[x] = mkConst<outtype>(contents[x]);
		return new LogRecordMemory<outtype>(this->thread(), size, mkConst<outtype>(start), b);
	}
	void visit(HeapVisitor &hv)
	{
		visit_aiv(start, hv);
	}
};

template <typename ait>
class LogRecordRdtsc : public LogRecord<ait> {
	friend class RdtscEvent<ait>;
	ait tsc;
protected:
	char *mkName() const {
		return my_asprintf("rdtsc()");
	}
public:
	LogRecordRdtsc(ThreadId _tid,
		       ait _tsc)
		: LogRecord<ait>(_tid),
		  tsc(_tsc)
	{
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
	template <typename outtype> LogRecordRdtsc<outtype> *abstract() const
	{
		return new LogRecordRdtsc<outtype>(this->thread(),
						   mkConst<outtype>(tsc));
	}
	void visit(HeapVisitor &hv) { visit_aiv(tsc, hv); }
};

template <typename ait>
class LogRecordSignal : public LogRecord<ait> {
public:
	virtual char *mkName() const {
		return my_asprintf("signal(nr = %d)", signr);
	}
public:
	ait rip;
	unsigned signr;
	ait err;
	ait virtaddr;
	LogRecordSignal(ThreadId _tid,
			ait _rip,
			unsigned _signr,
			ait _err,
			ait _va) :
		LogRecord<ait>(_tid),
		rip(_rip),
		signr(_signr),
		err(_err),
		virtaddr(_va)
	{
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
	template <typename outtype> LogRecordSignal<outtype> *abstract() const
	{
		return new LogRecordSignal<outtype>(this->thread(),
						    mkConst<outtype>(rip),
						    signr,
						    mkConst<outtype>(err),
						    mkConst<outtype>(virtaddr));
	}
	void visit(HeapVisitor &hv)
	{
		visit_aiv(rip, hv);
		visit_aiv(err, hv);
		visit_aiv(virtaddr, hv);
	}
};

template <typename ait>
class LogRecordAllocateMemory : public LogRecord<ait> {
	friend class AddressSpace<ait>;
	ait start;
	ait size;
	unsigned prot;
	unsigned flags;
protected:
	virtual char *mkName() const {
		return my_asprintf("allocate(prot = %x, flags = %x)",
				   prot, flags);
	}
public:
	LogRecordAllocateMemory(ThreadId _tid,
				ait _start,
				ait _size,
				unsigned _prot,
				unsigned _flags) :
		LogRecord<ait>(_tid),
		start(_start),
		size(_size),
		prot(_prot),
		flags(_flags)
	{
	}      
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
	template <typename outtype> LogRecordAllocateMemory<outtype> *abstract() const
	{
		return new LogRecordAllocateMemory<outtype>(this->thread(),
							    mkConst<outtype>(start),
							    mkConst<outtype>(size),
							    prot,
							    flags);
	}
	void visit(HeapVisitor &hv){ visit_aiv(start, hv); visit_aiv(size, hv); }
};

template <typename ait>
class LogRecordInitialRegisters : public LogRecord<ait> {
	friend class Thread<ait>;
	VexGuestAMD64State regs;
protected:
	virtual char *mkName() const {
		return strdup("initial_regs");
	}
public:
	LogRecordInitialRegisters(ThreadId tid,
				  const VexGuestAMD64State &r) :
		LogRecord<ait>(tid),
		regs(r)
	{
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
	template <typename outtype> LogRecordInitialRegisters<outtype> *abstract() const
	{
		return new LogRecordInitialRegisters<outtype>(this->thread(), regs);
	}
};

template <typename ait>
class LogRecordInitialBrk : public LogRecord<ait> {
protected:
	virtual char *mkName() const {
		return my_asprintf("initbrk()");
	}
public:
	ait brk;
	LogRecordInitialBrk(ThreadId tid,
			    ait _brk) :
		LogRecord<ait>(tid),
		brk(_brk)
	{
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
	template <typename outtype> LogRecordInitialBrk<outtype> *abstract() const
	{
		return new LogRecordInitialBrk<outtype>(this->thread(),
							mkConst<outtype>(brk));
	}
	void visit(HeapVisitor &hv){ visit_aiv(brk, hv); }
};

template <typename ait>
class LogRecordVexThreadState : public LogRecord<ait> {
protected:
	virtual char *mkName() const {
		return strdup("vex state");
	}
public:
	ait currentIRSBRip;
	expression_result_array<ait> tmp;
	unsigned statement_nr;
	LogRecordVexThreadState(ThreadId tid, ait _currentIRSBRip,
				unsigned _statement_nr, expression_result_array<ait> _tmp);
	void *marshal(unsigned *sz) const;
	unsigned marshal_size() const;
	template <typename outtype> LogRecordVexThreadState<outtype> *abstract() const
	{
		expression_result_array<outtype> ntmp;
		tmp.abstract(&ntmp);
		return new LogRecordVexThreadState<outtype>(
			this->thread(), mkConst<outtype>(currentIRSBRip),
			statement_nr, ntmp);
	}
	void visit(HeapVisitor &hv){ tmp.visit(hv); }
};

template <typename ait>
class client_freed_entry {
public:
	ait start;
	ait end;
	EventTimestamp when;
};

template <typename ait>
class AddressSpace : public GarbageCollected<AddressSpace<ait> > {
public:
	unsigned long brkptr;
	unsigned long brkMapPtr;
	VAMap *vamap;
	PMap<ait> *pmap;
	ait client_free;

	bool isOnFreeList(ait start, ait end,
			  ThreadId asker,
			  EventTimestamp *when = NULL,
			  ait *free_addr = NULL) const;
private:
	bool extendStack(unsigned long ptr, unsigned long rsp);
	void checkFreeList(ait start, ait end, ThreadId asking, EventTimestamp now);
public:
	IRSB *getIRSBForAddress(unsigned long rip);

	void findInterestingFunctions(const VAMap::VAMapEntry *vme);
	void findInterestingFunctions();

	void allocateMemory(ait start, ait size, VAMap::Protection prot,
			    VAMap::AllocFlags flags = VAMap::defaultFlags);
	void allocateMemory(const LogRecordAllocateMemory<ait> &rec)
	{
		allocateMemory(rec.start, rec.size, rec.prot, rec.flags);
	}
	void releaseMemory(ait start, ait size);
	void protectMemory(ait start, ait size, VAMap::Protection prot);
	void populateMemory(const LogRecordMemory<ait> &rec)
	{
		writeMemory(EventTimestamp::invalid, rec.start, rec.size, rec.contents, true, NULL);
	}
	void store(EventTimestamp when, ait start, unsigned size, const expression_result<ait> &val,
		   bool ignore_protection = false,
		   Thread<ait> *thr = NULL);
	void writeMemory(EventTimestamp when, ait start, unsigned size,
			 const ait *contents, bool ignore_protection,
			 Thread<ait> *thr);
	bool copyToClient(EventTimestamp when, ait start, unsigned size,
			  const void *source);
	bool copyFromClient(EventTimestamp when, ait start, unsigned size,
			    void *dest);
	void writeLiteralMemory(unsigned long start, unsigned size, const unsigned char *content);
	expression_result<ait> load(EventTimestamp when, ait start, unsigned size,
				    bool ignore_protection = false,
				    Thread<ait> *thr = NULL);
	template <typename t> const t fetch(unsigned long addr,
					    Thread<ait> *thr);
	EventTimestamp readMemory(ait start, unsigned size,
				  ait *contents, bool ignore_protection,
				  Thread<ait> *thr,
				  ait *storeAddr = NULL);
	bool isAccessible(ait start, unsigned size,
			  bool isWrite, Thread<ait> *thr);
	bool isWritable(ait start, unsigned size,
			Thread<ait> *thr = NULL) {
		return isAccessible(start, size, true, thr);
	}
	bool isReadable(ait start, unsigned size,
			Thread<ait> *thr = NULL) {
		return isAccessible(start, size, false, thr);
	}
	unsigned long setBrk(ait newBrk);

	static AddressSpace *initialAddressSpace(ait initialBrk);
	AddressSpace *dupeSelf() const;
	void visit(HeapVisitor &hv);
	void sanityCheck() const;

	void addVsyscalls();

	void dumpBrkPtr(LogWriter<ait> *lw) const;
	void dumpSnapshot(LogWriter<ait> *lw) const;

	char *readString(ait start, Thread<ait> *thr);

	template <typename new_type> AddressSpace<new_type> *abstract() const;

	void destruct() { this->~AddressSpace(); }

	typedef std::vector<client_freed_entry<ait> > freed_memory_t;
	freed_memory_t freed_memory;

	void client_freed(EventTimestamp when, ait ptr);

	NAMED_CLASS

	class trans_hash_entry : public GarbageCollected<trans_hash_entry> {
	public:
		trans_hash_entry *next;
		trans_hash_entry **pprev;

		unsigned long rip;
		WeakRef<IRSB> *irsb;

		void visit(HeapVisitor &hv) { hv(next); hv(irsb); }
		void destruct() { this->~trans_hash_entry(); }

		void relocate(trans_hash_entry *target, size_t sz) {
			if (target->next)
				target->next->pprev = &target->next;
			*target->pprev = target;
			memset(this, 0x73, sizeof(*this));
		}
		trans_hash_entry(unsigned long _rip)
			: next(NULL),
			  pprev(NULL),
			  rip(_rip)
		{
			irsb = new WeakRef<IRSB>();
		}
		NAMED_CLASS
	};

	WeakRef<IRSB> *searchDecodeCache(unsigned long rip);

	void relocate(AddressSpace<ait> *target, size_t sz);

	void sanityCheckDecodeCache(void) const
#if 1
	{}
#else
	;
#endif

private:
	static const unsigned nr_trans_hash_slots = 2048;
	trans_hash_entry *trans_hash[nr_trans_hash_slots];
};

template<typename ait> ThreadEvent<ait> * replay_syscall(const LogRecordSyscall<ait> *lrs,
							 Thread<ait> *thr,
							 MachineState<ait> *&mach,
							 LogReaderPtr ptr);

template<typename ait> void process_memory_records(VexPtr<AddressSpace<ait> > &addrSpace,
						   VexPtr<LogReader<ait> > &lf,
						   LogReaderPtr startOffset,
						   LogReaderPtr *endOffset,
						   VexPtr<LogWriter<ait> > &lw,
						   GarbageCollectionToken tok);

void debugger_attach(void);

void init_sli(void);

struct abstract_interpret_value;

class Expression;

#define FOREACH_EXPR_CLASS			\
	DO_EXPR_CLASS(BottomExpression)		\
	DO_EXPR_CLASS(ConstExpression)		\
	DO_EXPR_CLASS(ExpressionLastStore)	\
	DO_EXPR_CLASS(ExpressionHappensBefore)	\
	DO_EXPR_CLASS(LoadExpression)		\
	DO_EXPR_CLASS(BinaryExpression)		\
	DO_EXPR_CLASS(UnaryExpression)		\
	DO_EXPR_CLASS(ternarycondition)		\
	DO_EXPR_CLASS(ExpressionRip)		\
	DO_EXPR_CLASS(ExpressionBadPointer)

#define DO_EXPR_CLASS(x) class x;
FOREACH_EXPR_CLASS
#undef DO_EXPR_CLASS

class ExpressionMapper {
public:
#define DO_EXPR_CLASS(x) virtual Expression *map(x *e);
	FOREACH_EXPR_CLASS
#undef DO_EXPR_CLASS
	virtual Expression *idmap(Expression *e);
};

class ExpressionVisitor {
public:
	virtual void visit(Expression *e) = 0;
};

class Expression : public Named, public GarbageCollected<Expression> {
	friend class ConstExpression;
	friend void fixup_expression_table(void);

	static const unsigned nr_heads = 262147;
	static Expression *heads[nr_heads];
	static unsigned chain_lengths[nr_heads];
	static unsigned long eq_calls[nr_heads];
	static unsigned tot_outstanding;
	static unsigned nr_interned;
	Expression *next;
	Expression **pprev;
	unsigned long hashval;
	static void dump_eq_calls_table();
	static void dump_chain_length_table();
	void remove_from_hash() {
		if (pprev != &next)
			chain_lengths[hashval % nr_heads]--;
		*pprev = next;
		if (next)
			next->pprev = pprev;
		pprev = &next;
		next = NULL;
	}
	void add_to_hash() {
		assert(pprev == &next);
		pprev = &heads[hashval % nr_heads];
		next = *pprev;
		if (next)
			next->pprev = &next;
		*pprev = this;
		chain_lengths[hashval % nr_heads]++;
	}
	void pull_to_front() {
		if (heads[hashval % nr_heads] != this) {
			remove_from_hash();
			add_to_hash();
		}
	}
	mutable WeakRef<Expression> *cnf;
	mutable WeakRef<Expression> *concrete;
protected:
	static Expression *intern(Expression *e);
	virtual unsigned long _hash() const = 0;
	virtual bool _isEqual(const Expression *other) const = 0;
	virtual Expression *_CNF() { return this; }
	virtual Expression *_concretise() = 0;
	static void lastAccessTS(EventTimestamp ts, gc_map<ThreadId, unsigned long> *output)
	{
		if ((*output)[ts.tid] < ts.idx)
			(*output)[ts.tid] = ts.idx;
	}
	virtual const gc_map<ThreadId, unsigned long> *_lastAccessMap() = 0;
	virtual void _visit(HeapVisitor &hv) = 0;

	~Expression() {
		remove_from_hash();
		tot_outstanding--;
	}
private:
	WeakRef<const gc_map<ThreadId, unsigned long> > *lastAccessedMap;
public:
	static void mergeAccessMaps(gc_map<ThreadId, unsigned long> *out,
				    const gc_map<ThreadId, unsigned long> *in);
	unsigned hash() const { return hashval; }
	virtual bool isConstant(unsigned long *cv) const { return false; }
	virtual bool isLogical() const { return false; }
	virtual EventTimestamp timestamp() const { return EventTimestamp::invalid; }
	virtual Expression *refine(VexPtr<MachineState<abstract_interpret_value> > &ms,
				   VexPtr<LogReader<abstract_interpret_value> > &lf,
				   LogReaderPtr ptr,
				   bool *progress,
				   VexPtr<gc_map<ThreadId, unsigned long> > &validity,
				   EventTimestamp ev,
				   GarbageCollectionToken t) = 0;
	virtual void visit(ExpressionVisitor &ev) = 0;
	virtual Expression *map(ExpressionMapper &f) = 0;
	virtual Relevance relevance(const EventTimestamp &ev, Relevance low_threshold,
				    Relevance high_threshold) = 0;
	const gc_map<ThreadId, unsigned long> *lastAccessMap() {
		if (!lastAccessedMap)
			lastAccessedMap = new WeakRef<const gc_map<ThreadId, unsigned long> >();
		if (!lastAccessedMap->get())
			lastAccessedMap->set(_lastAccessMap());
		return lastAccessedMap->get();
	}
	Expression *concretise() {
		if (!concrete)
			concrete = new WeakRef<Expression>();
		if (!concrete->get())
			concrete->set(_concretise());
		return concrete->get();
	}
	Expression *CNF() {
		if (!cnf)
			cnf = new WeakRef<Expression>();
		if (!cnf->get())
			cnf->set(_CNF());
		return cnf->get();
	}
	Expression() : Named(), next(NULL), pprev(&next), hashval(0) {}
	bool isEqual(const Expression *other) const {
		if (other == this)
			return true;
		else if (hashval == other->hashval)
			return _isEqual(other);
		else
			return false;
	}

	void visit(HeapVisitor &hv) {
		hv(lastAccessedMap);
		hv(cnf);
		hv(concrete);
		_visit(hv);
	}

	void relocate(Expression *target, size_t) {
		if (target->next)
			target->next->pprev = &target->next;
		*target->pprev = target;
	}

	virtual Expression *restrictToMask(unsigned long mask) = 0;

	NAMED_CLASS
};

class UnrefinableExpression : public Expression {
public:
	Expression *refine(VexPtr<MachineState<abstract_interpret_value> > &ms,
			   VexPtr<LogReader<abstract_interpret_value> > &lf,
			   LogReaderPtr ptr,
			   bool *progress,
			   VexPtr<gc_map<ThreadId, unsigned long> >&validity,
			   EventTimestamp ev,
			   GarbageCollectionToken t) { return this; }
	Relevance relevance(const EventTimestamp &ev, Relevance, Relevance) { return Relevance::irrelevant; }
};

class BottomExpression : public UnrefinableExpression {
	static BottomExpression *bottom;
protected:
	unsigned long _hash() const { return 0x1234567; }
	char *mkName() const { return my_asprintf("_|_"); }
	bool _isEqual(const Expression *other) const { return false; }
	Expression *_concretise() { return this; }
	void _visit(HeapVisitor &hv) {}
	gc_map<ThreadId, unsigned long> *_lastAccessMap() { return new gc_map<ThreadId, unsigned long>(); }
public:
	static Expression *get()
	{
		if (!bottom)
			bottom = new BottomExpression();
		return bottom;
	}
	void visit(ExpressionVisitor &ev) { ev.visit(this); }
	Expression *map(ExpressionMapper &f) { return f.map(this); }
	virtual Expression *restrictToMask(unsigned long mask) { return this; }
};

class ConstExpression : public UnrefinableExpression {
public:
        unsigned long v;
protected:
	unsigned long _hash() const { return v; }
	char *mkName() const { return my_asprintf("%lx", v); }
	bool _isEqual(const Expression *other) const
	{
		const ConstExpression *ce = dynamic_cast<const ConstExpression *>(other);
		if (ce && ce->v == v)
			return true;
		else
			return false;
	}
	Expression *_concretise() { return this; }
	void _visit(HeapVisitor &hv) {}
	gc_map<ThreadId, unsigned long> *_lastAccessMap() { return new gc_map<ThreadId, unsigned long>();}
public:
	bool isLogical() const { return v == 0 || v == 1; }
	static Expression *get(unsigned long v)
	{
		/* Search the hash table first */
		unsigned h_index = v % nr_heads;
		Expression *cursor = Expression::heads[h_index];
		while (cursor) {
			if (cursor->hashval == v &&
			    dynamic_cast<ConstExpression *>(cursor)) {
				/* We know that, for const expressions, if the
				   hash matches then so does the value, so don't
				   need to do a full comparison. */
				cursor->pull_to_front();
				return cursor;
			}
			cursor = cursor->next;
		}
		ConstExpression *work = new ConstExpression();
		work->v = v;
		work->hashval = v;
		work->add_to_hash();
		Expression::nr_interned++;
		return work;
	}
	void visit(ExpressionVisitor &ev) { ev.visit(this); }
	Expression *map(ExpressionMapper &m) { return m.map(this); }
	bool isConstant(unsigned long *cv) const { *cv = v; return true; }
	virtual Expression *restrictToMask(unsigned long mask) { return get(v & mask); }
};

class ExpressionLastStore : public Expression {
public:
	EventTimestamp load;
	EventTimestamp store;
	Expression *vaddr;
	unsigned long concrete_vaddr;
private:
	ExpressionLastStore(EventTimestamp _load, EventTimestamp _store,
			    Expression *_vaddr, unsigned long _concrete_vaddr)
		: load(_load), store(_store), vaddr(_vaddr),
		  concrete_vaddr(_concrete_vaddr)
	{
	}
protected:
	char *mkName(void) const {
		return my_asprintf("(lastStore@%d:%lx:%s -> %d:%lx)",
				   load.tid._tid(),
				   load.idx,
				   vaddr->name(),
				   store.tid._tid(),
				   store.idx);
	}
	unsigned long _hash() const {
		return load.hash() ^ store.hash() ^ vaddr->hash();
	}
	bool _isEqual(const Expression *other) const {
		const ExpressionLastStore *oth = dynamic_cast<const ExpressionLastStore *>(other);
		if (oth &&
		    load == oth->load &&
		    store == oth->store &&
		    vaddr->isEqual(oth->vaddr))
			return true;
		else
			return false;
	}
	Expression *_concretise() {
		Expression *va = vaddr->concretise();
		if (va == vaddr)
			return this;
		return get(load, store, va, concrete_vaddr);
	}
	void _visit(HeapVisitor &hv) { hv(vaddr); }

	gc_map<ThreadId, unsigned long> *_lastAccessMap()
	{
		gc_map<ThreadId, unsigned long> *work;
		work = new gc_map<ThreadId, unsigned long>(*vaddr->lastAccessMap());
		lastAccessTS(load, work);
		lastAccessTS(store, work);
		return work;
	}

public:
	static Expression *get(EventTimestamp load, EventTimestamp store,
			       Expression *vaddr, unsigned long concrete_vaddr)
	{
		return intern(new ExpressionLastStore(load, store, vaddr,
						      concrete_vaddr));
	}
	Expression *refine(VexPtr<MachineState<abstract_interpret_value> > &ms,
			   VexPtr<LogReader<abstract_interpret_value> > &lf,
			   LogReaderPtr ptr,
			   bool *progress,
			   VexPtr<gc_map<ThreadId, unsigned long> >&validity,
			   EventTimestamp ev,
			   GarbageCollectionToken);
	void visit(ExpressionVisitor &ev) { ev.visit(this); vaddr->visit(ev); }
	Expression *map(ExpressionMapper &m) { return m.map(this); }
	EventTimestamp timestamp() const { return load; }
	bool isLogical() const { return true; }
	Relevance relevance(const EventTimestamp &ev, Relevance low_thresh, Relevance high_thresh) {
		if (low_thresh >= high_thresh)
			return low_thresh;
		Relevance r = Relevance(Relevance(load, ev),
					Relevance(store, ev));
		if (r >= high_thresh)
			return r;
		else
			return Relevance(r, vaddr->relevance(ev, r + 1, high_thresh));
	}

	virtual Expression *restrictToMask(unsigned long mask) { return this; }
};

class ExpressionHappensBefore : public Expression {
public:
	EventTimestamp before;
	EventTimestamp after;
private:
	ExpressionHappensBefore(EventTimestamp _before, EventTimestamp _after)
		: before(_before), after(_after)
	{
	}
protected:
	char *mkName(void) const {
		return my_asprintf("(%d:%lx <-< %d:%lx)",
				   before.tid._tid(),
				   before.idx,
				   after.tid._tid(),
				   after.idx);
	}
	unsigned long _hash() const {
		return before.hash() ^ after.hash();
	}
	bool _isEqual(const Expression *other) const {
		const ExpressionHappensBefore *oth = dynamic_cast<const ExpressionHappensBefore *>(other);
		if (oth &&
		    oth->before == before &&
		    oth->after == after)
			return true;
		else
			return false;
	}
	Expression *_concretise() { return this; }
	void _visit(HeapVisitor &hv) {}
	gc_map<ThreadId, unsigned long> *_lastAccessMap()
	{
		gc_map<ThreadId, unsigned long> *work = new gc_map<ThreadId, unsigned long>();
		lastAccessTS(before, work);
		lastAccessTS(after, work);
		return work;
	}
public:
	static Expression *get(EventTimestamp before, EventTimestamp after)
	{
		if (after.tid._tid() == 0 || after.tid == ThreadId::invalidTid)
			return ConstExpression::get(0);
		if (before.tid._tid() == 0 || before.tid == ThreadId::invalidTid)
			return ConstExpression::get(1);
		if (before.tid == after.tid) {
			if (before.idx < after.idx)
				return ConstExpression::get(1);
			else
				return ConstExpression::get(0);
		} else {
			return intern(new ExpressionHappensBefore(before, after));
		}
	}
	EventTimestamp timestamp() const { return after; }
	bool isLogical() const { return true; }
	void visit(ExpressionVisitor &ev) { ev.visit(this); }
	Expression *map(ExpressionMapper &m) { return m.map(this); }

	Expression *refine(VexPtr<MachineState<abstract_interpret_value> > &ms,
			   VexPtr<LogReader<abstract_interpret_value> > &lf,
			   LogReaderPtr ptr,
			   bool *progress,
			   VexPtr<gc_map<ThreadId, unsigned long> > &validity,
			   EventTimestamp ev,
			   GarbageCollectionToken) { return this; }

	Relevance relevance(const EventTimestamp &ev, Relevance, Relevance) {
		/* happens-before relations can't be refined, so their
		   relevance kind of doesn't matter. */
		return Relevance::irrelevant;
	}

	virtual Expression *restrictToMask(unsigned long mask) { return this; }
};

class LoadExpression : public Expression {
public:
	Expression *val;
	Expression *addr;
	Expression *storeAddr;
	unsigned long concrete_addr;
	EventTimestamp when;
	EventTimestamp store;
	unsigned size;
protected:
	char *mkName() const { return my_asprintf("(load%d@%d:%lx:%lx;%d:%lx:%lx %s:%s -> %s)",
						  size, when.tid._tid(), when.idx, when.rip,
						  store.tid._tid(), store.idx, store.rip,
						  addr->name(), storeAddr->name(),
						  val->name()); }
	unsigned long _hash() const { return val->hash() ^ (addr->hash() * 3) ^ (when.hash() * 5) ^ (store.hash() * 7) ^ (storeAddr->hash() * 11) ^ (size * 13); }
	bool _isEqual(const Expression *other) const {
		const LoadExpression *le = dynamic_cast<const LoadExpression *>(other);
		if (le &&
		    le->when == when &&
		    le->store == store &&
		    le->size == size &&
		    le->val->isEqual(val) &&
		    le->addr->isEqual(addr) &&
		    le->storeAddr->isEqual(storeAddr))
			return true;
		else
			return false;
	}
	Expression *_concretise() { return val->concretise(); }
	void _visit(HeapVisitor &hv) { hv(addr); hv(val); hv(storeAddr); }

	gc_map<ThreadId, unsigned long> *_lastAccessMap()
	{
		gc_map<ThreadId, unsigned long> *work;
		work = new gc_map<ThreadId, unsigned long>(*val->lastAccessMap());
		mergeAccessMaps(work, addr->lastAccessMap());
		mergeAccessMaps(work, storeAddr->lastAccessMap());
		lastAccessTS(when, work);
		lastAccessTS(store, work);
		return work;
	}

public:
	static Expression *get(EventTimestamp when, Expression *val, Expression *addr,
			       Expression *storeAddr, EventTimestamp store, unsigned size,
			       unsigned long concrete_addr)
	{
		LoadExpression *work = new LoadExpression();
		work->val = val;
		work->addr = addr;
		work->storeAddr = storeAddr;
		work->when = when;
		work->store = store;
		work->size = size;
		work->concrete_addr = concrete_addr;
		return intern(work);
	}
	Expression *refine(VexPtr<MachineState<abstract_interpret_value> > &ms,
			   VexPtr<LogReader<abstract_interpret_value> > &lf,
			   LogReaderPtr ptr,
			   bool *progress,
			   VexPtr<gc_map<ThreadId, unsigned long> >&validity,
			   EventTimestamp ev,
			   GarbageCollectionToken);

	EventTimestamp timestamp() const { return when; }
	void visit(ExpressionVisitor &ev) { ev.visit(this); val->visit(ev); addr->visit(ev); storeAddr->visit(ev); }
	Expression *map(ExpressionMapper &m) { return m.map(this); }
	Relevance relevance(const EventTimestamp &ev, Relevance low_thresh, Relevance high_thresh) {
		if (low_thresh >= high_thresh)
			return low_thresh;
		Relevance r = Relevance(Relevance(when, ev),
					Relevance(store, ev));
		if (r >= high_thresh)
			return r;
		return Relevance(
			r,
			Relevance(
				Relevance(val->relevance(ev, r + 1, high_thresh),
					  addr->relevance(ev, r + 1, high_thresh)),
				storeAddr->relevance(ev, r + 1, high_thresh)));
	}

	virtual Expression *restrictToMask(unsigned long mask) { return this; }
};

class BinaryExpression : public Expression {
protected:
	Expression *_concretise() {
		Expression *lc = l->concretise();
		Expression *rc = r->concretise();
		if (lc != l || rc != r)
			return semiDupe(lc, rc);
		else
			return this;
	}
	gc_map<ThreadId, unsigned long> *_lastAccessMap()
	{
		gc_map<ThreadId, unsigned long> *work = new gc_map<ThreadId, unsigned long>(*l->lastAccessMap());
		mergeAccessMaps(work, r->lastAccessMap());
		return work;
	}
	void _visit(HeapVisitor &hv)
	{
		hv(l);							
		hv(r);							
	}								
public:
	virtual Expression *semiDupe(Expression *l, Expression *r) const = 0;
	Expression *refine(VexPtr<MachineState<abstract_interpret_value> > &ms,
			   VexPtr<LogReader<abstract_interpret_value> > &lf,
			   LogReaderPtr ptr,
			   bool *progress,
			   VexPtr<gc_map<ThreadId, unsigned long> > &validity,
			   EventTimestamp ev,
			   GarbageCollectionToken);
	Expression *l, *r;

	void visit(ExpressionVisitor &ev)
	{
		ev.visit(this);
		l->visit(ev);
		r->visit(ev);
	}
	Expression *map(ExpressionMapper &m) { return m.map(this); }
	EventTimestamp timestamp() const				
	{								
		return max<EventTimestamp>(l->timestamp(),		
					   r->timestamp());		
	}
	virtual Relevance relevance(const EventTimestamp &ev, Relevance low_thresh,
				    Relevance high_thresh)
	{
		if (low_thresh >= high_thresh)
			return low_thresh;
		Relevance lr = l->relevance(ev, low_thresh, high_thresh);
		if (lr >= high_thresh)
			return lr;
		return Relevance(lr, r->relevance(ev, lr + 1, high_thresh));
	}
};

#define mk_binop_class(nme, pp, m)					\
	class nme : public BinaryExpression {				\
	protected:							\
		Expression *semiDupe(Expression *l,			\
				     Expression *r) const		\
		{							\
			return nme::get(l,r);				\
		}							\
	        char *mkName() const                                    \
		{							\
			return my_asprintf("(%s " #pp " %s)",		\
					   l->name(), r->name());	\
		}							\
		unsigned long _hash() const { return l->hash() ^ (r->hash() * 3) ^ sizeof(nme); } \
                bool _isEqual(const Expression *other) const		\
		{							\
			const nme *oth =				\
				dynamic_cast<const nme *>(other);	\
			if (oth &&					\
			    oth->l->isEqual(l) &&			\
			    oth->r->isEqual(r))				\
				return true;				\
			else						\
				return false;				\
		}							\
		m							\
	public:								\
	        bool isLogical() const;					\
	        static Expression *get(Expression *_l, Expression *_r);	\
		Expression *restrictToMask(unsigned long x);		\
	}

mk_binop_class(lshift, <<, );
mk_binop_class(rshift, >>, );
mk_binop_class(rshiftarith, >a>, );
mk_binop_class(bitwiseand, &, Expression *_CNF(););
mk_binop_class(bitwiseor, |, Expression *_CNF(); );
mk_binop_class(bitwisexor, ^, );
mk_binop_class(plus, +, );
mk_binop_class(subtract, -, );
mk_binop_class(times, *, );
mk_binop_class(divide, /, );
mk_binop_class(modulo, %%, );
mk_binop_class(greaterthanequals, >=, );
mk_binop_class(greaterthan, >, );
mk_binop_class(lessthanequals, <=, );
mk_binop_class(lessthan, <, );
mk_binop_class(equals, ==, );
mk_binop_class(notequals, !=, );
mk_binop_class(logicalor, ||, );
mk_binop_class(logicaland, &&, );
mk_binop_class(onlyif, onlyif, );

class UnaryExpression : public Expression {
protected:
	Expression *_concretise() {
		Expression *lc = l->concretise();
		if (lc != l)
			return semiDupe(l->concretise());
		else
			return this;
	}
	const gc_map<ThreadId, unsigned long> * _lastAccessMap()
	{
		return l->lastAccessMap();
	}
	void _visit(HeapVisitor &hv)
	{
		hv(l);							
	}								
public:
	virtual Expression *semiDupe(Expression *l) const = 0;
	virtual Expression *refine(VexPtr<MachineState<abstract_interpret_value> > &ms,
				   VexPtr<LogReader<abstract_interpret_value> > &lf,
				   LogReaderPtr ptr,
				   bool *progress,
				   VexPtr<gc_map<ThreadId, unsigned long> >&validity,
				   EventTimestamp ev,
				   GarbageCollectionToken);
	Expression *l;

	void visit(ExpressionVisitor &ev)
	{
		ev.visit(this);
		l->visit(ev);
	}
	Expression *map(ExpressionMapper &m) { return m.map(this); }
	EventTimestamp timestamp() const				
	{								
		return l->timestamp();					
	}
	virtual Relevance relevance(const EventTimestamp &ev, Relevance low_thresh, Relevance high_thresh)
	{
		return l->relevance(ev, low_thresh + 1, high_thresh + 1);
	}
};

#define mk_unop_class(nme, m)						\
	class nme : public UnaryExpression {				\
	protected:							\
	        Expression *semiDupe(Expression *l) const		\
		{							\
		        return nme::get(l);				\
		}							\
	        char *mkName() const					\
		{							\
			return my_asprintf("(" #nme " %s)", l->name());	\
		}							\
		unsigned long _hash() const { return l->hash() ^ sizeof(nme); } \
                bool _isEqual(const Expression *other) const		\
		{							\
			const nme *oth =				\
				dynamic_cast<const nme *>(other);	\
			if (oth &&					\
			    oth->l->isEqual(l))				\
				return true;				\
			else						\
				return false;				\
		}							\
		m							\
	public:								\
	        bool isLogical() const;					\
	        static Expression* get(Expression *_l);			\
		Expression *restrictToMask(unsigned long x);		\
	}

mk_unop_class(logicalnot, );
mk_unop_class(bitwisenot, Expression *_CNF(););
mk_unop_class(unaryminus, );

/* bitsaturate is 0 whenever its argument is zero and one
   otherwise. */
mk_unop_class(bitsaturate, Expression *_CNF(););

/* alias x is just x, but with a hint that x is in some sense
 * ``unlikely'' to be a useful candidate for refinement and can be
 * turned into a constant without too much loss of information.  It's
 * mostly used for alias analysis, because most of the time the
 * concrete alias graph is a very good approximation of the abstract
 * one, and building the full abstract one is very time consuming.
 */
mk_unop_class(alias,
	      Relevance relevance(const EventTimestamp &, Relevance, Relevance);
	      Expression *refine(VexPtr<MachineState<abstract_interpret_value> > &ms,
				 VexPtr<LogReader<abstract_interpret_value> > &lf,
				 LogReaderPtr ptr,
				 bool *progress,
				 VexPtr<gc_map<ThreadId, unsigned long> >&validity,
				 EventTimestamp ev,
				 GarbageCollectionToken);
	);

class ternarycondition : public Expression {
public:
	Expression *cond, *t, *f;
protected:
	char *mkName() const
	{
		return my_asprintf("(%s ? %s : %s)",
				   cond->name(), t->name(), f->name());
	}
	unsigned long _hash() const { return cond->hash() ^ (t->hash() * 3) ^ (f->hash() * 5) ^ 97; }
	bool _isEqual(const Expression *other) const			
	{							
		const ternarycondition *oth =				
			dynamic_cast<const ternarycondition *>(other);	
		if (oth &&					
		    oth->cond->isEqual(cond) &&
		    oth->t->isEqual(t) &&
		    oth->f->isEqual(f))
			return true;				
		else						
			return false;				
	}							
	Expression *_concretise() {
		Expression *cc = cond->concretise(),
			*tc = t->concretise(),
			*fc = f->concretise();
		return get(cc, tc, fc);
	}
	gc_map<ThreadId, unsigned long> *_lastAccessMap()
	{
		gc_map<ThreadId, unsigned long> *work;
		work = new gc_map<ThreadId, unsigned long>(*cond->lastAccessMap());
		mergeAccessMaps(work, t->lastAccessMap());
		mergeAccessMaps(work, f->lastAccessMap());
		return work;
	}
	void _visit(HeapVisitor &hv)
	{
		hv(cond);
		hv(t);
		hv(f);
	}
public:
	bool isLogical() const;
	static Expression *get(Expression *_cond, Expression *_t, Expression *_f);
	void visit(ExpressionVisitor &ev)
	{
		ev.visit(this);
		cond->visit(ev);
		t->visit(ev);
		f->visit(ev);
	}
	Expression *map(ExpressionMapper &m) { return m.map(this); }
	EventTimestamp timestamp() const					
	{								
		return max<EventTimestamp>(cond->timestamp(),
					   max<EventTimestamp>(t->timestamp(),
							       f->timestamp()));
	}								
	Expression *refine(VexPtr<MachineState<abstract_interpret_value> >&ms,
			   VexPtr<LogReader<abstract_interpret_value> >&lf,
			   LogReaderPtr ptr,
			   bool *progress,
			   VexPtr<gc_map<ThreadId, unsigned long> >&validity,
			   EventTimestamp ev,
			   GarbageCollectionToken) { return this; }
	Relevance relevance(const EventTimestamp &ev, Relevance low_thresh,
			    Relevance high_thresh)
	{
		Relevance c = cond->relevance(ev, low_thresh, high_thresh - 1);
		if (c >= high_thresh)
			return c;
		Relevance tr = t->relevance(ev, c + 1, high_thresh);
		if (tr >= high_thresh)
			return tr;
		if (tr >= c)
			low_thresh = c;
		else
			low_thresh = tr;
		Relevance fr = f->relevance(ev, low_thresh + 1, high_thresh);
		return Relevance(c, Relevance(tr, fr));
	}

	Expression *restrictToMask(unsigned long x) {
		return get(cond, t->restrictToMask(x), f->restrictToMask(x));
	}
};

struct abstract_interpret_value {
	mutable char *_name;
	unsigned long v;
	Expression *origin;
	bool isStack;
	abstract_interpret_value(unsigned long _v, Expression *_origin,
				 bool _isStack = false)
		: _name(NULL), v(_v), origin(_origin), isStack(_isStack)
	{assert(origin);}
	abstract_interpret_value() : _name(NULL), v(0), origin(NULL), isStack(false) {}
	const char *name() const {
		if (!_name) {
			if (origin)
				_name = vex_asprintf("{%lx:%s}", v, origin->name());
			else
				_name = vex_asprintf("<null>");
		}
		return _name;		
	}
};

template <>
abstract_interpret_value mkConst(unsigned long x)
{
	return abstract_interpret_value(x, ConstExpression::get(x));
}


static inline void visit_aiv(abstract_interpret_value &aiv, HeapVisitor &hv)
{
	hv(aiv.origin);
	hv(aiv._name);
}

static inline const char *name_aiv(const abstract_interpret_value &aiv)
{
	return aiv.name();
}

static inline unsigned long force(abstract_interpret_value aiv)
{
	return aiv.v;
}

static inline unsigned long force(unsigned long x)
{
	return x;
}

static inline bool is_stack(unsigned long x)
{
	return false;
}

static inline bool is_stack(abstract_interpret_value &x)
{
	return x.isStack;
}

static inline void mark_as_stack(unsigned long x)
{
}

static inline void mark_as_stack(abstract_interpret_value &aiv)
{
	aiv.isStack = true;
}

/* We track whether an AIV is likely to point at the stack.  The rule
   is basically that if the operator is ``stack-like'', and one of the
   operands is probably-stack, and the other operand is a constant,
   then the result is also probably-stack.  The RSP register is also
   permanently marked as probably-stack. */
#define OP(x, name, stackLike)						\
	static inline abstract_interpret_value operator x(const abstract_interpret_value &aiv, \
							  const abstract_interpret_value &cnt) \
	{								\
		abstract_interpret_value res;				\
		res.v = aiv.v x cnt.v;					\
		res.origin = name::get(aiv.origin, cnt.origin);		\
		res.isStack = false;					\
		unsigned long c;					\
		if (stackLike &&					\
			((aiv.isStack && cnt.origin->isConstant(&c)) ||	\
			 (aiv.origin->isConstant(&c) && cnt.isStack)))	\
			res.isStack = true;				\
		return res;						\
	}

OP(<<, lshift, false)
OP(>>, rshift, false)
OP(&, bitwiseand, true)
OP(|, bitwiseor, false)
OP(^, bitwisexor, false)
OP(+, plus, true)
OP(*, times, false)
OP(/, divide, false)
OP(%, modulo, false)
OP(-, subtract, true)
OP(>=, greaterthanequals, false)
OP(>, greaterthan, false)
OP(<, lessthan, false)
OP(<=, lessthanequals, false)
OP(==, equals, false)
OP(!=, notequals, false)
OP(||, logicalor, false)
OP(&&, logicaland, false)
#undef OP

static inline abstract_interpret_value operator !(const abstract_interpret_value &aiv)
{
	abstract_interpret_value res;
	res.v = !aiv.v;
	res.origin = logicalnot::get(aiv.origin);
	return res;
}

static inline abstract_interpret_value operator ~(const abstract_interpret_value &aiv)
{
	abstract_interpret_value res;
	res.v = ~aiv.v;
	res.origin = bitwisenot::get(aiv.origin);
	return res;
}

static inline abstract_interpret_value operator &=(abstract_interpret_value &lhs,
						   const abstract_interpret_value &rhs)
{
	lhs.v &= rhs.v;
	lhs.origin = bitwiseand::get(lhs.origin, rhs.origin);
	return lhs;
}

static inline abstract_interpret_value operator |=(abstract_interpret_value &lhs,
						   const abstract_interpret_value &rhs)
{
	lhs.v |= rhs.v;
	lhs.origin = bitwiseor::get(lhs.origin, rhs.origin);
	return lhs;
}

static inline abstract_interpret_value operator ^=(abstract_interpret_value &lhs,
						   const abstract_interpret_value &rhs)
{
	lhs.v ^= rhs.v;
	lhs.origin = bitwisexor::get(lhs.origin, rhs.origin);
	return lhs;
}

static inline bool isConstant(unsigned long x)
{
	return true;
}

static inline bool isConstant(abstract_interpret_value &x)
{
	unsigned long r;

	if (x.origin->isConstant(&r)) {
		assert(r == x.v);
		return true;
	} else {
		return false;
	}
}

/* For some obscure reason C++ doesn't let you overload the ?:
   operator, so do something almost but not equivalent here (not quite
   because the laziness is wrong.  Then again, the laziness is wrong
   on || and && as well, so what the hell.). */
template<typename ait> static inline ait ternary(ait cond,
						 ait t,
						 ait f);

template<> abstract_interpret_value ternary(abstract_interpret_value cond,
					    abstract_interpret_value t,
					    abstract_interpret_value f)
{
	unsigned long v = cond.v ? t.v : f.v;
	Expression *origin = ternarycondition::get(cond.origin, t.origin, f.origin);
	return abstract_interpret_value(v, origin);
}

template<> unsigned long ternary(unsigned long cond,
				 unsigned long t,
				 unsigned long f)
{
	return cond ? t : f;
}

template <>
class MemoryChunk<abstract_interpret_value> : public GarbageCollected<MemoryChunk<abstract_interpret_value> > {
public:
	static const unsigned long size = MEMORY_CHUNK_SIZE;
	static MemoryChunk<abstract_interpret_value> *allocate();

	unsigned long underlying_checksum;
	unsigned underlying_serial;

	void write(EventTimestamp when, unsigned offset, const abstract_interpret_value *source, unsigned nr_bytes,
		   abstract_interpret_value storeAddr);
	EventTimestamp read(unsigned offset, abstract_interpret_value *dest, unsigned nr_bytes,
			    abstract_interpret_value *storeAddr = NULL) const;

	MemoryChunk<abstract_interpret_value> *dupeSelf() const;

	const MemoryChunk<unsigned long> *underlying;
	struct MCLookasideEntry {
		MCLookasideEntry *next;
		unsigned offset;
		unsigned size;
		EventTimestamp when;
		abstract_interpret_value storeAddr;
		MCLookasideEntry *dupeSelf() const;
		abstract_interpret_value content[0];
	};
	mutable bool lookasideChainFrozen;
	MCLookasideEntry *headLookaside;
	PhysicalAddress base;
	unsigned write_counter;

	static VexAllocType mcl_allocator;

	void compact_lookaside_chain(void);

	void visit(HeapVisitor &hv)
	{
		hv(underlying);
		hv(headLookaside);
		sanity_check();
	}
	void destruct() {}
	void sanity_check() const;
	NAMED_CLASS
};


/* A History segment represents a chunk of per-thread history.  In
   theory, the only part which is really necessary, and the only part
   which is semantically important, is the condition, which is just a
   condition which is evaluated at the start of the segment and has to
   be true.

   We also store a timestamp, which is the point in the model
   execution at which the condition was evaluated.  This is used in
   the heuristic which decides which branch of an expression to refine
   first.

   Finally, we store the last memory index which is valid with this
   history, which is the index of the last memory operation after
   passing this condition and before reaching the next one.  This is
   extremely useful when checking whether a given expression is
   syntactically valid, in the sense that all memory indexes are
   defined by enclosing RIP expressions.
*/
class History : public GarbageCollected<History>, public Named {
public:
	Expression *condition;
	unsigned long last_valid_idx;
	EventTimestamp when;
	History *parent;
private:
	History(Expression *_condition,
		EventTimestamp _when,
		History *_parent)
		: condition(_condition),
		  last_valid_idx(_parent ? _parent->last_valid_idx : 0),
		  when(_when),
		  parent(_parent)
	{
		assert(when.tid.valid());
		calcLastAccessed();
	}
	History(Expression *cond,
		unsigned long _last_valid_idx,
		EventTimestamp _when,
		History *_parent)
		: condition(cond),
		  last_valid_idx(_last_valid_idx),
		  when(_when),
		  parent(_parent)
	{
		assert(when.tid.valid());
		calcLastAccessed();
	}
	static History *drop_matching_conditions(History *parent,
						 Expression *condition,
						 EventTimestamp *when)
	{
		bool doit;

		while (1) {
			if (!parent)
				break;
			doit = false;
			if (!parent->condition ||
			    parent->condition == condition) {
				doit = true;
			} else {
				unsigned long l;
				if (parent->condition->isConstant(&l)) {
					assert(l != 0);
					doit = true;
				}
			}
			if (!doit)
				break;
			*when = parent->when;
			parent = parent->parent;
		}
		return parent;
	}
public:
	static History *get(Expression *condition,
			    EventTimestamp when,
			    History *parent)
	{
		parent = drop_matching_conditions(parent, condition, &when);
		return new History(condition, when, parent);
	}
	static History *get(Expression *cond,
			    unsigned long last_valid_idx,
			    EventTimestamp when,
			    History *parent)
	{
		parent = drop_matching_conditions(parent, cond, &when);
		return new History(cond, last_valid_idx, when, parent);
	}

	Relevance relevance(const EventTimestamp &ev, Relevance low_thresh, Relevance high_thresh) {
		if (low_thresh >= high_thresh)
			return low_thresh;
		Relevance r = Relevance(condition->relevance(ev, low_thresh, high_thresh),
					Relevance(when, ev));
		if (parent)
			r = Relevance(parent->relevance(ev, r + 10, high_thresh) - 10,
				      r);
		return r;
	}
	const gc_map<ThreadId, unsigned long> *lastAccessMap()
	{
		return lastAccessed;
	}
private:
	WeakRef<History> *concrete;
	const gc_map<ThreadId, unsigned long> *lastAccessed;
	void calcLastAccessed();
protected:
	char *mkName() const {
		return my_asprintf("{%s}%s@%d:%lx->%lx", parent ? parent->name() : "",
				   condition->name(), when.tid._tid(), when.idx,
				   last_valid_idx);
	}
public:
	unsigned long hash() const
	{
		return (unsigned long)this;
	}
	void destruct()
	{
		this->~History();
	}
	void visit(HeapVisitor &hv)
	{
		hv(condition);
		hv(parent);
		hv(lastAccessed);
		hv(concrete);
	}
	void visit(ExpressionVisitor &ev)
	{
		condition->visit(ev);
		if (parent)
			parent->visit(ev);
	}
	History *map(ExpressionMapper &m)
	{
		return History::get(condition->map(m),
				    when,
				    parent ? parent->map(m) : NULL);
	}
	bool isEqual(const History *h) const
	{
		if (h == this)
			return true;
		if (when != h->when)
			return false;
		if (!condition->isEqual(h->condition))
			return false;
		if ((parent && !h->parent) ||
		    (!parent && h->parent))
			return false;
		if (!parent)
			return true;
		return parent->isEqual(h->parent);
	}
	void finish(unsigned long final_event)
	{
		last_valid_idx = final_event;
	}

	History *control_expression(EventTimestamp when, Expression *e)
	{
		finish(when.idx);
		return History::get(e, when, this);
	}

	EventTimestamp timestamp() const
	{
		return when;
	}

	History *dupeWithParentReplace(History *from, History *to)
	{
		if (this == from)
			return to;
		assert(parent != NULL);
		return History::get(condition,
				    last_valid_idx,
				    when,
				    parent->dupeWithParentReplace(from, to));
	}

	History *truncate(unsigned long, bool);
	History *truncateInclusive(unsigned long x) { return truncate(x, true); }
	History *truncateExclusive(unsigned long x) { return truncate(x, false); }

	History *concretise() {
		if (!concrete)
			concrete = new WeakRef<History>();
		if (!concrete->get()) {
			Expression *c = condition->concretise();
			unsigned long cc;
			if (c->isConstant(&cc) && cc && parent) {
				concrete->set(parent->concretise());
			} else {
				concrete->set(History::get(c,
							   last_valid_idx,
							   when,
							   parent ? parent->concretise() : NULL));
			}
		}
		return concrete->get();
	}
	NAMED_CLASS
};

/* A RIP expression asserts that a particular thread will follow a
 * particular control flow path, and hence that memory operations can
 * be identified by their position in the memory operation stream.
 */
class ExpressionRip : public Expression {
public:
	ThreadId tid;
	History *history;
	Expression *cond;
	LogReader<abstract_interpret_value> *model_execution;
	LogReaderPtr model_exec_start;
private:
	ExpressionRip(ThreadId _tid, History *_history, Expression *_cond,
		      LogReader<abstract_interpret_value> *model,
		      LogReaderPtr start)
		: tid(_tid),
		  history(_history),
		  cond(_cond),
		  model_execution(model),
		  model_exec_start(start)
	{
	}
	static Expression *refineHistory(VexPtr<ExpressionRip> &ths,
					 VexPtr<MachineState<abstract_interpret_value> > &ms,
					 VexPtr<LogReader<abstract_interpret_value> > &lf,
					 LogReaderPtr ptr,
					 VexPtr<gc_map<ThreadId, unsigned long> >&validity,
					 EventTimestamp ev,
					 GarbageCollectionToken);
	static Expression *refineSubCond(VexPtr<ExpressionRip> &ths,
					 VexPtr<MachineState<abstract_interpret_value> > &ms,
					 VexPtr<LogReader<abstract_interpret_value> > &lf,
					 LogReaderPtr ptr,
					 VexPtr<gc_map<ThreadId, unsigned long> > &validity,
					 EventTimestamp ev,
					 GarbageCollectionToken);

protected:
	char *mkName(void) const {
		return my_asprintf("(rip %d:{%s}:%s)", tid._tid(), history ? history->name() : "<nohistory>", cond ? cond->name() : "<nocond>");
	}
	unsigned long _hash() const {
		return (history ? history->hash() : 0) ^ tid._tid() ^ (cond ? cond->hash() : 0);
	}
	bool _isEqual(const Expression *other) const {
		const ExpressionRip *oth = dynamic_cast<const ExpressionRip *>(other);
		if (oth && oth->tid == tid && cond->isEqual(oth->cond) &&
		    oth->history->isEqual(history))
			return true;
		else
			return false;
	}
	Expression *_concretise() { return get(tid, history->concretise(), cond->concretise(), model_execution,
					       model_exec_start); }
	void _visit(HeapVisitor &hv)
	{
		hv(history);
		hv(cond);
		hv(model_execution);
	}

	const gc_map<ThreadId, unsigned long> *_lastAccessMap()
	{
		if (history) {
			gc_map<ThreadId, unsigned long> *work =
				new gc_map<ThreadId, unsigned long>(*cond->lastAccessMap());
			mergeAccessMaps(work, history->lastAccessMap());
			/* Filter out accesses which are requested by
			   a subexpression and which are defined by
			   this history expression. */
			if (history->last_valid_idx >= (*work)[tid])
				(*work)[tid] = 0;
			return work;
		} else {
			return cond->lastAccessMap();
		}
	}
public:
	static Expression *get(ThreadId tid, History *history, Expression *cond,
			       LogReader<abstract_interpret_value> *model,
			       LogReaderPtr start)
	{
		return intern(new ExpressionRip(tid, history, cond,
						model, start));
	}
	void visit(ExpressionVisitor &ev)
	{
		ev.visit(this);
		history->visit(ev);
		cond->visit(ev);
	}
	Expression *map(ExpressionMapper &m) { return m.map(this); }
	EventTimestamp timestamp() const {
		return max<EventTimestamp>(history->timestamp(),
					   cond->timestamp());
	}
	bool isLogical() const { return cond->isLogical(); }
	Expression *refine(VexPtr<MachineState<abstract_interpret_value> > &ms,
			   VexPtr<LogReader<abstract_interpret_value> > &lf,
			   LogReaderPtr ptr,
			   bool *progress,
			   VexPtr<gc_map<ThreadId, unsigned long> > &validity,
			   EventTimestamp ev,
			   GarbageCollectionToken);
	Relevance relevance(const EventTimestamp &ev, Relevance low_thresh, Relevance high_thresh) {
		Relevance cr = cond->relevance(ev, low_thresh, high_thresh);
		return Relevance(cr, history->relevance(ev, cr + 1, high_thresh));
	}

	Expression *restrictToMask(unsigned long mask) {
		return get(tid, history, cond->restrictToMask(mask), model_execution, model_exec_start);
	}
};

/* A bad pointer expression asserts that a particular memory location
 * is inaccessible at a particular time. */
class ExpressionBadPointer : public Expression {
public:
	Expression *addr;
	EventTimestamp when;
private:
	ExpressionBadPointer(EventTimestamp _when, Expression *_addr)
		: addr(_addr), when(_when)
	{
	}
protected:
	char *mkName(void) const {
		return my_asprintf("(bad ptr %d:%lx:%s)", when.tid._tid(), when.idx, addr->name());
	}
	unsigned long _hash() const {
		return addr->hash() ^ when.hash();
	}
	bool _isEqual(const Expression *other) const {
		const ExpressionBadPointer *oth = dynamic_cast<const ExpressionBadPointer *>(other);
		if (oth && oth->addr->isEqual(addr) && oth->when == when)
			return true;
		else
			return false;
	}
	Expression *_concretise() { return get(when, addr->concretise()); }
	void _visit(HeapVisitor &hv) { hv(addr); }
	gc_map<ThreadId, unsigned long> *_lastAccessMap()
	{
		gc_map<ThreadId, unsigned long> *work = new gc_map<ThreadId, unsigned long>(*addr->lastAccessMap());
		lastAccessTS(when, work);
		return work;
	}
public:
	static Expression *get(EventTimestamp _when, Expression *_addr)
	{
		return intern(new ExpressionBadPointer(_when, _addr));
	}
	void visit(ExpressionVisitor &ev) { ev.visit(this); addr->visit(ev); }
	Expression *map(ExpressionMapper &m) { return m.map(this); }
	EventTimestamp timestamp() const { return when; }
	Expression *refine(VexPtr<MachineState<abstract_interpret_value> > &ms,
			   VexPtr<LogReader<abstract_interpret_value> > &lf,
			   LogReaderPtr ptr,
			   bool *progress,
			   VexPtr<gc_map<ThreadId, unsigned long> > &validity,
			   EventTimestamp ev,
			   GarbageCollectionToken)
	{
		*progress = true;
		return equals::get(addr, addr->concretise());
	}

	Relevance relevance(const EventTimestamp &ev, Relevance low, Relevance high)
	{
		Relevance r = Relevance(when, ev);
		return Relevance(r, addr->relevance(ev, r + 1, high));
	}

Expression *restrictToMask(unsigned long mask) { return this; }
};

static inline void sanity_check_ait(unsigned long x) {}
static inline void sanity_check_ait(abstract_interpret_value v)
{
	if (ConstExpression *ce = dynamic_cast<ConstExpression *>(v.origin))
		assert(ce->v == v.v);
}

void considerPotentialFixes(Expression *expr);

void gdb_concrete(const MachineState<unsigned long> *ms);
void gdb_abstract(const MachineState<abstract_interpret_value> *ms);
void gdb(void);
void dbg_break(const char *msg, ...);

/* force some functions to be included even when they're not needed,
   so that they're available for calling from the debugger. */
static void force_linkage() __attribute__((unused, used));
static void
force_linkage()
{
	gdb_concrete(NULL);
	gdb_abstract(NULL);
}

class UseOfFreeMemoryException : public SliException {
public:
	EventTimestamp when;
	unsigned long ptr;
	EventTimestamp whenFreed;
	UseOfFreeMemoryException(EventTimestamp _when,
				 unsigned long _ptr,
				 EventTimestamp _whenFreed)
		: SliException(
			"guest used freed memory at %lx at %d:%lx (freed at %d:%lx)\n",
			_ptr, _when.tid._tid(), _when.idx, _whenFreed.tid._tid(), _whenFreed.idx),
		  when(_when),
		  ptr(_ptr),
		  whenFreed(_whenFreed)
	{
	}
};

#include <map>
class RipHistogram {
	std::map<void *, unsigned> m;
public:
	void dump();
	~RipHistogram() { dump(); }
	void click(void *k) { m[k]++; }
};

#define CALLER_HISTOGRAM(depth)						\
	extern RipHistogram __caller_histogram;				\
	__caller_histogram.click(__builtin_return_address(depth + 1))

bool address_is_interesting(ThreadId tid, unsigned long addr);
unsigned long extract_call_follower(IRSB *irsb);

#endif /* !SLI_H__ */
