#ifndef SLI_H__
#define SLI_H__

#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <map>
#include <algorithm>

#include "libvex_guest_amd64.h"
#include "libvex_ir.h"
#include "libvex.h"

#include "exceptions.h"

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
protected:
	virtual char *mkName(void) const = 0;
	void clearName() const { free(_name); _name = NULL; }
public:
	Named &operator=(const Named &src) {
		clearName();
		if (src._name)
			_name = strdup(src._name);
		return *this;
	}
	Named() : _name(NULL) {}
	Named(const Named &b) {
		if (b._name)
			_name = strdup(b._name);
		else
			_name = NULL;
	}
	const char *name() const {
		if (!_name)
			_name = mkName();
		return _name;
	}
	void destruct() { clearName(); }
	~Named() { destruct(); }
};

template <typename underlying>
void visit_object(const void *_ctxt, HeapVisitor &hv)
{
	const underlying *ctxt = (const underlying *)_ctxt;
	ctxt->visit(hv);
}

template <typename underlying>
void destruct_object(void *_ctxt)
{
	underlying *ctxt = (underlying *)_ctxt;
	ctxt->destruct();
}

template <typename underlying>
const char *get_name(const void *_ctxt)
{
	const underlying *ctxt = (const underlying *)_ctxt;
	return ctxt->cls_name();
}

template <typename t>
class GarbageCollected {
	static VexAllocType type;
public:
	static void *operator new(size_t s)
	{
		void *x = LibVEX_Alloc_Sized(&type, s);
		memset(x, 0, s);
		return x;
	}
	static void operator delete(void *)
	{
		abort();
	}
	virtual void visit(HeapVisitor &hv) const = 0;
	virtual void destruct() = 0;
};
template <typename t> VexAllocType GarbageCollected<t>::type = {-1, visit_object<t>, destruct_object<t>, NULL, get_name<t> };

template <typename p>
class VexPtr {
	p *content;
	VexGcRoot root;
public:
	VexPtr() : content(NULL), root((void **)&content, "VexPtr") {}
	VexPtr(p *_content) : content(_content), root((void **)&content, "VexPtr") {}
	VexPtr(VexPtr<p> &c) : content(c.content), root((void **)&content, "VexPtr") {}
	const VexPtr<p> &operator=(VexPtr<p> &x) { content = x.content; return *this; }
	const VexPtr<p> &operator=(p *x) { content = x; return *this; }
	p &operator*() const { return *content; }
	p *operator->() const { return content; }
	operator p*() const { return content; }
	p *get() const { return content; }
};

#define NAMED_CLASS static const char *cls_name() { return __PRETTY_FUNCTION__ + 19; }

template <typename t, const char *(*get_name)(const void *) = get_name<t>, void (*visit)(const void *, HeapVisitor &) = visit_object<t>, void (*destruct)(void *) = destruct_object<t> >
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
			irrelevance = (delta * delta) / 10;
			if (irrelevance < 0)
				irrelevance = 0;
		} else {
			irrelevance = -delta;
		}
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
	void visit(HeapVisitor &hv) const { visit_aiv(lo, hv); visit_aiv(hi, hv); }
	
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
	underlying get_reg(unsigned idx) const { assert(idx < NR_REGS); return registers[idx]; }
	void set_reg(unsigned idx, underlying val)
	{
		sanity_check_ait(val);
		assert(idx < NR_REGS);
		registers[idx] = val;
		if (idx == REGISTER_IDX(RSP))
			mark_as_stack(registers[idx]);
	}
	underlying rip() const { return get_reg(REGISTER_IDX(RIP)); }
	underlying rsp() const { return get_reg(REGISTER_IDX(RSP)); }

	template <typename new_type> void abstract(RegisterSet<new_type> *out) const;

	void visit(HeapVisitor &hv) const {
		for (unsigned x = 0; x < NR_REGS; x++)
			visit_aiv(registers[x], hv);
	}
};

template <typename ait> class AddressSpace;

template <typename ait>
class expression_result_array {
	static VexAllocType arrayAllocType;
public:
	struct expression_result<ait> *arr;
	unsigned nr_entries;
	void setSize(unsigned new_size) {
		void *b = LibVEX_Alloc_Sized(&arrayAllocType,
					     sizeof(arr[0]) * new_size + sizeof(unsigned));
		*(unsigned *)b = new_size;
		arr = (expression_result<ait> *)((unsigned *)b + 1);
		memset(arr, 0, sizeof(arr[0]) * new_size);
		nr_entries = new_size;
		for (unsigned x = 0; x < nr_entries; x++)
			new (&arr[x]) expression_result<ait>();
	}
	expression_result<ait> &operator[](unsigned idx) { return arr[idx]; }
	void visit(HeapVisitor &hv) const {
		if (arr)
			hv( (unsigned *)arr - 1);
	}
	expression_result_array() :
		arr(NULL),
		nr_entries(0)
	{
	}

	template <typename new_type> void abstract(expression_result_array<new_type> *out) const;
};

template <typename ait> class ThreadEvent;
template <typename ait> class MachineState;
template <typename ait> class LogRecordInitialRegisters;
template <typename ait> class LogWriter;
template <typename ait> class LogRecordVexThreadState;

template <typename abst_int_type>
class Thread : public GarbageCollected<Thread<abst_int_type> > {
	void translateNextBlock(AddressSpace<abst_int_type> *addrSpace);
	struct expression_result<abst_int_type> eval_expression(IRExpr *expr);
	ThreadEvent<abst_int_type> *do_dirty_call(IRDirty *details, MachineState<abst_int_type> *ms);
	expression_result<abst_int_type> do_ccall_calculate_condition(struct expression_result<abst_int_type> *args);
	expression_result<abst_int_type> do_ccall_calculate_rflags_c(expression_result<abst_int_type> *args);
	expression_result<abst_int_type> do_ccall_generic(IRCallee *cee, struct expression_result<abst_int_type> *rargs);
	expression_result<abst_int_type> do_ccall(IRCallee *cee, IRExpr **args);
	void redirectGuest(abst_int_type rip);
public:
	EventTimestamp bumpEvent(MachineState<abst_int_type> *ms);
	ThreadId tid;
	unsigned pid;
	RegisterSet<abst_int_type> regs;
	abst_int_type clear_child_tid;
	abst_int_type robust_list;
	abst_int_type set_child_tid;
	bool exitted;
	bool crashed;

	bool cannot_make_progress;

	unsigned long nrAccesses;
	unsigned long nrEvents;

	IRSB *currentIRSB;
	expression_result_array<abst_int_type> temporaries;
	int currentIRSBOffset;

	abst_int_type currentControlCondition;

	EventTimestamp lastEvent;

	bool runnable() const { return !exitted && !crashed && !cannot_make_progress; }

private:
	bool allowRipMismatch;
	~Thread();
public:
	ThreadEvent<abst_int_type> *runToEvent(AddressSpace<abst_int_type> *addrSpace, MachineState<abst_int_type> *ms);

	static Thread<abst_int_type> *initialThread(const LogRecordInitialRegisters<abst_int_type> &initRegs);
	Thread<abst_int_type> *fork(unsigned newPid);
	Thread<abst_int_type> *dupeSelf() const;
	void dumpSnapshot(LogWriter<abst_int_type> *lw) const;

	void imposeState(const LogRecordVexThreadState<abst_int_type> *rec,
			 AddressSpace<abst_int_type> *as);

	void visit(HeapVisitor &hv) const;

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
		template <typename ait> void visit(PMap<ait> *pmap, HeapVisitor &hv) const;
		VAMapEntry *promoteSmallest();
		VAMapEntry *dupeSelf() const;
		void sanityCheck(unsigned long max = 0,
				 bool have_max = false,
				 unsigned long min = 0,
				 bool have_min = false) const;
	};

private:
	/* Mutable because we splay the tree on lookup */
	mutable VAMapEntry *root;

	const VAMap *parent;

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
	VAMap *dupeSelf() const;
	template <typename ait> void visit(HeapVisitor &hv, PMap<ait> *pmap) const;
	void visit(HeapVisitor &hv) const;

	void sanityCheck() const;
};

#define MEMORY_CHUNK_SIZE 4096

template <typename ait> class MemoryChunk;

template <>
class MemoryChunk<unsigned long> {
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
template <typename ait>
class PMapEntry : public GarbageCollected<PMapEntry<ait> > {
public:
	PhysicalAddress pa;
	MemoryChunk<ait> *mc;
	PMapEntry<ait> *next;
	PMapEntry<ait> **pprev;
	bool readonly;
	static PMapEntry *alloc(PhysicalAddress pa, MemoryChunk<ait> *mc, bool readonly);
	void visit(HeapVisitor &hv) const {}
	void destruct() {
		*pprev = next;
		if (next)
			next->pprev = pprev;
	}
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
	const PMap<ait> *parent;

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

	void visitPA(PhysicalAddress pa, HeapVisitor &hv) const;
	void visit(HeapVisitor &hv) const;
	void destruct() {}

	template <typename newtype> PMap<newtype> *abstract() const;
	NAMED_CLASS
};

template <typename ait>
class LogRecord : public Named, public GarbageCollected<LogRecord<ait> > {
	ThreadId tid;
protected:
	void *marshal(unsigned cls, unsigned psize, unsigned *sz, void **r) const;
public:
	ThreadId thread() const { return tid; }
	LogRecord(ThreadId _tid) : tid(_tid) {}
	virtual void *marshal(unsigned *size) const = 0;
	virtual ~LogRecord() {};
	virtual void destruct() {}
	virtual void visit(HeapVisitor &hv) const {}
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

/* gcc struggles with member classes of template classes, so this has
   to be non-member. */
class LogReaderPtr {
public:
	unsigned char cls_data[32];
	LogReaderPtr() { memset(cls_data, 0, sizeof(cls_data)); }
};

template <typename ait>
class LogReader {
public:
	virtual LogRecord<ait> *read(LogReaderPtr startPtr, LogReaderPtr *outPtr) const = 0;
	virtual ~LogReader() {}
	template <typename new_type> LogReader<new_type> *abstract() const;
};

class LogFile : public LogReader<unsigned long>, public GarbageCollected<LogFile> {
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
	void visit(HeapVisitor &hv) const {}
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
	~MachineState();
	static MachineState *initialMachineState(AddressSpace<abst_int_type> *as,
						 const LogRecordInitialSighandlers<abst_int_type> &handlers);
public:
	AddressSpace<abst_int_type> *addressSpace;
	SignalHandlers<abst_int_type> signalHandlers;
	unsigned long nrEvents;
	static MachineState<abst_int_type> *initialMachineState(LogReader<abst_int_type> *lf,
								LogReaderPtr startPtr,
								LogReaderPtr *endPtr);

	template <typename new_type> MachineState<new_type> *abstract() const;

	void registerThread(Thread<abst_int_type> *t) {
		t->tid = nextTid;
		++nextTid;
		threads->push(t);
	}
	Thread<abst_int_type> *findThread(ThreadId id) {
		unsigned x;
		for (x = 0; x < threads->size(); x++)
			if (threads->index(x)->tid == id)
				return threads->index(x);
		abort();
	}
	const Thread<abst_int_type> *findThread(ThreadId id) const {
		unsigned x;
		for (x = 0; x < threads->size(); x++)
			if (threads->index(x)->tid == id)
				return threads->index(x);
		abort();
	}
	void exitGroup(abst_int_type result) {
		exitted = true;
		exit_status = result;
	}
	bool crashed() const;
	
	MachineState<abst_int_type> *dupeSelf() const;

	void dumpSnapshot(LogWriter<abst_int_type> *lw) const;

	void visit(HeapVisitor &hv) const;
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
class EventRecorder {
public:
	virtual void record(Thread<ait> *thr, ThreadEvent<ait> *evt) = 0;
};

template<typename abst_int_type>
class Interpreter {
	void replayFootstep(const LogRecordFootstep<abst_int_type> &lrf,
			    const LogReader<abst_int_type> *lr,
			    LogReaderPtr startOffset,
			    LogReaderPtr *endOffset);

	MachineState<abst_int_type> *currentState;
	VexGcRoot currentStateRoot;
public:
	Interpreter(MachineState<abst_int_type> *rootMachine) :
		currentState(rootMachine),
		currentStateRoot((void **)&currentState, "currentStateRoot")
	{
	}
	void replayLogfile(const LogReader<abst_int_type> *lf, LogReaderPtr startingPoint,
			   LogReaderPtr *endingPoint = NULL, LogWriter<abst_int_type> *log = NULL,
			   EventRecorder<abst_int_type> *er = NULL);
	InterpretResult getThreadMemoryTrace(ThreadId tid,
					     MemoryTrace<abst_int_type> **output,
					     unsigned max_events);
	void runToAccessLoggingEvents(ThreadId tid, unsigned nr_accesses,
				      LogWriter<abst_int_type> *output = NULL);
	void runToFailure(ThreadId tid, LogWriter<abst_int_type> *output,
			  unsigned max_events = 0);
	void runToEvent(EventTimestamp evt,
			const LogReader<abst_int_type> *lf,
			LogReaderPtr startingPoint,
			LogReaderPtr *endPoint = NULL);
};

template <typename ait>
class LogWriter {
public:
	virtual void append(LogRecord<ait> *lr, unsigned long idx) = 0;
	virtual ~LogWriter() {}
	InterpretResult recordEvent(Thread<ait> *thr, MachineState<ait> *ms, ThreadEvent<ait> *evt);
};

class LogFileWriter : public LogWriter<unsigned long> {
	int fd;
public:
	void append(LogRecord<unsigned long> *lr, unsigned long idx);
	static LogFileWriter *open(const char *fname);
	~LogFileWriter();
};

template <typename ait> void destroy_memlog(void *_ctxt);

template <typename ait>
class MemLog : public LogReader<ait>, public LogWriter<ait>, public GarbageCollected<MemLog<ait> > {
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
	static MemLog *emptyMemlog();
	static LogReaderPtr startPtr() { return mkPtr(0); }
	MemLog<ait> *dupeSelf() const;
	LogRecord<ait> *read(LogReaderPtr startPtr, LogReaderPtr *outPtr) const;
	void dump() const;

	void append(LogRecord<ait> *lr, unsigned long idx);

	/* Should only be called by GC destruct routine */
	virtual void destruct();

	virtual void visit(HeapVisitor &hv) const;

	NAMED_CLASS
};

template <typename ait>
class ThreadEvent : public Named, public GarbageCollected<ThreadEvent<ait> > {
protected:
	ThreadEvent(EventTimestamp _when) : when(_when) {}
public:
	EventTimestamp when;
	/* Replay the event using information in the log record */
	virtual ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> *ms) = 0;
	/* Try to ``replay'' the event without reference to a pre-existing logfile */
	virtual InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL) = 0;
	/* Use the logfile if it matches, and otherwise fake it.  This
	   can fast-forward through the log e.g. to find a matching
	   syscall. */
	virtual ThreadEvent<ait> *fuzzyReplay(MachineState<ait> *ms,
					      LogReader<ait> *lf,
					      LogReaderPtr startPtr,
					      LogReaderPtr *endPtr)
	{
		fake(ms, NULL);
		return NULL;
	}

	/* This should really be DNI, but g++ doesn't let you inherit
	 * from a class which has a private destructor. */
	~ThreadEvent() { abort(); }

	virtual void visit(HeapVisitor &hv) const {};
	virtual void destruct() {}

	NAMED_CLASS
};

template <typename ait>
class RdtscEvent : public ThreadEvent<ait> {
	IRTemp tmp;
	RdtscEvent(EventTimestamp when, IRTemp _tmp) : ThreadEvent<ait>(when), tmp(_tmp) {};
	~RdtscEvent();
protected:
	virtual char *mkName() const { return my_asprintf("rdtsc(%d)", tmp); }
public:
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> *ms);
	InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	ThreadEvent<ait> *fuzzyReplay(MachineState<ait> *ms, LogReader<ait> *lf,
				      LogReaderPtr startPtr, LogReaderPtr *endPtr);
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
	ait addr;
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
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> *ms);
	InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	static ThreadEvent<ait> *get(EventTimestamp when, IRTemp _tmp, ait _addr, unsigned _size)
	{
		return new LoadEvent<ait>(when, _tmp, _addr, _size);
	}
	void visit(HeapVisitor &hv) const { visit_aiv(addr, hv); ThreadEvent<ait>::visit(hv); }
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
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> *ms);
	InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	static ThreadEvent<ait> *get(EventTimestamp when, ait _addr, unsigned _size, expression_result<ait> data)
	{
		return new StoreEvent<ait>(when, _addr, _size, data);
	}

	void visit(HeapVisitor &hv) const { visit_aiv(addr, hv); data.visit(hv); ThreadEvent<ait>::visit(hv); }
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
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> *ms);
	InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	static InstructionEvent<ait> *get(EventTimestamp when, ait _rip, ait _reg0, ait _reg1,
					  ait _reg2, ait _reg3, ait _reg4, bool _allowRipMismatch)
	{
		return new InstructionEvent<ait>(when, _rip, _reg0, _reg1, _reg2, _reg3, _reg4,
						 _allowRipMismatch);
	}

	void visit(HeapVisitor &hv) const
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
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> *ms);
	virtual InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	virtual InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL,
				     LogRecord<ait> **lr2 = NULL);
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> *ms,
				 const LogReader<ait> *lf, LogReaderPtr ptr,
				 LogReaderPtr *outPtr, LogWriter<ait> *lw);
	ThreadEvent<ait> *fuzzyReplay(MachineState<ait> *ms,
				      LogReader<ait> *lf,
				      LogReaderPtr startPtr,
				      LogReaderPtr *endPtr);

	static ThreadEvent<ait> *get(EventTimestamp when,
				     IRTemp _dest,
				     expression_result<ait> _addr,
				     expression_result<ait> _data,
				     expression_result<ait> _expected,
				     unsigned _size)
	{
		return new CasEvent<ait>(when, _dest, _addr, _data, _expected, _size);
	}

	void visit(HeapVisitor &hv) const
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
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> *ms);
	InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	ThreadEvent<ait> *fuzzyReplay(MachineState<ait> *ms, LogReader<ait> *lf,
				      LogReaderPtr startPtr, LogReaderPtr *endPtr);
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
	ThreadEvent<ait> *replay(LogRecord<ait> *lr, MachineState<ait> *ms);
	InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	static ThreadEvent<ait> *get(EventTimestamp when, unsigned _signr, ait _virtaddr)
	{
		return new SignalEvent<ait>(when, _signr, _virtaddr);
	}

	void visit(HeapVisitor &hv) const
	{
		visit_aiv(virtaddr, hv);
		ThreadEvent<ait>::visit(hv);
	}
	NAMED_CLASS
};

static inline void maybeVisit(unsigned long x, HeapVisitor &hv) {}
static inline void maybeVisit(const void *x, HeapVisitor &hv) { hv(x); }

template<typename t> void
visit_container(const t &vector, HeapVisitor &hv)
{
	for (class t::const_iterator it = vector.begin();
	     it != vector.end();
	     it++)
		maybeVisit(*it, hv);
}

template <typename ait>
class MemoryAccess : public Named, public GarbageCollected<MemoryAccess<ait> > {
public:
	EventTimestamp when;
	ait addr;
	unsigned size;
	MemoryAccess(EventTimestamp _when, ait _addr, unsigned _size)
		: when(_when),
		  addr(_addr),
		  size(_size)
	{
	}
	virtual bool isLoad() = 0;
	void dump() const { printf("%s\n", name()); }
	void visit(HeapVisitor &hv) const { visit_aiv(addr, hv); }
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
	template <typename outtype> LogRecordLoad<outtype> *abstract() const
	{
		expression_result<outtype> nvalue;
		value.abstract(&nvalue);
		return new LogRecordLoad<outtype>(this->thread(),
						  size,
						  mkConst<outtype>(ptr),
						  nvalue);
	}
	void visit(HeapVisitor &hv) const { value.visit(hv); visit_aiv(ptr, hv); }
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
	template <typename outtype> LogRecordStore<outtype> *abstract() const
	{
		expression_result<outtype> res;
		value.abstract(&res);
		return new LogRecordStore<outtype>(this->thread(),
						   size,
						   mkConst<outtype>(ptr),
						   res);
	}
	void visit(HeapVisitor &hv) const { value.visit(hv); visit_aiv(ptr, hv); }
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
	MemoryTrace(const MachineState<ait> *, LogReader<ait> *, LogReaderPtr);
	size_t size() const { return content.size(); }
	MemoryAccess<ait> *&operator[](unsigned idx) { return content[idx]; }
	void push_back(MemoryAccess<ait> *x) { content.push_back(x); }
	MemoryTrace() : content() {}
	void dump() const;
	void visit(HeapVisitor &hv) const { visit_container(content, hv); }
	void destruct() { this->~MemoryTrace<ait>(); }
	NAMED_CLASS
};

template <typename ait>
class MemTracePool : public GarbageCollected<MemTracePool<ait> > {
	typedef std::map<ThreadId, MemoryTrace<ait> *> contentT;
	contentT content;
public:
	MemTracePool(MachineState<ait> *base_state, ThreadId ignoredThread);
	~MemTracePool() {}
	std::map<ThreadId, Maybe<unsigned> > *firstRacingAccessMap();
	void visit(HeapVisitor &hv) const;
	void destruct() { this->~MemTracePool<ait>(); }
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
	void visit(HeapVisitor &hv) const
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
	template <typename outtype> LogRecordSyscall<outtype> *abstract() const
	{
		return new LogRecordSyscall<outtype>(this->thread(),
						     mkConst<outtype>(sysnr),
						     mkConst<outtype>(res),
						     mkConst<outtype>(arg1),
						     mkConst<outtype>(arg2),
						     mkConst<outtype>(arg3));
	}
	void visit(HeapVisitor &hv) const
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
	{}
	virtual ~LogRecordMemory() { free((void *)contents); }
	void *marshal(unsigned *size) const;
	template <typename outtype> LogRecordMemory<outtype> *abstract() const
	{
		outtype *b = (outtype *)malloc(size * sizeof(outtype));
		for (unsigned x = 0; x < size; x++)
			b[x] = mkConst<outtype>(contents[x]);
		return new LogRecordMemory<outtype>(this->thread(), size, mkConst<outtype>(start), b);
	}
	void visit(HeapVisitor &hv) const
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
	template <typename outtype> LogRecordRdtsc<outtype> *abstract() const
	{
		return new LogRecordRdtsc<outtype>(this->thread(),
						   mkConst<outtype>(tsc));
	}
	void visit(HeapVisitor &hv) const { visit_aiv(tsc, hv); }
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
	template <typename outtype> LogRecordSignal<outtype> *abstract() const
	{
		return new LogRecordSignal<outtype>(this->thread(),
						    mkConst<outtype>(rip),
						    signr,
						    mkConst<outtype>(err),
						    mkConst<outtype>(virtaddr));
	}
	void visit(HeapVisitor &hv) const
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
	template <typename outtype> LogRecordAllocateMemory<outtype> *abstract() const
	{
		return new LogRecordAllocateMemory<outtype>(this->thread(),
							    mkConst<outtype>(start),
							    mkConst<outtype>(size),
							    prot,
							    flags);
	}
	void visit(HeapVisitor &hv) const { visit_aiv(start, hv); visit_aiv(size, hv); }
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
	template <typename outtype> LogRecordInitialBrk<outtype> *abstract() const
	{
		return new LogRecordInitialBrk<outtype>(this->thread(),
							mkConst<outtype>(brk));
	}
	void visit(HeapVisitor &hv) const { visit_aiv(brk, hv); }
};

template <typename ait>
class LogRecordVexThreadState : public LogRecord<ait> {
protected:
	virtual char *mkName() const {
		return strdup("vex state");
	}
public:
	expression_result_array<ait> tmp;
	unsigned statement_nr;
	LogRecordVexThreadState(ThreadId tid, unsigned _statement_nr,
				expression_result_array<ait> _tmp);
	void *marshal(unsigned *sz) const;
	template <typename outtype> LogRecordVexThreadState<outtype> *abstract() const
	{
		expression_result_array<outtype> ntmp;
		tmp.abstract(&ntmp);
		return new LogRecordVexThreadState<outtype>(this->thread(), statement_nr, ntmp);
	}
	void visit(HeapVisitor &hv) const { tmp.visit(hv); }
};

template <typename ait>
class AddressSpace : public GarbageCollected<AddressSpace<ait> > {
public:
	unsigned long brkptr;
	unsigned long brkMapPtr;
	VAMap *vamap;
	PMap<ait> *pmap;

private:
	bool extendStack(unsigned long ptr, unsigned long rsp);

public:
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
		writeMemory(EventTimestamp::invalid, rec.start, rec.size, rec.contents, true);
	}
	void store(EventTimestamp when, ait start, unsigned size, const expression_result<ait> &val,
		   bool ignore_protection = false,
		   const Thread<ait> *thr = NULL);
	void writeMemory(EventTimestamp when, ait start, unsigned size,
			 const ait *contents, bool ignore_protection = false,
			 const Thread<ait> *thr = NULL);
	void writeLiteralMemory(unsigned long start, unsigned size, const unsigned char *content);
	expression_result<ait> load(EventTimestamp when, ait start, unsigned size,
				    bool ignore_protection = false,
				    const Thread<ait> *thr = NULL);
	EventTimestamp readMemory(ait start, unsigned size,
				  ait *contents, bool ignore_protection = false,
				  const Thread<ait> *thr = NULL,
				  ait *storeAddr = NULL);
	bool isAccessible(ait start, unsigned size,
			  bool isWrite, const Thread<ait> *thr = NULL);
	bool isWritable(ait start, unsigned size,
			const Thread<ait> *thr = NULL) {
		return isAccessible(start, size, true, thr);
	}
	bool isReadable(ait start, unsigned size,
			const Thread<ait> *thr = NULL) {
		return isAccessible(start, size, false, thr);
	}
	unsigned long setBrk(ait newBrk);

	static AddressSpace *initialAddressSpace(ait initialBrk);
	AddressSpace *dupeSelf() const;
	void visit(HeapVisitor &hv) const;
	void sanityCheck() const;

	void addVsyscalls();

	void dumpBrkPtr(LogWriter<ait> *lw) const;
	void dumpSnapshot(LogWriter<ait> *lw) const;

	char *readString(ait start);

	template <typename new_type> AddressSpace<new_type> *abstract() const;

	void destruct() {}

	NAMED_CLASS
};

template<typename ait> ThreadEvent<ait> * replay_syscall(const LogRecordSyscall<ait> *lrs,
							 Thread<ait> *thr,
							 MachineState<ait> *mach);

template<typename ait> void process_memory_records(AddressSpace<ait> *addrSpace,
						   const LogReader<ait> *lf,
						   LogReaderPtr startOffset,
						   LogReaderPtr *endOffset,
						   LogWriter<ait> *lw);

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
	static const unsigned nr_heads = 262147;
	static Expression *heads[nr_heads];
	static unsigned chain_lengths[nr_heads];
	static unsigned long eq_calls[nr_heads];
	static unsigned tot_outstanding;
	static unsigned nr_interned;
	Expression *next;
	Expression **pprev;
	unsigned hashval;
	static void dump_eq_calls_table();
	static void dump_chain_length_table();
	void remove_from_hash() {
		*pprev = next;
		if (next)
			next->pprev = pprev;
		pprev = &next;
		next = NULL;
	}
	void add_to_hash() {
		pprev = &heads[hashval % nr_heads];
		next = *pprev;
		if (next)
			next->pprev = &next;
		*pprev = this;
	}
	void pull_to_front() {
		remove_from_hash();
		add_to_hash();
	}
	mutable WeakRef<Expression> cnf;
	mutable WeakRef<Expression> concrete;
protected:
	static Expression *intern(Expression *e);
	virtual unsigned _hash() const = 0;
	virtual bool _isEqual(const Expression *other) const = 0;
	virtual Expression *_CNF() { return this; }
	virtual Expression *_concretise() = 0;
	static void lastAccessTS(EventTimestamp ts, std::map<ThreadId, unsigned long> &output)
	{
		if (output[ts.tid] < ts.idx)
			output[ts.tid] = ts.idx;
	}
	virtual void _lastAccessMap(std::map<ThreadId, unsigned long> &output) = 0;
private:
	std::map<ThreadId, unsigned long> lastAccessedMap;
	bool haveLastAccessMap;
public:
	unsigned hash() const { return hashval; }
	virtual bool isConstant(unsigned long *cv) const { return false; }
	virtual bool isLogical() const { return false; }
	virtual EventTimestamp timestamp() const { return EventTimestamp::invalid; }
	virtual Expression *refine(const MachineState<abstract_interpret_value> *ms,
				   LogReader<abstract_interpret_value> *lf,
				   LogReaderPtr ptr,
				   bool *progress,
				   const std::map<ThreadId, unsigned long> &validity,
				   EventTimestamp ev) = 0;
	virtual void visit(ExpressionVisitor &ev) = 0;
	virtual Expression *map(ExpressionMapper &f) = 0;
	virtual Relevance relevance(const EventTimestamp &ev, Relevance low_threshold,
				    Relevance high_threshold) = 0;
	void lastAccessMap(std::map<ThreadId, unsigned long> &output) {
		if (!haveLastAccessMap) {
			_lastAccessMap(lastAccessedMap);
			haveLastAccessMap = true;
		}
		for (std::map<ThreadId, unsigned long>::iterator it = lastAccessedMap.begin();
		     it != lastAccessedMap.end();
		     it++) {
			if (output[it->first] < it->second)
				output[it->first] = it->second;
		}
	}
	Expression *concretise() {
		if (!concrete.get())
			concrete.set(_concretise());
		return concrete.get();
	}
	Expression *CNF() {
		if (!cnf.get())
			cnf.set(_CNF());
		return cnf.get();
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
	void destruct() {
		remove_from_hash();
		tot_outstanding--;
		Named::destruct();
	}

	virtual void visit(HeapVisitor &hv) const = 0;
	NAMED_CLASS
};

class UnrefinableExpression : public Expression {
public:
	Expression *refine(const MachineState<abstract_interpret_value> *ms,
			   LogReader<abstract_interpret_value> *lf,
			   LogReaderPtr ptr,
			   bool *progress,
			   const std::map<ThreadId, unsigned long> &validity,
			   EventTimestamp ev) { return this; }
	Relevance relevance(const EventTimestamp &ev, Relevance, Relevance) { return Relevance::irrelevant; }
};

class BottomExpression : public UnrefinableExpression {
	static BottomExpression *bottom;
protected:
	unsigned _hash() const { return 0x1234567; }
	char *mkName() const { return my_asprintf("_|_"); }
	bool _isEqual(const Expression *other) const { return false; }
	Expression *_concretise() { return this; }
public:
	static Expression *get()
	{
		if (!bottom)
			bottom = new BottomExpression();
		return bottom;
	}
	void visit(HeapVisitor &hv) const {}
	void visit(ExpressionVisitor &ev) { ev.visit(this); }
	Expression *map(ExpressionMapper &f) { return f.map(this); }
	void _lastAccessMap(std::map<ThreadId, unsigned long> &output) {}
};

class ConstExpression : public UnrefinableExpression {
public:
        unsigned long v;
protected:
	unsigned _hash() const { return v; }
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
public:
	bool isLogical() const { return v == 0 || v == 1; }
	static Expression *get(unsigned long v)
	{
		ConstExpression *work = new ConstExpression();
		work->v = v;
		return intern(work);
	}
	void visit(HeapVisitor &hv) const {}
	void visit(ExpressionVisitor &ev) { ev.visit(this); }
	Expression *map(ExpressionMapper &m) { return m.map(this); }
	bool isConstant(unsigned long *cv) const { *cv = v; return true; }
	void _lastAccessMap(std::map<ThreadId, unsigned long> &output) {}
};

class ExpressionLastStore : public Expression {
public:
	EventTimestamp load;
	EventTimestamp store;
	Expression *vaddr;
private:
	ExpressionLastStore(EventTimestamp _load, EventTimestamp _store,
			    Expression *_vaddr)
		: load(_load), store(_store), vaddr(_vaddr)
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
	unsigned _hash() const {
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
		return get(load, store, va);
	}
public:
	static Expression *get(EventTimestamp load, EventTimestamp store,
			       Expression *vaddr)
	{
		return new ExpressionLastStore(load, store, vaddr);
	}
	Expression *refine(const MachineState<abstract_interpret_value> *ms,
			   LogReader<abstract_interpret_value> *lf,
			   LogReaderPtr ptr,
			   bool *progress,
			   const std::map<ThreadId, unsigned long> &validity,
			   EventTimestamp ev);
	void visit(HeapVisitor &hv) const { hv(vaddr); }
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
	void _lastAccessMap(std::map<ThreadId, unsigned long> &output)
	{
		vaddr->lastAccessMap(output);
		lastAccessTS(load, output);		
		lastAccessTS(store, output);		
	}
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
	unsigned _hash() const {
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
			return new ExpressionHappensBefore(before, after);
		}
	}
	EventTimestamp timestamp() const { return after; }
	bool isLogical() const { return true; }
	void visit(HeapVisitor &hv) const {}
	void visit(ExpressionVisitor &ev) { ev.visit(this); }
	Expression *map(ExpressionMapper &m) { return m.map(this); }

	Expression *refine(const MachineState<abstract_interpret_value> *ms,
			   LogReader<abstract_interpret_value> *lf,
			   LogReaderPtr ptr,
			   bool *progress,
			   const std::map<ThreadId, unsigned long> &validity,
			   EventTimestamp ev) { return this; }

	Relevance relevance(const EventTimestamp &ev, Relevance, Relevance) {
		return Relevance(Relevance(before, ev),
				 Relevance(after, ev));
	}
	void _lastAccessMap(std::map<ThreadId, unsigned long> &output)
	{
		lastAccessTS(before, output);
		lastAccessTS(after, output);
	}
};

class LoadExpression : public Expression {
public:
	Expression *val;
	Expression *addr;
	Expression *storeAddr;
	EventTimestamp when;
	EventTimestamp store;
	unsigned size;
protected:
	char *mkName() const { return my_asprintf("(load%d@%d:%lx;%d:%lx %s:%s -> %s)",
						  size, when.tid._tid(), when.idx,
						  store.tid._tid(), store.idx,
						  addr->name(), storeAddr->name(),
						  val->name()); }
	unsigned _hash() const { return val->hash() ^ (addr->hash() * 3) ^ (when.hash() * 5) ^ (store.hash() * 7) ^ (storeAddr->hash() * 11) ^ (size * 13); }
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
public:
	static Expression *get(EventTimestamp when, Expression *val, Expression *addr,
			       Expression *storeAddr, EventTimestamp store, unsigned size)
	{
		LoadExpression *work = new LoadExpression();
		work->val = val;
		work->addr = addr;
		work->storeAddr = storeAddr;
		work->when = when;
		work->store = store;
		work->size = size;
		return intern(work);
	}
	Expression *refine(const MachineState<abstract_interpret_value> *ms,
			   LogReader<abstract_interpret_value> *lf,
			   LogReaderPtr ptr,
			   bool *progress,
			   const std::map<ThreadId, unsigned long> &validity,
			   EventTimestamp ev);

	EventTimestamp timestamp() const { return when; }
	void visit(HeapVisitor &hv) const {hv(addr); hv(val); hv(storeAddr);}
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
			Relevance(val->relevance(ev, r + 1, high_thresh),
				  addr->relevance(ev, r + 1, high_thresh)),
			storeAddr->relevance(ev, r + 1, high_thresh));
	}
	void _lastAccessMap(std::map<ThreadId, unsigned long> &output)
	{
		val->lastAccessMap(output);
		addr->lastAccessMap(output);
		storeAddr->lastAccessMap(output);
		lastAccessTS(when, output);
		lastAccessTS(store, output);
	}
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
public:
	virtual Expression *semiDupe(Expression *l, Expression *r) const = 0;
	Expression *refine(const MachineState<abstract_interpret_value> *ms,
			   LogReader<abstract_interpret_value> *lf,
			   LogReaderPtr ptr,
			   bool *progress,
			   const std::map<ThreadId, unsigned long> &validity,
			   EventTimestamp ev);
	Expression *l, *r;

	
	void visit(HeapVisitor &hv) const
	{								
		hv(l);							
		hv(r);							
	}								
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
	void _lastAccessMap(std::map<ThreadId, unsigned long> &output)
	{
		l->lastAccessMap(output);
		r->lastAccessMap(output);
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
		unsigned _hash() const { return l->hash() ^ (r->hash() * 3) ^ sizeof(nme); } \
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
public:
	virtual Expression *semiDupe(Expression *l) const = 0;
	virtual Expression *refine(const MachineState<abstract_interpret_value> *ms,
				   LogReader<abstract_interpret_value> *lf,
				   LogReaderPtr ptr,
				   bool *progress,
				   const std::map<ThreadId, unsigned long> &validity,
				   EventTimestamp ev);
	Expression *l;

	void visit(HeapVisitor &hv) const				
	{								
		hv(l);							
	}								
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
	void _lastAccessMap(std::map<ThreadId, unsigned long> &output)
	{
		l->lastAccessMap(output);
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
		unsigned _hash() const { return l->hash() ^ sizeof(nme); } \
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
	      Expression *refine(const MachineState<abstract_interpret_value> *ms,
					 LogReader<abstract_interpret_value> *lf,
					 LogReaderPtr ptr,
					 bool *progress,
					 const std::map<ThreadId, unsigned long> &validity,
					 EventTimestamp ev);
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
	unsigned _hash() const { return cond->hash() ^ (t->hash() * 3) ^ (f->hash() * 5) ^ 97; }
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
public:
	bool isLogical() const;
	static Expression *get(Expression *_cond, Expression *_t, Expression *_f);
	void visit(HeapVisitor &hv) const
	{
		hv(cond);
		hv(t);
		hv(f);
	}
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
	Expression *refine(const MachineState<abstract_interpret_value> *ms,
			   LogReader<abstract_interpret_value> *lf,
			   LogReaderPtr ptr,
			   bool *progress,
			   const std::map<ThreadId, unsigned long> &validity,
			   EventTimestamp ev) { return this; }
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
	void _lastAccessMap(std::map<ThreadId, unsigned long> &output)
	{
		cond->lastAccessMap(output);
		t->lastAccessMap(output);
		f->lastAccessMap(output);
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
		if (!_name)
			_name = vex_asprintf("{%lx:%s}", v, origin->name());
		return _name;		
	}
};

template <>
abstract_interpret_value mkConst(unsigned long x)
{
	return abstract_interpret_value(x, ConstExpression::get(x));
}


static inline void visit_aiv(const abstract_interpret_value &aiv, HeapVisitor &hv)
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
		abstract_interpret_value content[0];
	};
	MCLookasideEntry *headLookaside;
	PhysicalAddress base;

	static VexAllocType mcl_allocator;

	void visit(HeapVisitor &hv) const
	{
		hv(underlying);
		hv(headLookaside);
	}
	void destruct() {}

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

   We also store a log of the RIPs touched between each conditional
   expression (the ones in the vector are touched *after* the current
   condition is evaluated).  This is in theory redundant with the
   condition, because if you pass the condition then you ought to
   always follow the same RIP path, but it makes it a *lot* easier to
   see if something's gone wrong.

   Finally, we store the last memory index which is valid with this
   history, which is the index of the last memory operation after
   passing this condition and before reaching the next one.  This is
   extremely useful when checking whether a given expression is
   syntactically valid, in the sense that all memory indexes are
   defined by enclosing RIP expressions.
*/
class History : public Named, public GarbageCollected<History> {
public:
	Expression *condition;
	unsigned long last_valid_idx;
	EventTimestamp when;
	std::vector<unsigned long> rips;
	History *parent;
	History(Expression *_condition,
		EventTimestamp _when,
		History *_parent)
		: condition(_condition),
		  last_valid_idx(_parent ? _parent->last_valid_idx : 0),
		  when(_when),
		  rips(),
		  parent(_parent)
	{
		assert(when.tid.valid());
		calcLastAccessed();
	}
	History(Expression *cond,
		unsigned long _last_valid_idx,
		EventTimestamp _when,
		std::vector<unsigned long> &_rips,
		History *_parent)
		: condition(cond),
		  last_valid_idx(_last_valid_idx),
		  when(_when),
		  rips(_rips),
		  parent(_parent)
	{
		assert(when.tid.valid());
		calcLastAccessed();
	}
	Relevance relevance(const EventTimestamp &ev, Relevance low_thresh, Relevance high_thresh) {
		if (low_thresh >= high_thresh)
			return low_thresh;
		Relevance r = Relevance(condition->relevance(ev, low_thresh, high_thresh),
					Relevance(when, ev));
		if (parent)
			r = Relevance(parent->relevance(ev, r + 100, high_thresh) - 100,
				      r);
		return r;
	}
	void lastAccessMap(std::map<ThreadId, unsigned long> &output)
	{
		for (std::map<ThreadId, unsigned long>::iterator it = lastAccessed.begin();
		     it != lastAccessed.end();
		     it++) {
			if (it->second > output[it->first])
				output[it->first] = it->second;
		}
	}
private:
	WeakRef<History> concrete;
	std::map<ThreadId, unsigned long> lastAccessed;
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
	void visit(HeapVisitor &hv) const
	{
		hv(condition);
		hv(parent);
	}
	void visit(ExpressionVisitor &ev)
	{
		condition->visit(ev);
		if (parent)
			parent->visit(ev);
	}
	History *map(ExpressionMapper &m)
	{
		return new History(condition->map(m),
				   when,
				   parent ? parent->map(m) : NULL);
	}
	bool isEqual(const History *h) const
	{
		if (h == this)
			return true;
		if (when != h->when)
			return false;
		if (rips.size() != h->rips.size())
			return false;
		if (!condition->isEqual(h->condition))
			return false;
		if ((parent && !h->parent) ||
		    (!parent && h->parent))
			return false;
		std::vector<unsigned long>::const_iterator it1;
		std::vector<unsigned long>::const_iterator it2;
		it1 = rips.begin();
		it2 = h->rips.begin();
		while (it1 != rips.end()) {
			assert(it2 != h->rips.end());
			if (*it1 != *it2)
				return false;
		}
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
		return new History(e, when, this);
	}

	void footstep(unsigned long rip)
	{
		rips.push_back(rip);
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
		return new History(condition,
				   last_valid_idx,
				   when,
				   rips,
				   parent->dupeWithParentReplace(from, to));
	}

	History *truncate(unsigned long, bool);
	History *truncateInclusive(unsigned long x) { return truncate(x, true); }
	History *truncateExclusive(unsigned long x) { return truncate(x, false); }

	History *concretise() {
		if (!concrete.get())
			concrete.set(new History(condition->concretise(),
						 last_valid_idx,
						 when,
						 rips,
						 NULL));
		return concrete.get();
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
	Expression *refineHistory(const MachineState<abstract_interpret_value> *ms,
				  LogReader<abstract_interpret_value> *lf,
				  LogReaderPtr ptr,
				  const std::map<ThreadId, unsigned long> &validity,
				  EventTimestamp ev);
	Expression *refineSubCond(const MachineState<abstract_interpret_value> *ms,
				  LogReader<abstract_interpret_value> *lf,
				  LogReaderPtr ptr,
				  const std::map<ThreadId, unsigned long> &validity,
				  EventTimestamp ev);

protected:
	char *mkName(void) const {
		return my_asprintf("(rip %d:{%s}:%s)", tid._tid(), history ? history->name() : "<nohistory>", cond ? cond->name() : "<nocond>");
	}
	unsigned _hash() const {
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
public:
	static Expression *get(ThreadId tid, History *history, Expression *cond,
			       LogReader<abstract_interpret_value> *model,
			       LogReaderPtr start)
	{
		return intern(new ExpressionRip(tid, history, cond,
						model, start));
	}
	void visit(HeapVisitor &hv) const
	{
		hv(history);
		hv(cond);
		hv(model_execution);
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
	Expression *refine(const MachineState<abstract_interpret_value> *ms,
			   LogReader<abstract_interpret_value> *lf,
			   LogReaderPtr ptr,
			   bool *progress,
			   const std::map<ThreadId, unsigned long> &validity,
			   EventTimestamp ev);
	Relevance relevance(const EventTimestamp &ev, Relevance low_thresh, Relevance high_thresh) {
		Relevance cr = cond->relevance(ev, low_thresh, high_thresh);
		return Relevance(cr, history->relevance(ev, cr + 1, high_thresh));
	}

	void _lastAccessMap(std::map<ThreadId, unsigned long> &output)
	{
		cond->lastAccessMap(output);
		history->lastAccessMap(output);
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
	unsigned _hash() const {
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
public:
	static Expression *get(EventTimestamp _when, Expression *_addr)
	{
		return new ExpressionBadPointer(_when, _addr);
	}
	void visit(HeapVisitor &hv) const { hv(addr); }
	void visit(ExpressionVisitor &ev) { ev.visit(this); addr->visit(ev); }
	Expression *map(ExpressionMapper &m) { return m.map(this); }
	EventTimestamp timestamp() const { return when; }
	Expression *refine(const MachineState<abstract_interpret_value> *ms,
			   LogReader<abstract_interpret_value> *lf,
			   LogReaderPtr ptr,
			   bool *progress,
			   const std::map<ThreadId, unsigned long> &validity,
			   EventTimestamp ev) { return this; }

	Relevance relevance(const EventTimestamp &ev, Relevance low, Relevance high)
	{
		Relevance r = Relevance(when, ev);
		return Relevance(r, addr->relevance(ev, r + 1, high));
	}

	void _lastAccessMap(std::map<ThreadId, unsigned long> &output)
	{
		addr->lastAccessMap(output);
		lastAccessTS(when, output);
	}
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

/* force some functions to be included even when they're not needed,
   so that they're available for calling from the debugger. */
static void force_linkage() __attribute__((unused, used));
static void
force_linkage()
{
	gdb_concrete(NULL);
	gdb_abstract(NULL);
}



#endif /* !SLI_H__ */
