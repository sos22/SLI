#ifndef SLI_H__
#define SLI_H__

#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <map>

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
public:
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
	void destruct() { free(_name); _name = NULL; }
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

template <typename t, void (*visit)(const void *, HeapVisitor &) = visit_object<t>, void (*destruct)(void *) = destruct_object<t> >
class VexAllocTypeWrapper {
public:
	VexAllocType type;
	VexAllocTypeWrapper() {
		type.nbytes = sizeof(t);
		type.gc_visit = visit;
		type.destruct = destruct;
		type.name = "<wrapper type>";
	}
	t *alloc() const {
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
	ThreadId(unsigned _tid) : tid(_tid) {}
	ThreadId() : tid(0) {}
	bool operator==(const ThreadId &b) const { return b.tid == tid; }
	bool operator!=(const ThreadId &b) const { return b.tid != tid; }
	bool operator<(const ThreadId &b) const { return tid < b.tid; }
	ThreadId operator++() {
		tid++;
		return *this;
	}
	const unsigned _tid() const { return tid; }
};

class ReplayTimestamp {
public:
	unsigned long val;
	explicit ReplayTimestamp(unsigned long v) : val(v) {}
	ReplayTimestamp() { val = 0; }
	void operator++(int _ignore) { val++; }
	bool operator>(const ReplayTimestamp o) const { return val > o.val; }
	bool operator<(const ReplayTimestamp o) const { return val < o.val; }
	bool operator==(const ReplayTimestamp o) const { return val == o.val; }
};

template <typename t> t min(const t &a, const t &b)
{
	if (a < b)
		return a;
	else
		return b;
}

class ImportOrigin {
	static VexAllocType allocator;
	mutable char *_name;

protected:
	void *operator new(size_t s);
	/* DNI */
	static void operator delete(void *ptr);

	ImportOrigin() : _name(NULL) {}
	~ImportOrigin() {}

	virtual void visit(HeapVisitor &hv) const {hv(_name);}
	virtual void destruct() { this->~ImportOrigin(); }
	virtual char *mkName() const = 0;
public:
	static void visit(const void *ctxt, HeapVisitor &hv)
	{
		((const ImportOrigin *)ctxt)->visit(hv);
	}
	static void destruct(void *ctxt)
	{
		((ImportOrigin *)ctxt)->destruct();
	}
	char *name() const {
		if (!_name)
			_name = mkName();
		return _name;
	}
};

class ImportOriginLogfile : public ImportOrigin {
	static ImportOriginLogfile *w;
protected:
	char *mkName() const { return vex_asprintf("logfile"); }
public:
	static ImportOrigin *get();
};

class ImportOriginInitialValue : public ImportOrigin {
	static ImportOriginInitialValue *w;
protected:
	virtual char *mkName() const { return vex_asprintf("initial_value"); }
public:
	static ImportOrigin *get();
};

class ImportOriginInitialMemory : public ImportOriginInitialValue {
	static ImportOriginInitialMemory *w;
protected:
	char *mkName() const { return vex_asprintf("initial_memory"); }
public:
	static ImportOrigin *get();
};

class ImportOriginInitialRegister : public ImportOriginInitialValue {
	unsigned idx;
	ImportOriginInitialRegister(unsigned _idx) :
		ImportOriginInitialValue(),
		idx(_idx)
	{}
	/* DNI */
	~ImportOriginInitialRegister();
protected:
	char *mkName() const { return vex_asprintf("initial_register(%d)", idx); }
public:
	static ImportOrigin *get(unsigned x);
};

class ImportOriginInitialTemporary : public ImportOriginInitialValue {
	unsigned idx;
	ImportOriginInitialTemporary(unsigned _idx) :
		ImportOriginInitialValue(),
		idx(_idx)
	{}
	/* DNI */
	~ImportOriginInitialTemporary();
protected:
	char *mkName() const { return vex_asprintf("initial_temporary(%d)", idx); }
public:
	static ImportOrigin *get(unsigned x);
};

class ImportOriginSymbolicFailure : public ImportOrigin {
	static ImportOriginSymbolicFailure *w;
protected:
	char *mkName() const { return vex_asprintf("symbolic_failure"); }
public:
	static ImportOrigin *get();
};

template<typename src, typename dest> dest import_ait(src x, ImportOrigin *origin);
template<typename ait> ait load_ait(ait x, ait addr, ReplayTimestamp when);

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
	
	template <typename new_type> void abstract(expression_result<new_type> *out,
						   ImportOrigin *origin) const
	{
		out->lo = import_ait<abst_int_value, new_type>(lo, origin);
		out->hi = import_ait<abst_int_value, new_type>(hi, origin);
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
	void set_reg(unsigned idx, underlying val) { assert(idx < NR_REGS); registers[idx] = val; }
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
	static const VexAllocType arrayAllocType;
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
template <typename ait> class LogRecordInitialRegisters;
template <typename ait> class LogWriter;
template <typename ait> class LogRecordVexThreadState;

template <typename abst_int_type>
class Thread {
	void translateNextBlock(AddressSpace<abst_int_type> *addrSpace);
	struct expression_result<abst_int_type> eval_expression(IRExpr *expr);
	ThreadEvent<abst_int_type> *do_dirty_call(ReplayTimestamp when, IRDirty *details);
	expression_result<abst_int_type> do_ccall_calculate_condition(struct expression_result<abst_int_type> *args);
	expression_result<abst_int_type> do_ccall_calculate_rflags_c(expression_result<abst_int_type> *args);
	expression_result<abst_int_type> do_ccall_generic(IRCallee *cee, struct expression_result<abst_int_type> *rargs);
	expression_result<abst_int_type> do_ccall(IRCallee *cee, IRExpr **args);
public:
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

	IRSB *currentIRSB;
	expression_result_array<abst_int_type> temporaries;
	int currentIRSBOffset;

	static VexAllocTypeWrapper<Thread<abst_int_type> > allocator;

	abst_int_type currentControlCondition;

private:
	~Thread();
public:
	ThreadEvent<abst_int_type> *runToEvent(AddressSpace<abst_int_type> *addrSpace, ReplayTimestamp when);

	static Thread<abst_int_type> *initialThread(const LogRecordInitialRegisters<abst_int_type> &initRegs);
	Thread<abst_int_type> *fork(unsigned newPid);
	Thread<abst_int_type> *dupeSelf() const;
	void dumpSnapshot(LogWriter<abst_int_type> *lw) const;

	void imposeState(const LogRecordVexThreadState<abst_int_type> &rec,
			 AddressSpace<abst_int_type> *as);

	void visit(HeapVisitor &hv) const;

	template <typename new_type> Thread<new_type> *abstract() const;

	void destruct() { temporaries.~expression_result_array<abst_int_type>(); }
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

	void write(unsigned offset, const unsigned long *source, unsigned nr_bytes);
	void read(unsigned offset, unsigned long *dest, unsigned nr_bytes) const;

	MemoryChunk<unsigned long> *dupeSelf() const;
	template <typename nt> MemoryChunk<nt> *abstract() const;

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
class PMapEntry {
	static const VexAllocTypeWrapper<class PMapEntry > allocator;
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
};

template <typename ait>
class PMap {
public:
	static const VexAllocTypeWrapper<PMap<ait> > allocator;
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
};

template <typename ait>
class LogRecord : public Named {
	/* DNI */
	LogRecord(const LogRecord<ait> &);
	ThreadId tid;
protected:
	void *marshal(unsigned cls, unsigned psize, unsigned *sz, void **r) const;
public:
	ThreadId thread() const { return tid; }
	LogRecord(ThreadId _tid) : tid(_tid) {}
	virtual void *marshal(unsigned *size) const = 0;
	virtual ~LogRecord();
	virtual LogRecord *dupe() const = 0;
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
	LogRecord<ait> *dupe() const
	{
		return new LogRecordInitialSighandlers<ait>(this->thread(), handlers);
	}
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
};

template <typename ait>
class LogReader {
public:
	virtual LogRecord<ait> *read(LogReaderPtr startPtr, LogReaderPtr *outPtr) const = 0;
	virtual ~LogReader() {}
	template <typename new_type> LogReader<new_type> *abstract() const;
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
};

template <typename abst_int_type>
class MachineState {
public:
	LibvexVector<Thread<abst_int_type> > *threads;

	static VexAllocTypeWrapper<MachineState<abst_int_type> > allocator;

	bool exitted;
	abst_int_type exit_status;
	ThreadId nextTid;

private:
	/* DNI */
	MachineState();
	~MachineState();
	static MachineState *initialMachineState(AddressSpace<abst_int_type> *as,
						 const LogRecordInitialSighandlers<abst_int_type> &handlers);
public:
	AddressSpace<abst_int_type> *addressSpace;
	SignalHandlers<abst_int_type> signalHandlers;
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
	virtual void record(Thread<ait> *thr, const ThreadEvent<ait> *evt) = 0;
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
		currentStateRoot((void **)&currentState)
	{
	}
	void replayLogfile(const LogReader<abst_int_type> *lf, LogReaderPtr startingPoint,
			   LogReaderPtr *endingPoint = NULL, LogWriter<abst_int_type> *log = NULL,
			   EventRecorder<abst_int_type> *er = NULL, ReplayTimestamp when = ReplayTimestamp(0));
	InterpretResult getThreadMemoryTrace(ThreadId tid,
					     MemoryTrace<abst_int_type> **output,
					     unsigned max_events,
					     ReplayTimestamp when = ReplayTimestamp(0));
	void runToAccessLoggingEvents(ThreadId tid, unsigned nr_accesses,
				      LogWriter<abst_int_type> *output = NULL,
				      ReplayTimestamp when = ReplayTimestamp(0));
	void runToFailure(ThreadId tid, LogWriter<abst_int_type> *output,
			  unsigned max_events = 0, ReplayTimestamp when = ReplayTimestamp(0));

};

template <typename ait>
class LogWriter {
public:
	virtual void append(const LogRecord<ait> &lr) = 0;
	virtual ~LogWriter() {}
	InterpretResult recordEvent(Thread<ait> *thr, MachineState<ait> *ms, ThreadEvent<ait> *evt);
};

class LogFileWriter : public LogWriter<unsigned long> {
	int fd;
public:
	void append(const LogRecord<unsigned long> &lr);
	static LogFileWriter *open(const char *fname);
	~LogFileWriter();
};

template <typename ait> void destroy_memlog(void *_ctxt);

template <typename ait>
class MemLog : public LogReader<ait>, public LogWriter<ait> {
	static VexAllocTypeWrapper<MemLog<ait>, visit_object<MemLog<ait> >, destroy_memlog<ait> > allocator;
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
	MemLog();

	/* Should never be called, used to force construction of
	 * vtable. */
	virtual void forceVtable();

public:
	static MemLog *emptyMemlog();
	static LogReaderPtr startPtr() { return mkPtr(0); }
	MemLog<ait> *dupeSelf() const;
	LogRecord<ait> *read(LogReaderPtr startPtr, LogReaderPtr *outPtr) const;
	InterpretResult recordEvent(Thread<ait> *thr, MachineState<ait> *ms, ThreadEvent<ait> *evt);
	void dump() const;

	void append(const LogRecord<ait> &lr);

	/* Should only be called by GC destruct routine */
	void destruct();

	void visit(HeapVisitor &hv) const;
};

template <typename ait>
class ThreadEvent : public Named {
protected:
	ThreadEvent(Thread<ait> *_thr, ReplayTimestamp _when) : thr(_thr), when(_when) {}
public:
	Thread<ait> *thr;
	ReplayTimestamp when;
	/* Replay the event using information in the log record */
	virtual void replay(LogRecord<ait> *lr, MachineState<ait> *ms) = 0;
	virtual InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL) = 0;
	virtual ThreadEvent<ait> *dupe() const = 0;

	/* This should really be DNI, but g++ doesn't let you inherit
	 * from a class which has a private destructor. */
	~ThreadEvent() { abort(); }

	virtual void visit(HeapVisitor &hv) const {hv(thr);};
};

template <typename ait>
class RdtscEvent : public ThreadEvent<ait> {
	IRTemp tmp;
	RdtscEvent(Thread<ait> *thr, ReplayTimestamp when, IRTemp _tmp) : ThreadEvent<ait>(thr, when), tmp(_tmp) {};
	static VexAllocTypeWrapper<RdtscEvent<ait> > allocator;
	~RdtscEvent();
protected:
	virtual char *mkName() const { return my_asprintf("rdtsc(%d)", tmp); }
public:
	virtual void replay(LogRecord<ait> *lr, MachineState<ait> *ms);
	virtual InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	static ThreadEvent<ait> *get(Thread<ait> *thr, ReplayTimestamp when, IRTemp temp)
	{ return new (allocator.alloc()) RdtscEvent<ait>(thr, when, temp); }
	ThreadEvent<ait> *dupe() const { return get(this->thr, this->when, tmp); }
};

template <typename ait> class MemoryAccessLoad;
template <typename ait> class MemoryAccessStore;

template <typename ait>
class LoadEvent : public ThreadEvent<ait> {
	friend class MemoryAccessLoad<ait>;
	IRTemp tmp;
	ait addr;
	unsigned size;
	LoadEvent(Thread<ait> *thr, ReplayTimestamp when, IRTemp _tmp, ait _addr, unsigned _size) :
		ThreadEvent<ait>(thr, when),
		tmp(_tmp),
		addr(_addr),
		size(_size)
	{
	}
	static VexAllocTypeWrapper<LoadEvent<ait> > allocator;
protected:
	virtual char *mkName() const { return my_asprintf("load(%s, %d, %d)", name_aiv(addr), tmp, size); }
public:
	virtual void replay(LogRecord<ait> *lr, MachineState<ait> *ms);
	virtual InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	static ThreadEvent<ait> *get(Thread<ait> *thr, ReplayTimestamp when, IRTemp _tmp, ait _addr, unsigned _size)
	{
		void *b = allocator.alloc();
		return new (b) LoadEvent<ait>(thr, when, _tmp, _addr, _size);
	}
	ThreadEvent<ait> *dupe() const { return get(this->thr, this->when, tmp, addr, size); }
	void visit(HeapVisitor &hv) const { visit_aiv(addr, hv); ThreadEvent<ait>::visit(hv); }
};

template <typename ait>
class StoreEvent : public ThreadEvent<ait> {
	friend class MemoryAccessStore<ait>;
	ait addr;
	unsigned size;
	expression_result<ait> data;
	StoreEvent(Thread<ait> *thr, ReplayTimestamp when, ait addr, unsigned size, expression_result<ait> data);
	static VexAllocTypeWrapper<StoreEvent<ait> > allocator;
protected:
	virtual char *mkName() const { return my_asprintf("store(%d, %s, %s)", size, name_aiv(addr), data.name()); }
public:
	virtual void replay(LogRecord<ait> *lr, MachineState<ait> *ms);
	virtual InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	static ThreadEvent<ait> *get(Thread<ait> *thr, ReplayTimestamp when, ait _addr, unsigned _size, expression_result<ait> data)
	{
		void *b = allocator.alloc();
		return new (b) StoreEvent<ait>(thr, when, _addr, _size, data);
	}
	ThreadEvent<ait> *dupe() const { return get(this->thr, this->when, addr, size, data); }

	void visit(HeapVisitor &hv) const { visit_aiv(addr, hv); data.visit(hv); ThreadEvent<ait>::visit(hv); }
	void destruct() { data.~expression_result<ait>(); ThreadEvent<ait>::destruct(); }
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
	static VexAllocTypeWrapper<InstructionEvent<ait> > allocator;
	InstructionEvent(Thread<ait> *thr, ReplayTimestamp when, ait _rip, ait _reg0, ait _reg1,
			 ait _reg2, ait _reg3, ait _reg4) :
		ThreadEvent<ait>(thr, when),
		rip(_rip),
		reg0(_reg0),
		reg1(_reg1),
		reg2(_reg2),
		reg3(_reg3),
		reg4(_reg4)
	{
	}
protected:
	virtual char *mkName() const {
		return my_asprintf("footstep()");
	}
public:
	virtual void replay(LogRecord<ait> *lr, MachineState<ait> *ms);
	virtual InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	static InstructionEvent<ait> *get(Thread<ait> *thr, ReplayTimestamp when, ait _rip, ait _reg0, ait _reg1,
					  ait _reg2, ait _reg3, ait _reg4)
	{
		void *b = allocator.alloc();
		return new (b) InstructionEvent<ait>(thr, when, _rip, _reg0, _reg1, _reg2, _reg3, _reg4);
	}
	ThreadEvent<ait> *dupe() const { return get(this->thr, this->when, rip, reg0, reg1, reg2, reg3, reg4); }

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
};

template <typename ait>
class CasEvent : public ThreadEvent<ait> {
	IRTemp dest;
	expression_result<ait> addr;
	expression_result<ait> data;
	expression_result<ait> expected;
	unsigned size;
	static VexAllocTypeWrapper<CasEvent<ait> > allocator;
	CasEvent(Thread<ait> *thr,
		 ReplayTimestamp when,
		 IRTemp _dest,
		 expression_result<ait> _addr,
		 expression_result<ait> _data,
		 expression_result<ait> _expected,
		 unsigned _size) :
		ThreadEvent<ait>(thr, when),
		dest(_dest),
		addr(_addr),
		data(_data),
		expected(_expected),
		size(_size)
	{
	}
protected:
	virtual char *mkName() const {
		return my_asprintf("cas(dest %d, size %d)",
				   dest, size);
	}
public:
	virtual void replay(LogRecord<ait> *lr, MachineState<ait> *ms);
	virtual InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	virtual InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL,
				     LogRecord<ait> **lr2 = NULL);
	void replay(LogRecord<ait> *lr, MachineState<ait> *ms,
		    const LogReader<ait> *lf, LogReaderPtr ptr,
		    LogReaderPtr *outPtr, LogWriter<ait> *lw);

	static ThreadEvent<ait> *get(Thread<ait> *thr,
				     ReplayTimestamp when,
				     IRTemp _dest,
				     expression_result<ait> _addr,
				     expression_result<ait> _data,
				     expression_result<ait> _expected,
				     unsigned _size)
	{
		void *b = allocator.alloc();
		return new (b) CasEvent<ait>(thr, when, _dest, _addr, _data, _expected, _size);
	}
	ThreadEvent<ait> *dupe() const { return get(this->thr, this->when, dest, addr, data, expected, size); }

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
};

template <typename ait>
class SyscallEvent : public ThreadEvent<ait> {
protected:
	virtual char *mkName() const {
		return my_asprintf("syscall");
	}
	SyscallEvent(Thread<ait> *thr, ReplayTimestamp when) : ThreadEvent<ait>(thr, when) {}
	static VexAllocTypeWrapper<SyscallEvent<ait> > allocator;
public:
	virtual void replay(LogRecord<ait> *lr, MachineState<ait> *ms);
	virtual InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	ThreadEvent<ait> *dupe() const { return get(this->thr, this->when); }
	static ThreadEvent<ait> *get(Thread<ait> *thr, ReplayTimestamp when)
	{ return new (allocator.alloc()) SyscallEvent(thr, when); }
};

template <typename ait>
class SignalEvent : public ThreadEvent<ait> {
public:
	unsigned signr;
	ait virtaddr;
	SignalEvent(Thread<ait> *thr, ReplayTimestamp when, unsigned _signr, ait _va) :
		ThreadEvent<ait>(thr, when),
		signr(_signr),
		virtaddr(_va)
	{
	}
	static VexAllocTypeWrapper<SignalEvent<ait> > allocator;
protected:
	virtual char *mkName() const {
		return my_asprintf("signal(nr = %d)", signr);
	}
public:
	virtual void replay(LogRecord<ait> *lr, MachineState<ait> *ms);
	virtual InterpretResult fake(MachineState<ait> *ms, LogRecord<ait> **lr = NULL);

	static ThreadEvent<ait> *get(Thread<ait> *thr, ReplayTimestamp when, unsigned _signr, ait _virtaddr)
	{
		void *b = allocator.alloc();
		return new (b) SignalEvent<ait>(thr, when, _signr, _virtaddr);
	}
	ThreadEvent<ait> *dupe() const { return get(this->thr, this->when, signr, virtaddr); }

	void visit(HeapVisitor &hv) const
	{
		visit_aiv(virtaddr, hv);
		ThreadEvent<ait>::visit(hv);
	}
};

template <typename ait>
class MemoryAccess : public Named {
public:
	ThreadId tid;
	ait addr;
	unsigned size;
	MemoryAccess(ThreadId _tid, ait _addr, unsigned _size)
		: tid(_tid),
		  addr(_addr),
		  size(_size)
	{
	}
	virtual bool isLoad() = 0;
	void dump() const { printf("%s\n", name()); }
};

template <typename ait>
class LogRecordLoad : public LogRecord<ait> {
	friend class LoadEvent<ait>;
	friend class CasEvent<ait>;
	friend class MemoryAccessLoad<ait>;
	unsigned size;
	ait ptr;
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
	LogRecord<ait> *dupe() const
	{
		return new LogRecordLoad<ait>(this->thread(), size, ptr, value);
	}
	template <typename outtype> LogRecordLoad<outtype> *abstract() const
	{
		expression_result<outtype> nvalue;
		value.abstract(&nvalue, ImportOriginLogfile::get());
		return new LogRecordLoad<outtype>(this->thread(),
						  size,
						  outtype::import(ptr, ImportOriginLogfile::get()),
						  nvalue);
	}
};

template <typename ait>
class MemoryAccessLoad : public MemoryAccess<ait> {
protected:
	virtual char *mkName() const {
		return my_asprintf("%d: Load(%x)", this->tid._tid(),
				   this->size);
	}
public:
	MemoryAccessLoad(ThreadId tid, const class LoadEvent<ait> &evt)
		: MemoryAccess<ait>(tid, evt.addr, evt.size)
	{
	}
	MemoryAccessLoad(const LogRecordLoad<ait> &lrl)
		: MemoryAccess<ait>(lrl.thread(), lrl.ptr, lrl.size)
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
	ait ptr;
	expression_result<ait> value;
protected:
	virtual char *mkName() const {
		return my_asprintf("store(%x)", size);
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
	LogRecord<ait> *dupe() const
	{
		return new LogRecordStore<ait>(this->thread(), size, ptr, value);
	}
	template <typename outtype> LogRecordStore<outtype> *abstract() const
	{
		expression_result<outtype> res;
		value.abstract(&res, ImportOriginLogfile::get());
		return new LogRecordStore<outtype>(this->thread(),
						   size,
						   outtype::import(ptr, ImportOriginLogfile::get()),
						   res);
	}
};

template <typename ait>
class MemoryAccessStore : public MemoryAccess<ait> {
protected:
	virtual char *mkName() const {
		return my_asprintf("%d: Store(%x)",
				   this->tid._tid(),
				   this->size);
	}
public:
	MemoryAccessStore(ThreadId tid, const class StoreEvent<ait> &evt)
		: MemoryAccess<ait>(tid, evt.addr, evt.size)
	{
	}
	MemoryAccessStore(const LogRecordStore<ait> &lrs)
		: MemoryAccess<ait>(lrs.thread(), lrs.ptr, lrs.size)
	{
	}
	virtual bool isLoad() { return false; }
};

/* Essentially a thin wrapper around std::vector */
template <typename ait>
class MemoryTrace {
public:
	std::vector<MemoryAccess<ait> *> content;
	~MemoryTrace() {
		for (unsigned x; x < content.size(); x++)
			delete content[x];
	}
	size_t size() const { return content.size(); }
	MemoryAccess<ait> *&operator[](unsigned idx) { return content[idx]; }
	void push_back(MemoryAccess<ait> *x) { content.push_back(x); }
	MemoryTrace();
	MemoryTrace(const LogReader<ait> &lr, LogReaderPtr start);
	void dump() const;
};

template <typename ait>
class MemTracePool {
	typedef std::map<ThreadId, MemoryTrace<ait> *> contentT;
	contentT content;
public:
	~MemTracePool();
	MemTracePool(MachineState<ait> *base_state);

	std::map<ThreadId, Maybe<unsigned> > *firstRacingAccessMap();
};

template <typename ait>
class LogRecordFootstep : public LogRecord<ait> {
	VexGcVisitor<LogRecordFootstep<ait> > visitor;
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
		visitor(this),
		rip(_rip),
		reg0(_reg0),
		reg1(_reg1),
		reg2(_reg2),
		reg3(_reg3),
		reg4(_reg4)
	{
	}
	void *marshal(unsigned *size) const;
	LogRecordFootstep<ait> *dupe() const
	{
		return new LogRecordFootstep<ait>(this->thread(), rip, reg0, reg1, reg2, reg3, reg4);
	}
	template <typename outtype> LogRecordFootstep<outtype> *abstract() const
	{
		return new LogRecordFootstep<outtype>(this->thread(),
						      outtype::import(rip, ImportOriginLogfile::get()),
						      outtype::import(reg0, ImportOriginLogfile::get()),
						      outtype::import(reg1, ImportOriginLogfile::get()),
						      outtype::import(reg2, ImportOriginLogfile::get()),
						      outtype::import(reg3, ImportOriginLogfile::get()),
						      outtype::import(reg4, ImportOriginLogfile::get()));
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
	VexGcVisitor<LogRecordSyscall<ait> > visitor;
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
		visitor(this),
		sysnr(_sysnr),
		res(_res),
		arg1(_arg1),
		arg2(_arg2),
		arg3(_arg3)
	{
	}
	void *marshal(unsigned *size) const;
	LogRecord<ait> *dupe() const
	{
		return new LogRecordSyscall<ait>(this->thread(), sysnr, res, arg1, arg2, arg3);
	}
	template <typename outtype> LogRecordSyscall<outtype> *abstract() const
	{
		return new LogRecordSyscall<outtype>(this->thread(),
						     outtype::import(sysnr, ImportOriginLogfile::get()),
						     outtype::import(res, ImportOriginLogfile::get()),
						     outtype::import(arg1, ImportOriginLogfile::get()),
						     outtype::import(arg2, ImportOriginLogfile::get()),
						     outtype::import(arg3, ImportOriginLogfile::get()));
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
	VexGcVisitor<LogRecordMemory<ait> > visitor;
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
		visitor(this),
		size(_size),
		start(_start),
		contents(_contents)
	{}
	virtual ~LogRecordMemory() { free((void *)contents); }
	void *marshal(unsigned *size) const;
	LogRecord<ait> *dupe() const
	{
		ait *b = (ait *)malloc(size);
		for (unsigned x = 0; x < size; x++)
			b[x] = contents[x];
		return new LogRecordMemory<ait>(this->thread(), size, start, b);
	}
	template <typename outtype> LogRecordMemory<outtype> *abstract() const
	{
		outtype *b = (outtype *)malloc(size * sizeof(outtype));
		for (unsigned x = 0; x < size; x++)
			b[x] = outtype::import(contents[x], ImportOriginLogfile::get());
		return new LogRecordMemory<outtype>(this->thread(), size, outtype::import(start, ImportOriginLogfile::get()), b);
	}
	void visit(HeapVisitor &hv) const
	{
		visit_aiv(start, hv);
	}
};

template <typename ait>
class LogRecordRdtsc : public LogRecord<ait> {
	friend class RdtscEvent<ait>;
	VexGcVisitor<LogRecordRdtsc<ait> > visitor;
	ait tsc;
protected:
	char *mkName() const {
		return my_asprintf("rdtsc()");
	}
public:
	LogRecordRdtsc(ThreadId _tid,
		       ait _tsc)
		: LogRecord<ait>(_tid),
		  visitor(this),
		  tsc(_tsc)
	{
	}
	void *marshal(unsigned *size) const;
	LogRecord<ait> *dupe() const
	{
		return new LogRecordRdtsc<ait>(this->thread(), tsc);
	}
	template <typename outtype> LogRecordRdtsc<outtype> *abstract() const
	{
		return new LogRecordRdtsc<outtype>(this->thread(),
						   outtype::import(tsc, ImportOriginLogfile::get()));
	}
	void visit(HeapVisitor &hv) const { visit_aiv(tsc, hv); }
};

template <typename ait>
class LogRecordSignal : public LogRecord<ait> {
	VexGcVisitor<LogRecordSignal<ait> > visitor;
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
		visitor(this),
		rip(_rip),
		signr(_signr),
		err(_err),
		virtaddr(_va)
	{
	}
	void *marshal(unsigned *size) const;
	LogRecord<ait> *dupe() const
	{
		return new LogRecordSignal<ait>(this->thread(), rip, signr, err, virtaddr);
	}
	template <typename outtype> LogRecordSignal<outtype> *abstract() const
	{
		return new LogRecordSignal<outtype>(this->thread(),
						    outtype::import(rip, ImportOriginLogfile::get()),
						    signr,
						    outtype::import(err, ImportOriginLogfile::get()),
						    outtype::import(virtaddr, ImportOriginLogfile::get()));
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
	VexGcVisitor<LogRecordAllocateMemory<ait> > visitor;
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
		visitor(this),
		start(_start),
		size(_size),
		prot(_prot),
		flags(_flags)
	{
	}      
	void *marshal(unsigned *size) const;
	LogRecord<ait> *dupe() const
	{
		return new LogRecordAllocateMemory<ait>(this->thread(), start, size, prot, flags);
	}
	template <typename outtype> LogRecordAllocateMemory<outtype> *abstract() const
	{
		return new LogRecordAllocateMemory<outtype>(this->thread(),
							    outtype::import(start, ImportOriginLogfile::get()),
							    outtype::import(size, ImportOriginLogfile::get()),
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
	LogRecord<ait> *dupe() const
	{
		return new LogRecordInitialRegisters(this->thread(), regs);
	}
	template <typename outtype> LogRecordInitialRegisters<outtype> *abstract() const
	{
		return new LogRecordInitialRegisters<outtype>(this->thread(), regs);
	}
};

template <typename ait>
class LogRecordInitialBrk : public LogRecord<ait> {
	VexGcVisitor<LogRecordInitialBrk<ait> > visitor;
protected:
	virtual char *mkName() const {
		return my_asprintf("initbrk()");
	}
public:
	ait brk;
	LogRecordInitialBrk(ThreadId tid,
			    ait _brk) :
		LogRecord<ait>(tid),
		visitor(this),
		brk(_brk)
	{
	}
	void *marshal(unsigned *size) const;
	LogRecord<ait> *dupe() const
	{
		return new LogRecordInitialBrk(this->thread(), brk);
	}
	template <typename outtype> LogRecordInitialBrk<outtype> *abstract() const
	{
		return new LogRecordInitialBrk<outtype>(this->thread(),
							outtype::import(brk, ImportOriginLogfile::get()));
	}
	void visit(HeapVisitor &hv) const { visit_aiv(brk, hv); }
};

template <typename ait>
class LogRecordVexThreadState : public LogRecord<ait> {
	VexGcVisitor<LogRecordVexThreadState<ait> > visitor;
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
	LogRecord<ait> *dupe() const
	{
		return new LogRecordVexThreadState(this->thread(), statement_nr, tmp);
	}
	template <typename outtype> LogRecordVexThreadState<outtype> *abstract() const
	{
		expression_result_array<outtype> ntmp;
		tmp.abstract(&ntmp);
		return new LogRecordVexThreadState<outtype>(this->thread(), statement_nr, ntmp);
	}
	void visit(HeapVisitor &hv) const { tmp.visit(hv); }
};

template <typename ait>
class AddressSpace {
public:
	unsigned long brkptr;
	unsigned long brkMapPtr;
	VAMap *vamap;
	PMap<ait> *pmap;

	static VexAllocTypeWrapper<AddressSpace<ait> > allocator;

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
		writeMemory(rec.start, rec.size, rec.contents, true);
	}
	void store(ait start, unsigned size, const expression_result<ait> &val,
		   bool ignore_protection = false,
		   const Thread<ait> *thr = NULL);
	void writeMemory(ait start, unsigned size,
			 const ait *contents, bool ignore_protection = false,
			 const Thread<ait> *thr = NULL);
	expression_result<ait> load(ReplayTimestamp when, ait start, unsigned size,
				    bool ignore_protection = false,
				    const Thread<ait> *thr = NULL);
	void readMemory(ait start, unsigned size,
			ait *contents, bool ignore_protection = false,
			const Thread<ait> *thr = NULL);
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

	void dumpBrkPtr(LogWriter<ait> *lw) const;
	void dumpSnapshot(LogWriter<ait> *lw) const;

	template <typename new_type> AddressSpace<new_type> *abstract() const;

	void destruct() {}
};

template<typename ait> void replay_syscall(const LogRecordSyscall<ait> *lrs,
					   Thread<ait> *thr,
					   MachineState<ait> *mach);

template<typename ait> void process_memory_records(AddressSpace<ait> *addrSpace,
						   const LogReader<ait> *lf,
						   LogReaderPtr startOffset,
						   LogReaderPtr *endOffset,
						   LogWriter<ait> *lw);

void debugger_attach(void);

void init_sli(void);

void gdb_machine_state(const MachineState<unsigned long> *ms);

class Expression : public Named {
	static const unsigned nr_heads = 262144;
	static Expression *heads[nr_heads];
	static unsigned chain_lengths[nr_heads];
	static unsigned long eq_calls[nr_heads];
	static unsigned tot_outstanding;
	static unsigned nr_interned;
	Expression *next;
	Expression **pprev;
	unsigned hashval;
	static void dump_eq_calls_table();
protected:
	static Expression *intern(Expression *e);
	virtual unsigned _hash() const = 0;
	virtual bool _isEqual(const Expression *other) const = 0;
public:
	unsigned hash() const { return hashval; }
	virtual bool isConstant(unsigned long *cv) const { return false; }
	virtual ReplayTimestamp timestamp() const { return ReplayTimestamp(0); }
	Expression() : Named(), next(NULL) {}
	bool isEqual(const Expression *other) const {
		if (other == this)
			return true;
		else if (hashval == other->hashval)
			return _isEqual(other);
		else
			return false;
	}
	void destruct() {
		if (pprev) {
			*pprev = next;
			if (next)
				next->pprev = pprev;
			chain_lengths[hashval % nr_heads]--;
			nr_interned--;
		}
		tot_outstanding--;
		Named::destruct();
	}
};

class ConstExpression : public Expression {
	static VexAllocTypeWrapper<ConstExpression,
				   visit_object<ConstExpression>,
				   destruct_object<ConstExpression> > allocator;
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
public:
	static Expression *get(unsigned long v)
	{
		ConstExpression *work = new (allocator.alloc()) ConstExpression();
		work->v = v;
		return intern(work);
	}
	void visit(HeapVisitor &hv) const {}
	bool isConstant(unsigned long *cv) const { *cv = v; return true; }
};

class ImportExpression : public Expression {
	static VexAllocTypeWrapper<ImportExpression,
				   visit_object<ImportExpression>,
				   destruct_object<ImportExpression> > allocator;
        unsigned long v;
	ImportOrigin *origin;
protected:
	unsigned _hash() const { return (unsigned long)this / 64; }
	char *mkName() const { return my_asprintf("import:%s %lx", origin->name(), v); }
	bool _isEqual(const Expression *other) const {
		return other == this;
	}
public:
	static Expression *get(unsigned long v, ImportOrigin *origin)
	{
		ImportExpression *work = new (allocator.alloc()) ImportExpression();
		work->v = v;
		work->origin = origin;
		return intern(work);
	}
	void visit(HeapVisitor &hv) const {hv(origin);}
};

class LoadExpression : public Expression {
	static VexAllocTypeWrapper<LoadExpression> allocator;
	Expression *val;
	Expression *addr;
	ReplayTimestamp when;
protected:
	char *mkName() const { return my_asprintf("(load@%lx %s -> %s)", when.val, addr->name(), val->name()); }
	unsigned _hash() const { return val->hash() ^ (addr->hash() * 3) ^ (when.val * 5); }
	bool _isEqual(const Expression *other) const {
		const LoadExpression *le = dynamic_cast<const LoadExpression *>(other);
		if (le &&
		    le->when == when &&
		    le->val->isEqual(val) &&
		    le->addr->isEqual(addr))
			return true;
		else
			return false;
	}
public:
	static Expression *get(ReplayTimestamp when, Expression *val, Expression *addr)
	{
		LoadExpression *work = new (allocator.alloc()) LoadExpression();
		work->val = val;
		work->addr = addr;
		work->when = when;
		return intern(work);
	}
	ReplayTimestamp timestamp() const { return when; }
	void visit(HeapVisitor &hv) const {hv(addr); hv(val);}
};

#define mk_binop_class(nme)						\
	class nme : public Expression {					\
	public:								\
		Expression *l, *r;					\
	protected:							\
		static VexAllocTypeWrapper<nme, visit_object<nme>,	\
					   destruct_object<nme> > allocator; \
	protected:							\
	        char *mkName() const                                    \
		{							\
			return my_asprintf("(%s " #nme "  %s)",		\
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
	public:								\
	        static Expression *get(Expression *_l, Expression *_r);	\
		void visit(HeapVisitor &hv) const			\
		{							\
			hv(l);						\
			hv(r);						\
		}							\
                ReplayTimestamp timestamp() const			\
		{							\
		        return min<ReplayTimestamp>(l->timestamp(),	\
						    r->timestamp());	\
		}							\
	}

mk_binop_class(lshift);
mk_binop_class(rshift);
mk_binop_class(bitwiseand);
mk_binop_class(bitwiseor);
mk_binop_class(bitwisexor);
mk_binop_class(plus);
mk_binop_class(subtract);
mk_binop_class(times);
mk_binop_class(divide);
mk_binop_class(modulo);
mk_binop_class(greaterthanequals);
mk_binop_class(greaterthan);
mk_binop_class(lessthanequals);
mk_binop_class(lessthan);
mk_binop_class(equals);
mk_binop_class(notequals);
mk_binop_class(logicalor);
mk_binop_class(logicaland);

#define mk_unop_class(nme)						\
	class nme : public Expression {					\
		Expression *l;						\
		static VexAllocTypeWrapper<nme, visit_object<nme>,	\
					   destruct_object<nme> > allocator; \
	protected:							\
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
	public:								\
	        static Expression* get(Expression *_l);			\
		void visit(HeapVisitor &hv) const			\
		{							\
			hv(l);						\
		}							\
                ReplayTimestamp timestamp() const			\
		{							\
		        return l->timestamp();				\
		}							\
	}

mk_unop_class(logicalnot);
mk_unop_class(bitwisenot);
mk_unop_class(unaryminus);

class ternarycondition : public Expression {
	Expression *cond, *t, *f;
	static VexAllocTypeWrapper<ternarycondition,
				   visit_object<ternarycondition>,
				   destruct_object<ternarycondition> > allocator;
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
public:
	static Expression *get(Expression *_cond, Expression *_t, Expression *_f);
	void visit(HeapVisitor &hv) const
	{
		hv(cond);
		hv(t);
		hv(f);
	}
	ReplayTimestamp timestamp() const					
	{								
		return min<ReplayTimestamp>(cond->timestamp(),
					    min<ReplayTimestamp>(t->timestamp(),
								 f->timestamp()));
	}								
};

struct abstract_interpret_value {
	mutable char *_name;
	unsigned long v;
	Expression *origin;
	abstract_interpret_value(unsigned long _v, Expression *_origin) : _name(NULL), v(_v), origin(_origin) {assert(origin);}
	abstract_interpret_value() : _name(NULL), v(0), origin(NULL) {}
	template <typename ait> static abstract_interpret_value import(ait x,
								       ImportOrigin *origin);
	const char *name() const {
		if (!_name)
			_name = vex_asprintf("{%lx:%s}", v, origin->name());
		return _name;		
	}
};

static inline void visit_aiv(const abstract_interpret_value &aiv, HeapVisitor &hv)
{
	hv(aiv.origin);
	hv(aiv._name);
}

static inline const char *name_aiv(const abstract_interpret_value &aiv)
{
	return aiv.name();
}

template <typename ait> static inline ait mkConst(unsigned long x);

template <>
unsigned long mkConst(unsigned long x)
{
	return x;
}

template <>
abstract_interpret_value mkConst(unsigned long x)
{
	return abstract_interpret_value(x, ConstExpression::get(x));
}

static inline unsigned long force(abstract_interpret_value aiv)
{
	return aiv.v;
}

static inline unsigned long force(unsigned long x)
{
	return x;
}

#define OP(x, name)								\
	static inline abstract_interpret_value operator x(const abstract_interpret_value &aiv, \
							  const abstract_interpret_value &cnt) \
	{								\
		abstract_interpret_value res;				\
		res.v = aiv.v x cnt.v;					\
		res.origin = name::get(aiv.origin, cnt.origin);		\
		return res;						\
	}

OP(<<, lshift)
OP(>>, rshift)
OP(&, bitwiseand)
OP(|, bitwiseor)
OP(^, bitwisexor)
OP(+, plus)
OP(*, times)
OP(/, divide)
OP(%, modulo)
OP(-, subtract)
OP(>=, greaterthanequals)
OP(<, lessthan)
OP(<=, lessthanequals)
OP(==, equals)
OP(!=, notequals)
OP(||, logicalor)
OP(&&, logicaland)
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
class MemoryChunk<struct abstract_interpret_value> {
public:
	static const unsigned long size = MEMORY_CHUNK_SIZE;
	static MemoryChunk<abstract_interpret_value> *allocate();

	void write(unsigned offset, const abstract_interpret_value *source, unsigned nr_bytes);
	void read(unsigned offset, abstract_interpret_value *dest, unsigned nr_bytes) const;

	MemoryChunk<abstract_interpret_value> *dupeSelf() const;

	const MemoryChunk<unsigned long> *underlying;
	struct MCLookasideEntry {
		MCLookasideEntry *next;
		unsigned offset;
		unsigned size;
		abstract_interpret_value content[0];
	};
	MCLookasideEntry *headLookaside;

	static const VexAllocTypeWrapper<MemoryChunk<abstract_interpret_value> > allocator;
	static const VexAllocType mcl_allocator;

	void visit(HeapVisitor &hv) const
	{
		hv(underlying);
		hv(headLookaside);
	}
	void destruct() {}
};


#endif /* !SLI_H__ */
