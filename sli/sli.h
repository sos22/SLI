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
	
template <typename underlying> class PointerKeeper {
	underlying *x;
public:
	~PointerKeeper() { delete x; }
	PointerKeeper(underlying *y) : x(y) {}
};

template <typename underlying> class PointerKeeperArr {
	underlying *x;
public:
	~PointerKeeperArr() { delete [] x; }
	PointerKeeperArr(underlying *y) : x(y) {}
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
	~Named() { free(_name); }
};

template <typename underlying>
void visit_object(const void *_ctxt, HeapVisitor &hv)
{
	const underlying *ctxt = (const underlying *)_ctxt;
	ctxt->visit(hv);
}

/* Does absolutely nothing, could have been NULL, except that C++'s
   template machinery can't cope with NULL function pointers as
   template arguments, damn them. */
void noop_destructor(void *_ctxt);

template <typename t, void (*visit)(const void *, HeapVisitor &) = visit_object<t>, void (*destruct)(void *) = noop_destructor>
class VexAllocTypeWrapper {
public:
	VexAllocType type;
	VexAllocTypeWrapper() {
		type.nbytes = sizeof(t);
		type.gc_visit = visit;
		type.destruct = destruct;
		type.name = "<wrapper type>";
	}
	t *alloc() {
		return (t *)__LibVEX_Alloc(&type);
	}
};


class ThreadId {
	unsigned tid;
public:
	ThreadId(unsigned _tid) : tid(_tid) {}
	bool operator==(const ThreadId &b) const { return b.tid == tid; }
	bool operator<(const ThreadId &b) const { return tid < b.tid; }
	ThreadId operator++() {
		tid++;
		return *this;
	}
	const unsigned _tid() const { return tid; }
};

template<typename abst_int_value>
struct expression_result {
	abst_int_value lo;
	abst_int_value hi;
	void visit(HeapVisitor &hv) const { }
};

template <typename underlying>
class RegisterSet {
public:
	static const unsigned NR_REGS = sizeof(VexGuestAMD64State) / 8;
#define REGISTER_IDX(x) (offsetof(VexGuestAMD64State, guest_ ## x) / 8)
	underlying registers[NR_REGS];
	RegisterSet(const VexGuestAMD64State &r);
	underlying get_reg(unsigned idx) const { assert(idx < NR_REGS); return registers[idx]; }
	void set_reg(unsigned idx, underlying val) { assert(idx < NR_REGS); registers[idx] = val; }
	underlying rip() const { return get_reg(REGISTER_IDX(RIP)); }
	underlying rsp() const { return get_reg(REGISTER_IDX(RSP)); }
};

class AddressSpace;

template <typename ait>
class expression_result_array {
public:
	struct expression_result<ait> *arr;
	unsigned nr_entries;
	void setSize(unsigned new_size) {
		arr = (struct expression_result<ait> *)LibVEX_Alloc_Bytes(sizeof(arr[0]) * new_size);
		memset(arr, 0, sizeof(arr[0]) * new_size);
		nr_entries = new_size;
	}
	expression_result<ait> &operator[](unsigned idx) { return arr[idx]; }
	void visit(HeapVisitor &hv) const {
		unsigned x;
		for (x = 0; x < nr_entries; x++)
			arr[x].visit(hv);
		hv(arr);
	}
	expression_result_array() :
		arr(NULL),
		nr_entries(0)
	{
	}
};

template <typename ait> class ThreadEvent;
template <typename ait> class LogRecordInitialRegisters;
template <typename ait> class LogWriter;
template <typename ait> class LogRecordVexThreadState;

template <typename abst_int_type>
class Thread {
	void translateNextBlock(AddressSpace *addrSpace);
	struct expression_result<abst_int_type> eval_expression(IRExpr *expr);
	ThreadEvent<abst_int_type> *do_dirty_call(IRDirty *details);
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
public:
	expression_result_array<abst_int_type> temporaries;
private:
	int currentIRSBOffset;

	static VexAllocTypeWrapper<Thread<abst_int_type> > allocator;

	/* DNI */
	Thread();
	~Thread();
public:
	ThreadEvent<abst_int_type> *runToEvent(AddressSpace *addrSpace);

	static Thread<abst_int_type> *initialThread(const LogRecordInitialRegisters<abst_int_type> &initRegs);
	Thread<abst_int_type> *fork(unsigned newPid);
	Thread<abst_int_type> *dupeSelf() const;
	void dumpSnapshot(LogWriter<abst_int_type> *lw) const;

	void imposeState(const LogRecordVexThreadState<abst_int_type> &rec,
			 AddressSpace *as);

	void visit(HeapVisitor &hv) const;
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
		void visit(class PMap *pmap, HeapVisitor &hv) const;
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

	/* Bit of a hack, but needed if we're going to keep the
	   various bits of physical address space live. */

	class PMap *pmap;
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

	static VAMap *empty(class PMap *pmap);
	VAMap *dupeSelf(class PMap *pmap) const;
	void visit(HeapVisitor &hv) const;

	void sanityCheck() const;
};

class MemoryChunk {
public:
	static const unsigned long size = 4096;
	static MemoryChunk *allocate();

	void write(unsigned offset, const void *source, unsigned nr_bytes);
	void read(unsigned offset, void *dest, unsigned nr_bytes) const;

	MemoryChunk *dupeSelf() const;
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
class PMap {
public:
	class PMapEntry {
	public:
		PhysicalAddress pa;
		MemoryChunk *mc;
		PMapEntry *next;
		PMapEntry **pprev;
		bool readonly;
		static PMapEntry *alloc(PhysicalAddress pa, MemoryChunk *mc, bool readonly);
	};
private:
	static const unsigned nrHashBuckets = 1024;
	static unsigned paHash(PhysicalAddress pa);
	PhysicalAddress nextPa;
	/* mutable because we do pull-to-front in the lookup methods.
	 * The denotation of the mapping is unchanged, but its
	 * physical structure is. */
	mutable PMapEntry *heads[nrHashBuckets];
	const PMap *parent;

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

	void visitPA(PhysicalAddress pa, HeapVisitor &hv) const;
	void visit(HeapVisitor &hv) const;
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
};

template <typename ait>
class SignalHandlers {
public:
	struct sigaction handlers[64];
	SignalHandlers(const LogRecordInitialSighandlers<ait> &init) {
		memcpy(handlers, init.handlers, sizeof(init.handlers));
	}
	void dumpSnapshot(LogWriter<ait> *lw) const;
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
private:
	bool exitted;
	abst_int_type exit_status;
	ThreadId nextTid;

	/* DNI */
	MachineState();
	~MachineState();
	static MachineState *initialMachineState(AddressSpace *as,
						 const LogRecordInitialSighandlers<abst_int_type> &handlers);
public:
	AddressSpace *addressSpace;
	SignalHandlers<abst_int_type> signalHandlers;
	static MachineState<abst_int_type> *initialMachineState(LogReader<abst_int_type> *lf,
								LogReaderPtr startPtr,
								LogReaderPtr *endPtr);
	
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
			   LogReaderPtr *endingPoint = NULL, LogWriter<abst_int_type> *log = NULL);
	InterpretResult getThreadMemoryTrace(ThreadId tid,
					     MemoryTrace<abst_int_type> **output,
					     unsigned max_events);
	void runToAccessLoggingEvents(ThreadId tid, unsigned nr_accesses,
				      LogWriter<abst_int_type> *output = NULL);
	void runToFailure(ThreadId tid, LogWriter<abst_int_type> *output,
			  unsigned max_events = 0);
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
public:
	/* Replay the event using information in the log record */
	virtual void replay(Thread<ait> *thr, LogRecord<ait> *lr, MachineState<ait> *ms) = 0;
	virtual InterpretResult fake(Thread<ait> *thr, MachineState<ait> *ms, LogRecord<ait> **lr = NULL) = 0;
	virtual ~ThreadEvent() {};
};

template <typename ait>
class RdtscEvent : public ThreadEvent<ait> {
	IRTemp tmp;
protected:
	virtual char *mkName() const { return my_asprintf("rdtsc(%d)", tmp); }
public:
	virtual void replay(Thread<ait> *thr, LogRecord<ait> *lr, MachineState<ait> *ms);
	virtual InterpretResult fake(Thread<ait> *thr, MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	RdtscEvent(IRTemp _tmp) : tmp(_tmp) {};
};

template <typename ait> class MemoryAccessLoad;
template <typename ait> class MemoryAccessStore;

template <typename ait>
class LoadEvent : public ThreadEvent<ait> {
	friend class MemoryAccessLoad<ait>;
	IRTemp tmp;
	ait addr;
	unsigned size;
protected:
	virtual char *mkName() const { return my_asprintf("load(%d, 0x%lx, %d)", tmp, addr, size); }
public:
	virtual void replay(Thread<ait> *thr, LogRecord<ait> *lr, MachineState<ait> *ms);
	virtual InterpretResult fake(Thread<ait> *thr, MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	LoadEvent(IRTemp _tmp, ait _addr, unsigned _size) :
		tmp(_tmp),
		addr(_addr),
		size(_size)
	{
	}
};

template <typename ait>
class StoreEvent : public ThreadEvent<ait> {
	friend class MemoryAccessStore<ait>;
	ait addr;
	unsigned size;
	void *data;
protected:
	virtual char *mkName() const { return my_asprintf("store(0x%lx, %d)", addr, size); }
public:
	virtual void replay(Thread<ait> *thr, LogRecord<ait> *lr, MachineState<ait> *ms);
	virtual InterpretResult fake(Thread<ait> *thr, MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	StoreEvent(ait addr, unsigned size, const void *data);
	virtual ~StoreEvent();
};

template <typename ait>
class InstructionEvent : public ThreadEvent<ait> {
	ait rip;
	ait reg0;
	ait reg1;
	ait reg2;
	ait reg3;
	ait reg4;
protected:
	virtual char *mkName() const {
		return my_asprintf("footstep(rip =%lx, regs = %lx, %lx, %lx, %lx, %lx",
				   rip, reg0, reg1, reg2, reg3, reg4);
	}
public:
	virtual void replay(Thread<ait> *thr, LogRecord<ait> *lr, MachineState<ait> *ms);
	virtual InterpretResult fake(Thread<ait> *thr, MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	InstructionEvent(ait _rip, ait _reg0, ait _reg1,
			 ait _reg2, ait _reg3, ait _reg4) :
		rip(_rip),
		reg0(_reg0),
		reg1(_reg1),
		reg2(_reg2),
		reg3(_reg3),
		reg4(_reg4)
	{
	}
};

template <typename ait>
class CasEvent : public ThreadEvent<ait> {
	IRTemp dest;
	expression_result<ait> addr;
	expression_result<ait> data;
	expression_result<ait> expected;
	unsigned size;
protected:
	virtual char *mkName() const {
		return my_asprintf("cas(dest %d, size %d, addr %lx:%lx, data %lx:%lx, expected %lx:%lx)",
				   dest, size, addr.lo, addr.hi, data.lo, data.hi,
				   expected.lo, expected.hi);
	}
public:
	virtual void replay(Thread<ait> *thr, LogRecord<ait> *lr, MachineState<ait> *ms);
	virtual InterpretResult fake(Thread<ait> *thr, MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	virtual InterpretResult fake(Thread<ait> *thr, MachineState<ait> *ms, LogRecord<ait> **lr = NULL,
				     LogRecord<ait> **lr2 = NULL);
	void replay(Thread<ait> *thr, LogRecord<ait> *lr, MachineState<ait> *ms,
		    const LogReader<ait> *lf, LogReaderPtr ptr,
		    LogReaderPtr *outPtr, LogWriter<ait> *lw);
	void record(Thread<ait> *thr, LogRecord<ait> **lr1, LogRecord<ait> **lr2);
	CasEvent(IRTemp _dest,
		 expression_result<ait> _addr,
		 expression_result<ait> _data,
		 expression_result<ait> _expected,
		 unsigned _size) :
		dest(_dest),
		addr(_addr),
		data(_data),
		expected(_expected),
		size(_size)
	{
	}
};

template <typename ait>
class SyscallEvent : public ThreadEvent<ait> {
protected:
	virtual char *mkName() const {
		return my_asprintf("syscall");
	}
public:
	virtual void replay(Thread<ait> *thr, LogRecord<ait> *lr, MachineState<ait> *ms);
	virtual InterpretResult fake(Thread<ait> *thr, MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
};

template <typename ait>
class SignalEvent : public ThreadEvent<ait> {
	unsigned signr;
	ait virtaddr;
protected:
	virtual char *mkName() const {
		return my_asprintf("signal(nr = %d, va = %lx)", signr,
				   virtaddr);
	}
public:
	virtual void replay(Thread<ait> *thr, LogRecord<ait> *lr, MachineState<ait> *ms);
	virtual InterpretResult fake(Thread<ait> *thr, MachineState<ait> *ms, LogRecord<ait> **lr = NULL);
	SignalEvent(unsigned _signr, ait _va) :
		signr(_signr),
		virtaddr(_va)
	{
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
	const void *buf;
protected:
	char *mkName() const {
		return my_asprintf("load(%lx,%x)", ptr, size);
	}
public:
	LogRecordLoad(ThreadId _tid,
		      unsigned _size,
		      ait _ptr,
		      const void *_buf) :
		LogRecord<ait>(_tid),
		size(_size),
		ptr(_ptr),
		buf(_buf)
	{
	}
	virtual ~LogRecordLoad() { free((void *)buf); }
	void *marshal(unsigned *size) const;
	LogRecord<ait> *dupe() const
	{
		void *b = malloc(size);
		memcpy(b, buf, size);
		return new LogRecordLoad<ait>(this->thread(), size, ptr, b);
	}
};

template <typename ait>
class MemoryAccessLoad : public MemoryAccess<ait> {
protected:
	virtual char *mkName() const {
		return my_asprintf("%d: Load(%lx:%lx)", this->tid._tid(), this->addr,
				   this->addr + this->size);
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
	const void *buf;
protected:
	virtual char *mkName() const {
		return my_asprintf("store(%lx,%x)", ptr, size);
	}
public:
	LogRecordStore(ThreadId _tid,
		       unsigned _size,
		       ait _ptr,
		       const void *_buf) :
		LogRecord<ait>(_tid),
		size(_size),
		ptr(_ptr),
		buf(_buf)
	{
	}
	virtual ~LogRecordStore() { free((void *)buf); }
	void *marshal(unsigned *size) const;
	LogRecord<ait> *dupe() const
	{
		void *b = malloc(size);
		memcpy(b, buf, size);
		return new LogRecordStore<ait>(this->thread(), size, ptr, b);
	}
};

template <typename ait>
class MemoryAccessStore : public MemoryAccess<ait> {
protected:
	virtual char *mkName() const {
		return my_asprintf("%d: Store(%lx:%lx)",
				   this->tid._tid(),
				   this->addr,
				   this->addr + this->size);
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
protected:
	virtual char *mkName() const {
		return my_asprintf("footstep(rip = %lx, regs = %lx, %lx, %lx, %lx, %lx)",
				   rip, reg0, reg1, reg2, reg3, reg4);
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
	LogRecord<ait> *dupe() const
	{
		return new LogRecordFootstep<ait>(this->thread(), rip, reg0, reg1, reg2, reg3, reg4);
	}
};

template <typename ait>
class LogRecordSyscall : public LogRecord<ait> {
protected:
	virtual char *mkName() const {
		return my_asprintf("syscall(nr = %lx, res = %lx, args = %lx, %lx, %lx)",
				   sysnr, res, arg1, arg2, arg3);
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
	LogRecord<ait> *dupe() const
	{
		return new LogRecordSyscall<ait>(this->thread(), sysnr, res, arg1, arg2, arg3);
	}
};

template <typename ait>
class LogRecordMemory : public LogRecord<ait> {
protected:
	char *mkName() const {
		return my_asprintf("memory(%lx,%x)", start, size);
	}
public:
	unsigned size;
	ait start;
	const void *contents;
	LogRecordMemory(ThreadId _tid,
			unsigned _size,
			ait _start,
			const void *_contents) :
		LogRecord<ait>(_tid),
		size(_size),
		start(_start),
		contents(_contents)
	{}
	virtual ~LogRecordMemory() { free((void *)contents); }
	void *marshal(unsigned *size) const;
	LogRecord<ait> *dupe() const
	{
		void *b = malloc(size);
		memcpy(b, contents, size);
		return new LogRecordMemory<ait>(this->thread(), size, start, b);
	}
};

template <typename ait>
class LogRecordRdtsc : public LogRecord<ait> {
	friend class RdtscEvent<ait>;
	ait tsc;
protected:
	char *mkName() const {
		return my_asprintf("rdtsc(%lx)", tsc);
	}
public:
	LogRecordRdtsc(ThreadId _tid,
		       ait _tsc)
		: LogRecord<ait>(_tid),
		  tsc(_tsc)
	{
	}
	void *marshal(unsigned *size) const;
	LogRecord<ait> *dupe() const
	{
		return new LogRecordRdtsc<ait>(this->thread(), tsc);
	}
};

template <typename ait>
class LogRecordSignal : public LogRecord<ait> {
public:
	virtual char *mkName() const {
		return my_asprintf("signal(nr = %d, rip = %lx, err = %lx, va = %lx)",
				   signr, rip, err, virtaddr);
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
	LogRecord<ait> *dupe() const
	{
		return new LogRecordSignal<ait>(this->thread(), rip, signr, err, virtaddr);
	}
};

template <typename ait>
class LogRecordAllocateMemory : public LogRecord<ait> {
	friend class AddressSpace;
	ait start;
	ait size;
	unsigned prot;
	unsigned flags;
protected:
	virtual char *mkName() const {
		return my_asprintf("allocate(start = %lx, size = %lx, prot = %x, flags = %x)",
				   start, size, prot, flags);
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
	LogRecord<ait> *dupe() const
	{
		return new LogRecordAllocateMemory<ait>(this->thread(), start, size, prot, flags);
	}
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
};

template <typename ait>
class LogRecordInitialBrk : public LogRecord<ait> {
protected:
	virtual char *mkName() const {
		return my_asprintf("initbrk(%lx)", brk);
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
	LogRecord<ait> *dupe() const
	{
		return new LogRecordInitialBrk(this->thread(), brk);
	}
};

template <typename ait>
class LogRecordVexThreadState : public LogRecord<ait> {
protected:
	virtual char *mkName() const {
		return strdup("vex state");
	}
	VexGcRoot root;
	LogRecordVexThreadState **root_data;
public:
	expression_result_array<ait> tmp;
	unsigned statement_nr;
	LogRecordVexThreadState(ThreadId tid, unsigned _statement_nr,
				expression_result_array<ait> _tmp);
	void *marshal(unsigned *sz) const;
	void visit(HeapVisitor &hv) const;
	LogRecord<ait> *dupe() const
	{
		return new LogRecordVexThreadState(this->thread(), statement_nr, tmp);
	}
};

class AddressSpace {
	unsigned long brkptr;
	unsigned long brkMapPtr;
	VAMap *vamap;
	PMap *pmap;

	bool extendStack(unsigned long ptr, unsigned long rsp);

public:
	void allocateMemory(unsigned long start, unsigned long size, VAMap::Protection prot,
			    VAMap::AllocFlags flags = VAMap::defaultFlags);
	void allocateMemory(const LogRecordAllocateMemory<unsigned long> &rec)
	{
		allocateMemory(rec.start, rec.size, rec.prot, rec.flags);
	}
	void releaseMemory(unsigned long start, unsigned long size);
	void protectMemory(unsigned long start, unsigned long size, VAMap::Protection prot);
	void populateMemory(const LogRecordMemory<unsigned long> &rec)
	{
		writeMemory(rec.start, rec.size, rec.contents, true);
	}
	void writeMemory(unsigned long start, unsigned size,
			 const void *contents, bool ignore_protection = false,
			 const Thread<unsigned long> *thr = NULL);
	void readMemory(unsigned long start, unsigned size,
			void *contents, bool ignore_protection = false,
			const Thread<unsigned long> *thr = NULL);
	bool isAccessible(unsigned long start, unsigned size,
			  bool isWrite, const Thread<unsigned long> *thr = NULL);
	bool isWritable(unsigned long start, unsigned size,
			const Thread<unsigned long> *thr = NULL) {
		return isAccessible(start, size, true, thr);
	}
	bool isReadable(unsigned long start, unsigned size,
			const Thread<unsigned long> *thr = NULL) {
		return isAccessible(start, size, false, thr);
	}
	unsigned long setBrk(unsigned long newBrk);

	static AddressSpace *initialAddressSpace(unsigned long initialBrk);
	AddressSpace *dupeSelf() const;
	void visit(HeapVisitor &hv) const;
	void sanityCheck() const;

	void dumpBrkPtr(LogWriter<unsigned long> *lw) const;
	void dumpSnapshot(LogWriter<unsigned long> *lw) const;
};

template<typename ait> void replay_syscall(const LogRecordSyscall<ait> *lrs,
					   Thread<ait> *thr,
					   MachineState<ait> *mach);

template<typename ait> void process_memory_records(AddressSpace *addrSpace,
						   const LogReader<ait> *lf,
						   LogReaderPtr startOffset,
						   LogReaderPtr *endOffset,
						   LogWriter<ait> *lw);

void debugger_attach(void);

void init_sli(void);

void gdb_machine_state(const MachineState<unsigned long> *ms);

#endif /* !SLI_H__ */
