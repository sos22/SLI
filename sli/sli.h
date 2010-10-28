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
		if (!this)
			return NULL;
		if (!_name)
			_name = mkName();
		return _name;
	}
	~Named() { clearName(); }
};

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
		return my_asprintf("{%s, %s}",
				   name_aiv(lo), name_aiv(hi));
	}
public:
	unsigned long lo;
	unsigned long hi;
	expression_result() : Named() {}
};

class RegisterSet {
public:
	static const unsigned NR_REGS = sizeof(VexGuestAMD64State) / 8;
#define REGISTER_IDX(x) (offsetof(VexGuestAMD64State, guest_ ## x) / 8)
	unsigned long registers[NR_REGS];
	RegisterSet(const VexGuestAMD64State &r);
	RegisterSet() {};
	unsigned long &get_reg(unsigned idx) { assert(idx < NR_REGS); return registers[idx]; }
	void set_reg(unsigned idx, unsigned long val)
	{
		assert(idx < NR_REGS);
		registers[idx] = val;
	}
	unsigned long &rip() { return get_reg(REGISTER_IDX(RIP)); }
	unsigned long &rsp() { return get_reg(REGISTER_IDX(RSP)); }

	void pretty_print() const {
		for (unsigned x = 0; x < NR_REGS; x++)
			printf("\treg%d: %s\n", x, name_aiv(registers[x]));
	}
};

class expression_result_array {
public:
	std::vector<expression_result > content;
	void setSize(unsigned new_size) {
		content.clear();
		content.resize(new_size);
	}
	expression_result &operator[](unsigned idx) { return content[idx]; }
	expression_result_array() :
		content()
	{
	}

	void pretty_print() const {
		for (unsigned x = 0; x < content.size(); x++)
			printf("\tt%d: %s\n", x, content[x].name());
	}
};

class MachineState;
class AddressSpace;
class PMap;
class SignalHandlers;
class ThreadEvent;
class LogWriter;

class LogRecordFootstep;
class LogRecordInitialRegisters;
class LogRecordVexThreadState;

class LogReaderPtr {
public:
	unsigned char cls_data[32];
	LogReaderPtr() { memset(cls_data, 0, sizeof(cls_data)); }
};

class Thread : public GarbageCollected<Thread> {
	static void translateNextBlock(VexPtr<Thread > &ths,
				       VexPtr<AddressSpace > &addrSpace,
				       VexPtr<MachineState> &ms,
				       const LogReaderPtr &ptr,
				       unsigned long rip,
				       GarbageCollectionToken t);
	struct expression_result eval_expression(IRExpr *expr);
	ThreadEvent *do_dirty_call(IRDirty *details, MachineState *ms);
	ThreadEvent *do_load(IRTemp tmp,
			     unsigned long addr,
			     unsigned size,
			     MachineState *ms);
	expression_result do_ccall_calculate_condition(struct expression_result *args);
	expression_result do_ccall_calculate_rflags_c(expression_result *args);
	expression_result do_ccall_generic(IRCallee *cee, struct expression_result *rargs);
	expression_result do_ccall(IRCallee *cee, IRExpr **args);

	void amd64g_dirtyhelper_loadF80le(MachineState *, IRTemp tmp, unsigned long addr);
	void amd64g_dirtyhelper_storeF80le(MachineState *, unsigned long addr, unsigned long _f64);

	void redirectGuest(unsigned long rip);

public:
	std::vector<unsigned long> currentCallStack;
	bool inInfrastructure;

	unsigned decode_counter;
	ThreadId tid;
	unsigned pid;
	RegisterSet regs;
	unsigned long clear_child_tid;
	unsigned long robust_list;
	unsigned long set_child_tid;
	unsigned long futex_block_address;
	bool exitted;
	bool crashed;
	bool idle;

	bool cannot_make_progress;
	bool blocked;

	IRSB *currentIRSB;
	unsigned long currentIRSBRip;
	expression_result_array temporaries;
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
	ring_buffer<control_log_entry, CONTROL_LOG_DEPTH> controlLog;
	struct snapshot_log_entry {
		MachineState *ms;
		LogReaderPtr ptr;
		snapshot_log_entry(MachineState *_ms,
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

	unsigned long currentControlCondition;

	bool runnable() const { return !exitted && !crashed && !cannot_make_progress; }
	void futexBlock(unsigned long fba) { blocked = true; futex_block_address = fba; }
	void futexUnblock() { blocked = false; }

	void pretty_print() const;
private:
	bool allowRipMismatch;
public:
	static ThreadEvent *runToEvent(VexPtr<Thread > &ths,
						      VexPtr<MachineState > &ms,
						      const LogReaderPtr &ptr,
						      GarbageCollectionToken t);

	static Thread *initialThread(const LogRecordInitialRegisters &initRegs);
	Thread *fork(unsigned newPid);
	Thread *dupeSelf() const;
	void dumpSnapshot(LogWriter *lw);

	static void imposeState(VexPtr<Thread > &thr,
				VexPtr<LogRecordVexThreadState> &rec,
				VexPtr<AddressSpace > &as,
				VexPtr<MachineState > &ms,
				const LogReaderPtr &ptr,
				GarbageCollectionToken t);

	void visit(HeapVisitor &hv);

	void destruct() { temporaries.~expression_result_array(); }

	NAMED_CLASS
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
		static void visit(VAMapEntry *&ref, PMap *pmap, HeapVisitor &hv);
		VAMapEntry *promoteSmallest();
		VAMapEntry *dupeSelf() const;
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
	static void visit(VAMap *&ref, HeapVisitor &hv, PMap *pmap);
	void visit(HeapVisitor &hv);
};

#define MEMORY_CHUNK_SIZE 4096

class MemoryChunk : public GarbageCollected<MemoryChunk> {
public:
	static const unsigned long size = MEMORY_CHUNK_SIZE;
	static MemoryChunk *allocate();

	void write(unsigned offset, const unsigned long *source, unsigned nr_bytes,
		   unsigned long sa);
	void read(unsigned offset, unsigned long *dest, unsigned nr_bytes,
		  unsigned long *sa = NULL) const;

	MemoryChunk *dupeSelf() const;

	PhysicalAddress base;
	unsigned serial;
	unsigned long checksum;
	void visit(HeapVisitor &hv) {}
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
class PMapEntry : public GarbageCollected<PMapEntry> {
public:
	PhysicalAddress pa;
	MemoryChunk *mc;
	PMapEntry *next;
	PMapEntry **pprev;
	bool readonly;
	static PMapEntry *alloc(PhysicalAddress pa, MemoryChunk *mc, bool readonly);
	void visit(HeapVisitor &hv) { hv(mc); }
	void destruct() {
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

	void destruct() {}

	NAMED_CLASS
};

class LogRecord : public Named, public GarbageCollected<LogRecord> {
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

class LogRecordInitialSighandlers : public LogRecord {
	friend class SignalHandlers;
	struct sigaction handlers[64];
protected:
	virtual char *mkName() const {
		return strdup("initial_sighandlers");
	}
public:
	LogRecordInitialSighandlers(ThreadId tid,
				    const struct sigaction *sa)
		: LogRecord(tid)
	{
		memcpy(handlers, sa, sizeof(*sa) * 64);
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
};

class SignalHandlers {
public:
	struct sigaction handlers[64];
	SignalHandlers(const LogRecordInitialSighandlers &init) {
		memcpy(handlers, init.handlers, sizeof(init.handlers));
	}
	SignalHandlers() { memset(handlers, 0, sizeof(handlers)); }
	void dumpSnapshot(LogWriter *lw) const;
};

class LogReader : public GarbageCollected<LogReader> {
public:
	virtual LogRecord *read(LogReaderPtr startPtr, LogReaderPtr *outPtr) const = 0;
	virtual ~LogReader() {}
	NAMED_CLASS
};

class LogFile : public LogReader {
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
	virtual LogRecord *read(LogReaderPtr startPtr, LogReaderPtr *outPtr) const;
	~LogFile();
	static LogFile *open(const char *path, LogReaderPtr *initial_ptr);
	LogFile *truncate(LogReaderPtr eof);
	void visit(HeapVisitor &hv){}
	void destruct() { this->~LogFile(); }
	NAMED_CLASS
};

class MachineState : public GarbageCollected<MachineState > {
public:
	LibvexVector<Thread > *threads;

	bool exitted;
	unsigned long exit_status;
	ThreadId nextTid;

private:
	static MachineState *initialMachineState(AddressSpace *as,
						 const LogRecordInitialSighandlers &handlers);
public:
	AddressSpace *addressSpace;
	SignalHandlers signalHandlers;
	unsigned long nrEvents;
	static MachineState *initialMachineState(VexPtr<LogReader> &lf,
						 LogReaderPtr startPtr,
						 LogReaderPtr *endPtr,
						 GarbageCollectionToken t);

	void registerThread(Thread *t) {
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
	Thread *findThread(ThreadId id, bool allow_failure = false) {
		unsigned x;
		for (x = 0; x < threads->size(); x++)
			if (threads->index(x)->tid == id)
				return threads->index(x);
		assert(allow_failure);
		return NULL;
	}
	const Thread *findThread(ThreadId id) const {
		unsigned x;
		for (x = 0; x < threads->size(); x++)
			if (threads->index(x)->tid == id)
				return threads->index(x);
		return NULL;
	}
	void exitGroup(unsigned long result) {
		exitted = true;
		exit_status = result;
	}
	bool crashed() const;
	
	unsigned futexWake(unsigned long key, bool do_it) {
		unsigned cntr = 0;
		for (unsigned x = 0; x < threads->size(); x++)
			if (threads->index(x)->blocked &&
			    threads->index(x)->futex_block_address == key) {
				cntr++;
				if (do_it)
					threads->index(x)->futexUnblock();
			}
		return cntr;
	}
	MachineState *dupeSelf() const;

	void dumpSnapshot(LogWriter *lw) const;

	void visit(HeapVisitor &hv);

	void destruct() {}

	NAMED_CLASS
};

enum InterpretResult {
	InterpretResultContinue = 0xf001,
	InterpretResultExit,
	InterpretResultCrash,
	InterpretResultIncomplete,
	InterpretResultTimedOut
};

class EventRecorder : public GarbageCollected<EventRecorder> {
protected:
	virtual ~EventRecorder() {}
	virtual void record(Thread *thr, ThreadEvent *evt) = 0;
public:
	virtual void record(Thread *thr, ThreadEvent *evt,
			    MachineState *ms)
	{
		record(thr, evt);
	}
	void destruct() { this->~EventRecorder(); }
	NAMED_CLASS
};

class Interpreter {
	void replayFootstep(const LogRecordFootstep &lrf,
			    const LogReader *lr,
			    LogReaderPtr startOffset,
			    LogReaderPtr *endOffset);

public:
	VexPtr<MachineState > currentState;
	Interpreter(MachineState *rootMachine) : currentState(rootMachine)
	{
	}
	void replayLogfile(VexPtr<LogReader > &lf,
			   LogReaderPtr startingPoint,
			   GarbageCollectionToken,
			   LogReaderPtr *endingPoint,
			   VexPtr<LogWriter > &log,
			   VexPtr<EventRecorder> &er);
	void replayLogfile(VexPtr<LogReader > &lf,
			   LogReaderPtr startingPoint,
			   GarbageCollectionToken tok)
	{
		replayLogfile(lf, startingPoint, tok, NULL);
	}
	void replayLogfile(VexPtr<LogReader > &lf,
			   LogReaderPtr startingPoint,
			   GarbageCollectionToken tok,
			   LogReaderPtr *endingPoint)
	{
		VexPtr<LogWriter > l(NULL);
		replayLogfile(lf, startingPoint, tok, endingPoint, l);
	}
	void replayLogfile(VexPtr<LogReader > &lf,
			   LogReaderPtr startingPoint,
			   GarbageCollectionToken tok,
			   LogReaderPtr *endingPoint,
			   VexPtr<LogWriter > &log)
	{
		VexPtr<EventRecorder> er(NULL);
		replayLogfile(lf, startingPoint, tok, endingPoint, log, er);
	}
};

class LogWriter : public GarbageCollected<LogWriter> {
public:
	virtual void append(LogRecord *lr) = 0;
	virtual ~LogWriter() {}
	InterpretResult recordEvent(Thread *thr, MachineState *ms, ThreadEvent *evt);

	NAMED_CLASS
};

class LogFileWriter : public LogWriter {
	int fd;
public:
	void append(LogRecord *lr);
	static LogFileWriter *open(const char *fname);
	~LogFileWriter();
	void visit(HeapVisitor &hv) {}
	void destruct() { this->~LogFileWriter(); }
};

class ThreadEvent : public Named, public GarbageCollected<ThreadEvent > {
protected:
	ThreadEvent(ThreadId _tid) : tid(_tid) {}
public:
	ThreadId tid;
	/* Replay the event using information in the log record */
	virtual ThreadEvent *replay(LogRecord *lr, MachineState **ms,
					 bool &consumedRecord, LogReaderPtr ptr) = 0;
	/* Try to ``replay'' the event without reference to a pre-existing logfile */
	virtual InterpretResult fake(MachineState *ms, LogRecord **lr = NULL) = 0;
	/* Use the logfile if it matches, and otherwise fake it.  This
	   can fast-forward through the log e.g. to find a matching
	   syscall. */
	virtual ThreadEvent *fuzzyReplay(VexPtr<MachineState > &ms,
					      VexPtr<LogReader> &lf,
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

	virtual void visit(HeapVisitor &hv){}
	virtual void destruct() {}

	NAMED_CLASS
};

class RdtscEvent : public ThreadEvent {
	IRTemp tmp;
	RdtscEvent(ThreadId tid, IRTemp _tmp) : ThreadEvent(tid), tmp(_tmp) {};
protected:
	virtual char *mkName() const { return my_asprintf("rdtsc(%d)", tmp); }
public:
	ThreadEvent *replay(LogRecord *lr, MachineState **ms,
				 bool &consumedRecord, LogReaderPtr);
	InterpretResult fake(MachineState *ms, LogRecord **lr = NULL);
	ThreadEvent *fuzzyReplay(VexPtr<MachineState > &ms,
				      VexPtr<LogReader > &lf,
				      LogReaderPtr startPtr,
				      LogReaderPtr *endPtr,
				      GarbageCollectionToken);
	static ThreadEvent *get(ThreadId tid, IRTemp temp)
	{ return new RdtscEvent(tid, temp); }
	NAMED_CLASS
};

class LoadEvent : public ThreadEvent {
	IRTemp tmp;
public:
	unsigned long addr;
private:
	unsigned size;
	LoadEvent(ThreadId _tid, IRTemp _tmp, unsigned long _addr, unsigned _size) :
		ThreadEvent(_tid),
		tmp(_tmp),
		addr(_addr),
		size(_size)
	{
	}
protected:
	virtual char *mkName() const { return my_asprintf("load(%s, %d, %d)", name_aiv(addr), tmp, size); }
public:
	ThreadEvent *replay(LogRecord *lr, MachineState **ms,
				 bool &consumedRecord, LogReaderPtr);
	InterpretResult fake(MachineState *ms, LogRecord **lr = NULL);
	static ThreadEvent *get(ThreadId _tid, IRTemp _tmp, unsigned long _addr, unsigned _size)
	{
		return new LoadEvent(_tid, _tmp, _addr, _size);
	}
	NAMED_CLASS
};

class StoreEvent : public ThreadEvent {
public:
	unsigned long addr;
	unsigned size;
	expression_result data;
private:
	StoreEvent(ThreadId tid, unsigned long addr, unsigned size, expression_result data);
protected:
	virtual char *mkName() const { return my_asprintf("store(%d, %s, %s)", size, name_aiv(addr), data.name()); }
public:
	ThreadEvent *replay(LogRecord *lr, MachineState **ms,
				 bool &consumedRecord, LogReaderPtr);
	InterpretResult fake(MachineState *ms, LogRecord **lr = NULL);
	static ThreadEvent *get(ThreadId tid, unsigned long _addr, unsigned _size, expression_result data)
	{
		return new StoreEvent(tid, _addr, _size, data);
	}

	void destruct() { data.~expression_result(); ThreadEvent::destruct(); }
	NAMED_CLASS
};

class InstructionEvent : public ThreadEvent {
public:
	unsigned long rip;
	unsigned long reg0;
	unsigned long reg1;
	unsigned long reg2;
	unsigned long reg3;
	unsigned long reg4;
	bool allowRipMismatch;
	InstructionEvent(ThreadId _tid, unsigned long _rip, unsigned long _reg0, unsigned long _reg1,
			 unsigned long _reg2, unsigned long _reg3, unsigned long _reg4, bool _allowRipMismatch) :
		ThreadEvent(_tid),
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
	ThreadEvent *replay(LogRecord *lr, MachineState **ms,
				 bool &consumedRecord, LogReaderPtr);
	InterpretResult fake(MachineState *ms, LogRecord **lr = NULL);
	static InstructionEvent *get(ThreadId _tid, unsigned long _rip, unsigned long _reg0, unsigned long _reg1,
				     unsigned long _reg2, unsigned long _reg3, unsigned long _reg4, bool _allowRipMismatch)
	{
		return new InstructionEvent(_tid, _rip, _reg0, _reg1, _reg2, _reg3, _reg4,
					    _allowRipMismatch);
	}

	NAMED_CLASS
};

class CasEvent : public ThreadEvent {
	IRTemp dest;
	expression_result addr;
	expression_result data;
	expression_result expected;
	unsigned size;
	CasEvent(ThreadId _tid,
		 IRTemp _dest,
		 expression_result _addr,
		 expression_result _data,
		 expression_result _expected,
		 unsigned _size) :
		ThreadEvent(_tid),
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
	ThreadEvent *replay(LogRecord *lr, MachineState **ms,
				 bool &consumedRecord, LogReaderPtr);
	virtual InterpretResult fake(MachineState *ms, LogRecord **lr = NULL);
	virtual InterpretResult fake(MachineState *ms, LogRecord **lr = NULL,
				     LogRecord **lr2 = NULL);
	ThreadEvent *replay(LogRecord *lr, MachineState *ms,
				 const LogReader *lf, LogReaderPtr ptr,
				 LogReaderPtr *outPtr, LogWriter *lw);
	ThreadEvent *fuzzyReplay(VexPtr<MachineState > &ms,
				      VexPtr<LogReader > &lf,
				      LogReaderPtr startPtr,
				      LogReaderPtr *endPtr,
				      GarbageCollectionToken);

	static ThreadEvent *get(ThreadId _tid,
				IRTemp _dest,
				expression_result _addr,
				expression_result _data,
				expression_result _expected,
				unsigned _size)
	{
		return new CasEvent(_tid, _dest, _addr, _data, _expected, _size);
	}

	void destruct()
	{
		addr.~expression_result();
		data.~expression_result();
		expected.~expression_result();
		ThreadEvent::destruct();
	}
	NAMED_CLASS
};

class SyscallEvent : public ThreadEvent {
protected:
	virtual char *mkName() const {
		return my_asprintf("syscall");
	}
	SyscallEvent(ThreadId _tid) : ThreadEvent(_tid) {}
public:
	ThreadEvent *replay(LogRecord *lr, MachineState **ms,
				 bool &consumedRecord, LogReaderPtr ptr);
	InterpretResult fake(MachineState *ms, LogRecord **lr = NULL);
	ThreadEvent *fuzzyReplay(VexPtr<MachineState > &ms,
				      VexPtr<LogReader > &lf,
				      LogReaderPtr startPtr,
				      LogReaderPtr *endPtr,
				      GarbageCollectionToken);
	static ThreadEvent *get(ThreadId _tid)
	{ return new SyscallEvent(_tid); }
	NAMED_CLASS
};

class DetectedErrorEvent : public ThreadEvent {
protected:
	char *mkName() const { return my_asprintf("Detected error at %lx\n", rip); }
public:
	unsigned long rip;
	DetectedErrorEvent(ThreadId _tid, unsigned long _rip)
		: ThreadEvent(_tid), rip(_rip)
	{
	}
	/* Okay, we've crashed.  Consume to the end of the log and
	 * then stop. */
	ThreadEvent *replay(LogRecord *,
				 MachineState **ms,
				 bool &consumed,
				 LogReaderPtr)
	{
		Thread *thr = (*ms)->findThread(this->tid);
		thr->crashed = true;
		consumed = true;
		return this;
	}
	InterpretResult fake(MachineState *ms, LogRecord **lr = NULL)
	{
		Thread *thr = ms->findThread(this->tid);
		thr->crashed = true;
		return InterpretResultCrash;
	}
};

class SignalEvent : public ThreadEvent {
public:
	unsigned signr;
	unsigned long virtaddr;
	SignalEvent(ThreadId _tid, unsigned _signr, unsigned long _va) :
		ThreadEvent(_tid),
		signr(_signr),
		virtaddr(_va)
	{
	}
protected:
	virtual char *mkName() const {
		return my_asprintf("signal(nr = %d)", signr);
	}
public:
	ThreadEvent *replay(LogRecord *lr, MachineState **ms,
				 bool &consumedRecord, LogReaderPtr);
	InterpretResult fake(MachineState *ms, LogRecord **lr = NULL);
	static ThreadEvent *get(ThreadId _tid, unsigned _signr, unsigned long _virtaddr)
	{
		return new SignalEvent(_tid, _signr, _virtaddr);
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

class LogRecordLoad : public LogRecord {
	friend class LoadEvent;
	friend class CasEvent;
	unsigned size;
public:
	unsigned long ptr;
private:
	expression_result value;
protected:
	char *mkName() const {
		return my_asprintf("load(%x)", size);
	}
public:
	LogRecordLoad(ThreadId _tid,
		      unsigned _size,
		      unsigned long _ptr,
		      expression_result _value) :
		LogRecord(_tid),
		size(_size),
		ptr(_ptr),
		value(_value)
	{
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
};

class LogRecordStore : public LogRecord {
	friend class StoreEvent;
	friend class CasEvent;
	friend class MemoryAccessStore;
	unsigned size;
public:
	unsigned long ptr;
private:
	expression_result value;
protected:
	virtual char *mkName() const {
		return my_asprintf("store(%x,%s)", size, name_aiv(ptr));
	}
public:
	LogRecordStore(ThreadId _tid,
		       unsigned _size,
		       unsigned long _ptr,
		       expression_result _value) :
		LogRecord(_tid),
		size(_size),
		ptr(_ptr),
		value(_value)
	{
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
};

class LogRecordFootstep : public LogRecord {
protected:
	virtual char *mkName() const {
		return my_asprintf("footstep()");
	}
public:
	unsigned long rip;
	unsigned long reg0;
	unsigned long reg1;
	unsigned long reg2;
	unsigned long reg3;
	unsigned long reg4;
	LogRecordFootstep(ThreadId _tid,
			  unsigned long _rip,
			  unsigned long _reg0,
			  unsigned long _reg1,
			  unsigned long _reg2,
			  unsigned long _reg3,
			  unsigned long _reg4) :
		LogRecord(_tid),
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
};

class LogRecordSyscall : public LogRecord {
protected:
	virtual char *mkName() const {
		return my_asprintf("syscall()");
	}
public:
	unsigned long sysnr, res, arg1, arg2, arg3;
	LogRecordSyscall(ThreadId _tid,
			 unsigned long _sysnr,
			 unsigned long _res,
			 unsigned long _arg1,
			 unsigned long _arg2,
			 unsigned long _arg3) :
		LogRecord(_tid),
		sysnr(_sysnr),
		res(_res),
		arg1(_arg1),
		arg2(_arg2),
		arg3(_arg3)
	{
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
};

class LogRecordMemory : public LogRecord {
protected:
	char *mkName() const {
		return my_asprintf("memory(%x)", size);
	}
	LogRecordMemory(const LogRecordMemory &); /* DNI */
	void operator=(const LogRecordMemory &); /* DNI */
public:
	unsigned size;
	unsigned long start;
	const unsigned long *contents;
	LogRecordMemory(ThreadId _tid,
			unsigned _size,
			unsigned long _start,
			const unsigned long *_contents) :
		LogRecord(_tid),
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
};

class LogRecordRdtsc : public LogRecord {
	friend class RdtscEvent;
	unsigned long tsc;
protected:
	char *mkName() const {
		return my_asprintf("rdtsc()");
	}
public:
	LogRecordRdtsc(ThreadId _tid,
		       unsigned long _tsc)
		: LogRecord(_tid),
		  tsc(_tsc)
	{
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
};

class LogRecordSignal : public LogRecord {
public:
	virtual char *mkName() const {
		return my_asprintf("signal(nr = %d)", signr);
	}
public:
	unsigned long rip;
	unsigned signr;
	unsigned long err;
	unsigned long virtaddr;
	LogRecordSignal(ThreadId _tid,
			unsigned long _rip,
			unsigned _signr,
			unsigned long _err,
			unsigned long _va) :
		LogRecord(_tid),
		rip(_rip),
		signr(_signr),
		err(_err),
		virtaddr(_va)
	{
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
};

class LogRecordAllocateMemory : public LogRecord {
	friend class AddressSpace;
	unsigned long start;
	unsigned long size;
	unsigned prot;
	unsigned flags;
protected:
	virtual char *mkName() const {
		return my_asprintf("allocate(prot = %x, flags = %x)",
				   prot, flags);
	}
public:
	LogRecordAllocateMemory(ThreadId _tid,
				unsigned long _start,
				unsigned long _size,
				unsigned _prot,
				unsigned _flags) :
		LogRecord(_tid),
		start(_start),
		size(_size),
		prot(_prot),
		flags(_flags)
	{
	}      
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
};

class LogRecordInitialRegisters : public LogRecord {
	friend class Thread;
	VexGuestAMD64State regs;
protected:
	virtual char *mkName() const {
		return strdup("initial_regs");
	}
public:
	LogRecordInitialRegisters(ThreadId tid,
				  const VexGuestAMD64State &r) :
		LogRecord(tid),
		regs(r)
	{
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
};

class LogRecordInitialBrk : public LogRecord {
protected:
	virtual char *mkName() const {
		return my_asprintf("initbrk()");
	}
public:
	unsigned long brk;
	LogRecordInitialBrk(ThreadId tid,
			    unsigned long _brk) :
		LogRecord(tid),
		brk(_brk)
	{
	}
	void *marshal(unsigned *size) const;
	unsigned marshal_size() const;
};

class LogRecordVexThreadState : public LogRecord {
protected:
	virtual char *mkName() const {
		return strdup("vex state");
	}
public:
	unsigned long currentIRSBRip;
	expression_result_array tmp;
	unsigned statement_nr;
	LogRecordVexThreadState(ThreadId tid, unsigned long _currentIRSBRip,
				unsigned _statement_nr, expression_result_array _tmp);
	void *marshal(unsigned *sz) const;
	unsigned marshal_size() const;
};

class AddressSpace : public GarbageCollected<AddressSpace > {
public:
	unsigned long brkptr;
	unsigned long brkMapPtr;
	VAMap *vamap;
	PMap *pmap;

private:
	bool extendStack(unsigned long ptr, unsigned long rsp);
public:
	IRSB *getIRSBForAddress(unsigned long rip);

	void allocateMemory(unsigned long start, unsigned long size, VAMap::Protection prot,
			    VAMap::AllocFlags flags = VAMap::defaultFlags);
	void allocateMemory(const LogRecordAllocateMemory &rec)
	{
		allocateMemory(rec.start, rec.size, rec.prot, rec.flags);
	}
	void releaseMemory(unsigned long start, unsigned long size);
	void protectMemory(unsigned long start, unsigned long size, VAMap::Protection prot);
	void populateMemory(const LogRecordMemory &rec)
	{
		writeMemory(rec.start, rec.size, rec.contents, true, NULL);
	}
	void store(unsigned long start, unsigned size, const expression_result &val,
		   bool ignore_protection = false,
		   Thread *thr = NULL);
	void writeMemory(unsigned long start, unsigned size,
			 const unsigned long *contents, bool ignore_protection,
			 Thread *thr);
	bool copyToClient(unsigned long start, unsigned size, const void *source);
	bool copyFromClient(unsigned long start, unsigned size, void *dest);
	void writeLiteralMemory(unsigned long start, unsigned size, const unsigned char *content);
	expression_result load(unsigned long start, unsigned size,
			       bool ignore_protection = false,
			       Thread *thr = NULL);
	template <typename t> const t fetch(unsigned long addr,
					    Thread *thr);
	void readMemory(unsigned long start, unsigned size,
			unsigned long *contents, bool ignore_protection,
			Thread *thr,
			unsigned long *storeAddr = NULL);
	bool isAccessible(unsigned long start, unsigned size,
			  bool isWrite, Thread *thr);
	bool isWritable(unsigned long start, unsigned size,
			Thread *thr = NULL) {
		return isAccessible(start, size, true, thr);
	}
	bool isReadable(unsigned long start, unsigned size,
			Thread *thr = NULL) {
		return isAccessible(start, size, false, thr);
	}
	unsigned long setBrk(unsigned long newBrk);

	static AddressSpace *initialAddressSpace(unsigned long initialBrk);
	AddressSpace *dupeSelf() const;
	void visit(HeapVisitor &hv);

	void dumpBrkPtr(LogWriter *lw) const;
	void dumpSnapshot(LogWriter *lw) const;

	char *readString(unsigned long start, Thread *thr);

	void destruct() { this->~AddressSpace(); }

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

	void relocate(AddressSpace *target, size_t sz);

private:
	static const unsigned nr_trans_hash_slots = 2048;
	trans_hash_entry *trans_hash[nr_trans_hash_slots];
};

ThreadEvent * replay_syscall(const LogRecordSyscall *lrs,
			     Thread *thr,
			     MachineState *&mach,
			     LogReaderPtr ptr);

void process_memory_records(VexPtr<AddressSpace > &addrSpace,
			    VexPtr<LogReader > &lf,
			    LogReaderPtr startOffset,
			    LogReaderPtr *endOffset,
			    VexPtr<LogWriter> &lw,
			    GarbageCollectionToken tok);

void debugger_attach(void);

void init_sli(void);

void gdb_concrete(const MachineState *ms);
void gdb(void);
void dbg_break(const char *msg, ...);

/* force some functions to be included even when they're not needed,
   so that they're available for calling from the debugger. */
static void force_linkage() __attribute__((unused, used));
static void
force_linkage()
{
	gdb_concrete(NULL);
}

bool address_is_interesting(ThreadId tid, unsigned long addr);
unsigned long extract_call_follower(IRSB *irsb);

void check_fpu_control(void);

#endif /* !SLI_H__ */
