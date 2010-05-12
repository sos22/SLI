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
	char *_name;
protected:
	virtual char *mkName(void) = 0;
public:
	Named() : _name(NULL) {}
	Named(const Named &b) {
		if (b._name)
			_name = strdup(b._name);
		else
			_name = NULL;
	}
	const char *name() {
		if (!_name)
			_name = mkName();
		return _name;
	}
	~Named() { free(_name); }
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
	const unsigned _tid() { return tid; }
};

class LogRecord : public Named {
	/* DNI */
	LogRecord(const LogRecord &);
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

class LogRecordFootstep : public LogRecord {
protected:
	virtual char *mkName() {
		return my_asprintf("footstep(rip = %lx, regs = %lx, %lx, %lx, %lx, %lx)",
				   rip, reg0, reg1, reg2, reg3, reg4);
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
	LogRecord *dupe() const
	{
		return new LogRecordFootstep(thread(), rip, reg0, reg1, reg2, reg3, reg4);
	}
};

class LogRecordSyscall : public LogRecord {
protected:
	virtual char *mkName() {
		return my_asprintf("syscall(nr = %lx, res = %lx, args = %lx, %lx, %lx)",
				   sysnr, res, arg1, arg2, arg3);
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
	LogRecord *dupe() const
	{
		return new LogRecordSyscall(thread(), sysnr, res, arg1, arg2, arg3);
	}
};

class LogRecordMemory : public LogRecord {
protected:
	virtual char *mkName() {
		return my_asprintf("memory(%lx,%x)", start, size);
	}
public:
	unsigned size;
	unsigned long start;
	const void *contents;
	LogRecordMemory(ThreadId _tid,
			unsigned _size,
			unsigned long _start,
			const void *_contents) :
		LogRecord(_tid),
		size(_size),
		start(_start),
		contents(_contents)
	{}
	virtual ~LogRecordMemory() { free((void *)contents); }
	void *marshal(unsigned *size) const;
	LogRecord *dupe() const
	{
		void *b = malloc(size);
		memcpy(b, contents, size);
		return new LogRecordMemory(thread(), size, start, b);
	}
};

class LogRecordRdtsc : public LogRecord {
	friend class RdtscEvent;
	unsigned long tsc;
protected:
	virtual char *mkName() {
		return my_asprintf("rdtsc(%lx)", tsc);
	}
public:
	LogRecordRdtsc(ThreadId _tid,
		       unsigned long _tsc)
		: LogRecord(_tid),
		  tsc(_tsc)
	{
	}
	void *marshal(unsigned *size) const;
	LogRecord *dupe() const
	{
		return new LogRecordRdtsc(thread(), tsc);
	}
};

class LogRecordLoad : public LogRecord {
	friend class LoadEvent;
	friend class CasEvent;
	unsigned size;
	unsigned long ptr;
	const void *buf;
protected:
	virtual char *mkName() {
		return my_asprintf("load(%lx,%x)", ptr, size);
	}
public:
	LogRecordLoad(ThreadId _tid,
		      unsigned _size,
		      unsigned long _ptr,
		      const void *_buf) :
		LogRecord(_tid),
		size(_size),
		ptr(_ptr),
		buf(_buf)
	{
	}
	virtual ~LogRecordLoad() { free((void *)buf); }
	void *marshal(unsigned *size) const;
	LogRecord *dupe() const
	{
		void *b = malloc(size);
		memcpy(b, buf, size);
		return new LogRecordLoad(thread(), size, ptr, b);
	}
};

class LogRecordStore : public LogRecord {
	friend class StoreEvent;
	friend class CasEvent;
	unsigned size;
	unsigned long ptr;
	const void *buf;
protected:
	virtual char *mkName() {
		return my_asprintf("store(%lx,%x)", ptr, size);
	}
public:
	LogRecordStore(ThreadId _tid,
		       unsigned _size,
		       unsigned long _ptr,
		       const void *_buf) :
		LogRecord(_tid),
		size(_size),
		ptr(_ptr),
		buf(_buf)
	{
	}
	virtual ~LogRecordStore() { free((void *)buf); }
	void *marshal(unsigned *size) const;
	LogRecord *dupe() const
	{
		void *b = malloc(size);
		memcpy(b, buf, size);
		return new LogRecordStore(thread(), size, ptr, b);
	}
};

class LogRecordSignal : public LogRecord {
public:
	virtual char *mkName() {
		return my_asprintf("signal(nr = %d, rip = %lx, err = %lx, va = %lx)",
				   signr, rip, err, virtaddr);
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
	LogRecord *dupe() const
	{
		return new LogRecordSignal(thread(), rip, signr, err, virtaddr);
	}
};

class LogRecordAllocateMemory : public LogRecord {
	friend class AddressSpace;
	unsigned long start;
	unsigned long size;
	unsigned prot;
	unsigned flags;
protected:
	virtual char *mkName() {
		return my_asprintf("allocate(start = %lx, size = %lx, prot = %x, flags = %x)",
				   start, size, prot, flags);
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
	LogRecord *dupe() const
	{
		return new LogRecordAllocateMemory(thread(), start, size, prot, flags);
	}
};

class LogRecordInitialRegisters : public LogRecord {
	friend class Thread;
	VexGuestAMD64State regs;
protected:
	virtual char *mkName() {
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
	LogRecord *dupe() const
	{
		return new LogRecordInitialRegisters(thread(), regs);
	}
};

class LogRecordInitialBrk : public LogRecord {
protected:
	virtual char *mkName() {
		return my_asprintf("initbrk(%lx)", brk);
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
	LogRecord *dupe() const
	{
		return new LogRecordInitialBrk(thread(), brk);
	}
};

class LogRecordInitialSighandlers : public LogRecord {
	friend class SignalHandlers;
	struct sigaction handlers[64];
protected:
	virtual char *mkName() {
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
	LogRecord *dupe() const
	{
		return new LogRecordInitialSighandlers(thread(), handlers);
	}
};

class LogReader {
public:
	class ptr {
	public:
		unsigned char cls_data[32];
	};
	virtual LogRecord *read(ptr startPtr, ptr *outPtr) const = 0;
	virtual ~LogReader() {}
};

enum InterpretResult {
	InterpretResultContinue = 0xf001,
	InterpretResultExit,
	InterpretResultCrash,
	InterpretResultIncomplete
};

class Thread;
class MachineState;
class ThreadEvent;

class LogWriter {
public:
	virtual void append(const LogRecord &lr) = 0;
	virtual ~LogWriter() {}
	InterpretResult recordEvent(Thread *thr, MachineState *ms, ThreadEvent *evt);
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
	_ptr unwrapPtr(ptr p) const {
		return *(_ptr *)p.cls_data;
	}
	_ptr forcedEof;
public:
	LogReader::ptr mkPtr(uint64_t off, unsigned record_nr) const {
		ptr w;
		_ptr *p = (_ptr *)w.cls_data;
		p->off = off;
		p->record_nr = record_nr;
		p->valid = true;
		return w;
	}
	virtual LogRecord *read(ptr startPtr, ptr *outPtr) const;
	~LogFile();
	static LogFile *open(const char *path, ptr *initial_ptr);
	LogFile *truncate(ptr eof);
};

class LogFileWriter : public LogWriter {
	int fd;
public:
	void append(const LogRecord &lr);
	static LogFileWriter *open(const char *fname);
	~LogFileWriter();
};

class ThreadEvent;
class Thread;
class MachineState;

class MemLog : public LogReader, public LogWriter {
	std::vector<LogRecord *> *content;
	unsigned offset;
	const MemLog *parent;

	unsigned unwrapPtr(ptr p) const {
		return *(unsigned *)p.cls_data;
	}
	ptr mkPtr(unsigned o) const {
		ptr p;
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
	MemLog *dupeSelf() const;
	LogRecord *read(ptr startPtr, ptr *outPtr) const;
	InterpretResult recordEvent(Thread *thr, MachineState *ms, ThreadEvent *evt);
	void dump() const;

	void append(const LogRecord &lr);

	/* Should only be called by GC destruct routine */
	void destruct();

	void visit(HeapVisitor &hv) const;
};

struct abstract_interpret_value {
	unsigned long v;
	abstract_interpret_value() : v(0) {}
};

struct expression_result {
	struct abstract_interpret_value lo;
	struct abstract_interpret_value hi;
	void visit(HeapVisitor &hv) const {}
};


class RegisterSet {
public:
	VexGuestAMD64State regs;
	RegisterSet(const VexGuestAMD64State &r) : regs(r) {}
	unsigned long rip() { return regs.guest_RIP; }
};

class Thread;
class MachineState;

class ThreadEvent : public Named {
public:
	/* Replay the event using information in the log record */
	virtual void replay(Thread *thr, LogRecord *lr, MachineState *ms) = 0;
	virtual InterpretResult fake(Thread *thr, MachineState *ms, LogRecord **lr = NULL) = 0;
	virtual ~ThreadEvent() {};
};

class RdtscEvent : public ThreadEvent {
	IRTemp tmp;
protected:
	virtual char *mkName() { return my_asprintf("rdtsc(%d)", tmp); }
public:
	virtual void replay(Thread *thr, LogRecord *lr, MachineState *ms);
	virtual InterpretResult fake(Thread *thr, MachineState *ms, LogRecord **lr = NULL);
	RdtscEvent(IRTemp _tmp) : tmp(_tmp) {};
};

class LoadEvent : public ThreadEvent {
	friend class MemoryAccessLoad;
	IRTemp tmp;
	unsigned long addr;
	unsigned size;
protected:
	virtual char *mkName() { return my_asprintf("load(%d, 0x%lx, %d)", tmp, addr, size); }
public:
	virtual void replay(Thread *thr, LogRecord *lr, MachineState *ms);
	virtual InterpretResult fake(Thread *thr, MachineState *ms, LogRecord **lr = NULL);
	LoadEvent(IRTemp _tmp, unsigned long _addr, unsigned _size) :
		tmp(_tmp),
		addr(_addr),
		size(_size)
	{
	}
};

class StoreEvent : public ThreadEvent {
	friend class MemoryAccessStore;
	unsigned long addr;
	unsigned size;
	void *data;
protected:
	virtual char *mkName() { return my_asprintf("store(0x%lx, %d)", addr, size); }
public:
	virtual void replay(Thread *thr, LogRecord *lr, MachineState *ms);
	virtual InterpretResult fake(Thread *thr, MachineState *ms, LogRecord **lr = NULL);
	StoreEvent(unsigned long addr, unsigned size, const void *data);
	virtual ~StoreEvent();
};

class InstructionEvent : public ThreadEvent {
	unsigned long rip;
	unsigned long reg0;
	unsigned long reg1;
	unsigned long reg2;
	unsigned long reg3;
	unsigned long reg4;
protected:
	virtual char *mkName() {
		return my_asprintf("footstep(rip =%lx, regs = %lx, %lx, %lx, %lx, %lx",
				   rip, reg0, reg1, reg2, reg3, reg4);
	}
public:
	virtual void replay(Thread *thr, LogRecord *lr, MachineState *ms);
	virtual InterpretResult fake(Thread *thr, MachineState *ms, LogRecord **lr = NULL);
	InstructionEvent(unsigned long _rip, unsigned long _reg0, unsigned long _reg1,
			 unsigned long _reg2, unsigned long _reg3, unsigned long _reg4) :
		rip(_rip),
		reg0(_reg0),
		reg1(_reg1),
		reg2(_reg2),
		reg3(_reg3),
		reg4(_reg4)
	{
	}
};

class CasEvent : public ThreadEvent {
	IRTemp dest;
	expression_result addr;
	expression_result data;
	expression_result expected;
	unsigned size;
protected:
	virtual char *mkName() {
		return my_asprintf("cas(dest %d, size %d, addr %lx:%lx, data %lx:%lx, expected %lx:%lx)",
				   dest, size, addr.lo.v, addr.hi.v, data.lo.v, data.hi.v,
				   expected.lo.v, expected.hi.v);
	}
public:
	virtual void replay(Thread *thr, LogRecord *lr, MachineState *ms);
	virtual InterpretResult fake(Thread *thr, MachineState *ms, LogRecord **lr = NULL);
	virtual InterpretResult fake(Thread *thr, MachineState *ms, LogRecord **lr = NULL,
				     LogRecord **lr2 = NULL);
	void replay(Thread *thr, LogRecord *lr, MachineState *ms,
		    const LogReader *lf, LogReader::ptr ptr,
		    LogReader::ptr *outPtr, LogWriter *lw);
	void record(Thread *thr, LogRecord **lr1, LogRecord **lr2);
	CasEvent(IRTemp _dest,
		 expression_result _addr,
		 expression_result _data,
		 expression_result _expected,
		 unsigned _size) :
		dest(_dest),
		addr(_addr),
		data(_data),
		expected(_expected),
		size(_size)
	{
	}
};

class SyscallEvent : public ThreadEvent {
protected:
	virtual char *mkName() {
		return my_asprintf("syscall");
	}
public:
	virtual void replay(Thread *thr, LogRecord *lr, MachineState *ms);
	virtual InterpretResult fake(Thread *thr, MachineState *ms, LogRecord **lr = NULL);
};

class SignalEvent : public ThreadEvent {
	unsigned signr;
	unsigned long virtaddr;
protected:
	virtual char *mkName() {
		return my_asprintf("signal(nr = %d, va = %lx)", signr,
				   virtaddr);
	}
public:
	virtual void replay(Thread *thr, LogRecord *lr, MachineState *ms);
	virtual InterpretResult fake(Thread *thr, MachineState *ms, LogRecord **lr = NULL);
	SignalEvent(unsigned _signr, unsigned long _va) :
		signr(_signr),
		virtaddr(_va)
	{
	}
};

class MemoryAccess : public Named {
public:
	unsigned long addr;
	unsigned size;
	MemoryAccess(unsigned long _addr, unsigned _size)
		: addr(_addr),
		  size(_size)
	{
	}
	virtual bool isLoad() = 0;
};

class MemoryAccessLoad: public MemoryAccess {
protected:
	virtual char *mkName() {
		return my_asprintf("Load(%lx:%lx)", addr, addr + size);
	}
public:
	MemoryAccessLoad(const class LoadEvent &evt)
		: MemoryAccess(evt.addr, evt.size)
	{
	}
	virtual bool isLoad() { return true; }
};

class MemoryAccessStore : public MemoryAccess {
protected:
	virtual char *mkName() {
		return my_asprintf("Store(%lx:%lx)", addr, addr + size);
	}
public:
	MemoryAccessStore(const class StoreEvent &evt)
		: MemoryAccess(evt.addr, evt.size)
	{
	}
	virtual bool isLoad() { return false; }
};

/* Essentially a thin wrapper around std::vector */
class MemoryTrace {
public:
	std::vector<MemoryAccess *> content;
	~MemoryTrace() {
		for (unsigned x; x < content.size(); x++)
			delete content[x];
	}
	size_t size() const { return content.size(); }
	MemoryAccess *&operator[](unsigned idx) { return content[idx]; }
	void push_back(MemoryAccess *x) { content.push_back(x); }
};

class MemTracePool {
	typedef std::map<ThreadId, MemoryTrace *> contentT;
	contentT content;
public:
	~MemTracePool() {
		while (!content.empty()) {
			contentT::iterator it = content.begin();
			delete it->second;
			content.erase(it);
		}
	}
	MemTracePool(MachineState *base_state);

	std::map<ThreadId, Maybe<unsigned> > *firstRacingAccessMap();
};

class AddressSpace;

class expression_result_array {
public:
	struct expression_result *arr;
	unsigned nr_entries;
	void setSize(unsigned new_size) {
		arr = (struct expression_result *)LibVEX_Alloc_Bytes(sizeof(arr[0]) * new_size);
		memset(arr, 0, sizeof(arr[0]) * new_size);
		nr_entries = new_size;
	}
	expression_result &operator[](unsigned idx) { return arr[idx]; }
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

class LogRecordVexThreadState : public LogRecord {
protected:
	virtual char *mkName() {
		return strdup("vex state");
	}
	VexGcRoot root;
	LogRecordVexThreadState **root_data;
public:
	expression_result_array tmp;
	unsigned statement_nr;
	LogRecordVexThreadState(ThreadId tid, unsigned _statement_nr,
				expression_result_array _tmp);
	void *marshal(unsigned *sz) const;
	void visit(HeapVisitor &hv) const;
	LogRecord *dupe() const
	{
		return new LogRecordVexThreadState(thread(), statement_nr, tmp);
	}
};


class Thread {
	void translateNextBlock(AddressSpace *addrSpace);
	struct expression_result eval_expression(IRExpr *expr);
	ThreadEvent *do_dirty_call(IRDirty *details);
	expression_result do_ccall_calculate_condition(struct expression_result *args);
	expression_result do_ccall_calculate_rflags_c(expression_result *args);
	expression_result do_ccall_generic(IRCallee *cee, struct expression_result *rargs);
	expression_result do_ccall(IRCallee *cee, IRExpr **args);
public:
	ThreadId tid;
	unsigned pid;
	RegisterSet regs;
	unsigned long clear_child_tid;
	unsigned long robust_list;
	unsigned long set_child_tid;
	bool exitted;

	IRSB *currentIRSB;
public:
	expression_result_array temporaries;
private:
	int currentIRSBOffset;

	/* DNI */
	Thread();
	~Thread();
public:
	ThreadEvent *runToEvent(AddressSpace *addrSpace);

	static Thread *initialThread(const LogRecordInitialRegisters &initRegs);
	Thread *fork(unsigned newPid);
	Thread *dupeSelf() const;
	void dumpSnapshot(LogWriter *lw) const;

	void imposeState(const LogRecordVexThreadState &rec,
			 AddressSpace *as);
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
		static PMapEntry *alloc(PhysicalAddress pa, MemoryChunk *mc);
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
	const MemoryChunk *lookupConst(PhysicalAddress pa, unsigned long *mc_start) const;

	/* Add a new chunk to the map, and return a newly-assigned
	   physical address for it. */
	PhysicalAddress introduce(MemoryChunk *mc);

	static PMap *empty();
	PMap *dupeSelf() const;

	void visitPA(PhysicalAddress pa, HeapVisitor &hv) const;
	void visit(HeapVisitor &hv) const;
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
	void allocateMemory(const LogRecordAllocateMemory &rec)
	{
		allocateMemory(rec.start, rec.size, rec.prot, rec.flags);
	}
	void releaseMemory(unsigned long start, unsigned long size);
	void protectMemory(unsigned long start, unsigned long size, VAMap::Protection prot);
	void populateMemory(const LogRecordMemory &rec)
	{
		writeMemory(rec.start, rec.size, rec.contents, true);
	}
	void writeMemory(unsigned long start, unsigned size,
			 const void *contents, bool ignore_protection = false,
			 const Thread *thr = NULL);
	void readMemory(unsigned long start, unsigned size,
			void *contents, bool ignore_protection = false,
			const Thread *thr = NULL);
	bool isAccessible(unsigned long start, unsigned size,
			  bool isWrite, const Thread *thr = NULL);
	bool isWritable(unsigned long start, unsigned size,
			const Thread *thr = NULL) {
		return isAccessible(start, size, true, thr);
	}
	bool isReadable(unsigned long start, unsigned size,
			const Thread *thr = NULL) {
		return isAccessible(start, size, false, thr);
	}
	unsigned long setBrk(unsigned long newBrk);

	static AddressSpace *initialAddressSpace(unsigned long initialBrk);
	AddressSpace *dupeSelf() const;
	void visit(HeapVisitor &hv) const;
	void sanityCheck() const;

	void dumpBrkPtr(LogWriter *lw) const;
	void dumpSnapshot(LogWriter *lw) const;
};

class SignalHandlers {
public:
	struct sigaction handlers[64];
	SignalHandlers(const LogRecordInitialSighandlers &init) {
		memcpy(handlers, init.handlers, sizeof(init.handlers));
	}
	void dumpSnapshot(LogWriter *lw) const
	{
		lw->append(LogRecordInitialSighandlers(ThreadId(0), handlers));
	}
};

class MachineState {
public:
	LibvexVector<Thread> *threads;
private:
	bool exitted;
	unsigned exit_status;
	ThreadId nextTid;

	/* DNI */
	MachineState();
	~MachineState();
	static MachineState *initialMachineState(AddressSpace *as,
						 const LogRecordInitialSighandlers &handlers);
public:
	AddressSpace *addressSpace;
	SignalHandlers signalHandlers;
	static MachineState *initialMachineState(LogReader *lf,
						 LogFile::ptr startPtr,
						 LogFile::ptr *endPtr);

	void registerThread(Thread *t) {
		t->tid = nextTid;
		++nextTid;
		threads->push(t);
	}
	Thread *findThread(ThreadId id) {
		unsigned x;
		for (x = 0; x < threads->size(); x++)
			if (threads->index(x)->tid == id)
				return threads->index(x);
		abort();
	}
	void exitGroup(unsigned result) {
		exitted = true;
		exit_status = result;
	}

	MachineState *dupeSelf() const;

	void dumpSnapshot(LogWriter *lw) const;

	void visit(HeapVisitor &hv) const;
	void sanityCheck() const;
};

class Interpreter {
	void replayFootstep(const LogRecordFootstep &lrf,
			    const LogReader *lr,
			    LogReader::ptr startOffset,
			    LogReader::ptr *endOffset);

	MachineState *currentState;
	VexGcRoot currentStateRoot;
public:
	Interpreter(MachineState *rootMachine) :
		currentState(rootMachine),
		currentStateRoot((void **)&currentState)
	{
	}
	void replayLogfile(const LogReader *lf, LogReader::ptr startingPoint,
			   LogReader::ptr *endingPoint = NULL, LogWriter *log = NULL);
	InterpretResult getThreadMemoryTrace(ThreadId tid,
					     MemoryTrace **output);
	void runToAccessLoggingEvents(ThreadId tid, unsigned nr_accesses,
				      LogWriter *output = NULL);
};

void replay_syscall(const LogRecordSyscall *lrs,
		    Thread *thr,
		    MachineState *ms);
void
process_memory_records(AddressSpace *addrSpace,
		       const LogReader *lf,
		       LogReader::ptr startOffset,
		       LogReader::ptr *endOffset,
		       LogWriter *lw);

void debugger_attach(void);

void init_sli(void);

#endif /* !SLI_H__ */
