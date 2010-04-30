#ifndef SLI_H__
#define SLI_H__

#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <vector>

extern "C" {
#include "libvex_guest_amd64.h"
};

#include "exceptions.h"

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

class ThreadId {
	unsigned tid;
public:
	ThreadId(unsigned _tid) : tid(_tid) {}
	bool operator==(const ThreadId &b) { return b.tid == tid; }
	ThreadId operator++() {
		tid++;
		return *this;
	}
	const unsigned _tid() { return tid; }
};

class LogRecord {
	/* DNI */
	LogRecord(const LogRecord &);
	ThreadId tid;
public:
	ThreadId thread() const { return tid; }
	LogRecord(ThreadId _tid) : tid(_tid) {}
	virtual ~LogRecord();
};

class LogRecordFootstep : public LogRecord {
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
};

class LogRecordSyscall : public LogRecord {
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
};

class LogRecordMemory : public LogRecord {
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
};

class LogRecordRdtsc : public LogRecord {
public:
	unsigned long tsc;
	LogRecordRdtsc(ThreadId _tid,
		       unsigned long _tsc)
		: LogRecord(_tid),
		  tsc(_tsc)
	{
	}
};

class LogRecordAllocateMemory : public LogRecord {
	friend class AddressSpace;
	unsigned long start;
	unsigned long size;
	unsigned prot;
	unsigned flags;
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
};

class LogRecordInitialRegisters : public LogRecord {
	friend class Thread;
	VexGuestAMD64State regs;
public:
	LogRecordInitialRegisters(ThreadId tid,
				  const VexGuestAMD64State &r) :
		LogRecord(tid),
		regs(r)
	{
	}
};

class LogRecordInitialBrk : public LogRecord {
public:
	unsigned long brk;
	LogRecordInitialBrk(ThreadId tid,
			    unsigned long _brk) :
		LogRecord(tid),
		brk(_brk)
	{
	}
};

class LogRecordInitialSighandlers : public LogRecord {
	friend class SignalHandlers;
	struct sigaction handlers[64];
public:
	LogRecordInitialSighandlers(ThreadId tid,
				    const struct sigaction *sa)
		: LogRecord(tid)
	{
		memcpy(handlers, sa, sizeof(*sa));
	}
};

class LogReader {
	int fd;
public:
	class ptr {
		friend class LogReader;
		uint64_t off;
		bool valid;
		unsigned record_nr;
		ptr(uint64_t o, unsigned rn) :
			off(o), valid(true),
			record_nr(rn) {};
		uint64_t &offset() {
			assert(valid);
			return off;
		}
	public:
		ptr() : valid(false) {};
		unsigned rn() { return record_nr; }
	};

	LogRecord *read(ptr startPtr, ptr *outPtr) const;
	~LogReader();
	static LogReader *open(const char *path, ptr *initial_ptr);
};


class RegisterSet {
public:
	VexGuestAMD64State regs;
	RegisterSet(const VexGuestAMD64State &r) : regs(r) {}
	unsigned long rip() { return regs.guest_RIP; }
};

class Thread {
public:
	ThreadId tid;
	unsigned pid;
	RegisterSet regs;
	unsigned long clear_child_tid;
	unsigned long robust_list;
	unsigned long set_child_tid;
	bool exitted;
	Thread(const LogRecordInitialRegisters &initRegs);
	Thread(unsigned _pid, const Thread &parent) :
		tid(0),
		pid(_pid),
		regs(parent.regs),
		clear_child_tid(0),
		robust_list(0),
		set_child_tid(0),
		exitted(false)
	{
	}
};

class AddressSpace {
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
	};
	class AllocFlags {
	public:
		bool expandsDown;
		AllocFlags(bool _e) :
			expandsDown(_e)
		{
		}
		AllocFlags(unsigned flags); /* MAP_* flags */
	};
	static const AllocFlags defaultFlags;
private:
	struct AddressSpaceEntry {
		unsigned long start; /* inclusive */
		unsigned long end; /* not inclusive */
		Protection prot;
		AllocFlags flags;
		void *content;
		AddressSpaceEntry *next;
		AddressSpaceEntry(unsigned long _start,
				  unsigned long _end,
				  Protection _prot,
				  void *_content,
				  AllocFlags _flags) :
			start(_start),
			end(_end),
			prot(_prot),
			flags(_flags),
			content(_content),
			next(NULL)
		{
		}
		void splitAt(unsigned long addr);
	};

	unsigned long brkptr;

	AddressSpaceEntry *head;
	AddressSpaceEntry *findAseForPointer(unsigned long ptr);
	bool expandStack(const Thread &thr, unsigned long ptr);
public:
	void allocateMemory(unsigned long start, unsigned long size, Protection prot,
			    AllocFlags flags = defaultFlags);
	void allocateMemory(const LogRecordAllocateMemory &rec)
	{
		allocateMemory(rec.start, rec.size, rec.prot, rec.flags);
	}
	void releaseMemory(unsigned long start, unsigned long size);
	void protectMemory(unsigned long start, unsigned long size, Protection prot);
	void populateMemory(const LogRecordMemory &rec);
	void writeMemory(unsigned long start, unsigned size,
			 const void *contents, bool ignore_protection = false,
			 const Thread *thr = NULL);
	void readMemory(unsigned long start, unsigned size,
			void *contents, bool ignore_protection = false,
			const Thread *thr = NULL);

	unsigned long setBrk(unsigned long newBrk);

	const void *getRawPointerUnsafe(unsigned long ptr);

	AddressSpace(unsigned long initialBrk) :
		brkptr(initialBrk),
		head(NULL)
	{
	}
};

class SignalHandlers {
public:
	struct sigaction handlers[64];
	SignalHandlers(const LogRecordInitialSighandlers &init) {
		memcpy(handlers, init.handlers, sizeof(init.handlers));
	}
};

class MachineState {
	std::vector<Thread *>threads;
	bool exitted;
	unsigned exit_status;
	ThreadId nextTid;
public:
	AddressSpace *addressSpace;
	SignalHandlers signalHandlers;
	MachineState(AddressSpace *as, Thread *rootThread,
		     const LogRecordInitialSighandlers &handlers) :
		threads(),
		nextTid(1),
		addressSpace(as),
		signalHandlers(handlers)
	{
		registerThread(rootThread);
	}
	void registerThread(Thread *t) {
		printf("Register thread %d\n", t->tid._tid());
		t->tid = nextTid;
		++nextTid;
		threads.push_back(t);
	}
	Thread *findThread(ThreadId id) {
		for (std::vector<Thread *>::iterator it = threads.begin();
		     it != threads.end();
		     it++) {
			if ((*it)->tid == id)
				return *it;
		}
		abort();
	}
	void exitGroup(unsigned result) {
		exitted = true;
		exit_status = result;
	}
};

class Interpreter {
	void replayFootstep(const LogRecordFootstep &lrf,
			    const LogReader *lr,
			    LogReader::ptr startOffset,
			    LogReader::ptr *endOffset);

	MachineState *currentState;
public:
	Interpreter(MachineState *rootMachine) :
		currentState(rootMachine)
	{
	}
	void replayLogfile(const LogReader *lf, LogReader::ptr startingPoint);
};

void replay_syscall(const LogReader *lr,
		    LogReader::ptr startOffset,
		    LogReader::ptr *endOffset,
		    AddressSpace *addrSpace,
		    Thread *thr,
		    MachineState *ms);

#endif /* !SLI_H__ */
