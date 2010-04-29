#ifndef SLI_H__
#define SLI_H__

#include <assert.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <exception>
#include <string>

extern "C" {
#include "libvex_guest_amd64.h"
};

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
	ThreadId(unsigned _tid) : tid(_tid) {};

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
	};

	LogRecord *read(ptr startPtr, ptr *outPtr) const;
	~LogReader();
	static LogReader *open(const char *path, ptr *initial_ptr);
};


class RegisterSet {
	friend class Thread;
public:
	VexGuestAMD64State regs;
	RegisterSet(const VexGuestAMD64State &r) : regs(r) {}
	unsigned long rip() { return regs.guest_RIP; }
};

class Thread {
public:
	Thread(const LogRecordInitialRegisters &initRegs);
	RegisterSet regs;
	unsigned long clear_child_tid;
	unsigned long robust_list;
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
private:
	struct AddressSpaceEntry {
		unsigned long start; /* inclusive */
		unsigned long end; /* not inclusive */
		class Protection prot;
		void *content;
		AddressSpaceEntry *next;
		AddressSpaceEntry(unsigned long _start,
				  unsigned long _end,
				  Protection _prot,
				  void *_content) :
			start(_start),
			end(_end),
			prot(_prot),
			content(_content),
			next(NULL)
		{
		}
		void splitAt(unsigned long addr);
	};

	unsigned long brkptr;

	AddressSpaceEntry *head;
	AddressSpaceEntry *findAseForPointer(unsigned long ptr);
public:
	void allocateMemory(unsigned long start, unsigned long size, Protection prot);
	void allocateMemory(const LogRecordAllocateMemory &rec)
	{
		allocateMemory(rec.start, rec.size, rec.prot);
	}
	void releaseMemory(unsigned long start, unsigned long size);
	void protectMemory(unsigned long start, unsigned long size, Protection prot);
	void populateMemory(const LogRecordMemory &rec);
	void writeMemory(unsigned long start, unsigned size, const void *contents,
			 bool ignore_protection = false);
	void readMemory(unsigned long start, unsigned size, void *contents,
			bool ignore_protection = false);

	unsigned long setBrk(unsigned long newBrk);

	const void *getRawPointerUnsafe(unsigned long ptr);

	AddressSpace(unsigned long initialBrk) :
		brkptr(initialBrk),
		head(NULL)
	{
	}
};

class MachineState {
	Thread *thread;
	bool exitted;
	unsigned exit_status;
public:
	AddressSpace *addressSpace;
	MachineState(AddressSpace *as, Thread *rootThread) :
		thread(rootThread),
		addressSpace(as)
	{
	}
	Thread *findThread(ThreadId id) { return thread; }
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

class SliException : public std::exception {
	char *msg;
protected:
	void setMessage(const char *fmt, va_list args)
	{
		free(msg);
		vasprintf(&msg, fmt, args);
	}
public:
	SliException(const SliException &b)
	{
		msg = strdup(b.msg);
	}
	SliException(const char *fmt, ...)
	{
		va_list args;
		va_start(args, fmt);
		vasprintf(&msg, fmt, args);
		va_end(args);
	}
	SliException()
		: msg(strdup(""))
	{
	}
	~SliException() throw()
	{
		free(msg);
	}
	virtual const char *what() const throw() {
		return msg;
	}
};

class ReplayFailedException : public SliException {
public:
	ReplayFailedException(const char *fmt, ...)
	{
		va_list args;
		va_start(args, fmt);
		setMessage(fmt, args);
		va_end(args);
	}
};

class ReplayFailedBadRip : public ReplayFailedException {
public:
	unsigned long observed;
	unsigned long expected;
	ReplayFailedBadRip(unsigned long _observed,
			   unsigned long _expected) :
		ReplayFailedException(
			"replay failed due to bad RIP: wanted %lx, got %lx\n",
			_expected,
			_observed),
		observed(_observed),
		expected(_expected)
	{
	}
};

class ReplayFailedBadRegister : public ReplayFailedException {
public:
	const char *reg_name;
	unsigned long observed;
	unsigned long expected;
	ReplayFailedBadRegister(const char *_name,
				unsigned long _observed,
				unsigned long _expected) :
		ReplayFailedException(
			"replay failed due to bad register %s: wanted %lx, got %lx\n",
			_name,
			_expected,
			_observed),
		reg_name(_name),
		observed(_observed),
		expected(_expected)
	{
	}
};

class InstructionDecodeFailedException : public SliException {
};

class NotImplementedException : public SliException {
};

class BadMemoryException : public SliException {
public:
	bool isWrite;
	unsigned long ptr;
	unsigned size;
	BadMemoryException(bool _isWrite,
			   unsigned long _ptr,
			   unsigned _size) :
		SliException(
			"guest dereferenced a bad pointer: address %lx, size %x, isWrite %d\n",
			_ptr,
			_size,
			_isWrite),
		isWrite(_isWrite),
		ptr(_ptr),
		size(_size)
	{
	}
};

class UnknownSyscallException : public SliException {
public:
	unsigned nr;
	UnknownSyscallException(unsigned _nr) :
		SliException("unknown syscall %d\n", _nr),
		nr(_nr)
	{
	}
};




void replay_syscall(const LogReader *lr,
		    LogReader::ptr startOffset,
		    LogReader::ptr *endOffset,
		    AddressSpace *addrSpace,
		    Thread *thr,
		    MachineState *ms);

#endif /* !SLI_H__ */
