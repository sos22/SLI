#include <asm/prctl.h>
#include <asm/unistd.h>
#include <sched.h>

#include "sli.h"

static bool
isErrnoSysres(long x)
{
	return x >= -4096 && x < 0;
}

void
process_memory_records(AddressSpace *addrSpace,
		       const LogReader *lf,
		       LogReader::ptr startOffset,
		       LogReader::ptr *endOffset,
		       LogWriter *lw)
{
	while (1) {
		LogReader::ptr nextOffset;
		LogRecord *lr = lf->read(startOffset, &nextOffset);
		if (!lr)
			break;
		PointerKeeper<LogRecord> pk(lr);
		LogRecordMemory *lrm = dynamic_cast<LogRecordMemory*>(lr);
		if (!lrm)
			break;
		if (lw)
			lw->append(*lr);
		addrSpace->writeMemory(lrm->start, lrm->size, lrm->contents,
				       true);
		startOffset = nextOffset;
	}
	*endOffset = startOffset;
}

template<typename ait>
static void
handle_clone(AddressSpace *addrSpace,
	     Thread<ait> *thr,
	     MachineState<ait> *mach,
	     unsigned long flags,
	     unsigned long childRsp,
	     unsigned long parent_tidptr,
	     unsigned long child_tidptr,
	     unsigned long set_tls,
	     unsigned pid)
{
	if (flags != (CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND |
		      CLONE_THREAD | CLONE_SYSVSEM | CLONE_SETTLS |
		      CLONE_PARENT_SETTID | CLONE_CHILD_CLEARTID)) {
		printf("can't handle clone flags %lx\n", flags);
		abort();
	}

	/* Create a new thread.  This is, as you might expect, closely
	   modelled on the kernel's version of the same process. */
	Thread<ait> *newThread = thr->fork(pid);
	if (flags & CLONE_CHILD_SETTID)
		newThread->set_child_tid = child_tidptr;
	if (flags & CLONE_CHILD_CLEARTID)
		newThread->clear_child_tid = child_tidptr;
	newThread->robust_list = 0;
#if 0
	if (flags & CLONE_VM)
		newThread->sas_ss_sp = newThread->sas_ss_size = 0;
	newThread->exit_signal = (flags & CLONE_THREAD) ? -1 : (clone_flags & CSIGNAL);
#endif
	newThread->regs.set_reg(REGISTER_IDX(RAX), 0);
	newThread->regs.set_reg(REGISTER_IDX(RSP), childRsp);
	if (flags & CLONE_SETTLS)
		newThread->regs.set_reg(REGISTER_IDX(FS_ZERO), set_tls);

	mach->registerThread(newThread);
}

template<typename ait>
void
replay_syscall(const LogRecordSyscall *lrs,
	       Thread<ait> *thr,
	       MachineState<ait> *mach)
{
	AddressSpace *addrSpace = mach->addressSpace;
	unsigned long sysnr = thr->regs.get_reg(REGISTER_IDX(RAX));
	unsigned long res = lrs->res;
	unsigned long args[6];

	args[0] = thr->regs.get_reg(REGISTER_IDX(RDI));
	args[1] = thr->regs.get_reg(REGISTER_IDX(RSI));
	args[2] = thr->regs.get_reg(REGISTER_IDX(RDX));
	args[3] = thr->regs.get_reg(REGISTER_IDX(R10));
	args[4] = thr->regs.get_reg(REGISTER_IDX(R8));
	args[5] = thr->regs.get_reg(REGISTER_IDX(R9));

	if (sysnr != lrs->sysnr)
		throw ReplayFailedBadRegister("<sysnr>",
					      sysnr,
					      lrs->sysnr);
	if (args[0] != lrs->arg1)
		throw ReplayFailedBadRegister("<sys_arg1>",
					      args[0],
					      lrs->arg1);
	if (args[1] != lrs->arg2)
		throw ReplayFailedBadRegister("<sys_arg2>",
					      args[1],
					      lrs->arg2);
	if (args[2] != lrs->arg3)
		throw ReplayFailedBadRegister("<sys_arg3>",
					      args[2],
					      lrs->arg3);

	res = lrs->res;

	switch (sysnr) {
	case __NR_read: /* 0 */
		break;
	case __NR_write: /* 1 */
		break;
	case __NR_open: /* 2 */
		break;
	case __NR_close: /* 3 */
		break;
	case __NR_stat: /* 4 */
		break;
	case __NR_fstat: /* 5 */
		break;
	case __NR_lseek: /* 8 */
		break;
	case __NR_mmap: { /* 9 */
		unsigned long addr = lrs->res;
		unsigned long length = args[1];
		unsigned long prot = args[2];
		
		if (!isErrnoSysres(lrs->res)) {
			length = (length + 4095) & ~4095;
			addrSpace->allocateMemory(addr, length, prot);
		}
		break;
	}
	case __NR_mprotect: { /* 10 */
		unsigned long addr = args[0];
		unsigned long size = args[1];
		unsigned long prot = args[2];
		if (!isErrnoSysres(lrs->res))
			addrSpace->protectMemory(addr, size, prot);
		break;
	}
	case __NR_munmap: { /* 11 */
		addrSpace->releaseMemory(args[0], (args[1] + 4095) & ~4095);
		break;
	}
	case __NR_brk: /* 12 */
		res = addrSpace->setBrk(args[0]);
		break;
	case __NR_rt_sigaction: /* 13 */
		if (!isErrnoSysres(lrs->res) &&
		    args[1] != 0) {

			/* Or else the call should have returned an error */
			assert(args[0] < 64);

			addrSpace->readMemory(args[1],
					      sizeof(struct sigaction),
					      &mach->signalHandlers.handlers[args[0]]);
		}
		/* A memory record will follow and handle the old
		   handler if appropriate. */
		break;

	case __NR_rt_sigprocmask: /* 14 */
		printf("WARNING: sys_rt_sigprocmask not correctly handled\n");
		break;
	case __NR_ioctl: /* 16 */
		/* ioctls generally either do IO or fill out in-memory
		   structures.  IO we want to discard, and in-memory
		   things will be handled by memory records, so we can
		   pretty much ignore these. */		   
		break;
	case __NR_access: /* 21 */
		break;
	case __NR_getpid: /* 39 */
		break;
	case __NR_clone: /* 56 */
		if (!isErrnoSysres(lrs->res))
			handle_clone(addrSpace,
				     thr,
				     mach,
				     args[0],
				     args[1],
				     args[2],
				     args[3],
				     args[4],
				     lrs->res);
		break;
	case __NR_exit:
		thr->exitted = true;
		break;
	case __NR_uname: /* 63 */
		break;
	case __NR_fcntl: /* 72 */
		break;
	case __NR_getdents: /* 78 */
		break;
	case __NR_getcwd: /* 79 */
		break;
	case __NR_readlink: /* 89 */
		break;
	case __NR_getrlimit: /* 97 */
		break;
	case __NR_getuid: /* 102 */
		break;
	case __NR_getgid: /* 104 */
		break;
	case __NR_geteuid: /* 107 */
		break;
	case __NR_getegid: /* 108 */
		break;
	case __NR_getppid: /* 110 */
		break;
	case __NR_getgroups: /* 115 */
		break;
	case __NR_statfs: /* 137 */
		break;
	case __NR_arch_prctl: /* 158 */
		assert(args[0] == ARCH_SET_FS);
		thr->regs.set_reg(REGISTER_IDX(FS_ZERO), args[1]);
		break;
	case __NR_sync: /* 162 */
		break;
	case __NR_time: /* 201 */
		break;
	case __NR_futex: /* 202 */
		break;
	case __NR_set_tid_address: /* 218 */
		thr->clear_child_tid = args[0];
		break;
	case __NR_clock_gettime: /* 228 */
		break;
	case __NR_exit_group: /* 231 */
		mach->exitGroup(args[0]);
		break;
	case __NR_set_robust_list: /* 273 */
		thr->robust_list = args[0];
		break;
	default:
		throw UnknownSyscallException(sysnr);
	}

	assert(res == lrs->res);	
	thr->regs.set_reg(REGISTER_IDX(RAX), res);
}

InterpretResult SyscallEvent::fake(Thread<unsigned long> *thr, MachineState<unsigned long> *ms, LogRecord **lr)
{
	unsigned long res;
	unsigned long sysnr = thr->regs.get_reg(REGISTER_IDX(RAX));

	switch (sysnr) {
	case __NR_futex:
		res = 0;
		break;
	default:
		printf("can't fake syscall %ld yet\n", sysnr);
		if (lr)
			*lr = NULL;
		return InterpretResultIncomplete;
	}
	LogRecordSyscall *llr = new LogRecordSyscall(thr->tid,
						     sysnr,
						     res,
						     thr->regs.get_reg(REGISTER_IDX(RDI)),
						     thr->regs.get_reg(REGISTER_IDX(RSI)),
						     thr->regs.get_reg(REGISTER_IDX(RDX)));

	if (lr)
		*lr = llr;
	replay_syscall<unsigned long>(llr, thr, ms);
	if (!lr)
		delete llr;
	return InterpretResultContinue;
}
