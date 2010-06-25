#include <asm/prctl.h>
#include <asm/unistd.h>
#include <sched.h>

#include "sli.h"

static bool
isErrnoSysres(long x)
{
	return x >= -4096 && x < 0;
}

template<typename ait> void
process_memory_records(AddressSpace<ait> *addrSpace,
		       const LogReader<ait> *lf,
		       LogReaderPtr startOffset,
		       LogReaderPtr *endOffset,
		       LogWriter<ait> *lw)
{
	while (1) {
		LogReaderPtr nextOffset;
		LogRecord<ait> *lr = lf->read(startOffset, &nextOffset);
		if (!lr)
			break;
		LogRecordMemory<ait> *lrm = dynamic_cast<LogRecordMemory<ait>*>(lr);
		if (!lrm)
			break;
		if (lw)
			lw->append(*lr, 0);
		addrSpace->writeMemory(EventTimestamp::invalid, lrm->start, lrm->size, lrm->contents,
				       true);
		startOffset = nextOffset;
	}
	*endOffset = startOffset;
}

template<typename ait>
static void
handle_clone(AddressSpace<ait> *addrSpace,
	     Thread<ait> *thr,
	     MachineState<ait> *mach,
	     ait flags,
	     ait childRsp,
	     ait parent_tidptr,
	     ait child_tidptr,
	     ait set_tls,
	     unsigned pid)
{
	if (force(flags != mkConst<ait>((CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND |
					 CLONE_THREAD | CLONE_SYSVSEM | CLONE_SETTLS |
					 CLONE_PARENT_SETTID | CLONE_CHILD_CLEARTID)))) {
		printf("can't handle clone flags %lx\n", force(flags));
		abort();
	}

	/* Create a new thread.  This is, as you might expect, closely
	   modelled on the kernel's version of the same process. */
	Thread<ait> *newThread = thr->fork(pid);
	if (force(flags & mkConst<ait>(CLONE_CHILD_SETTID)))
		newThread->set_child_tid = child_tidptr;
	if (force(flags & mkConst<ait>(CLONE_CHILD_CLEARTID)))
		newThread->clear_child_tid = child_tidptr;
	newThread->robust_list = mkConst<ait>(0);
#if 0
	if (flags & CLONE_VM)
		newThread->sas_ss_sp = newThread->sas_ss_size = 0;
	newThread->exit_signal = (flags & CLONE_THREAD) ? -1 : (clone_flags & CSIGNAL);
#endif
	newThread->regs.set_reg(REGISTER_IDX(RAX), mkConst<ait>(0));
	newThread->regs.set_reg(REGISTER_IDX(RSP), childRsp);
	if (force(flags & mkConst<ait>(CLONE_SETTLS)))
		newThread->regs.set_reg(REGISTER_IDX(FS_ZERO), set_tls);

	mach->registerThread(newThread);
}

template<typename ait> ThreadEvent<ait> *
replay_syscall(const LogRecordSyscall<ait> *lrs,
	       Thread<ait> *thr,
	       MachineState<ait> *mach)
{
	AddressSpace<ait> *addrSpace = mach->addressSpace;
	ait sysnr = thr->regs.get_reg(REGISTER_IDX(RAX));
	ait res = lrs->res;
	ait args[6];
	ThreadEvent<ait> *evt = NULL;
	args[0] = thr->regs.get_reg(REGISTER_IDX(RDI));
	args[1] = thr->regs.get_reg(REGISTER_IDX(RSI));
	args[2] = thr->regs.get_reg(REGISTER_IDX(RDX));
	args[3] = thr->regs.get_reg(REGISTER_IDX(R10));
	args[4] = thr->regs.get_reg(REGISTER_IDX(R8));
	args[5] = thr->regs.get_reg(REGISTER_IDX(R9));

	if (force(sysnr != lrs->sysnr))
		throw ReplayFailedBadRegister("<sysnr>",
					      force(sysnr),
					      force(lrs->sysnr));
	if (force(args[0] != lrs->arg1))
		throw ReplayFailedBadRegister("<sys_arg1>",
					      force(args[0]),
					      force(lrs->arg1));
	if (force(args[1] != lrs->arg2))
		throw ReplayFailedBadRegister("<sys_arg2>",
					      force(args[1]),
					      force(lrs->arg2));
	if (force(args[2] != lrs->arg3))
		throw ReplayFailedBadRegister("<sys_arg3>",
					      force(args[2]),
					      force(lrs->arg3));

	res = lrs->res;

	switch (force(sysnr)) {
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
		ait addr = lrs->res;
		ait length = args[1];
		ait prot = args[2];
		
		if (!isErrnoSysres(force(lrs->res))) {
			length = (length + mkConst<ait>(4095)) & ~mkConst<ait>(4095);
			addrSpace->allocateMemory(addr, length, force(prot));
		}
		break;
	}
	case __NR_mprotect: { /* 10 */
		ait addr = args[0];
		ait size = args[1];
		ait prot = args[2];
		if (!isErrnoSysres(force(lrs->res)))
			addrSpace->protectMemory(addr, size, force(prot));
		break;
	}
	case __NR_munmap: { /* 11 */
		addrSpace->releaseMemory(args[0], (args[1] + mkConst<ait>(4095)) & mkConst<ait>(~4095));
		break;
	}
	case __NR_brk: /* 12 */
		res = mkConst<ait>(addrSpace->setBrk(args[0]));
		break;
	case __NR_rt_sigaction: /* 13 */
		if (!isErrnoSysres(force(lrs->res)) &&
		    force(args[1] != mkConst<ait>(0))) {
			ait buf[sizeof(struct sigaction)];
			addrSpace->readMemory(args[1],
					      sizeof(struct sigaction),
					      buf);
			unsigned long arg0 = force(args[0]);
			for (unsigned x = 0; x < sizeof(struct sigaction); x++)
				((unsigned char *)&mach->signalHandlers.handlers[arg0])[x] =
					force(buf[x]);
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
		if (!isErrnoSysres(force(lrs->res)))
			handle_clone(addrSpace,
				     thr,
				     mach,
				     args[0],
				     args[1],
				     args[2],
				     args[3],
				     args[4],
				     force(lrs->res));
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
	case __NR_gettimeofday: /* 96 */
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
	case __NR_sched_getparam: /* 143 */
		break;
	case __NR_sched_getscheduler: /* 145 */
		break;
	case __NR_sched_get_priority_max: /* 146 */
		break;
	case __NR_sched_get_priority_min: /* 147 */
		break;
	case __NR_arch_prctl: /* 158 */
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
	case __NR_clock_getres: /* 229 */
		break;
	case __NR_exit_group: /* 231 */
		mach->exitGroup(args[0]);
		break;
	case __NR_tgkill: /* 234 */
		/* Hack: assume that this came from raise() */
		evt = SignalEvent<ait>::get(thr->bumpEvent(mach), force(args[2]), mkConst<ait>(0));
		break;

	case __NR_set_robust_list: /* 273 */
		thr->robust_list = args[0];
		break;
	default:
		throw UnknownSyscallException(force(sysnr));
	}

	assert(force(res == lrs->res));
	thr->regs.set_reg(REGISTER_IDX(RAX), res);

	return evt;
}

template <typename ait>
InterpretResult SyscallEvent<ait>::fake(MachineState<ait> *ms, LogRecord<ait> **lr)
{
	ait res;
	Thread<ait> *thr = ms->findThread(this->when.tid);
	ait sysnr = thr->regs.get_reg(REGISTER_IDX(RAX));

	switch (force(sysnr)) {
	case __NR_open: {
		char *path =
			ms->addressSpace->readString(
				thr->regs.get_reg(REGISTER_IDX(RDI)));
		printf("Can't fake open syscall (file %s)\n",
		       path);
		free(path);
		if (lr)
			*lr = NULL;
		return InterpretResultIncomplete;
	}
	case __NR_futex:
		res = mkConst<ait>(0);
		break;
	default:
		printf("can't fake syscall %ld yet\n", force(sysnr));
		if (lr)
			*lr = NULL;
		return InterpretResultIncomplete;
	}
	LogRecordSyscall<ait> *llr = new LogRecordSyscall<ait>(thr->tid,
							       sysnr,
							       res,
							       thr->regs.get_reg(REGISTER_IDX(RDI)),
							       thr->regs.get_reg(REGISTER_IDX(RSI)),
							       thr->regs.get_reg(REGISTER_IDX(RDX)));

	if (lr)
		*lr = llr;
	replay_syscall<ait>(llr, thr, ms);
	return InterpretResultContinue;
}
