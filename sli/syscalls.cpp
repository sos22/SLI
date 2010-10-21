#include <sys/time.h>
#include <linux/futex.h>
#include <asm/prctl.h>
#include <asm/unistd.h>
#include <errno.h>
#include <poll.h>
#include <sched.h>
#include <time.h>

#include "sli.h"
#include "main_util.h"

static bool
isErrnoSysres(long x)
{
	return x >= -4096 && x < 0;
}

void
process_memory_records(VexPtr<AddressSpace> &addrSpace,
		       VexPtr<LogReader > &lf,
		       LogReaderPtr startOffset,
		       LogReaderPtr *endOffset,
		       VexPtr<LogWriter> &lw,
		       GarbageCollectionToken tok)
{
	while (1) {
		LogReaderPtr nextOffset;
		LogRecord *lr = lf->read(startOffset, &nextOffset);
		if (!lr)
			break;
		LogRecordMemory *lrm = dynamic_cast<LogRecordMemory*>(lr);
		if (!lrm)
			break;
		if (lw)
			lw->append(lr, 0);
		try {
			addrSpace->writeMemory(EventTimestamp::invalid, lrm->start, lrm->size, lrm->contents,
					       true, NULL);
		} catch (BadMemoryException<unsigned long> bme) {
		}
		startOffset = nextOffset;

		/* That can sometimes do a lot of work (e.g. mmap()ing
		   a new shared library).  That makes this loop a good
		   place to try to do a GC pass. */
		vexSetAllocModeTEMP_and_clear(tok);
	}
	*endOffset = startOffset;
}

static void
handle_clone(AddressSpace *addrSpace,
	     Thread *thr,
	     MachineState *&mach,
	     unsigned long flags,
	     unsigned long childRsp,
	     unsigned long parent_tidptr,
	     unsigned long child_tidptr,
	     unsigned long set_tls,
	     unsigned pid,
	     LogReaderPtr ptr)
{
	if (flags == (CLONE_CHILD_SETTID | CLONE_CHILD_CLEARTID | SIGCHLD)) {
		/* Simple fork() -> don't need to do anything */
		return;
	}

	if (flags != ((CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND |
		       CLONE_THREAD | CLONE_SYSVSEM | CLONE_SETTLS |
		       CLONE_PARENT_SETTID | CLONE_CHILD_CLEARTID))) {
		printf("can't handle clone flags %lx\n", flags);
		abort();
	}

	/* Create a new thread.  This is, as you might expect, closely
	   modelled on the kernel's version of the same process. */
	Thread *newThread = thr->fork(pid);
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

	newThread->snapshotLog.push(Thread::snapshot_log_entry(mach, ptr));
	mach = mach->dupeSelf();

	printf("Clone created thread %d from %d\n", newThread->tid._tid(),
	       thr->tid._tid());
}

ThreadEvent *
replay_syscall(const LogRecordSyscall *lrs,
	       Thread *thr,
	       MachineState *&mach,
	       LogReaderPtr ptr)
{
	AddressSpace *addrSpace = mach->addressSpace;
	unsigned long sysnr = thr->regs.get_reg(REGISTER_IDX(RAX));
	unsigned long res = lrs->res;
	unsigned long args[6];
	ThreadEvent *evt = NULL;
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
	case __NR_lstat: /* 6 */
		break;
	case __NR_poll: /* 7 */
		break;
	case __NR_lseek: /* 8 */
		break;
	case __NR_mmap: { /* 9 */
		unsigned long addr = lrs->res;
		unsigned long length = args[1];
		unsigned long prot = args[2];
		
		if (!isErrnoSysres(lrs->res)) {
			length = (length + 4095ul) & ~4095ul;
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
		addrSpace->releaseMemory(args[0], (args[1] + 4095ul) & ~4095);
		break;
	}
	case __NR_brk: /* 12 */
		res = addrSpace->setBrk(args[0]);
		break;
	case __NR_rt_sigaction: /* 13 */
		if (!isErrnoSysres(lrs->res) &&
		    args[1] != 0ul) {
			unsigned long buf[sizeof(struct sigaction)];
			addrSpace->readMemory(args[1],
					      sizeof(struct sigaction),
					      buf,
					      false,
					      thr);
			unsigned long arg0 = args[0];
			for (unsigned x = 0; x < sizeof(struct sigaction); x++)
				((unsigned char *)&mach->signalHandlers.handlers[arg0])[x] =
					buf[x];
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
	case __NR_writev: /* 20 */
		break;
	case __NR_access: /* 21 */
		break;
	case __NR_pipe: /* 22 */
		break;
	case __NR_select: /* 23 */
		break;
	case __NR_sched_yield: /* 24 */
		break;
	case __NR_nanosleep: /* 35 */
		printf("Thread %d issues nanosleep\n",
		       thr->tid._tid());
		break;
	case __NR_getpid: /* 39 */
		break;
	case __NR_socket: /* 41 */
		break;
	case __NR_connect: /* 42 */
		break;
	case __NR_accept: /* 43 */
		break;
	case __NR_sendto: /* 44 */
		break;
	case __NR_recvfrom: /* 45 */
		break;
	case __NR_recvmsg: /* 47 */
		break;
	case __NR_bind: /* 49 */
		break;
	case __NR_listen: /* 50 */
		break;
	case __NR_getsockname: /* 51 */
		break;
	case __NR_setsockopt: /* 54 */
		break;
	case __NR_getsockopt: /* 55 */
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
				     lrs->res,
				     ptr);
		break;
	case __NR_exit: /* 60 */
		printf("Thread %d exits\n", thr->tid._tid());
		thr->exitted = true;
		if (thr->clear_child_tid) {
			struct expression_result v;
			v.lo = 0ul;
			try {
				addrSpace->store(EventTimestamp(thr->tid,
								thr->nrEvents,
								mach->nrEvents,
								thr->regs.rip()),
						 thr->clear_child_tid, 4, v);
			} catch (BadMemoryException<unsigned long> &e) {
				/* Kernel ignores errors clearing the
				   child TID pointer, and so we do
				   to. */
			}
		}
		break;
	case __NR_wait4: /* 61 */
		break;
	case __NR_uname: /* 63 */
		break;
	case __NR_fcntl: /* 72 */
		break;
	case __NR_getdents: /* 78 */
		break;
	case __NR_getcwd: /* 79 */
		break;
	case __NR_mkdir: /* 83 */
		break;
	case __NR_unlink: /* 87 */
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
	case __NR_utime: /* 132 */
		break;
	case __NR_statfs: /* 137 */
		break;
	case __NR_sched_getparam: /* 143 */
		break;
	case __NR_sched_setscheduler: /* 144 */
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
	case __NR_gettid: /* 186 */
		break;
	case __NR_time: /* 201 */
		break;
	case __NR_futex: /* 202 */
		switch (args[1] & FUTEX_CMD_MASK) {
		case FUTEX_WAIT:
			if (res == 0ul)
				thr->futexBlock(args[0]);
			break;
		case FUTEX_WAKE:
			mach->futexWake(args[0], true);
			break;
		case FUTEX_CMP_REQUEUE:
			break;
		case FUTEX_WAKE_OP:
			break;
		default:
			break;
		}
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
		evt = SignalEvent::get(thr->bumpEvent(mach), args[2], 0ul);
		break;

	case __NR_set_robust_list: /* 273 */
		thr->robust_list = args[0];
		break;
	default:
		throw UnknownSyscallException(sysnr);
	}

	assert(res == lrs->res);
	thr->regs.set_reg(REGISTER_IDX(RAX), res);

	return evt;
}

/* Try to ``fake'' a system call.  This tries to do something sensible
   which will encourage the client to continue and allow us to explore
   more of its behaviour.  This is all very ad-hoc and hacky, but
   seems to work often enough to be useful (at least for some
   programs). */
InterpretResult SyscallEvent::fake(MachineState *ms, LogRecord **lr)
{
	unsigned long res;
	Thread *thr = ms->findThread(this->when.tid);
	unsigned long sysnr = thr->regs.get_reg(REGISTER_IDX(RAX));
	unsigned long args[6];
	args[0] = thr->regs.get_reg(REGISTER_IDX(RDI));
	args[1] = thr->regs.get_reg(REGISTER_IDX(RSI));
	args[2] = thr->regs.get_reg(REGISTER_IDX(RDX));
	args[3] = thr->regs.get_reg(REGISTER_IDX(R10));
	args[4] = thr->regs.get_reg(REGISTER_IDX(R8));
	args[5] = thr->regs.get_reg(REGISTER_IDX(R9));

	res = -ENOSYS;
	switch (sysnr) {
	case __NR_write: { /* 1 */
		printf("write(%ld, 0x%lx, %ld)\n",
		       args[0], args[1],
		       args[2]);
		if (args[0] == 1 ||
		    args[0] == 2) {
			char *s = ms->addressSpace->readString(args[1], thr);
			printf("Client %s %.*s",
			       args[0] == 1 ? "message" : "error",
			       (int)args[2], s);
			free(s);
		}
		res = args[2];
		break;
	}

	case __NR_open: { /* 2 */
		char *path = ms->addressSpace->readString(args[0], thr);
		printf("Can't fake open syscall (file %s)\n",
		       path);
		free(path);
		res = -ENOENT;
		break;
	}

	case __NR_close: /* 3 */
		res = 0ul;
		break;

	case __NR_poll: { /* 7 */
		struct pollfd pfd;
		unsigned n_fds = args[1];
		bool fault;
		int result;

		/* Say that every FD is writable but not readable, and
		   that we have no errors.  The idea is that we want
		   to pump the client's state machine as far as
		   possible, but we don't want to encourage the client
		   to read if we can avoid it (because we won't be
		   able to synthesise any useful results if it
		   does). */
		fault = false;
		result = 0;
		for (unsigned x = 0; x < n_fds && !fault; x++) {
			fault |= ms->addressSpace->copyFromClient(this->when,
								  args[0] + x * sizeof(pfd),
								  sizeof(pfd),
								  &pfd);
			pfd.revents = pfd.events & POLLOUT;
			fault |= ms->addressSpace->copyToClient(this->when,
								args[0] + x * sizeof(pfd),
								sizeof(pfd),
								&pfd);
			if (pfd.revents)
				result++;
		}

		if (fault)
			res = -EFAULT;
		else if (result != 0)
			res = result;
		else {
			printf("thread %d appears to have gone idle...\n",
			       thr->tid._tid());
			res = -ENOSYS;
			thr->idle = true;
		}
		break;
	}

	case __NR_writev: { /* 20 */
		/* Just say that everything went out fine */
		struct iovec iov;
		unsigned nr_iovs = args[3];
		ssize_t written;
		written = 0;
		for (unsigned x = 0; x < nr_iovs; x++) {
			ms->addressSpace->copyFromClient(this->when,
							 args[0] + x * sizeof(iov),
							 sizeof(iov),
							 &iov);
			written += iov.iov_len;
		}
		res = written;
		break;
	}

	case __NR_stat: /* 4 */
	case __NR_lstat: /* 6 */
	case __NR_access: /* 21 */
		res = -ENOENT;
		break;

	case __NR_select: { /* 23 */
		/* Leave the masks unchanged, so every fd which was
		 * polled on is flagged as ready, and return 1, so
		 * that the client actually goes and looks at them. */
		res = 1ul;		
		break;
	}

	case __NR_nanosleep: /* 35 */
		printf("Thread %d sleeping...\n", thr->tid._tid());
		thr->idle = true;
		res = 0ul;
		break;

	case __NR_mkdir: /* 83 */
	case __NR_rmdir: /* 84 */
	case __NR_unlink: /* 87 */
		res = 0ul;
		break;

	case __NR_gettimeofday: { /* 96 */
		struct timeval tv;
		struct timezone tz;
		bool fault;

		gettimeofday(&tv, &tz);
		fault = false;
		if (args[0])
			fault |= ms->addressSpace->copyToClient(this->when, args[0], sizeof(tv),
								&tv);
		if (args[1])
			fault |= ms->addressSpace->copyToClient(this->when, args[1], sizeof(tv),
								&tv);
		if (fault)
			res = -EFAULT;
		else
			res = 0ul;
		break;
	}

	case __NR_futex: { /* 202 */
		switch (args[1] & FUTEX_CMD_MASK) {
		case FUTEX_WAIT: {
			expression_result m =
				ms->addressSpace->load(this->when,
						       args[0],
						       4,
						       false,
						       thr);
			if (m.lo == args[2]) {
				res = 0ul;
			} else {
				res = -EWOULDBLOCK;
			}
			break;
		}
		case FUTEX_WAKE: {
			res = ms->futexWake(args[0], false);
			break;
		}
		default:
			printf("unknown futex op %lx\n", args[1]);
			break;
		}

		break;
	}

	case __NR_clock_gettime: {
		struct timespec ts;
		clock_gettime(args[0], &ts);
		ms->addressSpace->copyToClient(this->when, args[1], sizeof(ts),
					       &ts);
		res = 0ul;
		break;
	}

	case __NR_exit: /* 60 */
	case __NR_exit_group: { /* 231 */
		res = 0ul;
		break;
	}

	default:
		printf("can't fake syscall %ld yet\n", sysnr);
		break;
	}
	LogRecordSyscall *llr = new LogRecordSyscall(thr->tid,
						     sysnr,
						     res,
						     thr->regs.get_reg(REGISTER_IDX(RDI)),
						     thr->regs.get_reg(REGISTER_IDX(RSI)),
						     thr->regs.get_reg(REGISTER_IDX(RDX)));

	if (lr)
		*lr = llr;
	ThreadEvent *evt = replay_syscall(llr, thr, ms, LogReaderPtr());
	if (evt)
		return evt->fake(ms);
	else
		return InterpretResultContinue;
}
