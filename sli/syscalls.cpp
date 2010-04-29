#include <asm/prctl.h>
#include <asm/unistd.h>

#include "sli.h"

static bool
isErrnoSysres(long x)
{
	return x >= -4096 && x < 0;
}

static void
process_memory_records(AddressSpace *addrSpace,
		       const LogReader *lf,
		       LogReader::ptr startOffset,
		       LogReader::ptr *endOffset)
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
		addrSpace->writeMemory(lrm->start, lrm->size, lrm->contents,
				       true);
		startOffset = nextOffset;
	}
	*endOffset = startOffset;
}

void
replay_syscall(const LogReader *lr,
	       LogReader::ptr startOffset,
	       LogReader::ptr *endOffset,
	       AddressSpace *addrSpace,
	       Thread *thr,
	       MachineState *mach)
{
	LogRecordSyscall *lrs = dynamic_cast<LogRecordSyscall *>(lr->read(startOffset, endOffset));
	PointerKeeper<LogRecordSyscall> pk(lrs);
	unsigned long sysnr = thr->regs.regs.guest_RAX;
	unsigned long res = lrs->res;
	unsigned long args[6];

	args[0] = thr->regs.regs.guest_RDI;
	args[1] = thr->regs.regs.guest_RSI;
	args[2] = thr->regs.regs.guest_RDX;
	args[3] = thr->regs.regs.guest_R10;
	args[4] = thr->regs.regs.guest_R8;
	args[5] = thr->regs.regs.guest_R9;

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

	switch (thr->regs.regs.guest_RAX) {
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
		printf("WARNING: sys_rt_sigaction not correctly handled\n");
		break;
	case __NR_rt_sigprocmask: /* 14 */
		printf("WARNING: sys_rt_sigprocmask not correctly handled\n");
		break;
	case __NR_access: /* 21 */
		break;
	case __NR_uname: /* 63 */
		break;
	case __NR_getcwd: /* 79 */
		break;
	case __NR_getrlimit: /* 97 */
		break;
	case __NR_arch_prctl: /* 158 */
		assert(args[0] == ARCH_SET_FS);
		thr->regs.regs.guest_FS_ZERO = args[1];
		break;
	case __NR_futex: /* 202 */
		printf("WARNING: sys_futex not correctly handled\n");
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
		throw UnknownSyscallException(thr->regs.regs.guest_RAX);
	}

	assert(res == lrs->res);	
	thr->regs.regs.guest_RAX = res;

	process_memory_records(addrSpace, lr, *endOffset, endOffset);
}
