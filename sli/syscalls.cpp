#include <asm/unistd.h>

#include "sli.h"

void
replay_syscall(const LogReader *lr,
	       LogReader::ptr startOffset,
	       LogReader::ptr *endOffset,
	       AddressSpace *addrSpace,
	       Thread *thr)
{
	LogRecordSyscall *lrs = dynamic_cast<LogRecordSyscall *>(lr->read(startOffset, endOffset));

	if (thr->regs.regs.guest_RAX != lrs->sysnr)
		throw ReplayFailedBadRegister("<sysnr>",
					      thr->regs.regs.guest_RAX,
					      lrs->sysnr);
	if (thr->regs.regs.guest_RDI != lrs->arg1)
		throw ReplayFailedBadRegister("<sys_arg1>",
					      thr->regs.regs.guest_RDI,
					      lrs->arg1);
	if (thr->regs.regs.guest_RSI != lrs->arg2)
		throw ReplayFailedBadRegister("<sys_arg2>",
					      thr->regs.regs.guest_RSI,
					      lrs->arg2);
	if (thr->regs.regs.guest_RDX != lrs->arg3)
		throw ReplayFailedBadRegister("<sys_arg3>",
					      thr->regs.regs.guest_RDX,
					      lrs->arg3);

	switch (thr->regs.regs.guest_RAX) {
	case __NR_brk:
		thr->regs.regs.guest_RAX = addrSpace->setBrk(thr->regs.regs.guest_RDI);
		assert(thr->regs.regs.guest_RAX = lrs->res);
		break;
	default:
		throw UnknownSyscallException(thr->regs.regs.guest_RAX);
	}
}
