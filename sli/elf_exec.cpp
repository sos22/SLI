/* Stuff for loading an ELF executable file into a machine state.  The
   MS reflects the start-of-day state of the program, excluding shared
   libraries. */
#include <sys/fcntl.h>
#include <sys/mman.h>
#include <elf.h>
#include <errno.h>
#include <unistd.h>

#include <sys/procfs.h>

#include "sli.h"
#include "mapping.hpp"

MachineState *
MachineState::readELFExec(const char *path)
{
	Mapping m;
	if (m.init(path) < 0)
		return NULL;
	const Elf64_Ehdr *eh = m.get<Elf64_Ehdr>(0);
	if (!eh ||
	    eh->e_ident[0] != ELFMAG0 ||
	    eh->e_ident[1] != ELFMAG1 ||
	    eh->e_ident[2] != ELFMAG2 ||
	    eh->e_ident[3] != ELFMAG3 ||
	    eh->e_type != ET_EXEC ||
	    eh->e_machine != EM_X86_64)
		return NULL;
	const Elf64_Phdr *phdrs = m.get<Elf64_Phdr>(eh->e_phoff, eh->e_phnum);
	if (!phdrs)
		return NULL;

	AddressSpace *as = AddressSpace::initialAddressSpace(0);
	MachineState *work = new MachineState();
	work->addressSpace = as;
	for (int p = 0; p < eh->e_phnum; p++) {
		if (phdrs[p].p_type != PT_LOAD ||
		    phdrs[p].p_flags == 0)
			continue;
		if (phdrs[p].p_filesz > phdrs[p].p_memsz) {
			/* Huh? */
			return NULL;
		}
		unsigned long start = phdrs[p].p_vaddr;
		unsigned long end = start + phdrs[p].p_memsz;
		start = start & ~(PAGE_SIZE - 1);
		end = (end + PAGE_SIZE - 1) & ~(PAGE_SIZE - 1);
		as->allocateMemory(start,
				   end - start,
				   VAMap::Protection(
					   phdrs[p].p_flags & PF_R,
					   phdrs[p].p_flags & PF_W,
					   phdrs[p].p_flags & PF_X));
		as->copyToClient(phdrs[p].p_vaddr,
				 phdrs[p].p_filesz,
				 m.window(phdrs[p].p_offset,
					  phdrs[p].p_filesz),
				 true);
	}

	Thread *thr = new Thread();
	thr->regs.set_reg(REGISTER_IDX(RIP), eh->e_entry);

	/* Cunning hack: setting the initial value of RCX to one,
	   rather than zero, means that rep movs instructions take at
	   least one step, which in turn means that we generate memory
	   access events for them when trying to find proximal
	   causes. */
	thr->regs.set_reg(REGISTER_IDX(RCX), 1);

	work->registerThread(thr);
	printf("Psuedo thread has id %d\n", thr->tid._tid());
	return work;
}
