#include <sys/fcntl.h>
#include <sys/mman.h>
#include <elf.h>
#include <errno.h>
#include <unistd.h>

/* This is the obvious place to put elf_prstatus... */
#include <sys/procfs.h>

#include "sli.h"

#include "../VEX/priv/guest_generic_bb_to_IR.h"
#include "../VEX/priv/guest_amd64_defs.h"

class Mapping {
	const void *content;
	off_t size;
public:
	Mapping() : content(NULL) {}
	int init(const char *path);
	~Mapping() { if (content) munmap((void *)content, size); }
	template <typename t> const t *get(off_t offset, int nr = 1);
	const void *window(off_t offset, size_t size);
};

int
Mapping::init(const char *path)
{
	int fd = open(path, O_RDONLY);
	if (fd < 0)
		return -1;
	size = lseek(fd, 0, SEEK_END);
	if (size < 0) {
		close(fd);
		return -1;
	}
	size = (size + 4095) & ~4095ul;
	content = mmap(NULL, size, PROT_READ, MAP_SHARED,
		       fd, 0);
	close(fd);
	if (content == MAP_FAILED) {
		content = NULL;
		return -1;
	}
	return 0;
}

template <typename t> const t *
Mapping::get(off_t offset, int nr)
{
	if (offset < 0 || (off_t)(offset + sizeof(t) * nr) > size)
		return NULL;
	else
		return (const t *)((unsigned long)content + offset);
}

const void *
Mapping::window(off_t offset, size_t sz)
{
	if (offset < 0 || (off_t)(offset + sz) > size)
		return NULL;
	else
		return (const void *)((unsigned long)content + offset);
}

MachineState *
MachineState::readCoredump(const char *path)
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
	    eh->e_type != ET_CORE ||
	    eh->e_machine != EM_X86_64) {
		/* Whoops, not a core dump */
		errno = EINVAL;
		return NULL;
	}
	const Elf64_Phdr *phdrs = m.get<Elf64_Phdr>(eh->e_phoff, eh->e_phnum);
	if (!phdrs)
		return NULL;

	/* Bits of a MachineState:

	   -- threads vector
	   -- exitted flag
	   -- exit_status
	   -- nextTid
	   -- addressSpace
	   -- signalHandlers
	   -- nrEvents (XXX is this still needed?)
	*/

	AddressSpace *as = AddressSpace::initialAddressSpace(0); /* XXX don't know the BRK */
	MachineState *work = new MachineState();
	work->addressSpace = as;
	for (int p = 0; p < eh->e_phnum; p++) {
		if (phdrs[p].p_type == PT_LOAD) {
			/* Skip no-access segments.  Not entirely valid, but the best we can do. */
			if (phdrs[p].p_flags == 0)
				continue;

			printf("%d: type %x flags %x offset %lx vaddr %lx paddr %lx filesz %lx memsz %lx align %lx\n",
			       p,
			       phdrs[p].p_type,
			       phdrs[p].p_flags,
			       phdrs[p].p_offset,
			       phdrs[p].p_vaddr,
			       phdrs[p].p_paddr,
			       phdrs[p].p_filesz,
			       phdrs[p].p_memsz,
			       phdrs[p].p_align);
			if (phdrs[p].p_filesz > phdrs[p].p_memsz) {
				/* Huh? */
				return NULL;
			}
			as->allocateMemory(phdrs[p].p_vaddr,
					   phdrs[p].p_memsz,
					   VAMap::Protection(
						   phdrs[p].p_flags & PF_R,
						   phdrs[p].p_flags & PF_W,
						   phdrs[p].p_flags & PF_X));
			as->copyToClient(phdrs[p].p_vaddr,
					 phdrs[p].p_filesz,
					 m.window(phdrs[p].p_offset,
						  phdrs[p].p_filesz),
					 true);
		} else if (phdrs[p].p_type == PT_NOTE) {
			printf("Notes section\n");
			off_t off = phdrs[p].p_offset;
			off_t end = off + phdrs[p].p_filesz;
			const Elf64_Nhdr *note;
			while (off < (off_t)(end - sizeof(Elf64_Nhdr))) {
				note = m.get<Elf64_Nhdr>(off);
				if (!note)
					return NULL;
				if ((off_t)(off + ((note->n_namesz + 3) & ~3) + note->n_descsz + sizeof(*note)) >
				    end)
					return NULL;
				printf("Name sz %x, desc size %x, type %x, name %.*s\n",
				       note->n_namesz, note->n_descsz,
				       note->n_type,
				       note->n_namesz,
				       (const char *)(note + 1));
				if (note->n_type == NT_PRSTATUS) {
					/* This pretty much
					 * corresponds to a thread. */
					Thread *thr;
					thr = new Thread();
					if (note->n_descsz < sizeof(elf_prstatus))
						return NULL;
					const struct elf_prstatus *prs =
						(const struct elf_prstatus *)
						((unsigned long)note + sizeof(*note) +
						 ((note->n_namesz + 3) & ~3));
					const struct user_regs_struct *regs =
						(const struct user_regs_struct *)prs->pr_reg;
#define do_reg(linux_name, our_name)					\
					thr->regs.set_reg(REGISTER_IDX(our_name), \
							  regs-> linux_name)
					do_reg(r15, R15);
					do_reg(r14, R14);
					do_reg(r13, R13);
					do_reg(r12, R12);
					do_reg(r11, R11);
					do_reg(r10, R10);
					do_reg(r9, R9);
					do_reg(r8, R8);
					do_reg(rdi, RDI);
					do_reg(rsi, RSI);
					do_reg(rbp, RBP);
					do_reg(rsp, RSP);
					do_reg(rdx, RDX);
					do_reg(rcx, RCX);
					do_reg(rbx, RBX);
					do_reg(rax, RAX);
					do_reg(rip, RIP);

					thr->regs.set_reg(REGISTER_IDX(CC_OP), AMD64G_CC_OP_COPY);
					thr->regs.set_reg(REGISTER_IDX(CC_DEP1), regs->eflags);
					thr->regs.set_reg(REGISTER_IDX(CC_DEP2), 0);
#undef do_reg

					work->registerThread(thr);

					printf("Thread %d has rip %lx\n",
					       thr->tid._tid(),
					       thr->regs.rip());
				}
				off += sizeof(*note) +
					((note->n_namesz + 3) & ~3) +
					note->n_descsz;
			}
		}
	}

	return work;
}
