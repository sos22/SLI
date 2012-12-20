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

static void
findPlt(ElfData *ed, Mapping &m, const Elf64_Ehdr *eh)
{
	const Elf64_Shdr *shdrs = m.get<Elf64_Shdr>(eh->e_shoff, eh->e_shnum);
	assert(shdrs);
	assert(eh->e_shstrndx < eh->e_shnum);
	const Elf64_Shdr *shstr_shdr = &shdrs[eh->e_shstrndx];
	const char *section_strings = m.get<char>(shstr_shdr->sh_offset, shstr_shdr->sh_size);
	assert(section_strings);
	const Elf64_Shdr *plt_shdr = NULL;
	const Elf64_Shdr *rela_shdr = NULL;
	for (unsigned idx = 0; idx < eh->e_shnum; idx++) {
		const Elf64_Shdr *shdr = &shdrs[idx];
		if (!shdr->sh_name || shdr->sh_name >= shstr_shdr->sh_size)
			continue;
		if (!strncmp(section_strings + shdr->sh_name, ".plt", shstr_shdr->sh_size - shdr->sh_name)) {
			assert(!plt_shdr);
			plt_shdr = shdr;
		}
		if (!strncmp(section_strings + shdr->sh_name, ".rela.plt", shstr_shdr->sh_size - shdr->sh_name)) {
			assert(!rela_shdr);
			rela_shdr = shdr;
		}
	}
	assert(plt_shdr);
	ed->plt_start = plt_shdr->sh_addr;
	ed->plt_end = ed->plt_start + plt_shdr->sh_size;
	assert(rela_shdr);
	assert(rela_shdr->sh_link);
	const Elf64_Shdr *dynsym_shdr = &shdrs[rela_shdr->sh_link];
	assert(dynsym_shdr->sh_link);
	const Elf64_Shdr *dynstr_shdr = &shdrs[dynsym_shdr->sh_link];
	const char *symbol_strings = m.get<char>(dynstr_shdr->sh_offset, dynstr_shdr->sh_size);
	assert(symbol_strings);
	const Elf64_Sym *symbols = m.get<Elf64_Sym>(dynsym_shdr->sh_offset, dynsym_shdr->sh_size);
	assert(symbols);
	const Elf64_Rela *relas = m.get<Elf64_Rela>(rela_shdr->sh_offset, rela_shdr->sh_size);
	assert(relas);
	std::vector<std::pair<unsigned, char *> > symbol_table;
	for (unsigned idx = 0; idx < rela_shdr->sh_size / sizeof(Elf64_Rela); idx++) {
		const Elf64_Rela *rela = &relas[idx];
		if (ELF64_R_TYPE(rela->r_info) != R_X86_64_JUMP_SLOT)
			continue;
		unsigned sym_idx = ELF64_R_SYM(rela->r_info);
		assert(sym_idx);
		assert(sym_idx < dynsym_shdr->sh_size / sizeof(symbols[0]));
		const Elf64_Sym *sym = &symbols[sym_idx];
		const char *name = symbol_strings + sym->st_name;
		size_t l = strnlen(name, dynstr_shdr->sh_size - sym->st_name);
		assert(l != dynstr_shdr->sh_size - sym->st_name);
		char *n = (char *)malloc(l + 1);
		memcpy(n, name, l);
		n[l] = 0;
		symbol_table.push_back(std::pair<unsigned, char *>(idx, n));
	}
	if (symbol_table.empty()) {
		printf("No symbols?\n");
		abort();
	}
	/* This is easier if the symbol table is sorted */
	std::sort(symbol_table.begin(), symbol_table.end());

	/* Should be no duplicate indexes. */
	auto it1 = symbol_table.begin();
	auto it2 = it1 + 1;
	while (it2 != symbol_table.end()) {
		assert(it1->first != it2->first);
		it1++;
		it2++;
	}

	ed->plt_symbol_names = symbol_table;
}

const char *
ElfData::lookupPltSymbol(unsigned idx) const
{
	int probe = idx;
	if (probe >= (int)plt_symbol_names.size())
		probe = 0;
	if (plt_symbol_names[probe].first == idx)
		return plt_symbol_names[probe].second;
	int delta;
	if (plt_symbol_names[probe].first > idx)
		delta = -1;
	else
		delta = 1;
	while (probe >= 0 && probe < (int)plt_symbol_names.size())
		if (plt_symbol_names[probe].first == idx)
			return plt_symbol_names[probe].second;
	return NULL;
}

unsigned long
ElfData::getPltAddress(AddressSpace *as, const char *name) const
{
	int idx = -1;
	for (auto it = plt_symbol_names.begin(); it != plt_symbol_names.end(); it++) {
		if (!strcmp(name, it->second)) {
			idx = it->first;
			break;
		}
	}
	if (idx == -1)
		return 0;
	for (unsigned long res = plt_start; res < plt_end; res += 16)
		if (as->fetch<int>(res + 7) == idx)
			return res;
	return -1;
}

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

	AddressSpace *as = AddressSpace::initialAddressSpace();
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
					  phdrs[p].p_filesz));
	}

	ElfData *ed = new ElfData();
	findPlt(ed, m, eh);
	work->elfData = ed;
	
	Thread *thr = new Thread();
	thr->regs.set_reg(REGISTER_IDX(RIP), eh->e_entry);

	/* Cunning hack: setting the initial value of RCX to one,
	   rather than zero, means that rep movs instructions take at
	   least one step, which in turn means that we generate memory
	   access events for them when trying to find proximal
	   causes. */
	thr->regs.set_reg(REGISTER_IDX(RCX), 1);

	work->registerThread(thr);
	return work;
}
