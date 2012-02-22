#include <sys/types.h>
#include <sys/fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <err.h>
#include <stdio.h>
#include <unistd.h>

#include "sli.h"

#include "types_db.hpp"

#define PAGE_SIZE (4096ul)

static bool
read_rip(FILE *f, bool *is_private, AddressSpace *as, VexRip *out)
{
	unsigned long rip;
	unsigned nr_entries;
	std::vector<unsigned long> stack;

	if (fread(&rip, sizeof(rip), 1, f) != 1 ||
	    fread(&nr_entries, sizeof(nr_entries), 1, f) != 1)
		err(1, "reading input");
	stack.reserve(nr_entries);
	for (unsigned x = 0; x < nr_entries; x++) {
		unsigned long a;
		if (fread(&a, sizeof(a), 1, f) != 1)
			err(1, "reading input");
		if (as->isReadable(a, 1))
			stack.push_back(a);
	}
	if (rip & (1ul << 63)) {
		*is_private = true;
		rip &= ~(1ul << 63);
	} else {
		*is_private = false;
	}
	if (!as->isReadable(rip, 1))
		return false;
	stack.push_back(rip);
	*out = VexRip(stack);
	return true;
}

struct tag_hdr {
	int nr_loads;
	int nr_stores;	
};

struct mapped_file {
	int fd;
	unsigned long used_size;
	unsigned long on_disk_size;
	void *base;

	unsigned long extend(unsigned long amt) {
		unsigned long old_size = used_size;
		unsigned long old_on_disk_size = on_disk_size;
		used_size += amt;
		if (used_size > on_disk_size) {
			on_disk_size = (used_size + (PAGE_SIZE - 1)) & ~(PAGE_SIZE - 1);
			if (ftruncate(fd, on_disk_size) == -1)
				err(1, "extending mapped file");
			void *new_map;
			/* do mmap then munmap so as to force the base
			   to change, which makes some classes of bugs
			   much more obvious. */
			new_map = mmap(NULL, on_disk_size, PROT_READ|PROT_WRITE,
				       MAP_SHARED, fd, 0);
			if (new_map == MAP_FAILED)
				err(1, "mapping extended file");
			munmap(base, old_on_disk_size);
			base = new_map;
		}
		return old_size;
	}

	mapped_file(const char *fname, int flags, int mode, unsigned long size) {
		fd = open(fname, flags, mode);
		if (fd < 0)
			err(1, "opening %s", fname);
		used_size = size;
		on_disk_size = (size + (PAGE_SIZE - 1)) & ~(PAGE_SIZE - 1);
		if (ftruncate(fd, on_disk_size) == -1)
			err(1, "setting size of %s", fname);
		base = mmap(NULL, on_disk_size, PROT_READ|PROT_WRITE, MAP_SHARED,
			    fd, 0);
		if (base == MAP_FAILED)
			err(1, "mapping %s", fname);
	}
	~mapped_file() {
		munmap(base, on_disk_size);
		close(fd);
	}
};

struct tag_file_foreach_closure {
	virtual void operator()(const VexRip &vr,
				unsigned long offset,
				bool is_load,
				bool is_private) = 0;
};
static void
tag_file_foreach(const char *fname, AddressSpace *as, tag_file_foreach_closure &consumer)
{
	FILE *inp = fopen(fname, "r");
	if (!inp)
		err(1, "opening %s", fname);

	while (1) {
		struct tag_hdr hdr;
		long offset = ftell(inp);
		if (fread(&hdr, sizeof(hdr), 1, inp) < 1) {
			if (ferror(inp))
				err(1, "reading input %s", fname);
			assert(feof(inp));
			break;
		}
		struct {
			FILE *inp;
			tag_file_foreach_closure *consumer;
			unsigned long offset;
			AddressSpace *as;
			void operator()(int nr_items, bool is_load) {
				for (int x = 0; x < nr_items; x++) {
					VexRip rip;
					bool is_private;
					if (read_rip(inp, &is_private, as, &rip))
						(*consumer)(rip, offset, true, is_private);
				}
			}
		} doit = {inp, &consumer, offset, as};
		doit(hdr.nr_loads, true);
		doit(hdr.nr_stores, false);
	}
	fclose(inp);
}

static void
insert_rip_into_output(struct mapped_file *output, const VexRip &vr, unsigned long offset)
{
	unsigned long hash = vr.hash();
	struct hash_head *heads = (struct hash_head *)output->base;
	struct hash_head *head = &heads[hash % NR_HASH_HEADS];

	unsigned long he_offset;
	unsigned long prev_he_offset;
	struct hash_entry *he;

	prev_he_offset = 0;
	he = NULL;
	/* Find the hash entry for this vr */
	for (he_offset = head->offset;
	     he_offset != 0;
		) {
		he = (struct hash_entry *)((unsigned long)output->base + he_offset);
		if (he->for_rip(vr)) {
			/* This is the one */
			break;
		}
		prev_he_offset = he_offset;
		he_offset = he->chain;
	}
	if (he_offset == 0) {
		/* Not currently present -> allocate it. */
		he_offset = output->extend(hash_entry::size_for(vr));
		if (prev_he_offset != 0) {
			he = (struct hash_entry *)((unsigned long)output->base + prev_he_offset);
			he->chain = he_offset;
		} else {
			heads = (struct hash_head *)output->base;
			head = &heads[hash % NR_HASH_HEADS];
			head->offset = he_offset;
		}
		he = (struct hash_entry *)((unsigned long)output->base + he_offset);
		he->initialise(vr);
		unsigned long new_offset = output->extend(offsets_list::default_size);
		he = (struct hash_entry *)((unsigned long)output->base + he_offset);
		he->offsets_start = new_offset;
		struct offsets_list *offset_list;
		offset_list = (struct offsets_list *)((unsigned long)output->base + he->offsets_start);
		offset_list->initialise();
	}

	unsigned long offsets_list_offset, prev_offsets_list_offset;
	struct offsets_list *offset_list = NULL;
	prev_offsets_list_offset = 0; /* shut compiler up */
	for (offsets_list_offset = he->offsets_start;
	     offsets_list_offset != 0;
		) {
		offset_list = (struct offsets_list *)((unsigned long)output->base + offsets_list_offset);
		for (unsigned x = 0; x < offset_list->nr_entries; x++) {
			if (offset_list->offsets[x] == offset) {
				/* It was already present -> get out */
				return;
			}
		}
		prev_offsets_list_offset = offsets_list_offset;
		offsets_list_offset = offset_list->chain;
	}

	assert(offset_list != NULL);
	assert(prev_offsets_list_offset != 0);

	if (offset_list->nr_entries == offset_list->nr_entries_allocated) {
		unsigned long ptr;
		ptr = output->extend(offsets_list::default_size);
		offset_list = (struct offsets_list *)((unsigned long)output->base + prev_offsets_list_offset);
		offset_list->chain = ptr;
		offset_list = (struct offsets_list *)((unsigned long)output->base + ptr);
		offset_list->initialise();
		offsets_list_offset = ptr;
	} else {
		offsets_list_offset = prev_offsets_list_offset;
	}
	offset_list->push_back(offset);
}

int
main(int argc, char *argv[])
{
	init_sli();

	if (argc != 4)
		errx(1, "need three arguments, the binary, the raw type file and the output file");

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));

	mapped_file output(argv[3], O_RDWR|O_CREAT|O_EXCL, 0666, NR_HASH_HEADS * sizeof(struct hash_head));

	struct _ : public tag_file_foreach_closure {
		mapped_file *output;
		void operator()(const VexRip &vr, unsigned long offset, bool, bool) {
			insert_rip_into_output(output, vr, offset);
		}
		_(mapped_file *_output)
			: output(_output)
		{}
	} doit = { &output };
	tag_file_foreach(argv[2], ms->addressSpace, doit);

	return 0;
}
