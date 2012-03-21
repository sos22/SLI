#include "sli.h"

struct tag_rip {
	unsigned long rip;
	std::vector<unsigned long> stack;
};

struct tag_entry {
	std::vector<tag_rip> loads;
	std::vector<tag_rip> stores;
};

static struct tag_rip
read_rip_entry(FILE *f)
{
	struct tag_rip work;
	unsigned nr_entries;
	if (fread(&work.rip, sizeof(work.rip), 1, f) < 1 ||
	    fread(&nr_entries, sizeof(nr_entries), 1, f) < 1)
		err(1, "reading rip entry header from input");
	work.stack.reserve(nr_entries);
	for (unsigned x = 0; x < nr_entries; x++) {
		unsigned long e;
		if (fread(&e, sizeof(e), 1, f) < 1)
			err(1, "reading rip entry %d/%d from input", x, nr_entries);
		work.stack.push_back(e);
	}
	return work;
}

static struct tag_entry *
read_tag_entry(FILE *f)
{
	struct {
		int nr_loads;
		int nr_stores;
	} hdr;
	if (fread(&hdr, sizeof(hdr), 1, f) < 1) {
		if (ferror(f))
			err(1, "reading input");
		assert(feof(f));
		return NULL;
	}

	struct tag_entry *work = new tag_entry();
	work->loads.reserve(hdr.nr_loads);
	work->stores.reserve(hdr.nr_stores);
	for (int i = 0; i < hdr.nr_loads; i++)
		work->loads.push_back(read_rip_entry(f));
	for (int i = 0; i < hdr.nr_stores; i++)
		work->stores.push_back(read_rip_entry(f));
	return work;
}

static void
canonicalise_entry_set(std::vector<tag_rip> &set, AddressSpace *as)
{
	for (auto it = set.begin();
	     it != set.end();
		) {
		unsigned long rip = it->rip & ~(1ul << 63);
		if (!as->isReadable(rip, 1)) {
			it = set.erase(it);
		} else {
			for (auto it2 = it->stack.begin();
			     it2 != it->stack.end();
				) {
				if (!as->isReadable(*it2, 1)) {
					it2 = it->stack.erase(it2);
				} else {
					it2++;
				}
			}
			it++;
		}
	}
}

static void
canonicalise_tag_entry(struct tag_entry *te, AddressSpace *as)
{
	canonicalise_entry_set(te->loads, as);
	canonicalise_entry_set(te->stores, as);
}

static void
write_rip_entry(const tag_rip &entry, FILE *output)
{
	fwrite(&entry.rip, sizeof(entry.rip), 1, output);
	unsigned nr_entries = entry.stack.size();
	fwrite(&nr_entries, sizeof(nr_entries), 1, output);
	for (auto it = entry.stack.begin(); it != entry.stack.end(); it++) {
		unsigned long e = *it;
		fwrite(&e, sizeof(e), 1, output);
	}
}

static void
write_tag_entry(const struct tag_entry *te, FILE *output)
{
	if (te->loads.size() == 0 &&
	    te->stores.size() == 0)
		return;
	struct {
		int nr_loads;
		int nr_stores;
	} hdr;
	hdr.nr_loads = te->loads.size();
	hdr.nr_stores = te->stores.size();
	fwrite(&hdr, sizeof(hdr), 1, output);
	for (auto it = te->loads.begin(); it != te->loads.end(); it++)
		write_rip_entry(*it, output);
	for (auto it = te->stores.begin(); it != te->stores.end(); it++)
		write_rip_entry(*it, output);
}

int
main(int argc, char *argv[])
{
	init_sli();

	if (argc != 4)
		errx(1, "need three arguments, the binary, the raw type file and the output file");

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));

	FILE *inp = fopen(argv[2], "r");
	if (!inp)
		err(1, "opening %s", argv[2]);
	FILE *output = fopen(argv[3], "w");
	if (!output)
		err(1, "opening %s", argv[3]);

	while (1) {
		struct tag_entry *te = read_tag_entry(inp);
		if (!te)
			break;
		canonicalise_tag_entry(te, ms->addressSpace);
		write_tag_entry(te, output);
		delete te;
	}

	if (fclose(output) == EOF)
		err(1, "closing output file");
	return 0;  
}
