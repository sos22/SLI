/* This converts the types table from the format generated by the
   dynamic analysis into the one which is used by the oracle.  That
   means two things:

   1) Remove anything which refers to stuff outside of the main
      binary.
   2) Sort and index the table.
*/
#include "sli.h"

#include "raw_types.hpp"

#define PRIVATE_RIP_FLAG 0x80000000
#define SECOND_LEVEL_IDX_INTERVAL 4096

bool
rip_t::read(FILE *f, AddressSpace *as)
{
	unsigned nr_items;
	if (fread(&nr_items, sizeof(nr_items), 1, f) != 1)
		errx(1, "input truncated");
	assert(nr_items < 1000000);
	unsigned long content[nr_items];
	if (fread(content, sizeof(content[0]), nr_items, f) != nr_items)
		errx(1, "input truncated");
	is_private = 0;
	if (content[nr_items - 1] & (1ul << 63)) {
		is_private = 1;
		content[nr_items - 1] &= ~(1ul << 63);
	}
	for (unsigned x = 0; x < nr_items; x++)
		if (!as || as->isReadable(content[x], 1))
			stack.push_back(content[x]);
	if (as && !as->isReadable(content[nr_items - 1], 1))
		return false;
	return true;
}


bool
input_record::read(FILE *f, AddressSpace *as)
{
	int nr_loads, nr_stores;
	bool res;
	if (fread(&nr_loads, sizeof(nr_loads), 1, f) != 1)
		return false;
	fread(&nr_stores, sizeof(nr_stores), 1, f);
	res = rip.read(f, as);
	for (int i = 0; i < nr_loads; i++) {
		rip_t r;
		if (r.read(f, as))
			loads.push_back(r);
	}
	for (int i = 0; i < nr_stores; i++) {
		rip_t r;
		if (r.read(f, as))
			stores.push_back(r);
	}
	if (loads.empty() && stores.empty())
		return false;
	return res;
}

void
input_database::read(FILE *f, AddressSpace *as)
{
	while (1) {
		struct input_record ir;
		if (ir.read(f, as)) {
			content.push_back(ir);
		} else if (feof(f)) {
			break;
		} else if (ferror(f)) {
			err(1, "reading input");
		}
	}
}

void
rip_t::write(sane_write_file &output) const
{
	unsigned nr_entries = stack.size();
	if (is_private)
		nr_entries |= PRIVATE_RIP_FLAG;
	output.write(nr_entries);
	for (auto it = stack.begin(); it != stack.end(); it++)
		output.write(*it);
}

void
input_record::write(sane_write_file &output) const
{
	int nr_loads, nr_stores;
	nr_loads = loads.size();
	nr_stores = stores.size();
	output.write(nr_loads);
	output.write(nr_stores);
	for (auto it = loads.begin(); it != loads.end(); it++)
		it->write(output);
	for (auto it = stores.begin(); it != stores.end(); it++)
		it->write(output);
}

static void
copy_rip(FILE *input, sane_write_file &output)
{
	rip_t r;
	r.read(input, NULL);
	r.write(output);
}

static void
copy_record(FILE *input, sane_write_file &output)
{
	input_record ir;
	ir.read(input);
	ir.write(output);
}

static void
add_index_entry(const rip_t &rip, unsigned long offset, sane_write_file &f)
{
	rip.write(f);
	f.write(offset);
}

static void
rewrite_index_entry(FILE *input, sane_write_file &output, unsigned long delta)
{
	copy_rip(input, output);
	unsigned long offset;
	fread(&offset, sizeof(offset), 1, input);
	offset += delta;
	output.write(offset);
}

static void
write_index(sane_write_file &output,
	    const std::vector<std::pair<rip_t, unsigned long> > idx,
	    std::vector<std::pair<rip_t, unsigned long> > &idx_next_level,
	    std::vector<std::pair<unsigned long, unsigned long> > &regions)
{
	unsigned long idx_start = output.ftell();
	unsigned long last_idx2 = idx_start;
	
	for (auto it = idx.begin(); it != idx.end(); it++) {
		if (output.ftell() >= last_idx2 + SECOND_LEVEL_IDX_INTERVAL) {
			idx_next_level.push_back(std::pair<rip_t, unsigned long>(it->first, output.ftell() - idx_start));
			last_idx2 = output.ftell();
		}
		add_index_entry(it->first, it->second, output);
	}
	regions.push_back(std::pair<unsigned long, unsigned long>(idx_start, output.ftell()));
}

int
main(int argc, char *argv[])
{
	init_sli();

	if (argc != 4)
		errx(1, "need three arguments, the binary, the raw type file and the output file");

	const char *binary = argv[1];
	const char *input_fname = argv[2];
	const char *output_fname = argv[3];

	VexPtr<MachineState> ms(MachineState::readELFExec(binary));

	FILE *inp = fopen(input_fname, "r");
	if (!inp)
		err(1, "opening %s", input_fname);
	sane_write_file tmp(tmpfile());

	input_database input;
	input.read(inp, ms->addressSpace);
	fclose(inp);
	std::sort(input.content.begin(), input.content.end());

	std::vector<std::pair<rip_t, unsigned long> > idx;
	for (auto it = input.content.begin(); it != input.content.end(); it++) {
		idx.push_back(std::pair<rip_t, unsigned long>(it->rip, tmp.ftell()));
		it->write(tmp);
	}

	std::vector<std::pair<unsigned long, unsigned long> > indexes;

	std::vector<std::pair<rip_t, unsigned long> > idx2;
	write_index(tmp, idx, idx2, indexes);
	while (idx2.size() > 10) {
		idx = idx2;
		idx2.clear();
		write_index(tmp, idx, idx2, indexes);
	}

	sane_write_file output(fopen(output_fname, "w"));
	if (!output.f)
		err(1, "opening output");

	/* Now write the final thing by reversing the order of the
	 * indexes, so that the root index is at the front of the
	 * file. */

	/* Start with the index shape. */
	unsigned long o = 4 + 16 * indexes.size();
	{
		unsigned nr_indexes = indexes.size();
		output.write(nr_indexes);
		for (auto it = indexes.rbegin(); it != indexes.rend(); it++) {
			unsigned long old_begin = it->first;
			unsigned long old_end = it->second;
			unsigned long new_begin = o;
			unsigned long new_end = new_begin + old_end - old_begin;
			o = new_end;
			output.write(new_begin);
			output.write(new_end);
		}
	}
	o = 4 + 16 * indexes.size();
	for (auto it = indexes.rbegin(); it != indexes.rend(); it++) {
		unsigned long begin = it->first;
		unsigned long end = it->second;
		o += end - begin;
		printf("Index %lx -> %lx, o %lx\n", begin, end, o);
		fseek(tmp.f, begin, SEEK_SET);
		while (ftell(tmp.f) < (long)end)
			rewrite_index_entry(tmp.f, output, o);
	}
	/* Now write out the actual content of the file */
	fseek(tmp.f, 0, SEEK_SET);
	while (ftell(tmp.f) < (long)indexes[0].first)
		copy_record(tmp.f, output);

	if (fclose(output.f) == EOF)
		err(1, "closing output file");

	return 0;  
}
