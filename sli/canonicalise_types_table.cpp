/* This converts the types table from the format generated by the
   dynamic analysis into the one which is used by the oracle.  That
   means two things:

   1) Remove anything which refers to stuff outside of the main
      binary.
   2) Sort and index the table.
*/
#include "sli.h"

#include "raw_types.hpp"

#define SECOND_LEVEL_IDX_INTERVAL 4096

static void
copy_rip(FILE *input, sane_write_file &output)
{
	rip_t r;
	r.read(input, NULL, false);
	r.write(output);
}

static void
copy_record(FILE *input, sane_write_file &output)
{
	int nr_loads, nr_stores;
	if (fread(&nr_loads, sizeof(nr_loads), 1, input) != 1 ||
	    fread(&nr_stores, sizeof(nr_stores), 1, input) != 1)
		err(1, "reading in copy_record");
	output.write(nr_loads);
	output.write(nr_stores);
	for (int i = 0; i < nr_loads; i++)
		copy_rip(input, output);
	for (int i = 0; i < nr_stores; i++)
		copy_rip(input, output);
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
	if (fread(&offset, sizeof(offset), 1, input) != 1)
		err(1, "reading input");
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
