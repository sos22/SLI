#include "sli.h"

#include "raw_types.hpp"

#include <assert.h>
#include <err.h>

#define PRIVATE_RIP_FLAG 0x80000000

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

