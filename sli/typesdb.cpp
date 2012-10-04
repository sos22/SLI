#include "sli.h"

#include "libvex_parse.h"

#include "typesdb.hpp"
#include "types_db.hpp"

#define PRIVATE_RIP_FLAG 0x80000000

TypesDb::all_instrs_iterator *
TypesDb::enumerateAllInstructions() const
{
	return new all_instrs_iterator(this, indexes.back().first, indexes.back().second);
}

__types_db_instr_iterator::__types_db_instr_iterator(const TypesDb *_owner,
						     unsigned long _start,
						     unsigned long _end)
	: start(_start), end(_end), owner(_owner)
{
}

void
__types_db_instr_iterator::advance(void)
{
	unsigned nr_entries = *owner->mapping.get<unsigned>(start);
	nr_entries &= ~PRIVATE_RIP_FLAG;
	start += 12;
	start += nr_entries * 8;
}

static unsigned long
parse_db_rip(const void *start, DynAnalysisRip *out, bool *is_private)
{
	int nr_entries = *(unsigned*)start;
	if (is_private) {
		if (nr_entries & PRIVATE_RIP_FLAG)
			*is_private = true;
		else
			*is_private = false;
	}
	nr_entries &= ~PRIVATE_RIP_FLAG;
	out->nr_rips = nr_entries;
	if (nr_entries > DynAnalysisRip::DATABASE_RIP_DEPTH)
		out->nr_rips = DynAnalysisRip::DATABASE_RIP_DEPTH;
	for (int x = 0; x < out->nr_rips; x++)
		out->rips[x] = *(unsigned long *)((unsigned long)start + 4 + x * 8);
	out->changed();
	return 4 + 8 * nr_entries;
}

void
__types_db_instr_iterator::fetch(DynAnalysisRip *out) const
{
	parse_db_rip(owner->mapping.get<char>(start), out, NULL);
}

unsigned long
TypesDb::nrDistinctInstructions() const
{
	auto it = enumerateAllInstructions();
	unsigned long res = 0;
	while (!it->finished()) {
		res++;
		it->advance();
	}
	return res;
}

bool
TypesDb::ripPresent(const DynAnalysisRip &vr) const
{
	unsigned long o = index_lookup(vr);
	if (o == 0)
		return false;
	else
		return true;
}


bool
TypesDb::lookupEntry(const DynAnalysisRip &dr,
		     std::vector<types_entry> &loads,
		     std::vector<types_entry> &stores)
{
	unsigned long o = index_lookup(dr);
	if (o == 0)
		return false;
	unsigned nr_loads = *mapping.get<unsigned>(o);
	unsigned nr_stores = *mapping.get<unsigned>(o + 4);
	o += 8;
	for (unsigned x = 0; x < nr_loads; x++) {
		types_entry te;
		o += parse_db_rip(mapping.get<char>(o), &te.rip, &te.is_private);
		loads.push_back(te);
	}
	for (unsigned x = 0; x < nr_stores; x++) {
		types_entry te;
		o += parse_db_rip(mapping.get<char>(o), &te.rip, &te.is_private);
		stores.push_back(te);
	}
	return true;
}

unsigned long
TypesDb::index_lookup(const DynAnalysisRip &dr) const
{
	unsigned long idx_start = indexes[0].first;
	unsigned long idx_end = indexes[0].second;
	for (unsigned idx = 0; idx < indexes.size() - 1; idx++) {
		unsigned long o = idx_start;
		DynAnalysisRip idx_dr;
		unsigned long sz;
		sz = parse_db_rip(mapping.get<char>(idx_start), &idx_dr, NULL);
		if (idx_dr > dr) {
			idx_start = indexes[idx + 1].first;
			idx_end = *mapping.get<unsigned long>(idx_start + sz);
			continue;
		}
		bool s = false;
		while (o < idx_end) {
			sz = parse_db_rip(mapping.get<char>(o), &idx_dr, NULL);
			if (idx_dr > dr) {
				idx_end = *mapping.get<unsigned long>(o + sz);
				s = true;
				break;
			}
			idx_start = *mapping.get<unsigned long>(o + sz);
			o += sz + 8;
		}
		if (!s) {
			assert(o == idx_end);
			idx_end = indexes[idx+1].second;
		}
	}
	unsigned long o = idx_start;
	while (1) {
		if (o >= idx_end) {
			assert(o == idx_end);
			return 0;
		}
		DynAnalysisRip idx_dr;
		unsigned long sz;
		sz = parse_db_rip(mapping.get<char>(o), &idx_dr, NULL);
		if (idx_dr == dr)
			return *mapping.get<unsigned long>(o + sz);
		if (idx_dr > dr)
			return 0;
		o += sz + 8;
	}
}

void
TypesDb::read_index_shape()
{
	unsigned nr_levels = *mapping.get<unsigned>(0);
	printf("Type index has %d levels.\n", nr_levels);
	for (unsigned x = 0; x < nr_levels; x++) {
		std::pair<unsigned long, unsigned long> entry;
		entry.first = *mapping.get<unsigned long>(4 + x * 16);
		entry.second = *mapping.get<unsigned long>(12 + x * 16);
		printf("\tLevel %d: %lx -> %lx\n", x, entry.first, entry.second);
		indexes.push_back(entry);
	}
}

bool
parseDynAnalysisRip(DynAnalysisRip *out, const char *inp, const char **suffix)
{
	if (!parseThisString("DynRip[", inp, &inp))
		return false;

	DynAnalysisRip work;
	while (1) {
		if (parseThisChar(']', inp, suffix)) {
			*out = work;
			return true;
		}
		if (work.nr_rips == DynAnalysisRip::DATABASE_RIP_DEPTH)
			return false;
		unsigned long x;
		if (!parseHexUlong(&x, inp, &inp))
			return false;
		work.rips[work.nr_rips] = x;
		work.nr_rips++;
		parseThisString(", ", inp, &inp);
	}
}
