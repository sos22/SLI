#include "sli.h"

#include "libvex_parse.h"

#include "typesdb.hpp"
#include "types_db.hpp"

void
TypesDb::findOffsets(const DynAnalysisRip &vr, std::vector<unsigned long> &out) const
{
	unsigned long hash = vr.hash();
	const struct hash_head *heads = mapping.get<hash_head>(0, NR_HASH_HEADS);
	const struct hash_head *head = &heads[hash % NR_HASH_HEADS];

	unsigned long he_offset;
	const hash_entry *he;
	he = NULL;
	for (he_offset = head->offset; he_offset != 0; ) {
		he = mapping.get<hash_entry>(he_offset);
		if (he->for_rip(vr))
			break;
		he_offset = he->chain;
	}
	if (he_offset == 0) {
		/* Nothing found */
		return;
	}

	unsigned long ol_offset;
	const offsets_list *ol;
	for (ol_offset = he->offsets_start;
	     ol_offset != 0;
		) {
		ol = mapping.get<offsets_list>(ol_offset);
		for (unsigned x = 0; x < ol->nr_entries; x++)
			out.push_back(ol->offsets[x]);
		ol_offset = ol->chain;
	}
}

TypesDb::all_instrs_iterator *
TypesDb::enumerateAllInstructions() const
{
	return new all_instrs_iterator(this);
}

__types_db_instr_iterator::__types_db_instr_iterator(const TypesDb *_owner)
	: owner(_owner), have_finished(false)
{
	const struct hash_head *heads = owner->mapping.get<hash_head>(0, NR_HASH_HEADS);
		for (bucket_index = 0; bucket_index < NR_HASH_HEADS; bucket_index++) {
		const struct hash_head *head = &heads[bucket_index];
		offset = head->offset;
		if (offset != 0)
			return;
	}
	/* Index is empty? */
	have_finished = true;
}

void
__types_db_instr_iterator::advance(void)
{
	const hash_entry *he;
	he = owner->mapping.get<hash_entry>(offset);
	offset = he->chain;
	if (offset != 0)
		return;

	/* finished the bucket, move on to next one. */
	bucket_index++;
	const struct hash_head *heads = owner->mapping.get<hash_head>(0, NR_HASH_HEADS);
	for (; bucket_index < NR_HASH_HEADS; bucket_index++) {
		const struct hash_head *head = &heads[bucket_index];
		offset = head->offset;
		if (offset != 0)
			return;
	}
	/* Index is empty? */
	have_finished = true;
}

void
__types_db_instr_iterator::fetch(DynAnalysisRip *out) const
{
	const struct hash_entry *he = owner->mapping.get<hash_entry>(offset);
	out->nr_rips = he->nr_rips;
	if (out->nr_rips > DynAnalysisRip::DATABASE_RIP_DEPTH)
		out->nr_rips = DynAnalysisRip::DATABASE_RIP_DEPTH;
	for (int x = 0; x < out->nr_rips; x++)
		out->rips[out->nr_rips - x - 1] = he->rips[he->nr_rips - x - 1];
	out->changed();
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

struct vexrip_hdr {
	unsigned long rip;
	unsigned nr_entries;
};

void
TypesDb::parse_vexrip_canon(DynAnalysisRip *out, const Mapping &mapping, unsigned long offset, bool *is_private, unsigned long *sz)
{
	const struct vexrip_hdr *hdr = mapping.get<vexrip_hdr>(offset);
	if (!hdr)
		err(1, "reading vexrip header");

	/* sizeof(vexrip_hdr) would be 12 if we'd properly packed
	 * vexrip_hdr. :( */
	*sz = 12 + sizeof(unsigned long) * hdr->nr_entries;

	unsigned long rip = hdr->rip;
	if (rip & (1ul << 63)) {
		*is_private = true;
		rip &= ~(1ul << 63);
	} else {
		*is_private = false;
	}

	const unsigned long *body = mapping.get<unsigned long>(offset + 12, hdr->nr_entries);
	out->nr_rips = hdr->nr_entries + 1;
	if (out->nr_rips > DynAnalysisRip::DATABASE_RIP_DEPTH - 1)
		out->nr_rips = DynAnalysisRip::DATABASE_RIP_DEPTH;
	for (int x = 0; x < out->nr_rips - 1; x++)
		out->rips[x] = body[x + hdr->nr_entries - out->nr_rips + 1];
	out->rips[out->nr_rips - 1] = rip;
}

void
TypesDb::read_vexrip_canon(FILE *f, DynAnalysisRip *out, bool *is_private)
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
		stack.push_back(a);
	}
	if (rip & (1ul << 63)) {
		*is_private = true;
		rip &= ~(1ul << 63);
	} else {
		*is_private = false;
	}
	stack.push_back(rip);

	out->nr_rips = stack.size();
	if (out->nr_rips > DynAnalysisRip::DATABASE_RIP_DEPTH)
		out->nr_rips = DynAnalysisRip::DATABASE_RIP_DEPTH;
	for (int x = 0; x < out->nr_rips; x++)
		out->rips[out->nr_rips - x - 1] = stack[stack.size() - x - 1];
}

TypesDb::read_vexrip_res
TypesDb::read_vexrip_noncanon(FILE *f, DynAnalysisRip *out, AddressSpace *as, bool *is_private)
{
	unsigned long rip;
	unsigned nr_entries;
	std::vector<unsigned long> stack;

	if (fread(&rip, sizeof(rip), 1, f) != 1 ||
	    fread(&nr_entries, sizeof(nr_entries), 1, f) != 1)
		return read_vexrip_error;
	stack.reserve(nr_entries);
	for (unsigned x = 0; x < nr_entries; x++) {
		unsigned long a;
		if (fread(&a, sizeof(a), 1, f) != 1)
			return read_vexrip_error;
		if (as->isReadable(a, 1))
			stack.push_back(a);
	}
	if (rip & (1ul << 63)) {
		*is_private = true;
		rip &= ~(1ul << 63);
	} else {
		*is_private = false;
	}
	read_vexrip_res res;
	if (as->isReadable(rip, 1)) {
		stack.push_back(rip);
		res = read_vexrip_take;
	} else {
		res = read_vexrip_skip;
	}
	
	out->nr_rips = stack.size();
	if (out->nr_rips > DynAnalysisRip::DATABASE_RIP_DEPTH)
		out->nr_rips = DynAnalysisRip::DATABASE_RIP_DEPTH;
	for (int x = 0; x < out->nr_rips; x++)
		out->rips[out->nr_rips - x - 1] = stack[stack.size() - x - 1];
	return res;
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
