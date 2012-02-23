#include "sli.h"

#include "typesdb.hpp"
#include "types_db.hpp"

void
TypesDb::findOffsets(const VexRip &vr, std::vector<unsigned long> &out) const
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
__types_db_instr_iterator::fetch(VexRip *out) const
{
	const struct hash_entry *he = owner->mapping.get<hash_entry>(offset);
	out->stack.resize(he->nr_rips);
	for (unsigned x = 0; x < he->nr_rips; x++)
		out->stack[x] = he->rips[x];
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
