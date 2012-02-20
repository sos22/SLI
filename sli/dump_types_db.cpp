#include <err.h>

#include "sli.h"
#include "mapping.hpp"

#include "types_db.hpp"

class TypesDb : public GarbageCollected<TypesDb> {
public:
	Mapping mapping;
	TypesDb(const char *path) {
		if (mapping.init(path) < 0)
			err(1, "loading %s", path);
	}
	void findOffsets(const VexRip &vr, std::vector<unsigned long> &out);

	void visit(HeapVisitor &hv) {}
	NAMED_CLASS
};

void
TypesDb::findOffsets(const VexRip &vr, std::vector<unsigned long> &out)
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

int
main(int argc, char *argv[])
{
	init_sli();

	TypesDb *types = new TypesDb(argv[1]);
	VexRip vr;

	const char *ign;
	if (!parseVexRip(&vr, argv[2], &ign))
		errx(1, "cannot parse %s as vex rip", argv[2]);

	std::vector<unsigned long> o;
	types->findOffsets(vr, o);

	printf("Offsets: ");
	for (auto it = o.begin(); it != o.end(); it++)
		printf("%lx, ", *it);
	printf("\n");

	return 0;
}
