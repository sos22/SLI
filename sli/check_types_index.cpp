#include <assert.h>
#include <err.h>
#include <stdio.h>

#include "libvex_ir.h"
#include "types_db.hpp"
#include "mapping.hpp"

int
main(int argc, char *argv[])
{
	Mapping mapping;
	if (mapping.init(argv[1]) < 0)
		err(1, "loading %s", argv[1]);

	const struct hash_head *heads = mapping.get<hash_head>(0, NR_HASH_HEADS);
	for (unsigned head_idx = 0; head_idx < NR_HASH_HEADS; head_idx++) {
		const struct hash_head *head = &heads[head_idx];
		unsigned chain_length = 0;
		unsigned long he_offset;
		const hash_entry *he;
		he = NULL;
		for (he_offset = head->offset; he_offset != 0; ) {
			he = mapping.get<hash_entry>(he_offset);
			he_offset = he->chain;
			chain_length++;
		}
		for (unsigned x = 0; x < chain_length; x++)
			printf("%d\n", x + 1);
	}

	return 0;
}
