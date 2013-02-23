#include <assert.h>
#include <err.h>
#include <stdio.h>

#include "sli.h"

#define debug_mode 0

struct rip_t {
	unsigned long rip:63;
	unsigned long is_private:1;
	bool operator<(const rip_t &o) const {
		if (rip < o.rip) {
			return true;
		} else if (o.rip < rip) {
			return false;
		} else {
			return is_private < o.is_private;
		}
	}
};
struct edge : public Named {
	char *mkName() const {
		return my_asprintf("%08lx:%s <-> %08lx:%s",
				   from.rip,
				   from.is_private ? "private" : "shared ",
				   to.rip,
				   to.is_private ? "private" : "shared ");
	}
	rip_t from;
	rip_t to;
	edge(const rip_t &a, const rip_t &b)
	{
		if (a < b) {
			from = a;
			to = b;
		} else {
			from = b;
			to = a;
		}
	}
	bool operator<(const edge &o) const {
		if (from < o.from) {
			return true;
		} else if (o.from < from) {
			return false;
		} else {
			return to < o.to;
		}
	}
};
typedef std::set<edge> aliasingGraph;

struct hdr {
	int nr_loads;
	int nr_stores;
};

static void
slurp_types_db(const char *filename, aliasingGraph &out)
{
	FILE *f = fopen(filename, "r");
	if (!f) {
		err(1, "opening %s", filename);
	}
	unsigned long magic;
	fread(&magic, sizeof(magic), 1, f);
	if (magic != 0x1122334455) {
		errx(1, "only support new format");
	}
	while (1) {
		struct hdr hdr;
		if (!fread(&hdr, sizeof(hdr), 1, f)) {
			if (feof(f)) {
				break;
			}
			err(1, "reading header from %s", filename);
		}
		rip_t r;
		if (!fread(&r, sizeof(r), 1, f)) {
			err(1, "reading %s", filename);
		}
		for (int i = 0; i < hdr.nr_loads + hdr.nr_stores; i++) {
			rip_t q;
			if (!fread(&q, sizeof(q), 1, f)) {
				err(1, "reading2 %s", filename);
			}
			out.insert(edge(r, q));
		}
	}
	fclose(f);
}

int
main(int argc, char *argv[])
{
	init_sli();

	const char *db = argv[1];
	const char *reference = argv[2];

	aliasingGraph ref;
	slurp_types_db(reference, ref);
	aliasingGraph thing;
	slurp_types_db(db, thing);

	if (debug_mode) {
		printf("Reference table:\n");
		for (auto it = ref.begin(); it != ref.end(); it++) {
			printf("\t%s\n", it->name());
		}
		printf("other table:\n");
		for (auto it = thing.begin(); it != thing.end(); it++) {
			printf("\t%s\n", it->name());
		}
	}

	for (auto it = thing.begin(); it != thing.end(); it++) {
		assert(ref.count(*it));
	}

	printf("%f\n", double(thing.size()) / ref.size());

	return 0;
}
