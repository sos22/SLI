#ifndef TYPES_DB_HPP__
#define TYPES_DB_HPP__

#define NR_HASH_HEADS 511559

struct hash_head {
	unsigned long offset;
};

struct hash_entry {
	unsigned long chain;
	unsigned nr_rips;
	unsigned long offsets_start;
	unsigned long rips[0];

	bool for_rip(const VexRip &vr) const {
		if (nr_rips != vr.stack.size())
			return false;
		for (unsigned x = 0; x < nr_rips; x++)
			if (rips[x] != vr.stack[x])
				return false;
		return true;
	}
	void initialise(const VexRip &vr) {
		chain = 0;
		nr_rips = vr.stack.size();
		offsets_start = 0;
		for (unsigned x = 0; x < nr_rips; x++)
			rips[x] = vr.stack[x];
	}
	static unsigned long size_for(const VexRip &vr) {
		return sizeof(hash_entry) + sizeof(unsigned long) * vr.stack.size();
	}
};

struct offsets_list {
	unsigned long chain;
	unsigned nr_entries;
	unsigned nr_entries_allocated;
	unsigned long offsets[0];

	/* 16 == sizeof(offsets_list) */
	static const unsigned long default_size = 16 + 14 * sizeof(unsigned long);
	void initialise() {
		chain = 0;
		nr_entries = 0;
		nr_entries_allocated = 14;
	}
	void push_back(unsigned long o) {
		assert(nr_entries < nr_entries_allocated);
		offsets[nr_entries] = o;
		nr_entries++;
	}
};

#endif /* !TYPES_DB_HPP__ */
