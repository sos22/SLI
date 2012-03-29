#ifndef TYPES_DB_HPP__
#define TYPES_DB_HPP__

#define NR_HASH_HEADS 8185501

struct hash_head {
	unsigned long offset;
};

struct hash_entry {
	unsigned long chain;
	unsigned nr_rips;
	unsigned long offsets_start;
	unsigned long rips[0];

	bool for_rip(const DynAnalysisRip &vr) const {
		if (vr.nr_rips > (int)nr_rips)
			return false;
		for (int x = 0; x < vr.nr_rips; x++)
			if (vr.rips[x] != rips[x])
				return false;
		return true;
	}
	void initialise(const DynAnalysisRip &vr) {
		chain = 0;
		nr_rips = vr.nr_rips;
		offsets_start = 0;
		for (unsigned x = 0; x < nr_rips; x++)
			rips[x] = vr.rips[x];
	}
	static unsigned long size_for(const DynAnalysisRip &vr) {
		return sizeof(hash_entry) + sizeof(unsigned long) * vr.nr_rips;
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
