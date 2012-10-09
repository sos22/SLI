extern unsigned char release_lock[];
extern unsigned char acquire_lock[];

struct relocation {
	unsigned offset;
	unsigned size;
	long addend;
	int relative;
	unsigned long target;
};

struct trans_table_entry {
	unsigned long rip;
	unsigned offset;
};

struct entry_context {
	unsigned offset;
	unsigned long rip;
};

struct patch {
	const unsigned char *content;
	unsigned content_sz;
	const struct relocation *relocations;
	int nr_relocations;
	const struct trans_table_entry *trans_table;
	int nr_trans_table_entries;
	const struct entry_context *entry_points;
	int nr_entry_points;
};
