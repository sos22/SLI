extern unsigned char release_lock[];

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

struct patch {
	const struct relocation *relocations;
	int nr_relocations;
	const struct trans_table_entry *trans_table;
	int nr_translations;
	unsigned long *entry_points;
	int nr_entry_points;
	const unsigned char *content;
	unsigned content_size;
};
