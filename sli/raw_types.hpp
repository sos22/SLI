/* Bits for dealing with the raw types database produced by dynamic
   analysis. */

/* A wrapper around FILE which doesn't force a flush every time you
 * call ftell() */
struct sane_write_file {
	FILE *f;
	unsigned long offset;
	sane_write_file(FILE *_f)
		: f(_f), offset(::ftell(f))
	{}
	unsigned long ftell() const { return offset; }
	template <typename t> void write(const t &value)
	{
		fwrite(&value, sizeof(value), 1, f);
		offset += sizeof(value);
	}
	template <typename t> void write(const t *value, size_t nr_elems)
	{
		fwrite(value, sizeof(*value), nr_elems, f);
		offset += sizeof(value) * nr_elems;
	}
};

struct rip_t {
	int is_private;
	std::vector<unsigned long> stack;
	bool read(FILE *f, AddressSpace *as = NULL);
	bool operator<(const rip_t &o) const {
		if (stack < o.stack)
			return true;
		if (stack > o.stack)
			return false;
		return is_private < o.is_private;
	}
	bool operator>(const rip_t &o) const {
		return o < *this;
	}
	void write(sane_write_file &output) const;
};

struct input_record {
	rip_t rip;
	std::vector<rip_t> loads;
	std::vector<rip_t> stores;
	bool read(FILE *f, AddressSpace *as = NULL);
	void write(sane_write_file &f) const;
	bool operator<(const input_record &o) const {
		if (rip < o.rip)
			return true;
		if (rip > o.rip)
			return false;
		if (loads < o.loads)
			return true;
		if (loads > o.loads)
			return false;
		if (stores < o.stores)
			return true;
		return false;
	}
};

struct input_database {
	std::vector<input_record> content;
	void read(FILE *f, AddressSpace *as = NULL);
};


