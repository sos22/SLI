#ifndef TYPESDB_HPP__
#define TYPESDB_HPP__

#include <err.h>

#include "mapping.hpp"

class TypesDb;

class __types_db_instr_iterator : public GarbageCollected<__types_db_instr_iterator> {
	friend class TypesDb;
	const TypesDb *owner;
	unsigned bucket_index;
	unsigned long offset;
	bool have_finished;
	__types_db_instr_iterator(const TypesDb *_owner);
public:
	bool finished() const { return have_finished; }
	void advance();
	void fetch(VexRip *out) const;
	void visit(HeapVisitor &hv) { hv(owner); }
	NAMED_CLASS
};

class TypesDb : public GarbageCollected<TypesDb> {
public:
	typedef __types_db_instr_iterator all_instrs_iterator;
	Mapping mapping;
	TypesDb(const char *path) {
		if (mapping.init(path) < 0)
			err(1, "loading %s", path);
	}
	void findOffsets(const VexRip &vr, std::vector<unsigned long> &out) const;
	all_instrs_iterator *enumerateAllInstructions() const;
	unsigned long nrDistinctInstructions() const;
	void visit(HeapVisitor &hv) {}

	/* Parse a vexrip which has already been canonicalised. */
	static void parse_vexrip_canon(VexRip *out, const Mapping &mapping,
				       unsigned long offset, bool *is_private,
				       unsigned long *sz);
	/* Read a vexrip which has already been canonicalised */
	static void read_vexrip_canon(FILE *f, VexRip *out, bool *is_private);

	enum read_vexrip_res {
		read_vexrip_take,
		read_vexrip_skip,
		read_vexrip_error
	};
	/* Read a vexrip which has not been canonicalised,
	 * canonicalising as we go. */
	static read_vexrip_res read_vexrip_noncanon(FILE *f,
						    VexRip *out,
						    AddressSpace *as,
						    bool *is_private);


	NAMED_CLASS
};

#endif /* !TYPESDB_HPP__ */
