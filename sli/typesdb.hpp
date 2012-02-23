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
	NAMED_CLASS
};

#endif /* !TYPESDB_HPP__ */
