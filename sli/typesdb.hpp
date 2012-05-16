#ifndef TYPESDB_HPP__
#define TYPESDB_HPP__

#include <err.h>

#include "mapping.hpp"

class TypesDb;
class AddressSpace;

class DynAnalysisRip : public Named {
	char *mkName() const {
		char *acc = strdup("DynRip[");
		int i;
		for (i = 0; i < nr_rips; i++) {
			char *a2;
			if (i == 0)
				a2 = my_asprintf("%s%lx", acc, rips[i]);
			else
				a2 = my_asprintf("%s, %lx", acc, rips[i]);
			free(acc);
			acc = a2;
		}
		char *a2 = my_asprintf("%s]", acc);
		free(acc);
		return a2;
	}
public:
	static const int DATABASE_RIP_DEPTH = CONFIG_DATABASE_RIP_DEPTH;
	int nr_rips;
	unsigned long rips[DATABASE_RIP_DEPTH];

	bool operator==(const DynAnalysisRip &r) const {
		if (nr_rips != r.nr_rips)
			return false;
		for (int x = 0; x < nr_rips; x++)
			if (rips[x] != r.rips[x])
				return false;
		return true;
	}
	bool operator<(const DynAnalysisRip &o) const {
		for (int x = 0; x < nr_rips && x < o.nr_rips; x++)
			if (rips[x] < o.rips[x])
				return true;
			else if (rips[x] > o.rips[x])
				return false;
		return nr_rips < o.nr_rips;
	}

	bool isValid() const { return nr_rips != 0; }

	explicit DynAnalysisRip(const VexRip &vr)
	{
		if (vr.getStack().size() > (unsigned)DATABASE_RIP_DEPTH)
			nr_rips = DATABASE_RIP_DEPTH;
		else
			nr_rips = vr.getStack().size();
		for (int x = 0; x < nr_rips; x++)
			rips[x] = vr.getStack()[x + vr.getStack().size() - nr_rips];
	}
	DynAnalysisRip()
		: nr_rips(0)
	{}

	VexRip toVexRip() const {
		VexRip res;
		for (int x = 0; x < nr_rips; x++)
			res.getStack().push_back(rips[x]);
		return res;
	}

	/* True if comparing this RIP with @vr suggests that this rip
	   might be reached by exploring functions called from @vr. */
	bool rootedIn(const VexRip &vr) const {
		/* We consider them to match if some prefix of this
		   rip matches up with some suffix of @vr.  The
		   algorithm is essentially to scan backwards through
		   @vr until we first the first entry in @this and
		   then work forwards from there to see if it's a
		   match. */
		assert(nr_rips != 0);
		for (int baseOfThis = vr.getStack().size() - 1;
		     baseOfThis >= 0 && baseOfThis >= (int)vr.getStack().size() - nr_rips;
		     baseOfThis--) {
			if (vr.getStack()[baseOfThis] != rips[0])
				continue;
			/* We have one match.  Everything after
			   @baseOfThis must match as well, to the end
			   of @vr. */
			bool match = true;
			for (int idx = baseOfThis;
			     match && idx < (int)vr.getStack().size();
			     idx++) {
				assert(idx - baseOfThis < nr_rips);
				if (rips[idx - baseOfThis] != vr.getStack()[idx])
					match = false;
			}
			if (match)
				return true;
		}
		return false;
	}

	unsigned long hash() const {
		unsigned long acc = 0;
		for (int i = 0; i < nr_rips; i++)
			acc = acc * 1000000447 + rips[i];
		return acc;
	}

	void changed() { clearName(); }
};

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
	void fetch(DynAnalysisRip *out) const;
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
	void findOffsets(const DynAnalysisRip &vr, std::vector<unsigned long> &out) const;
	all_instrs_iterator *enumerateAllInstructions() const;
	unsigned long nrDistinctInstructions() const;
	void visit(HeapVisitor &) {}

	/* Parse a vexrip which has already been canonicalised. */
	static void parse_vexrip_canon(DynAnalysisRip *out, const Mapping &mapping,
				       unsigned long offset, bool *is_private,
				       unsigned long *sz);
	/* Read a vexrip which has already been canonicalised */
	static void read_vexrip_canon(FILE *f, DynAnalysisRip *out, bool *is_private);

	enum read_vexrip_res {
		read_vexrip_take,
		read_vexrip_skip,
		read_vexrip_error
	};
	/* Read a vexrip which has not been canonicalised,
	 * canonicalising as we go. */
	static read_vexrip_res read_vexrip_noncanon(FILE *f,
						    DynAnalysisRip *out,
						    AddressSpace *as,
						    bool *is_private);


	NAMED_CLASS
};

bool parseDynAnalysisRip(DynAnalysisRip *out, const char *inp, const char **suffix);

#endif /* !TYPESDB_HPP__ */
