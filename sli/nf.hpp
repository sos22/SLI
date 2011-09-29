/* All the bits for dealing with CNF and DNF. */
#ifndef NF_HPP__
#define NF_HPP__

/* The ordering we use for NF disjunctions works like this:

   -- If a is a subset of b (i.e. a implies b) then a is less than b.
   -- If a is a superset of b (i.e. b implies a) then a is greather than b.
   -- Otherwise, if they're unordered by the subset ordering, we
      using a per-element dictionary ordering.

   This enumeration gives every possible result.
*/
enum nf_ordering {
	nf_subset = -2,
	nf_less = -1,
	nf_eq = 0,
	nf_greater = 1,
	nf_superset = 2
};

class NF_Atom : public std::pair<bool, IRExpr *>, public PrettyPrintable {
public:
	NF_Atom(bool b, IRExpr *e)
		: std::pair<bool, IRExpr *>(b, e)
	{}
	void prettyPrint(FILE *f) const {
		if (first)
			fprintf(f, "!");
		else
			fprintf(f, " ");
		ppIRExpr(second, f);
	}
};

class NF_Term : public std::vector<NF_Atom>, public PrettyPrintable {
public:
	void prettyPrint(FILE *f) const;
};
class NF_Expression : public std::vector<NF_Term>, public PrettyPrintable {
public:
	void prettyPrint(FILE *f) const;
};

#endif /* !NF_HPP__ */
