/* All the bits for dealing with CNF and DNF. */
#ifndef NF_HPP__
#define NF_HPP__

#include "simplify_irexpr.hpp"
#include "maybe.hpp"

template <unsigned sz, class content> class bloom_filter {
	unsigned long words[(sz+63)/64];
public:
	static const unsigned size = sz;
	bloom_filter() { clear(); }
	void clear() { bzero(words, sizeof(words)); }
	bool test(const content &x) {
		/* It's a lot easier to design a hash function which
		   behaves well modulo (sz-1) than one which behaves
		   well module sz, at least if sz is a power of
		   two. */
		unsigned long h = x.hash() % (sz - 1);
		if (words[h/64] & (1ul << (h % 64)))
			return true;
		else
			return false;
	}
	void set(const content &x) {
		unsigned long h = x.hash() % (sz - 1);
		words[h/64] |= (1ul << (h % 64));
	}

	bool definitelyNotSubset(const bloom_filter<sz, content> &other) const {
		/* Check whether @this is a subset of @other.  Return
		   true if we can prove that it isn't, which means if
		   there's some bit which is set in @this which is not
		   set in @other. */
		for (unsigned x = 0; x < (sz+63)/64; x++) {
			if (words[x] & ~other.words[x])
				return true;
		}
		return false;
	}
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
	unsigned hash() const {
		unsigned long acc = (unsigned long)second;
		return (acc ^ (acc >> 32)) * (first ? 1 : 2);
	}
};
class NF_Term : public std::vector<NF_Atom> {
public:
	bloom_filter<64, NF_Atom> bloom;
	void push_back(const NF_Atom &x) {
		std::vector<NF_Atom>::push_back(x);
		bloom.set(x);
	}
	void clear() {
		std::vector<NF_Atom>::clear();
		bloom.clear();
	}
	void prettyPrint(FILE *f, const char *) const;
	iterator findMatchingAtom(const NF_Atom &a);
};
class NF_Expression : public std::vector<NF_Term> {
public:
	void prettyPrint(FILE *f, const char *, const char *) const;
	bool isContradiction() const;
};

bool convert_to_nf(IRExpr *e, NF_Expression &out, IROp expressionOp, IROp termOp);
IRExpr *convert_from_nf(NF_Expression &inp, IROp expressionOp, IROp termOp);

IRExpr *convert_to_cnf(IRExpr *e);
IRExpr *convert_to_dnf(IRExpr *e);

#endif /* !NF_HPP__ */
