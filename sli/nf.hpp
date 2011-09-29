/* All the bits for dealing with CNF and DNF. */
#ifndef NF_HPP__
#define NF_HPP__

#include "simplify_irexpr.hpp"

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
	unsigned complexity() const {
		return exprComplexity(second) + (first ? 10 : 0);
	}
};
class NF_Term : public std::vector<NF_Atom> {
public:
	void prettyPrint(FILE *f, const char *) const;
	int complexity() const {
		if (size() == 1)
			return (*this)[0].complexity();
		int acc = 10;
		for (auto it = begin(); it != end(); it++)
			acc += it->complexity();
		return acc;
	}
};
class NF_Expression : public std::vector<NF_Term> {
public:
	void prettyPrint(FILE *f, const char *, const char *) const;
	int complexity() const {
		if (size() == 1)
			return (*this)[0].complexity();
		int acc = 10;
		for (auto it = begin(); it != end(); it++)
			acc += it->complexity();
		return acc;
	}
};

bool convert_to_nf(IRExpr *e, NF_Expression &out, IROp expressionOp, IROp termOp);
IRExpr *convert_from_nf(NF_Expression &inp, IROp expressionOp, IROp termOp);

#endif /* !NF_HPP__ */
