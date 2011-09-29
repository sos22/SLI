/* All the bits for dealing with CNF and DNF. */
#ifndef NF_HPP__
#define NF_HPP__

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

#endif /* !NF_HPP__ */
