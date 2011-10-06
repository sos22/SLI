#ifndef DNF_HPP__
#define DNF_HPP__

#include "../nf.hpp"

typedef NF_Atom DNF_Atom;
typedef NF_Term DNF_Conjunction;
typedef NF_Expression DNF_Disjunction;

static inline void
printDnf(NF_Expression &dnf, FILE *f)
{
	dnf.prettyPrint(f, "&&&&&&&&&&", "|||||||||");
}

static inline Maybe<bool>
dnf(IRExpr *e, NF_Expression &out)
{
	return convert_to_nf(e, out, Iop_Or1, Iop_And1);
}

#endif /* !DNF_HPP__ */
