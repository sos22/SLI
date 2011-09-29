/* Various bits for manipulating expressions in explicit CNF form. */
#include <map>

#include "sli.h"
#include "cnf.hpp"
#include "offline_analysis.hpp"
#include "intern.hpp"
#include "nf.hpp"

#include "libvex_prof.hpp"

static bool
cnf(IRExpr *e, NF_Expression &out)
{
	return convert_to_nf(e, out, Iop_And1, Iop_Or1);
}

/* A different kind of simplification: assume that @inp is a boolean
   expression, and consists of some tree of And1, Or1, and Not1
   expressions with other stuff at the leaves.  Treat all of the other
   stuff as opaque boolean variables, and then convert to NF.  Try to
   simplify it there.  If we make any reasonable progress, convert
   back to the standard IRExpr form and return the result.  Otherwise,
   just return @inp. */
IRExpr *
simplifyIRExprAsBoolean(IRExpr *inp, bool *done_something)
{
	__set_profiling(simplifyIRExprAsBoolean);
	
	if (!((inp->tag == Iex_Unop &&
	       ((IRExprUnop *)inp)->op == Iop_Not1) ||
	      (inp->tag == Iex_Associative &&
	       (((IRExprAssociative *)inp)->op == Iop_Or1 ||
		((IRExprAssociative *)inp)->op == Iop_And1))))
		return inp;

	inp = internIRExpr(inp);

	NF_Expression res;
	if (!cnf(inp, res))
		return inp;
	if (res.complexity() < exprComplexity(inp)) {
		*done_something = true;
		return convert_from_nf(res, Iop_And1, Iop_Or1);
	} else {
		return inp;
	}
}
