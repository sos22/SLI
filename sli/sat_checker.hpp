#ifndef SAT_CHECKER_HPP__
#define SAT_CHECKER_HPP__

#include "nd_chooser.h"

class AllowableOptimisations;
class IRExpr;

bool satisfiable(IRExpr *e,
		 const AllowableOptimisations &opt);
IRExpr *simplify_via_anf(IRExpr *a, IRExpr *assumption = NULL);
IRExpr *interval_simplify(IRExpr *what);
IRExpr *sat_simplify(IRExpr *a, const AllowableOptimisations &);

class satisfier {
public:
	/* Map from expressions to a pair<is_true, is_primary>.
	   is_true is obvious: whether that expression is actually
	   true.  is_primary is less obvious: it's true for
	   expressions where we actually specified a value, or false
	   for ones where we calculated it.  e.g. if we have
	   x && (x || y) then x and y are the primaries and
	   (x || y) will be a secondary. */
	std::map<IRExpr *, std::pair<bool, bool> > memo;
	std::set<IRExpr *> fixedVariables;
	void prettyPrint(FILE *f) const;
	void clear() { memo.clear(); fixedVariables.clear(); }
};
class sat_enumerator {
	satisfier content;
	NdChooser chooser;
	IRExpr *expr;
	bool _finished;
	void skipToSatisfying(void);
public:
	sat_enumerator(IRExpr *what)
		: expr(what), _finished(false)
	{ skipToSatisfying(); }
	bool finished() const;
	void advance();
	const satisfier &get() { assert(!_finished); return content; }
};

#endif /* !SAT_CHECKER_HPP__ */
