#include "sli.h"
#include "enforce_crash.hpp"
#include "offline_analysis.hpp"

void
enumerateNeededExpressions(const IRExpr *e, std::set<const IRExpr *> &out)
{
	struct v {
		static visit_result Iex(std::set<const IRExpr *> *state,
					const IRExpr *what) {
			if (what->tag == Iex_Get ||
			    what->tag == Iex_HappensBefore ||
			    what->tag == Iex_EntryPoint ||
			    what->tag == Iex_ControlFlow) {
				state->insert(what);
			}
			return visit_continue;
		}
	};
	static irexpr_visitor<std::set<const IRExpr *> > visitor;
	visitor.Iex = v::Iex;
	visit_irexpr(&out, &visitor, e);
}
