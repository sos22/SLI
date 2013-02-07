#include "sli.h"
#include "enforce_crash.hpp"
#include "offline_analysis.hpp"

void
enumerateNeededExpressions(const bbdd *e, std::set<input_expression> &out)
{
	struct v {
		static visit_result Iex(std::set<input_expression> *state,
					const IRExpr *what) {
			if (what->tag == Iex_Get ||
			    what->tag == Iex_HappensBefore ||
			    what->tag == Iex_EntryPoint ||
			    what->tag == Iex_ControlFlow) {
				state->insert(input_expression::wrap(what));
			}
			return visit_continue;
		}
	};
	static bdd_visitor<std::set<input_expression> > visitor;
	visitor.irexpr.Iex = v::Iex;
	visit_const_bdd(&out, &visitor, e);
}
