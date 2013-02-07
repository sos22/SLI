#include "sli.h"
#include "enforce_crash.hpp"
#include "offline_analysis.hpp"

void
enumerateNeededExpressions(const bbdd *e, std::set<input_expression> &out)
{
	struct v {
		static visit_result Get(std::set<input_expression> *state,
					const IRExprGet *ieg)
		{
			state->insert(input_expression::registr(ieg));
			return visit_continue;
		}
		static visit_result EntryPoint(std::set<input_expression> *state,
					       const IRExprEntryPoint *ieg)
		{
			state->insert(input_expression::entry_point(ieg));
			return visit_continue;
		}
		static visit_result ControlFlow(std::set<input_expression> *state,
						const IRExprControlFlow *ieg)
		{
			state->insert(input_expression::control_flow(ieg));
			return visit_continue;
		}
	};
	static bdd_visitor<std::set<input_expression> > visitor;
	visitor.irexpr.Get = v::Get;
	visitor.irexpr.EntryPoint = v::EntryPoint;
	visitor.irexpr.ControlFlow = v::ControlFlow;
	visit_const_bdd(&out, &visitor, e);
}
