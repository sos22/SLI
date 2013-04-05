#include "sli.h"
#include "enforce_crash.hpp"
#include "offline_analysis.hpp"
#include "reorder_bdd.hpp"

void
enumerateNeededExpressions(const reorder_bbdd *e, std::set<input_expression> &out)
{
	std::set<const reorder_bbdd *> visited;
	std::vector<const reorder_bbdd *> q;
	std::vector<const IRExpr *> expr_q;
	q.push_back(e);
	while (!q.empty()) {
		auto n = q.back();
		q.pop_back();
		if (n->isLeaf || !visited.insert(n).second) {
			continue;
		}
		expr_q.push_back(n->cond.cond);
		q.push_back(n->trueBranch);
		q.push_back(n->falseBranch);
	}
	std::set<const IRExpr *> visited_exprs;
	while (!expr_q.empty()) {
		auto n = expr_q.back();
		expr_q.pop_back();
		if (!visited_exprs.insert(n).second) {
			continue;
		}
		switch (n->tag) {
		case Iex_Get:
			out.insert(input_expression::registr((IRExprGet *)n));
			break;
		case Iex_EntryPoint:
			out.insert(input_expression::entry_point((IRExprEntryPoint *)n));
			break;
		case Iex_ControlFlow:
			out.insert(input_expression::control_flow((IRExprControlFlow *)n));
			break;
		case Iex_GetI:
			abort();
		case Iex_Qop:
			expr_q.push_back( ((IRExprQop *)n)->arg1);
			expr_q.push_back( ((IRExprQop *)n)->arg2);
			expr_q.push_back( ((IRExprQop *)n)->arg3);
			expr_q.push_back( ((IRExprQop *)n)->arg4);
			break;
		case Iex_Triop:
			expr_q.push_back( ((IRExprTriop *)n)->arg1);
			expr_q.push_back( ((IRExprTriop *)n)->arg2);
			expr_q.push_back( ((IRExprTriop *)n)->arg3);
			break;
		case Iex_Binop:
			expr_q.push_back( ((IRExprBinop *)n)->arg1);
			expr_q.push_back( ((IRExprBinop *)n)->arg2);
			break;
		case Iex_Unop:
			expr_q.push_back( ((IRExprUnop *)n)->arg);
			break;
		case Iex_Const:
			break;
		case Iex_Mux0X:
			abort();
		case Iex_CCall:
			abort();
		case Iex_Associative: {
			auto a = (IRExprAssociative *)n;
			for (int i = 0; i < a->nr_arguments; i++) {
				expr_q.push_back(a->contents[i]);
			}
			break;
		}
		case Iex_Load:
			expr_q.push_back(((IRExprLoad *)n)->addr);
			break;
		case Iex_HappensBefore:
			abort();
		case Iex_FreeVariable:
			abort();
		}
	}
}
