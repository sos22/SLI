/* This pass takes advantage of variable undefinedness to simplify
   machines.  The idea is that we arrange that uninitialised variables
   can never influence the result of a machine, but that doesn't imply
   that they will never be referenced.  You might, for instance, find
   that you have an expression like ``x && <something_complicated>''.
   If x is definitely uninitialised at that point then it can't
   influence the outcome of the machine, so <something_complicated>
   must definitely be zero, and hence the whole expression must be
   zero. */
#include "sli.h"
#include "offline_analysis.hpp"

#define UNDEFINED_EXPR ((IRExpr *)3)

#ifndef NDEBUG
static bool debug_undefinedness = false;
#else
#define debug_undefinedness false
#endif

namespace _undefinedness {

template <typename t, typename s> static bool
operator |=(std::set<t, s> &a, const std::set<t, s> &b)
{
	bool res = false;
	for (auto it = b.begin(); it != b.end(); it++)
		res |= a.insert(*it).second;
	return res;
}

class VariableDefinednessMap {
	typedef std::set<threadAndRegister, threadAndRegister::fullCompare> entryT ;
	std::map<StateMachineState *, entryT> content;
public:
	void prettyPrint(FILE *f, const std::map<const StateMachineState *, int> &labels) const {
		for (auto it = content.begin(); it != content.end(); it++) {
			auto it2 = labels.find(it->first);
			fprintf(f, "l%d: ", it2 == labels.end() ? -1 : it2->second);
			for (auto it3 = it->second.begin(); it3 != it->second.end(); it3++) {
				if (it3 != it->second.begin())
					fprintf(f, ", ");
				fprintf(f, "%s", it3->name());
			}
			fprintf(f, "\n");
		}
	}
	bool isUndefined(StateMachineState *sm, const threadAndRegister &tr) const {
		if (tr.gen() == (unsigned)-1)
			return false;
		auto it = content.find(sm);
		assert(it != content.end());
		return it->second.count(tr) == 0;
	}
	void init(StateMachine *sm);
};

void
VariableDefinednessMap::init(StateMachine *sm)
{
	content.insert(std::pair<StateMachineState *, entryT>(sm->root, entryT()));
	std::queue<StateMachineState *> pending;
	pending.push(sm->root);
	while (!pending.empty()) {
		StateMachineState *p = pending.front();
		pending.pop();
		const entryT &entrySet(content[p]);
		entryT exitSet(entrySet);
		StateMachineSideEffect *se = p->getSideEffect();
		threadAndRegister tr(threadAndRegister::invalid());
		if (se && se->definesRegister(tr))
			exitSet.insert(tr);
		std::vector<StateMachineState *> succ;
		p->targets(succ);
		for (auto it = succ.begin(); it != succ.end(); it++) {
			auto it2_did_insert = content.insert(std::pair<StateMachineState *, entryT>(*it, exitSet));
			auto it2 = it2_did_insert.first;
			auto did_insert = it2_did_insert.second;
			if (did_insert || (it2->second |= exitSet))
				pending.push(*it);
		}
	}
}


class UndefinednessTransformer : public StateMachineTransformer {
	const VariableDefinednessMap &vdm;
	bool rewriteNewStates() const { return false; }

	IRExpr *transformIex(IRExprGet *ieg) {
		if (vdm.isUndefined(currentState, ieg->reg))
			return UNDEFINED_EXPR;
		return ieg;
	}
	IRExpr *transformIex(IRExprUnop *e)
	{
		bool t = false;
		IRExpr *a1 = transformIRExpr(e->arg, &t);
		if (a1 == UNDEFINED_EXPR)
			return UNDEFINED_EXPR;

		if (!t)
			return NULL;
		else
			return IRExpr_Unop(e->op, a1);
	}
	IRExpr *transformIex(IRExprAssociative *e) {
		bool t = false;
		int x = 0;
		IRExpr *newE;
		while (x < e->nr_arguments) {
			newE = transformIRExpr(e->contents[x], &t);
			if (t)
				break;
			assert(newE != UNDEFINED_EXPR);
			x++;
		}
		if (!t)
			return NULL;
		if (newE == UNDEFINED_EXPR) {
			switch (e->op) {
			case Iop_And1:
				return IRExpr_Const(IRConst_U1(0));
			case Iop_Or1:
				return IRExpr_Const(IRConst_U1(1));
			default:
				abort();
			}
		}
		IRExprAssociative *r = (IRExprAssociative *)IRExpr_Associative(e);
		r->contents[x] = newE;
		x++;
		while (x < e->nr_arguments) {
			r->contents[x] = transformIRExpr(e->contents[x], &t);
			x++;
		}
		return r;
	}
	IRExpr *transformIex(IRExprMux0X *e) {
		bool t = false;
		IRExpr *c = transformIRExpr(e->cond, &t);
		IRExpr *z = transformIRExpr(e->expr0, &t);
		IRExpr *x = transformIRExpr(e->exprX, &t);
		
		if (c == UNDEFINED_EXPR) {
			if (z == UNDEFINED_EXPR || x == UNDEFINED_EXPR)
				return UNDEFINED_EXPR;
			return z;
		}
		if (z == UNDEFINED_EXPR)
			return x;
		if (x == UNDEFINED_EXPR)
			return z;
		if (!t)
			return NULL;
		else
			return IRExpr_Mux0X(c, z, x);		
	}
public:
	UndefinednessTransformer(const VariableDefinednessMap &_vdm)
		: vdm(_vdm)
	{}
};


static StateMachine *
undefinednessSimplification(StateMachine *sm, bool *done_something)
{
	std::map<const StateMachineState *, int> stateLabels;
	if (debug_undefinedness) {
		printf("undefinednessSimplification:\n");
		printStateMachine(sm, stdout, stateLabels);
	}
	VariableDefinednessMap vdm;
	vdm.init(sm);
	if (debug_undefinedness) {
		printf("Variable definedness:\n");
		vdm.prettyPrint(stdout, stateLabels);
	}
	bool p = false;
	UndefinednessTransformer t(vdm);
	sm = t.transform(sm, &p);
	if (debug_undefinedness) {
		if (p) {
			printf("Result:\n");
			printStateMachine(sm, stdout);
		} else {
			printf("Achieved nothing\n");
		}
	}
	*done_something |= p;
	return sm;
}

};

StateMachine *
undefinednessSimplification(StateMachine *sm, bool *done_something)
{
	return _undefinedness::undefinednessSimplification(sm, done_something);
}

