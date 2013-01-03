#ifndef SAT_CHECKER_HPP__
#define SAT_CHECKER_HPP__

#include "nd_chooser.h"

class IRExprOptimisations;
class IRExpr;

IRExpr *simplify_via_anf(IRExpr *a, IRExpr *assumption = NULL);
IRExpr *setVariable(IRExpr *expression, IRExpr *variable, bool value);

class satisfier {
public:
	std::set<IRExpr *> trueBooleans;
	std::set<IRExpr *> falseBooleans;
	std::map<unsigned, CfgLabel> entryPoints;
	void prettyPrint(FILE *f) const;
	void clear() {
		trueBooleans.clear();
		falseBooleans.clear();
		entryPoints.clear();
	}
	void makeTrue(IRExpr *e);
	void makeFalse(IRExpr *e);
};
class sat_enumerator {
	struct stack_entry {
		satisfier partial_sat;
		IRExpr *remainder;
		stack_entry(const satisfier &_partial_sat,
			    IRExpr *_remainder)
			: partial_sat(_partial_sat),
			  remainder(_remainder)
		{}
		void prettyPrint(FILE *f) const {
			fprintf(f, "Remainder: %s\n", nameIRExpr(remainder));
			partial_sat.prettyPrint(stdout);
		}
	};
	std::vector<stack_entry> stack;
	internIRExprTable intern;
	bool _finished;
	const IRExprOptimisations &opt;
	void skipToSatisfying(void);
public:
	sat_enumerator(IRExpr *what, const IRExprOptimisations &_opt);
	bool finished() const { return stack.empty(); }
	void advance() {
		assert(!stack.empty());
		stack.pop_back();
		skipToSatisfying();
	}
	const satisfier &get() {
		assert(!stack.empty());
		assert(stack.back().remainder->tag == Iex_Const);
		assert( ((IRExprConst *)stack.back().remainder)->Ico.U1 );
		return stack.back().partial_sat;
	}
};

#endif /* !SAT_CHECKER_HPP__ */
