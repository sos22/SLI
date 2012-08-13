#include "sli.h"
#include "offline_analysis.hpp"
#include "inferred_information.hpp"
#include "intern.hpp"

typedef std::set<threadAndRegister, threadAndRegister::fullCompare> reg_set_t;

#ifndef NDEBUG
static bool debug_find_constants = false;
static bool debug_build_possible = false;
static bool debug_function_matches = false;
static bool debug_use_functions = false;
#else
#define debug_find_constants false
#define debug_build_possible false
#define debug_function_matches false
#define debug_use_functions false
#endif

/* Used to represent arguments in our function representation. */
class IRExprPlaceholder : public IRExpr {
public:
	int idx;
	IRExprPlaceholder(int _idx)
		: IRExpr(IRExprTag(1)),
		  idx(_idx)
	{}
	void visit(HeapVisitor &) {}
	void prettyPrint(FILE *f) const {
		fprintf(f, "<arg%d>", idx);
	}
	unsigned long hashval() const { return idx * 785234789; }
	IRType type() const { return Ity_INVALID; }
	void sanity_check() const { assert(idx >= 1); }
};

template <typename exprTransformer>
class StateIRExprTransformer : public StateMachineTransformer {
	exprTransformer &et;
	bool rewriteNewStates() const { return false; }
	IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
		return et.doit(e, done_something);
	}
public:
	StateIRExprTransformer(exprTransformer &_et)
		: et(_et)
	{}
};

template <typename t, typename c> void
printNamedSet(const std::set<t, c> &s)
{
	printf("{");
	for (auto it = s.begin(); it != s.end(); it++) {
		if (it != s.begin())
			printf(", ");
		printf("%s", it->name());
	}
	printf("}");
}

class EnumRegistersTransformer : public IRExprTransformer {
	IRExpr *transformIex(IRExprGet *iex) {
		res.insert(iex->reg);
		return iex;
	}
	reg_set_t &res;
	bool rewriteNewStates() const { return false; }
public:
	EnumRegistersTransformer(reg_set_t &_res)
		: res(_res)
	{}
};

template <typename t, typename c>
struct complement_set {
	const std::set<t, c> &content;
	complement_set(const std::set<t, c> &_content)
		: content(_content)
	{}
};

template <typename t, typename c> static complement_set<t, c>
operator ~(const std::set<t, c> &a)
{
	return complement_set<t, c>(a);
}
template <typename t, typename c> static void
operator &=(std::set<t, c> &a, const complement_set<t, c> &b)
{
	for (auto it = b.content.begin(); it != b.content.end(); it++)
		a.erase(*it);
}

class Function : public GarbageCollected<Function>, public Named {
	static bool matches(IRExpr *what, IRExpr *tmpl, std::map<int, IRExpr *> &argVals);
	static int complexity(const IRExpr *what);
	char *mkName() const {
		return my_asprintf("func(%d) ==> %s",
				    nr_arguments,
				    nameIRExpr(result));
	}
public:
	int nr_arguments;
	IRExpr *result;
	int complexity() const;
	bool matches(IRExpr *what);
	bool matches(IRExpr *what, std::map<int, IRExpr *> &argVals);
	Function(int _nr_arguments, IRExpr *_result)
		: nr_arguments(_nr_arguments),
		  result(_result)
	{}
	void visit(HeapVisitor &hv) {
		hv(result);
	}
	NAMED_CLASS
};

int
Function::complexity() const
{
	return complexity(result);
}
int
Function::complexity(const IRExpr *e)
{
	if (dynamic_cast<const IRExprPlaceholder *>(e))
		return 0;
	switch (e->tag) {
	case Iex_Get:
		return 0;
	case Iex_GetI:
		return 100 + complexity( ((IRExprGetI *)e)->ix );
	case Iex_Qop:
		return 1 +
			complexity( ((IRExprQop *)e)->arg1) +
			complexity( ((IRExprQop *)e)->arg2) +
			complexity( ((IRExprQop *)e)->arg3) +
			complexity( ((IRExprQop *)e)->arg4);
	case Iex_Triop:
		return 1 +
			complexity( ((IRExprTriop *)e)->arg1) +
			complexity( ((IRExprTriop *)e)->arg2) +
			complexity( ((IRExprTriop *)e)->arg3);
	case Iex_Binop:
		return 1 +
			complexity( ((IRExprBinop *)e)->arg1) +
			complexity( ((IRExprBinop *)e)->arg2);
	case Iex_Unop:
		return 1 + complexity( ((IRExprUnop *)e)->arg );
	case Iex_Const:
		return 1;
	case Iex_Mux0X:
		return 1 +
			complexity( ((IRExprMux0X *)e)->cond ) +
			complexity( ((IRExprMux0X *)e)->expr0 ) +
			complexity( ((IRExprMux0X *)e)->exprX );
	case Iex_CCall:
		return 100;
	case Iex_Associative: {
		IRExprAssociative *iex = (IRExprAssociative *)e;
		int acc = 1;
		for (int i = 0; i < iex->nr_arguments; i++)
			acc += complexity(iex->contents[i]);
		return acc;
	}
	case Iex_Load:
		return 1 + complexity(((IRExprLoad *)e)->addr);
	case Iex_HappensBefore:
		return 1;
	case Iex_FreeVariable:
		return 1;
	}
	abort();
}

bool
Function::matches(IRExpr *what)
{
	std::map<int, IRExpr *> argVals;
	return matches(what, argVals);
}
bool
Function::matches(IRExpr *what, std::map<int, IRExpr *> &argVals)
{
	bool res = matches(what, result, argVals);
	if (debug_function_matches) {
		printf("Function(%s)::matches(%s) -> %s\n",
		       name(), nameIRExpr(what), res ? "true" : "false");
		if (res) {
			for (auto it = argVals.begin(); it != argVals.end(); it++)
				printf("\targ%d -> %s\n", it->first, nameIRExpr(it->second));
		}
	}
	return res;
}
bool
Function::matches(IRExpr *what, IRExpr *tmpl, std::map<int, IRExpr *> &argVals)
{
	if (what == tmpl)
		return true;
	IRExprPlaceholder *p = dynamic_cast<IRExprPlaceholder *>(tmpl);
	if (p) {
		auto it_did_insert = argVals.insert(std::pair<int, IRExpr *>(p->idx, what));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (did_insert || it->second == what)
			return true;
		return false;
	}
	if (what->tag != tmpl->tag)
		return false;
	switch (what->tag) {
	case Iex_Get:
		assert( !threadAndRegister::fullEq(((IRExprGet *)what)->reg,
						   ((IRExprGet *)tmpl)->reg));
		return false;
	case Iex_GetI: {
		IRExprGetI *whatI = (IRExprGetI *)what;
		IRExprGetI *tmplI = (IRExprGetI *)tmpl;
		return whatI->descr == tmplI->descr &&
			whatI->bias == tmplI->bias &&
			whatI->tid == tmplI->tid &&
			matches(whatI->ix, tmplI->ix, argVals);
	}
	case Iex_Qop: {
		IRExprQop *whatI = (IRExprQop *)what;
		IRExprQop *tmplI = (IRExprQop *)tmpl;
		if (!matches(whatI->arg4, tmplI->arg4, argVals))
			return false;
		/* fall through */
	}
	case Iex_Triop: {
		IRExprTriop *whatI = (IRExprTriop *)what;
		IRExprTriop *tmplI = (IRExprTriop *)tmpl;
		if (!matches(whatI->arg3, tmplI->arg3, argVals))
			return false;
		/* fall through */
	}
	case Iex_Binop: {
		IRExprBinop *whatI = (IRExprBinop *)what;
		IRExprBinop *tmplI = (IRExprBinop *)tmpl;
		if (!matches(whatI->arg2, tmplI->arg2, argVals))
			return false;
		/* fall through */
	}
	case Iex_Unop: {
		IRExprUnop *whatI = (IRExprUnop *)what;
		IRExprUnop *tmplI = (IRExprUnop *)tmpl;
		return whatI->op == tmplI->op &&
			matches(whatI->arg, tmplI->arg, argVals);
	}
	case Iex_Load: {
		IRExprLoad *whatI = (IRExprLoad *)what;
		IRExprLoad *tmplI = (IRExprLoad *)tmpl;
		return whatI->ty == tmplI->ty &&
			matches(whatI->addr, tmplI->addr, argVals);
	}
	case Iex_CCall: {
		IRExprCCall *whatI = (IRExprCCall *)what;
		IRExprCCall *tmplI = (IRExprCCall *)tmpl;
		if (whatI->cee != tmplI->cee ||
		    whatI->retty != tmplI->retty)
			return false;
		int i;
		for (i = 0; whatI->args[i] && tmplI->args[i]; i++)
			if (!matches(whatI->args[i], tmplI->args[i], argVals))
				return false;
		if (whatI->args[i] || tmplI->args[i])
			return false;
		return true;
	}
	case Iex_Mux0X: {
		IRExprMux0X *whatI = (IRExprMux0X *)what;
		IRExprMux0X *tmplI = (IRExprMux0X *)tmpl;
		return matches(whatI->cond, tmplI->cond, argVals) &&
			matches(whatI->expr0, tmplI->expr0, argVals) &&
			matches(whatI->exprX, tmplI->exprX, argVals);
	}
	case Iex_Associative: {
		IRExprAssociative *whatI = (IRExprAssociative *)what;
		IRExprAssociative *tmplI = (IRExprAssociative *)tmpl;
		if (whatI->op != tmplI->op ||
		    whatI->nr_arguments != tmplI->nr_arguments)
			return false;
		for (int i = 0; i < whatI->nr_arguments; i++)
			if (!matches(whatI->contents[i], tmplI->contents[i], argVals))
				return false;
		return true;
	}

		/* return false for the last four because we're
		   interned, and we've already tested for pointer
		   equality. */
	case Iex_Const:
		return false;
	case Iex_HappensBefore:
		return false;
	case Iex_FreeVariable:
		return false;
	}
	abort();
}

static void
introduceCandidateFunction(IRExpr *e, std::map<Function *, int> &functions, const reg_set_t &constRegs)
{
	reg_set_t input_regs;
	(EnumRegistersTransformer(input_regs)).doit(e);
	input_regs &= ~constRegs;
	if (input_regs.size() == 0)
		return;
	std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> placeholders;
	int cntr = 1;
	for (auto it = input_regs.begin(); it != input_regs.end(); it++) {
		std::pair<threadAndRegister, IRExpr *> t(*it, new IRExprPlaceholder(cntr++));
		placeholders.insert(t);
	}
	struct : public IRExprTransformer {
		std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> *placeholders;
		IRExpr *transformIex(IRExprGet *ieg) {
			auto it = placeholders->find(ieg->reg);
			if (it != placeholders->end())
				return it->second;
			return ieg;
		}
	} buildResult;
	buildResult.placeholders = &placeholders;
	IRExpr *newE = buildResult.doit(e);
	/* Filter out identify functions.  There are two interesting
	   forms:

	   -- \x -> x
	   -- \x -> f(x), where f is one of our new functions.
	*/
	if (dynamic_cast<IRExprPlaceholder *>(newE))
		return;
	if (newE->tag == Iex_CCall) {
		IRExprCCall *iec = (IRExprCCall *)newE;
		int i;
		bool isBad = true;
		for (i = 0; isBad && iec->args[i]; i++)
			if (!dynamic_cast<IRExprPlaceholder *>(iec->args[i]))
				isBad = false;
		if (isBad && i == (int)input_regs.size())
			return;
	}
	functions[new Function(placeholders.size(), newE)] = 1;
}

static CrashSummary *
introduceCompoundFunctions(CrashSummary *summary,
			   int *f_cntr,
			   bool *done_something)
{
	summary = internCrashSummary(summary);

	reg_set_t constRegisters;
	{
		EnumRegistersTransformer er(constRegisters);
		StateIRExprTransformer<EnumRegistersTransformer> enumUsedRegisters(er);
		transformCrashSummary(summary, enumUsedRegisters);
		std::set<StateMachineSideEffect *> sideEffects;
		enumSideEffects(summary->loadMachine, sideEffects);
		enumSideEffects(summary->storeMachine, sideEffects);
		for (auto it = sideEffects.begin(); it != sideEffects.end(); it++) {
			threadAndRegister tr(threadAndRegister::invalid());
			if ((*it)->definesRegister(tr))
				constRegisters.erase(tr);
		}
	}
	if (debug_find_constants) {
		printf("Constant registers: ");
		printNamedSet(constRegisters);
		printf("\n");
	}

	/* Map from functions to raw number of places in which they
	 * can be used. */
	std::map<Function *, int> possibleFunctions;
	{
		struct _ : public StateMachineTransformer {
			std::map<Function *, int> &possibleFunctions;
			std::set<threadAndRegister, threadAndRegister::fullCompare> &constRegisters;
			IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
				bool found_one = false;
				for (auto it = possibleFunctions.begin(); it != possibleFunctions.end(); it++) {
					if (it->first->matches(e)) {
						found_one = true;
						it->second++;
					}
				}
				if (!found_one)
					introduceCandidateFunction(e, possibleFunctions, constRegisters);
				return IRExprTransformer::transformIRExpr(e, done_something);
			}
			bool rewriteNewStates() const { return false; }
		public:
			_(std::map<Function *, int> &_possibleFunctions,
			  std::set<threadAndRegister, threadAndRegister::fullCompare> &_constRegisters)
				: possibleFunctions(_possibleFunctions),
				  constRegisters(_constRegisters)
			{}
		} findPossibleFunctions(possibleFunctions, constRegisters);
		transformCrashSummary(summary, findPossibleFunctions);
	}
	if (debug_build_possible) {
		printf("Possible functions:\n");
		for (auto it = possibleFunctions.begin(); it != possibleFunctions.end(); it++)
			printf("\t%s -> %d\n", it->first->name(), it->second);
	}

	/* The usefulness of a function is roughly proportional to the
	   number of operations we could eliminate by using it.
	   That's in turn equal to the number of operations in the
	   function multiplied by the number of places it can be used.
	   Graph the best function. */
	Function *bestF = NULL;
	int bestUsefulness = -1;
	for (auto it = possibleFunctions.begin(); it != possibleFunctions.end(); it++) {
		if (it->second == 1)
			continue;
		int usefulness = it->second * it->first->complexity();
		if (usefulness > bestUsefulness) {
			bestUsefulness = usefulness;
			bestF = it->first;
		}
	}
	if (!bestF)
		return summary;

	if (debug_build_possible)
		printf("Select function %s\n", bestF->name());

	struct _ : public StateMachineTransformer {
		Function *f;
		IRCallee *cee;
		int *f_cntr;
		IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
			std::map<int, IRExpr *> argVals;
			if (f->matches(e, argVals)) {
				*done_something = true;
				if (!cee)
					cee = mkIRCallee(
						0,
						my_asprintf("f%d", (*f_cntr)++), /* XXX memory leak XXX */
						NULL);
				IRExpr **args;
				args = alloc_irexpr_array(argVals.size() + 1);
				for (int i = 0; i < (int)argVals.size(); i++) {
					assert(argVals[i+1]);
					args[i] = argVals[i+1];
				}
				args[argVals.size()] = NULL;
				IRExpr *res = IRExpr_CCall(cee, e->type(), args);
				if (debug_use_functions)
					printf("Transform %s to %s using %s\n",
					       nameIRExpr(e),
					       nameIRExpr(res),
					       f->name());
				return res;
			}
			return StateMachineTransformer::transformIRExpr(e, done_something);
		}
		bool rewriteNewStates() const { return false; }
	} doit;
	doit.f = bestF;
	doit.cee = NULL;
	doit.f_cntr = f_cntr;
	return transformCrashSummary(summary, doit, done_something);
}

int
main(int argc, char *argv[])
{
	init_sli();
	char *first_line;
	CrashSummary *summary = readBugReport(argv[1], &first_line);
	bool progress = true;
	int f_cntr = 0;
	while (progress) {
		progress = false;
		summary = introduceCompoundFunctions(summary, &f_cntr, &progress);
	}

	FILE *f = fopen(argv[2], "w");
	fprintf(f, "%s\n", first_line);
	printCrashSummary(summary, f);
	fclose(f);
	return 0;
}
