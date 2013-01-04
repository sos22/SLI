#include <err.h>

#include <map>

#include "sli.h"
#include "state_machine.hpp"
#include "oracle.hpp"
#include "simplify_irexpr.hpp"
#include "offline_analysis.hpp"
#include "alloc_mai.hpp"
#include "allowable_optimisations.hpp"
#include "visitor.hpp"

#include "libvex_parse.h"

#ifdef NDEBUG
#define debug_state_machine_sanity_checks 0
#else
static int debug_state_machine_sanity_checks = 0;
#endif

static unsigned current_optimisation_gen;

VexPtr<StateMachineSideEffectUnreached, &ir_heap> StateMachineSideEffectUnreached::_this;
VexPtr<StateMachineSideEffectStartAtomic, &ir_heap> StateMachineSideEffectStartAtomic::singleton;
VexPtr<StateMachineSideEffectEndAtomic, &ir_heap> StateMachineSideEffectEndAtomic::singleton;
AllowableOptimisations AllowableOptimisations::defaultOptimisations(7.3);

StateMachine *
StateMachine::optimise(SMScopes *scopes, const AllowableOptimisations &opt, bool *done_something)
{
	current_optimisation_gen++;
	if (current_optimisation_gen == 0)
		current_optimisation_gen = 1;

	bool b = false;
	StateMachineState *new_root = root->optimise(scopes, opt, &b);
	if (b) {
		*done_something = true;
		return new StateMachine(new_root, cfg_roots);
	} else {
		return this;
	}
}

StateMachineState *
StateMachineBifurcate::optimise(SMScopes *scopes, const AllowableOptimisations &opt, bool *done_something)
{
	if (current_optimisation_gen == last_optimisation_gen)
		return this;
	last_optimisation_gen = current_optimisation_gen;

	if (trueTarget == falseTarget) {
		*done_something = true;
		return trueTarget;
	}
	if (trueTarget->type == StateMachineState::Terminal &&
	    falseTarget->type == StateMachineState::Terminal) {
		*done_something = true;
		smrbdd *n = 
			smrbdd::ifelse(
				&scopes->smrs,
				condition,
				((StateMachineTerminal *)trueTarget)->res,
				((StateMachineTerminal *)falseTarget)->res);
		if (TIMEOUT)
			return this;
		return new StateMachineTerminal(dbg_origin, n);
	}
	set_condition(simplifyBDD(&scopes->bools, condition, opt));
	if (condition->isLeaf) {
		*done_something = true;
		if (condition->leaf())
			return trueTarget->optimise(scopes, opt, done_something);
		else
			return falseTarget->optimise(scopes, opt, done_something);
	}
	trueTarget = trueTarget->optimise(scopes, opt, done_something);
	falseTarget = falseTarget->optimise(scopes, opt, done_something);

	if (falseTarget->type == StateMachineState::Bifurcate) {
		StateMachineBifurcate *falseBifur = (StateMachineBifurcate *)falseTarget;
		if (falseTarget != falseBifur->falseTarget &&
		    trueTarget == falseBifur->trueTarget) {
			falseTarget = falseBifur->falseTarget;
			set_condition(bbdd::Or(&scopes->bools, condition, falseBifur->condition));
			*done_something = true;
			return this;
		}
		if (falseTarget != falseBifur->trueTarget &&
		    trueTarget == falseBifur->falseTarget) {
			falseTarget = falseBifur->trueTarget;
			set_condition(
				bbdd::Or(&scopes->bools,
					 condition,
					 bbdd::invert(&scopes->bools,
						      falseBifur->condition)));
			*done_something = true;
			return this;
		}
	}
	if (trueTarget->type == StateMachineState::Bifurcate) {
		StateMachineBifurcate *trueBifur = (StateMachineBifurcate *)trueTarget;
		if (trueTarget != trueBifur->trueTarget &&
		    falseTarget == trueBifur->falseTarget) {
			trueTarget = trueBifur->trueTarget;
			set_condition(
				bbdd::And(
					&scopes->bools,
					condition,
					trueBifur->condition));
			*done_something = true;
			return this;
		}
		if (trueTarget != trueBifur->falseTarget &&
		    falseTarget == trueBifur->trueTarget) {
			trueTarget = trueBifur->falseTarget;
			set_condition(
				bbdd::And(
					&scopes->bools,
					condition,
					bbdd::invert(
						&scopes->bools,
						trueBifur->condition)));
			*done_something = true;
			return this;
		}
	}

	return this;
}

StateMachineSideEffect *
StateMachineSideEffectStore::optimise(SMScopes *scopes, const AllowableOptimisations &opt, bool *done_something)
{
	addr = simplifyBDD(&scopes->exprs, &scopes->bools, addr, opt);
	data = simplifyBDD(&scopes->exprs, &scopes->bools, data, opt);
	if (isBadAddress(addr)) {
		*done_something = true;
		return StateMachineSideEffectUnreached::get();
	}
	return this;
}

StateMachineSideEffect *
StateMachineSideEffectLoad::optimise(SMScopes *scopes, const AllowableOptimisations &opt, bool *done_something)
{
	addr = simplifyBDD(&scopes->exprs, &scopes->bools, addr, opt);
	if (isBadAddress(addr)) {
		*done_something = true;
		return StateMachineSideEffectUnreached::get();
	}
	return this;
}

StateMachineSideEffect *
StateMachineSideEffectCopy::optimise(SMScopes *scopes, const AllowableOptimisations &opt, bool *)
{
	value = simplifyBDD(&scopes->exprs, &scopes->bools, value, opt);
	return this;
}

StateMachineSideEffect *
StateMachineSideEffectAssertFalse::optimise(SMScopes *scopes, const AllowableOptimisations &opt, bool *done_something)
{
	value = simplifyBDD(&scopes->bools, value, opt);
	if (value->isLeaf) {
		*done_something = true;
		if (value->leaf())
			return StateMachineSideEffectUnreached::get();
		else
			return NULL;
	}
	return this;
}

StateMachineSideEffect *
StateMachineSideEffectStartFunction::optimise(SMScopes *scopes, const AllowableOptimisations &opt, bool *)
{
	rsp = simplifyBDD(&scopes->exprs, &scopes->bools, rsp, opt);
	return this;
}

StateMachineSideEffect *
StateMachineSideEffectEndFunction::optimise(SMScopes *scopes, const AllowableOptimisations &opt, bool *)
{
	rsp = simplifyBDD(&scopes->exprs, &scopes->bools, rsp, opt);
	return this;
}

StateMachineSideEffect *
StateMachineSideEffectStartAtomic::optimise(SMScopes *, const AllowableOptimisations &opt, bool *done_something)
{
	if (opt.assumeExecutesAtomically()) {
		*done_something = true;
		return NULL;
	}
	return this;
}

StateMachineSideEffect *
StateMachineSideEffectEndAtomic::optimise(SMScopes *, const AllowableOptimisations &opt, bool *done_something)
{
	if (opt.assumeExecutesAtomically()) {
		*done_something = true;
		return NULL;
	}
	return this;
}

struct availEntry {
	IRExpr *addr;
	IRExpr *value;
	bool local;
	availEntry(IRExpr *a, IRExpr *v, bool l)
		: addr(a), value(v), local(l)
	{}
	bool operator<(const availEntry &o) const {
		if (addr < o.addr) return true;
		if (addr > o.addr) return false;
		if (value < o.value) return true;
		if (value > o.value) return false;
		if (local < o.local) return true;
		return false;
	}
};

static void
buildStateLabelTable(const StateMachineState *sm,
		     std::map<const StateMachineState *, int> &table,
		     std::vector<const StateMachineState *> &states)
{
	enumStates(sm, &states);
	for (unsigned x = 0; x < states.size(); x++)
		table[states[x]] = x + 1;
}

template <typename cont, void printer(const typename cont::value_type, FILE *)> static void
printContainer(const cont &v, FILE *f)
{
	fprintf(f, "[");
	for (auto it = v.begin(); it != v.end(); it++) {
		if (it != v.begin())
			fprintf(f, ", ");
		printer(*it, f);
	}
	fprintf(f, "]");
}

static void
printCFGRootedAt(const CFGNode *root, FILE *f,
		 std::set<const CFGNode *> &done,
		 const std::vector<std::pair<unsigned, const CFGNode *> > &roots)
{
	if (!done.insert(root).second)
		return;
	std::set<unsigned> rootOf;
	for (auto it = roots.begin(); it != roots.end(); it++)
		if (root == it->second)
			rootOf.insert(it->first);
	if (!rootOf.empty()) {
		int printed = 1;
		fprintf(f, "-");
		for (auto it = rootOf.begin(); it != rootOf.end(); it++) {
			if (it != rootOf.begin())
				printed += fprintf(f, ",");
			printed += fprintf(f, "%d", *it);
		}
		if (printed < 9) {
			char buf[] = "----------";
			fprintf(f, "%.*s", 9 - printed, buf);
		}
		fprintf(f, "->");
	} else {
		fprintf(f, ".%10s", "");
	}
	fprintf(f, "%s: %s",
		root->label.name(),
		root->rip.name());
	std::vector<CFGNode *> successors;
	bool done_one = false;
	for (auto it = root->successors.begin(); it != root->successors.end(); it++) {
		if (it->instr == NULL)
			continue;
		if (done_one)
			fprintf(f, ", ");
		else
			fprintf(f, " -> ");
		done_one = true;
		it->prettyPrint(f);
		successors.push_back(it->instr);
	}
	fprintf(f, "\n");
	for (auto it = successors.begin(); it != successors.end(); it++)
		printCFGRootedAt(*it, f, done, roots);
}

void
printStateMachine(const StateMachineState *sm, FILE *f, std::map<const StateMachineState *, int> &labels)
{
	std::vector<const StateMachineState *> states;
	buildStateLabelTable(sm, labels, states);
	for (auto it = states.begin(); it != states.end(); it++) {
		fprintf(f, "l%d: ", labels[*it]);
		(*it)->prettyPrint(f, labels);
		fprintf(f, "\n");
	}
}

void
printStateMachine(const std::set<const StateMachineState *> &sm, FILE *f, std::map<const StateMachineState *, int> &labels)
{
	std::set<const StateMachineState *> statesS;
	for (auto it = sm.begin(); it != sm.end(); it++)
		enumStates(*it, &statesS);
	std::vector<const StateMachineState *> statesV(statesS.begin(), statesS.end());
	for (unsigned x = 0; x < statesV.size(); x++)
		labels[statesV[x]] = x + 1;
	for (auto it = statesV.begin(); it != statesV.end(); it++) {
		fprintf(f, "l%d: ", labels[*it]);
		(*it)->prettyPrint(f, labels);
		fprintf(f, "\n");
	}
	fprintf(f, "Roots: [");
	for (auto it = sm.begin(); it != sm.end(); it++){
		if (it != sm.begin())
			fprintf(f, ", ");
		fprintf(f, "l%d", labels[*it]);
	}
	fprintf(f, "]\n");
}

void
printStateMachinePair(const char *label1, const StateMachine *sm1, const char *label2, const StateMachine *sm2, FILE *f)
{
	std::map<const StateMachineState *, int> labels;
	{
		std::vector<const StateMachineState *> states;
		enumStates(sm1, &states);
		enumStates(sm2, &states);
		for (unsigned x = 0; x < states.size(); x++)
			labels[states[x]] = x + 1;
	}

	fprintf(f, "%s", label1);
	{
		fprintf(f, "CFG:\n");
		std::set<const CFGNode *> done_cfg;
		for (auto it = sm1->cfg_roots.begin(); it != sm1->cfg_roots.end(); it++)
			printCFGRootedAt(it->second, f, done_cfg, sm1->cfg_roots);
		std::vector<const StateMachineState *> states;
		enumStates(sm1, &states);
		for (auto it = states.begin(); it != states.end(); it++) {
			fprintf(f, "l%d: ", labels[*it]);
			(*it)->prettyPrint(f, labels);
			fprintf(f, "\n");
		}
		fprintf(f, "Root: l%d\n", labels[sm1->root]);
	}

	fprintf(f, "%s", label2);
	{
		fprintf(f, "CFG:\n");
		std::set<const CFGNode *> done_cfg;
		for (auto it = sm2->cfg_roots.begin(); it != sm2->cfg_roots.end(); it++)
			printCFGRootedAt(it->second, f, done_cfg, sm2->cfg_roots);
		std::vector<const StateMachineState *> states;
		enumStates(sm2, &states);
		for (auto it = states.begin(); it != states.end(); it++) {
			fprintf(f, "l%d: ", labels[*it]);
			(*it)->prettyPrint(f, labels);
			fprintf(f, "\n");
		}
		fprintf(f, "Root: l%d\n", labels[sm2->root]);
	}
}

void
printStateMachine(const StateMachineState *sm, FILE *f)
{
	std::map<const StateMachineState *, int> labels;
	printStateMachine(sm, f, labels);
}

void
printStateMachine(const StateMachine *sm, FILE *f, std::map<const StateMachineState *, int> &labels)
{
	fprintf(f, "CFG:\n");
	std::set<const CFGNode *> done_cfg;
	for (auto it = sm->cfg_roots.begin(); it != sm->cfg_roots.end(); it++)
		printCFGRootedAt(it->second, f, done_cfg, sm->cfg_roots);
	printStateMachine(sm->root, f, labels);
	fprintf(f, "Root: l%d\n", labels[sm->root]);
}

void
printStateMachine(const StateMachine *sm, FILE *f)
{
	std::map<const StateMachineState *, int> labels;
	printStateMachine(sm, f, labels);
}

bool
StateMachineSideEffect::parse(SMScopes *scopes,
			      StateMachineSideEffect **out,
			      const char *str,
			      const char **suffix)
{
#define do_one(n)							\
	{								\
		StateMachineSideEffect ## n *res;			\
		/* shut compiler up */					\
		res = (StateMachineSideEffect ## n *)0xf001deadul;	\
		if (StateMachineSideEffect ## n :: parse(scopes, &res, str, suffix) ) { \
			*out = res;					\
			return true;					\
		}							\
	}
	all_side_effect_types(do_one)
#undef do_one
	return false;
}

/* State machine parser.  We cheat a little bit and stash the edge
 * labels in the target fields of state machine states until we have
 * find the state we're actually supposed to point at. */
static bool
parseStateMachineState(SMScopes *scopes, StateMachineState **out, const char *str, const char **suffix)
{
#define try_state_type(t)						\
	{								\
		StateMachine ## t *res;					\
		/* shut compiler up */					\
		res = (StateMachine ## t *)0xf001deadul;		\
		if (StateMachine ## t :: parse(scopes, &res, str, suffix)) { \
			*out = res;					\
			return true;					\
		}							\
	}
	all_state_types(try_state_type)
#undef try_state_type
	return false;
}

static bool
parseOneState(SMScopes *scopes,
	      std::map<int, StateMachineState *> &out,
	      const char *str,
	      const char **suffix)
{
	int label;
	StateMachineState *res;

	res = (StateMachineState *)0xf001; /* shut the compiler up */

	if (!parseThisChar('l', str, &str) ||
	    !parseDecimalInt(&label, str, &str) ||
	    !parseThisString(": ", str, &str) ||
	    !parseStateMachineState(scopes, &res, str, &str))
		return false;
	if (out.count(label))
		return false;
	out[label] = res;
	*suffix = str;
	return true;
}

static bool
parseStateMachine(SMScopes *scopes,
		  StateMachineState **out,
		  const char *str,
		  const char **suffix,
		  std::map<int, StateMachineState *> &labelToState)
{
	while (*str) {
		if (!parseOneState(scopes, labelToState, str, &str))
			break;
	}
	class _ {
	public:
		std::map<int, StateMachineState *> &labelToState;
		_(std::map<int, StateMachineState *> &_labelToState)
			: labelToState(_labelToState)
		{}
		bool operator()(StateMachineState *s) {
			std::vector<StateMachineState **> targets;
			s->targets(targets);
			for (auto it = targets.begin(); it != targets.end(); it++) {
				**it = labelToState[(int)(unsigned long)**it];
				if (!**it)
					return false;
			}
			return true;
		}
	} doOneState(labelToState);
	int root;
	if (!parseThisString("Root: l", str, &str) ||
	    !parseDecimalInt(&root, str, &str) ||
	    !parseThisChar('\n', str, &str))
		return false;
	for (auto it = labelToState.begin(); it != labelToState.end(); it++)
		if (!doOneState(it->second))
			return false;
	if (!labelToState.count(root))
		return false;
	*suffix = str;
	*out = labelToState[root];
	return true;
}

typedef CfgSuccessorT<CfgLabel> succ;

static bool
parseSucc(succ *out, const char *str, const char **suffix)
{
	if (!out->instr.parse(str, &str) ||
	    !parseThisChar(':', str, &str))
		return false;
	if (parseThisString("default", str, &str)) {
		out->type = succ_default;
	} else if (parseThisString("branch", str, &str)) {
		out->type = succ_branch;
	} else if (parseThisString("call", str, &str)) {
		out->type = succ_call;
	} else if (parseThisString("unroll", str, &str)) {
		out->type = succ_unroll;
	} else {
		return false;
	}
	parseThisChar(':', str, &str);
	if (!LibraryFunctionTemplate::parse(&out->calledFunction, str, &str))
		out->calledFunction = LibraryFunctionTemplate::none;
	*suffix = str;
	return true;
}

static bool
parseCFG(std::vector<std::pair<unsigned, const CFGNode *> > &roots,
	 const char *str, const char **suffix,
	 std::map<CfgLabel, const CFGNode *> &cfg_labels)
{
	std::map<CFGNode *, std::vector<succ> > relocations;
	while (1) {
		std::set<unsigned> rootOf;
		if (parseThisChar('-', str, &str)) {
			while (1) {
				unsigned v;
				if (!parseDecimalUInt(&v, str, &str))
					return false;
				rootOf.insert(v);
				if (parseThisChar(',', str, &str))
					continue;
				if (!parseThisChar('-', str, &str))
					return false;
				while (parseThisChar('-', str, &str))
					;
				if (!parseThisChar('>', str, &str))
					return false;
				break;
			}
		} else if (!parseThisString(". ", str, &str)) {
			break;
		}
		VexRip rip;
		CfgLabel label(CfgLabel::uninitialised());
		if (!label.parse(str, &str) ||
		    cfg_labels.count(label) ||
		    !parseThisString(": ", str, &str) ||
		    !parseVexRip(&rip, str, &str))
			return false;
		CFGNode *work = new CFGNode(rip, label);
		std::vector<succ> &successors(relocations[work]);
		if (parseThisString(" -> ", str, &str)) {
			succ l(succ::unroll(CfgLabel::uninitialised()));
			if (!parseSucc(&l, str, &str))
				return false;
			successors.push_back(l);
			while (1) {
				if (!parseThisString(", ", str, &str))
					break;
				if (!parseSucc(&l, str, &str))
					return false;
				successors.push_back(l);
			}
		}
		if (!parseThisChar('\n', str, &str))
			return false;
		cfg_labels[label] = work;
		for (auto it = rootOf.begin(); it != rootOf.end(); it++)
			roots.push_back(std::pair<unsigned, const CFGNode *>(*it, work));
	}
	for (auto it = relocations.begin(); it != relocations.end(); it++) {
		CFGNode *n = it->first;
		n->successors.resize(it->second.size(), CFGNode::successor_t(CFGNode::successor_t::unroll(NULL)));
		for (unsigned x = 0; x < it->second.size(); x++) {
			assert(cfg_labels.count(it->second[x].instr));
			n->successors[x] = CFGNode::successor_t(
				it->second[x],
				const_cast<CFGNode *>(cfg_labels[it->second[x].instr]));
		}
	}
	*suffix = str;
	return true;
}

bool
parseStateMachine(SMScopes *scopes,
		  StateMachine **out,
		  const char *str,
		  const char **suffix,
		  std::map<CfgLabel, const CFGNode *> &labelToNode)
{
	std::map<int, StateMachineState *> labelToState;
	StateMachineState *root;

	/* Shut the compiler up: it can't tell that
	   parseStateMachine() will always initialise root if it
	   returns true. */
	root = (StateMachineState *)0xf001deadbeeful; 

	std::vector<std::pair<unsigned, const CFGNode *> > cfg_roots;
	if (!parseThisString("CFG:\n", str, &str) ||
	    !parseCFG(cfg_roots, str, &str, labelToNode) ||
	    !parseStateMachine(scopes, &root, str, suffix, labelToState))
		return false;
	*out = new StateMachine(root, cfg_roots);
	return true;
}

StateMachine *
readStateMachine(SMScopes *scopes, int fd)
{
	char *content = readfile(fd);
	const char *end;
	StateMachine *res;
	if (!parseStateMachine(scopes, &res, content, &end) || *end)
		errx(1, "error parsing state machine:\n%s", content);
	free(content);
	return res;
}

StateMachine *
readStateMachine(SMScopes *scopes, const char *fname)
{
	int fd = open(fname, O_RDONLY);
	if (fd < 0)
		err(1, "opening %s", fname);
	char *content = readfile(fd);
	close(fd);

	const char *end;
	StateMachine *res;
	if (!parseStateMachine(scopes, &res, content, &end) || *end)
		errx(1, "error parsing state machine:\n%s", content);
	free(content);
	return res;
}

#ifndef NDEBUG
void
StateMachineState::assertAcyclic(std::vector<const StateMachineState *> &stack,
				std::set<const StateMachineState *> &clean) const
{
	if (clean.count(this))
		return;
	if (std::find(stack.begin(), stack.end(), this) != stack.end())
		goto found_cycle;
	stack.push_back(this);
	{
		std::vector<const StateMachineState *> targ;
		targets(targ);
		for (auto it = targ.begin(); it != targ.end(); it++)
			(*it)->assertAcyclic(stack, clean);
	}
	assert(stack.back() == this);
	stack.pop_back();
	clean.insert(this);
	return;

found_cycle:
	printf("Unexpected cycle in state machine!\n");
	printf("Found at %p\n", this);
	std::map<const StateMachineState *, int> labels;
	prettyPrint(stdout, labels);
	printf("Path: \n");
	for (auto it = stack.begin(); it != stack.end(); it++)
		printf("\t%d\n", labels[*it]);
	printf("End\n");
	assert(0);
}
#endif

#ifndef NDEBUG
void
StateMachine::assertAcyclic() const
{
	std::vector<const StateMachineState *> stack;
	std::set<const StateMachineState *> clean;
	root->assertAcyclic(stack, clean);
}
#endif

void
StateMachineState::enumerateMentionedMemoryAccesses(std::set<MemoryAccessIdentifier> &instrs)
{
	std::vector<StateMachineState *> targ;
	if (type == SideEffecting) {
		StateMachineSideEffecting *se = (StateMachineSideEffecting *)this;
		if (se->sideEffect) {
			StateMachineSideEffectMemoryAccess *smse =
				dynamic_cast<StateMachineSideEffectMemoryAccess *>(se->sideEffect);
			if (smse)
				instrs.insert(smse->rip);
		}
	}
	targets(targ);
	for (auto it = targ.begin(); it != targ.end(); it++)
		(*it)->enumerateMentionedMemoryAccesses(instrs);
}

StateMachineState::RoughLoadCount
StateMachineState::roughLoadCount(StateMachineState::RoughLoadCount acc) const
{
	if (acc == StateMachineState::multipleLoads)
		return StateMachineState::multipleLoads;

	if (type == SideEffecting) {
		StateMachineSideEffecting *se = (StateMachineSideEffecting *)this;
		if (se->sideEffect && dynamic_cast<StateMachineSideEffectLoad *>(se->sideEffect)) {
			if (acc == noLoads)
				acc = singleLoad;
			else
				acc = multipleLoads;
		}
	}
	std::vector<const StateMachineState *> targ;
	targets(targ);
	for (auto it = targ.begin();
	     acc != multipleLoads && it != targ.end();
	     it++)
		acc = (*it)->roughLoadCount(acc);
	return acc;
}

void
StateMachineState::targets(std::queue<StateMachineState *> &out)
{
	std::vector<StateMachineState *> edges;
	targets(edges);
	for (auto it = edges.begin(); it != edges.end(); it++)
		out.push(*it);
}

#ifndef NDEBUG
void
StateMachine::assertSSA() const
{
	std::set<const StateMachineSideEffecting *> states;
	enumStates(this, &states);
	std::set<threadAndRegister> discoveredAssignments;
	for (auto it = states.begin(); it != states.end(); it++) {
		StateMachineSideEffect *smse = (*it)->sideEffect;
		if (!smse)
			continue;
		threadAndRegister tr(threadAndRegister::invalid());
		if (smse->definesRegister(tr)) {
			assert(tr.gen() != 0);
			if (!discoveredAssignments.insert(tr).second)
				abort();
		}
	}

	struct {
		static visit_result Get(void *, const IRExprGet *ieg) {
			assert(ieg->reg.gen() != 0);
			return visit_continue;
		}
	} foo;
	static irexpr_visitor<void> visitor;
	visitor.Get = foo.Get;
	visit_state_machine((void *)NULL, &visitor, this);
}
#endif

void
StateMachineSideEffecting::prependSideEffect(StateMachineSideEffect *se)
{
	if (sideEffect)
		target = new StateMachineSideEffecting(dbg_origin, sideEffect, target);
	sideEffect = se;
}

StateMachineState *
StateMachineSideEffecting::optimise(SMScopes *scopes, const AllowableOptimisations &opt, bool *done_something)
{
	if (current_optimisation_gen == last_optimisation_gen || TIMEOUT)
		return this;
	last_optimisation_gen = current_optimisation_gen;
	if (!sideEffect) {
		*done_something = true;
		return target->optimise(scopes, opt, done_something);
	}

	if (target->type == StateMachineState::Terminal &&
	    ((StateMachineTerminal *)target)->res == scopes->smrs.cnst(smr_unreached)) {
		*done_something = true;
		return target;
	}
	if (sideEffect->type == StateMachineSideEffect::Unreached) {
		*done_something = true;
		return new StateMachineTerminal(dbg_origin, scopes->smrs.cnst(smr_unreached));
	}
	sideEffect = sideEffect->optimise(scopes, opt, done_something);
	target = target->optimise(scopes, opt, done_something);
	if (!sideEffect) {
		assert(*done_something);
		return target;
	}

	if (sideEffect->type == StateMachineSideEffect::AssertFalse &&
	    target->type == StateMachineState::SideEffecting &&
	    ((StateMachineSideEffecting *)target)->sideEffect &&
	    ((StateMachineSideEffecting *)target)->sideEffect->type == StateMachineSideEffect::EndAtomic) {
		StateMachineSideEffecting *t = (StateMachineSideEffecting *)target;
		assert(sideEffect->type != StateMachineSideEffect::EndAtomic);
		*done_something = true;
		return (new StateMachineSideEffecting(
				t->dbg_origin,
				t->sideEffect,
				new StateMachineSideEffecting(
					dbg_origin,
					sideEffect,
					t->target)))->optimise(scopes, opt, done_something);
	}

	if (sideEffect->type == StateMachineSideEffect::StartAtomic) {
		if (target->type == StateMachineState::SideEffecting) {
			StateMachineSideEffecting *t = (StateMachineSideEffecting *)target;
			if (t->sideEffect && t->sideEffect->type == StateMachineSideEffect::EndAtomic) {
				/* Remove empty atomic section */
				*done_something = true;
				return t->target;
			}

			if (t->sideEffect && t->sideEffect->type == StateMachineSideEffect::AssertFalse) {
				/* Pull non-memory-accesses out of
				 * atomic blocks whenever possible. */
				*done_something = true;
				return (new StateMachineSideEffecting(
						t->dbg_origin,
						t->sideEffect,
						new StateMachineSideEffecting(
							dbg_origin,
							sideEffect,
							t->target)))->optimise(scopes, opt, done_something);
			}
		} else if (target->type == StateMachineState::Terminal) {
			/* START_ATOMIC followed by a terminal is a
			 * bit pointless. */
			*done_something = true;
			return target;
		} else {
			/* It's a bifurcate i.e. we have
			   START_ATOMIC; if (x) a else b.
			   You might think we'd want to transform
			   that to

			   if (x) {
			      START_ATOMIC
			      a
			   } else { 
			      START_ATOMIC
			      b
			   }

			   which would shrink the size of the atomic
			   block, but we then get into an infinite
			   loop where the other analyses then go and
			   undo it.  That could be fixed, but it
			   wouldn't actually do any good: it'd only
			   matter if the first things in a and b were
			   END_ATOMICs, but in that case we'll already
			   merge across the condition and it's all
			   fine. */
		}
	}

	if (sideEffect->type == StateMachineSideEffect::StartFunction &&
	    target->type == StateMachineState::SideEffecting &&
	    ((StateMachineSideEffecting *)target)->sideEffect &&
	    ((StateMachineSideEffecting *)target)->sideEffect->type == StateMachineSideEffect::EndFunction) {
		/* No point in keeping an empty
		 * StartFunction/EndFunction block. */
		*done_something = true;
		return ((StateMachineSideEffecting *)target)->target;
	}

	if (sideEffect->type == StateMachineSideEffect::AssertFalse &&
	    target->type == StateMachineState::SideEffecting &&
	    ((StateMachineSideEffecting *)target)->sideEffect &&
	    ((StateMachineSideEffecting *)target)->sideEffect->type == StateMachineSideEffect::AssertFalse &&
	    ((StateMachineSideEffectAssertFalse *)((StateMachineSideEffecting *)target)->sideEffect)->reflectsActualProgram ==
	    ((StateMachineSideEffectAssertFalse *)sideEffect)->reflectsActualProgram) {
		/* Take:

		   assert(!x);
		   assert(!y);

		   and turn it into

		   assert(!x && !y) -> assert(!(x || y));
		*/
		*done_something = true;
		sideEffect = new StateMachineSideEffectAssertFalse(
			bbdd::Or(
				&scopes->bools,
				((StateMachineSideEffectAssertFalse *)sideEffect)->value,
				((StateMachineSideEffectAssertFalse *)((StateMachineSideEffecting *)target)->sideEffect)->value),
			((StateMachineSideEffectAssertFalse *)sideEffect)->reflectsActualProgram);
		sideEffect = sideEffect->optimise(scopes, opt, done_something);
		target = ((StateMachineSideEffecting *)target)->target;
		return this;
	}

	return this;
}

template <typename t, typename s> static bool
intersectSets(std::set<t, s> &out, const std::set<t, s> &inp)
{
	bool res = false;
	for (auto it1 = out.begin(); it1 != out.end(); ) {
		if (inp.count(*it1)) {
			it1++;
		} else {
			out.erase(it1++);
			res = true;
		}
	}
	return res;
}

#ifndef NDEBUG
void
StateMachine::sanityCheck(const MaiMap &mai, SMScopes *scopes) const
{
	/* These are expensive enough that we don't want them on
	   unconditionally even in !NDEBUG builds. */
	if (!debug_state_machine_sanity_checks)
		return;

	std::set<const StateMachineState *> allStates;
	enumStates(this, &allStates);
	for (auto it = allStates.begin(); it != allStates.end(); it++)
		(*it)->sanityCheck(scopes);

	struct {
		static visit_result HappensBefore(std::set<MemoryAccessIdentifier> *neededMais,
						  const IRExprHappensBefore *hb)
		{
			neededMais->insert(hb->before);
			neededMais->insert(hb->after);
			return visit_continue;
		}
		static visit_result Load(std::set<MemoryAccessIdentifier> *neededMais,
					 const StateMachineSideEffectLoad *smse)
		{
			neededMais->insert(smse->rip);
			return visit_continue;
		}
		static visit_result Store(std::set<MemoryAccessIdentifier> *neededMais,
					  const StateMachineSideEffectStore *smse)
		{
			neededMais->insert(smse->rip);
			return visit_continue;
		}
	} foo;
	static state_machine_visitor<std::set<MemoryAccessIdentifier> > visitor;
	visitor.irexpr.HappensBefore = foo.HappensBefore;
	visitor.Load = foo.Load;
	visitor.Store = foo.Store;
	std::set<MemoryAccessIdentifier> neededMais;
	visit_state_machine(&neededMais, &visitor, this);

	std::set<const CFGNode *> neededLabels;
	for (auto it = neededMais.begin(); it != neededMais.end(); it++) {
		for (auto it2 = mai.begin(*it); !it2.finished(); it2.advance())
			neededLabels.insert(it2.node());
	}

	std::queue<const CFGNode *> pending;
	for (auto it = cfg_roots.begin(); it != cfg_roots.end(); it++)
		pending.push(it->second);
	while (!pending.empty()) {
		const CFGNode *n = pending.front();
		pending.pop();
		neededLabels.erase(n);
		for (auto it = n->successors.begin(); it != n->successors.end(); it++)
			if (it->instr)
				pending.push(it->instr);
	}
	assert(neededLabels.empty());
}
#endif

MemoryAccessIdentifier
MaiMap::operator()(unsigned tid, const CFGNode *node)
{
	MemoryAccessIdentifier res(nextId, tid);
	nextId++;
	assert(!maiCorrespondence->count(res));
	(*maiCorrespondence)[res].push_back(node);
	return res;
}

IRExpr *
MaiMap::freeVariable(IRType ty, unsigned tid, const CFGNode *node, bool isUnique)
{
	return IRExpr_FreeVariable((*this)(tid, node), ty, isUnique);
}

void
MaiMap::print(FILE *f) const
{
	fprintf(f, "Memory access identifiers:\n");
	for (auto it = maiCorrespondence->begin(); it != maiCorrespondence->end(); it++) {
		fprintf(f, "\t%s -> {", it->first.name());
		bool n = false;
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			if (n && !*it2)
				continue;
			if (it2 != it->second.begin())
				fprintf(f, ", ");
			if (*it2) {
				fprintf(f, "%s", (*it2)->label.name());
			} else {
				fprintf(f, "<null>");
				n = true;
			}
		}
		fprintf(f, "}\n");
	}
	fprintf(f, "Next id %d\n", nextId);
}

MaiMap *
MaiMap::parse(const std::map<CfgLabel, const CFGNode *> &labels, const char *buf, const char **suffix)
{
	if (!parseThisString("Memory access identifiers:\n", buf, &buf))
		return false;
	std::map<MemoryAccessIdentifier, std::vector<const CFGNode *> > *res =
		new std::map<MemoryAccessIdentifier, std::vector<const CFGNode *> >();
	while (1) {
		int nextId;
		if (parseThisString("Next id ", buf, &buf) &&
		    parseDecimalInt(&nextId, buf, suffix))
			return new MaiMap(nextId, res);
		MemoryAccessIdentifier mai(MemoryAccessIdentifier::uninitialised());
		if (!mai.parse(buf, &buf) ||
		    !parseThisString(" -> {", buf, &buf))
			break;
		std::vector<const CFGNode *> entry;
		if (!parseThisChar('}', buf, &buf)) {
			CfgLabel l(CfgLabel::uninitialised());
			if (parseThisString("<null>", buf, &buf)) {
				entry.push_back(NULL);
			} else {
				if (!l.parse(buf, &buf))
					break;
				auto it = labels.find(l);
				if (it != labels.end())
					entry.push_back(it->second);
			}
			while (!parseThisChar('}', buf, &buf)) {
				if (!parseThisString(", ", buf, &buf))
					goto failed;
				if (parseThisString("<null>", buf, &buf)) {
					entry.push_back(NULL);
				} else {
					if (!l.parse(buf, &buf))
						goto failed;
					auto it = labels.find(l);
					if (it != labels.end())
						entry.push_back(it->second);
				}
			}
		}
		if (!parseThisChar('\n', buf, &buf))
			break;
		auto it_did_insert = res->insert(std::pair<MemoryAccessIdentifier, std::vector<const CFGNode *> >(mai, entry));
		if (!it_did_insert.second)
			break;
	}
failed:
	delete res;
	return NULL;
}

MaiMap *
MaiMap::fromFile(const StateMachine *sm1, const StateMachine *sm2, const char *fname)
{
	std::map<CfgLabel, const CFGNode *> lookup;
	std::queue<const CFGNode *> pending;
	for (auto it = sm1->cfg_roots.begin(); it != sm1->cfg_roots.end(); it++)
		pending.push(it->second);
	if (sm2) {
		for (auto it = sm2->cfg_roots.begin(); it != sm2->cfg_roots.end(); it++)
			pending.push(it->second);
	}
	while (!pending.empty()) {
		const CFGNode *n = pending.front();
		pending.pop();
		auto it_did_insert = lookup.insert(std::pair<CfgLabel, const CFGNode *>(n->label, n));
		auto did_insert = it_did_insert.second;
		if (did_insert) {
			for (auto it = n->successors.begin(); it != n->successors.end(); it++)
				pending.push(it->instr);
		}
	}

	int fd = open(fname, O_RDONLY);
	if (fd < 0)
		err(1, "opening %s", fname);
	char *buf = readfile(fd);
	const char *suffix;
	MaiMap *res = parse(lookup, buf, &suffix);
	free(buf);
	return res;
}

MaiMap *
MaiMap::fromFile(const StateMachine *sm1, const char *fname)
{
	return fromFile(sm1, NULL, fname);
}

void
dumpStateMachine(const StateMachine *sm, const char *fname)
{
	FILE *f = fopen(fname, "w");
	printStateMachine(sm, f);
	fclose(f);
}

void
MaiMap::restrict(const std::set<const CFGNode *> &cfgNodes,
		 const std::set<MemoryAccessIdentifier> &mais)
{
	for (auto it = maiCorrespondence->begin();
	     it != maiCorrespondence->end();
		) {
		if (!mais.count(it->first)) {
			maiCorrespondence->erase(it++);
			continue;
		}
		for (auto it2 = it->second.begin(); it2 != it->second.end(); ) {
			if (cfgNodes.count(*it2)) {
				it2++;
			} else {
				it2 = it->second.erase(it2);
			}
		}
		it++;
	}
}

AllowableOptimisations
AllowableOptimisations::fromFile(std::set<DynAnalysisRip> *is, std::set<DynAnalysisRip> *nll,
				 AddressSpace *as, const char *path)
{
	int fd = open(path, O_RDONLY);
	if (fd < 0)
		err(1, "opening %s\n", path);
	char *content = readfile(fd);
	if (!content)
		err(1, "reading %s\n", path);
	close(fd);

	AllowableOptimisations res(1.0);
	const char *p;
	if (!res.parse(is, nll, as, content, &p))
		err(1, "parsing %s as AllowableOptimisations set", content);
	free(content);
	return res;
}

void
StateMachineBifurcate::prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const
{
	fprintf(f, "%s: if ()\n", dbg_origin.name());
	condition->prettyPrint(f);
	fprintf(f, "then: l%d\n else: l%d\n",
		labels[trueTarget], labels[falseTarget]);
}
bool
StateMachineBifurcate::parse(SMScopes *scopes, StateMachineBifurcate **out, const char *str, const char **suffix)
{
	VexRip origin;
	int targ1;
	int targ2;
	bbdd *condition;
	if (!parseVexRip(&origin, str, &str) ||
	    !parseThisString(": if ()", str, &str) ||
	    !bbdd::parse(&scopes->bools, &condition, str, &str) ||
	    !parseThisString("then: l", str, &str) ||
	    !parseDecimalInt(&targ1, str, &str) ||
	    !parseThisString(" else: l", str, &str) ||
	    !parseDecimalInt(&targ2, str, &str) ||
	    !parseThisChar('\n', str, suffix))
		return false;
	*out = new StateMachineBifurcate(origin,
					 condition,
					 (StateMachineState *)targ1,
					 (StateMachineState *)targ2);
	return true;
}

void
StateMachineTerminal::prettyPrint(FILE *f, std::map<const StateMachineState *, int> &) const
{
	fprintf(f, "%s: terminal:\n", dbg_origin.name());
	res->prettyPrint(f);
}
bool
StateMachineTerminal::parse(SMScopes *scopes, StateMachineTerminal **out, const char *str, const char **suffix)
{
	VexRip origin;
	smrbdd *res;
	if (!parseVexRip(&origin, str, &str) ||
	    !parseThisString(": terminal:", str, &str) ||
	    !smrbdd::parse(&scopes->smrs, &res, str, suffix))
		return false;
	*out = new StateMachineTerminal(origin, res);
	return true;
}

bool
parseSmr(StateMachineRes *out, const char *str, const char **suffix)
{
	if (parseThisString("crash", str, suffix)) {
		*out = smr_crash;
		return true;
	} else if (parseThisString("survive", str, suffix)) {
		*out = smr_survive;
		return true;
	} else if (parseThisString("unreached", str, suffix)) {
		*out = smr_unreached;
		return true;
	} else {
		return false;
	}
}

bool
SMScopes::read(const char *fname)
{
	int fd = open(fname, O_RDONLY);
	if (fd < 0)
		return -1;
	char *content = readfile(fd);
	close(fd);
	const char *end;
	bool res = parse(content, &end);
	free(content);
	return res;
}

void
SMScopes::prettyPrint(FILE *f) const
{
	ordering.prettyPrint(f);
}

bool
SMScopes::parse(const char *buf, const char **end)
{
	return ordering.parse(buf, end);
}

StateMachineState *
StateMachineTerminal::optimise(SMScopes *scopes, const AllowableOptimisations &opt, bool *)
{
	if (current_optimisation_gen == last_optimisation_gen)
		return this;
	last_optimisation_gen = current_optimisation_gen;

	set_res(simplifyBDD(&scopes->smrs, &scopes->bools, res, opt));
	return this;
}
