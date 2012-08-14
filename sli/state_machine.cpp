#include <err.h>

#include <map>

#include "sli.h"
#include "state_machine.hpp"
#include "oracle.hpp"
#include "simplify_irexpr.hpp"
#include "offline_analysis.hpp"
#include "alloc_mai.hpp"
#include "allowable_optimisations.hpp"

#include "libvex_parse.h"

#ifdef NDEBUG
#define debug_state_machine_sanity_checks 0
#else
static int debug_state_machine_sanity_checks = 0;
#endif

VexPtr<StateMachineSideEffectUnreached, &ir_heap> StateMachineSideEffectUnreached::_this;
VexPtr<StateMachineSideEffectStartAtomic, &ir_heap> StateMachineSideEffectStartAtomic::singleton;
VexPtr<StateMachineSideEffectEndAtomic, &ir_heap> StateMachineSideEffectEndAtomic::singleton;
VexPtr<StateMachineUnreached, &ir_heap> StateMachineUnreached::_this;
VexPtr<StateMachineCrash, &ir_heap> StateMachineCrash::_this;
VexPtr<StateMachineNoCrash, &ir_heap> StateMachineNoCrash::_this;
AllowableOptimisations AllowableOptimisations::defaultOptimisations(7.3);

StateMachine *
StateMachine::optimise(const AllowableOptimisations &opt, bool *done_something)
{
	bool b = false;
	StateMachineState *new_root = root->optimise(opt, &b);
	if (b) {
		*done_something = true;
		return new StateMachine(new_root, bad_origin, cfg_roots);
	} else {
		return this;
	}
}

StateMachineState *
StateMachineBifurcate::optimise(const AllowableOptimisations &opt, bool *done_something)
{
	if (trueTarget == StateMachineUnreached::get()) {
		*done_something = true;
		if (falseTarget == StateMachineUnreached::get())
			return StateMachineUnreached::get();
		return (new StateMachineSideEffecting(
				origin,
				new StateMachineSideEffectAssertFalse(
					condition,
					true),
				falseTarget))->optimise(opt, done_something);
	}
	if (falseTarget == StateMachineUnreached::get()) {
		*done_something = true;
		return (new StateMachineSideEffecting(
				origin,
				new StateMachineSideEffectAssertFalse(
					IRExpr_Unop(
						Iop_Not1,
						condition),
					true),
				trueTarget))->optimise(opt, done_something);
	}
	if (trueTarget == falseTarget) {
		*done_something = true;
		return trueTarget;
	}
	condition = optimiseIRExprFP(condition, opt, done_something);
	if (condition->tag == Iex_Const) {
		*done_something = true;
		if (((IRExprConst *)condition)->con->Ico.U1)
			return trueTarget->optimise(opt, done_something);
		else
			return falseTarget->optimise(opt, done_something);
	}
	if (condition->tag == Iex_Unop && ((IRExprUnop *)condition)->op == Iop_Not1) {
		*done_something = true;
		condition = ((IRExprUnop *)condition)->arg;
		StateMachineState *t = trueTarget;
		trueTarget = falseTarget;
		falseTarget = t;
	}
	if (definitelyUnevaluatable(condition)) {
		*done_something = true;
		return StateMachineUnreached::get();
	}
	trueTarget = trueTarget->optimise(opt, done_something);
	falseTarget = falseTarget->optimise(opt, done_something);

	if (falseTarget->type == StateMachineState::Bifurcate) {
		StateMachineBifurcate *falseBifur = (StateMachineBifurcate *)falseTarget;
		if (falseTarget != falseBifur->falseTarget &&
		    trueTarget == falseBifur->trueTarget) {
			falseTarget = falseBifur->falseTarget;
			condition = IRExpr_Binop(
				Iop_Or1,
				condition,
				falseBifur->condition);
			*done_something = true;
			return this;
		}
		if (falseTarget != falseBifur->trueTarget &&
		    trueTarget == falseBifur->falseTarget) {
			falseTarget = falseBifur->trueTarget;
			condition = IRExpr_Binop(
				Iop_Or1,
				condition,
				IRExpr_Unop(
					Iop_Not1,
					falseBifur->condition));
			*done_something = true;
			return this;
		}
	}
	if (trueTarget->type == StateMachineState::Bifurcate) {
		StateMachineBifurcate *trueBifur = (StateMachineBifurcate *)trueTarget;
		if (trueTarget != trueBifur->trueTarget &&
		    falseTarget == trueBifur->falseTarget) {
			trueTarget = trueBifur->trueTarget;
			condition = IRExpr_Binop(
				Iop_And1,
				condition,
				trueBifur->condition);
			*done_something = true;
			return this;
		}
		if (trueTarget != trueBifur->falseTarget &&
		    falseTarget == trueBifur->trueTarget) {
			trueTarget = trueBifur->falseTarget;
			condition = IRExpr_Binop(
				Iop_And1,
				condition,
				IRExpr_Unop(
					Iop_Not1,
					trueBifur->condition));
			*done_something = true;
			return this;
		}
	}
	return this;
}

StateMachineSideEffect *
StateMachineSideEffectStore::optimise(const AllowableOptimisations &opt, bool *done_something)
{
	addr = optimiseIRExprFP(addr, opt, done_something);
	data = optimiseIRExprFP(data, opt, done_something);
	if (isBadAddress(addr) || definitelyUnevaluatable(data)) {
		*done_something = true;
		return StateMachineSideEffectUnreached::get();
	}
	return this;
}
void
StateMachineSideEffectStore::updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &opt)
{
	for (std::set<IRExpr *>::iterator it = l.begin();
	     it != l.end();
		) {
		if (definitelyEqual(*it, addr, opt))
			l.erase(it++);
		else
			it++;
	}
}

StateMachineSideEffect *
StateMachineSideEffectLoad::optimise(const AllowableOptimisations &opt, bool *done_something)
{
	addr = optimiseIRExprFP(addr, opt, done_something);
	if (isBadAddress(addr)) {
		*done_something = true;
		return StateMachineSideEffectUnreached::get();
	}
	return this;
}

StateMachineSideEffect *
StateMachineSideEffectCopy::optimise(const AllowableOptimisations &opt, bool *done_something)
{
	value = optimiseIRExprFP(value, opt, done_something);
	if (definitelyUnevaluatable(value)) {
		*done_something = true;
		return StateMachineSideEffectUnreached::get();
	}
	return this;
}

StateMachineSideEffect *
StateMachineSideEffectAssertFalse::optimise(const AllowableOptimisations &opt, bool *done_something)
{
	value = optimiseIRExprFP(value, opt, done_something);
	if ((value->tag == Iex_Const && ((IRExprConst *)value)->con->Ico.U1) ||
	    definitelyUnevaluatable(value)) {
		*done_something = true;
		return StateMachineSideEffectUnreached::get();
	}
	if (value->tag == Iex_Const && !((IRExprConst *)value)->con->Ico.U1) {
		*done_something = true;
		return NULL;
	}
	return this;
}

StateMachineSideEffect *
StateMachineSideEffectStartFunction::optimise(const AllowableOptimisations &opt, bool *done_something)
{
	rsp = optimiseIRExprFP(rsp, opt, done_something);
	return this;
}

StateMachineSideEffect *
StateMachineSideEffectEndFunction::optimise(const AllowableOptimisations &opt, bool *done_something)
{
	rsp = optimiseIRExprFP(rsp, opt, done_something);
	return this;
}

StateMachineSideEffect *
StateMachineSideEffectStartAtomic::optimise(const AllowableOptimisations &opt, bool *done_something)
{
	if (opt.assumeExecutesAtomically()) {
		*done_something = true;
		return NULL;
	}
	return this;
}

StateMachineSideEffect *
StateMachineSideEffectEndAtomic::optimise(const AllowableOptimisations &opt, bool *done_something)
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
buildStateLabelTable(const StateMachine *sm,
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
		 const std::vector<const CFGNode *> &roots)
{
	if (!done.insert(root).second)
		return;
	bool is_root = false;
	for (auto it = roots.begin(); !is_root && it != roots.end(); it++)
		if (root == *it)
			is_root = true;
	fprintf(f, "%s%s: %s",
		is_root ? "-->" : ".  ",
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
		fprintf(f, "%s:", it->instr->label.name());
		switch (it->type) {
		case CFGNode::successor_t::succ_default:
			fprintf(f, "default");
			break;
		case CFGNode::successor_t::succ_branch:
			fprintf(f, "branch");
			break;
		case CFGNode::successor_t::succ_call:
			fprintf(f, "call");
			break;
		case CFGNode::successor_t::succ_unroll:
			fprintf(f, "unroll");
			break;
		}
		if (it->calledFunction != LibraryFunctionTemplate::none) {
			fprintf(f, ":");
			LibraryFunctionTemplate::pp(it->calledFunction, f);
		}
		successors.push_back(it->instr);
	}
	fprintf(f, "\n");
	for (auto it = successors.begin(); it != successors.end(); it++)
		printCFGRootedAt(*it, f, done, roots);
}

void
printStateMachine(const StateMachine *sm, FILE *f, std::map<const StateMachineState *, int> &labels)
{
	std::vector<const StateMachineState *> states;

	fprintf(f, "Machine for ");
	for (auto it = sm->bad_origin.begin(); it != sm->bad_origin.end(); it++) {
		if (it != sm->bad_origin.begin())
			fprintf(f, ", ");
		fprintf(f, "%s:%d", it->second.name(), it->first);
	}
	fprintf(f, ":\n");
	fprintf(f, "CFG:\n");
	std::set<const CFGNode *> done_cfg;
	for (auto it = sm->cfg_roots.begin(); it != sm->cfg_roots.end(); it++)
		printCFGRootedAt(*it, f, done_cfg, sm->cfg_roots);
	buildStateLabelTable(sm, labels, states);
	for (auto it = states.begin(); it != states.end(); it++) {
		fprintf(f, "l%d: ", labels[*it]);
		(*it)->prettyPrint(f, labels);
		fprintf(f, "\n");
	}
}

void
printStateMachine(const StateMachine *sm, FILE *f)
{
	std::map<const StateMachineState *, int> labels;
	printStateMachine(sm, f, labels);
}

bool
sideEffectsBisimilar(StateMachineSideEffect *smse1,
		     StateMachineSideEffect *smse2,
		     const AllowableOptimisations &opt)
{
	if (smse1 == smse2)
		return true;
	if (smse1 == NULL || smse2 == NULL)
		return false;
	if (smse1->type != smse2->type)
		return false;
	switch (smse1->type) {
	case StateMachineSideEffect::Store: {
		StateMachineSideEffectStore *smses1 =
			dynamic_cast<StateMachineSideEffectStore *>(smse1);
		StateMachineSideEffectStore *smses2 =
			dynamic_cast<StateMachineSideEffectStore *>(smse2);
		return smses1->data->type() == smses2->data->type() &&
			definitelyEqual(smses1->addr, smses2->addr, opt) &&
			definitelyEqual(smses1->data, smses2->data, opt);
	}
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *smsel1 =
			dynamic_cast<StateMachineSideEffectLoad *>(smse1);
		StateMachineSideEffectLoad *smsel2 =
			dynamic_cast<StateMachineSideEffectLoad *>(smse2);
		return threadAndRegister::fullEq(smsel1->target, smsel2->target) &&
			smsel1->type == smsel2->type &&
			definitelyEqual(smsel1->addr, smsel2->addr, opt);
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec1 =
			dynamic_cast<StateMachineSideEffectCopy *>(smse1);
		StateMachineSideEffectCopy *smsec2 =
			dynamic_cast<StateMachineSideEffectCopy *>(smse2);
		return threadAndRegister::fullEq(smsec1->target, smsec2->target) &&
			smsec1->value->type() == smsec2->value->type() &&
			definitelyEqual(smsec1->value, smsec2->value, opt);
	}
	case StateMachineSideEffect::Unreached:
		return true;
	case StateMachineSideEffect::AssertFalse: {
		StateMachineSideEffectAssertFalse *smseaf1 =
			dynamic_cast<StateMachineSideEffectAssertFalse *>(smse1);
		StateMachineSideEffectAssertFalse *smseaf2 =
			dynamic_cast<StateMachineSideEffectAssertFalse *>(smse2);
		return definitelyEqual(smseaf1->value, smseaf2->value, opt);
	}
	case StateMachineSideEffect::Phi: {
		StateMachineSideEffectPhi *smsep1 =
			(StateMachineSideEffectPhi *)smse1;
		StateMachineSideEffectPhi *smsep2 =
			(StateMachineSideEffectPhi *)smse2;
		return threadAndRegister::fullEq(smsep1->reg, smsep2->reg) &&
			smsep1->generations == smsep2->generations;
	}
	case StateMachineSideEffect::StartFunction: {
		StateMachineSideEffectStartFunction *smsep1 =
			(StateMachineSideEffectStartFunction *)smse1;
		StateMachineSideEffectStartFunction *smsep2 =
			(StateMachineSideEffectStartFunction *)smse2;
		return definitelyEqual(smsep1->rsp, smsep2->rsp, opt);
	}
	case StateMachineSideEffect::EndFunction: {
		StateMachineSideEffectEndFunction *smsep1 =
			(StateMachineSideEffectEndFunction *)smse1;
		StateMachineSideEffectEndFunction *smsep2 =
			(StateMachineSideEffectEndFunction *)smse2;
		return definitelyEqual(smsep1->rsp, smsep2->rsp, opt);
	}
	case StateMachineSideEffect::StartAtomic:
	case StateMachineSideEffect::EndAtomic:
		/* These are singletons, so should have been handled
		   by the smse1 == smse2 test above. */
		abort();
	}
	abort();
}

bool
StateMachineSideEffect::parse(StateMachineSideEffect **out,
			      const char *str,
			      const char **suffix)
{
#define do_one(n)							\
	{								\
		StateMachineSideEffect ## n *res;			\
		/* shut compiler up */					\
		res = (StateMachineSideEffect ## n *)0xf001deadul;	\
		if (StateMachineSideEffect ## n :: parse(&res, str, suffix) ) {	\
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
parseStateMachineState(StateMachineState **out, const char *str, const char **suffix)
{
#define try_state_type(t)						\
	{								\
		StateMachine ## t *res;					\
		/* shut compiler up */					\
		res = (StateMachine ## t *)0xf001deadul;		\
		if (StateMachine ## t :: parse(&res, str, suffix)) {	\
			*out = res;					\
			return true;					\
		}							\
	}
	all_state_types(try_state_type)
#undef try_state_type
	return false;
}

static bool
parseOneState(std::map<int, StateMachineState *> &out,
	      const char *str,
	      const char **suffix)
{
	int label;
	StateMachineState *res;

	res = (StateMachineState *)0xf001; /* shut the compiler up */

	if (!parseThisChar('l', str, &str) ||
	    !parseDecimalInt(&label, str, &str) ||
	    !parseThisString(": ", str, &str) ||
	    !parseStateMachineState(&res, str, &str) ||
	    !parseThisChar('\n', str, &str))
		return false;
	if (out.count(label))
		return false;
	out[label] = res;
	*suffix = str;
	return true;
}

static bool
parseStateMachine(StateMachineState **out,
		  const char *str,
		  const char **suffix)
{
	std::map<int, StateMachineState *> labelToState;
	while (*str) {
		if (!parseOneState(labelToState, str, &str))
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
	for (auto it = labelToState.begin(); it != labelToState.end(); it++)
		if (!doOneState(it->second))
			return false;
	if (!labelToState.count(1))
		return false;
	*suffix = str;
	*out = labelToState[1];
	return true;
}

struct succ {
	succ() : label(CfgLabel::uninitialised()) {}
	CfgLabel label;
	CFGNode::successor_t::succ_type type;
	LibraryFunctionType l;
	static bool parse(succ *out, const char *str, const char **suffix)
	{
		if (!out->label.parse(str, &str) ||
		    !parseThisChar(':', str, &str))
			return false;
		if (parseThisString("default", str, &str)) {
			out->type = CFGNode::successor_t::succ_default;
		} else if (parseThisString("branch", str, &str)) {
			out->type = CFGNode::successor_t::succ_branch;
		} else if (parseThisString("call", str, &str)) {
			out->type = CFGNode::successor_t::succ_call;
		} else if (parseThisString("unroll", str, &str)) {
			out->type = CFGNode::successor_t::succ_unroll;
		} else {
			return false;
		}
		if (parseThisChar(':', str, &str)) {
			if (!LibraryFunctionTemplate::parse(&out->l, str, &str))
				return false;
		} else {
			out->l = LibraryFunctionTemplate::none;
		}
		*suffix = str;
		return true;
	}
};

static bool
parseCFG(std::vector<const CFGNode *> &roots,
	 const char *str, const char **suffix)
{
	std::map<CfgLabel, CFGNode *> cfg_labels;
	std::vector<std::pair<CFGNode **, CfgLabel> > relocations;
	while (1) {
		bool is_root;
		if (parseThisString(". ", str, &str)) {
			is_root = false;
		} else if (parseThisString("-->", str, &str)) {
			is_root = true;
		} else {
			break;
		}
		VexRip rip;
		CfgLabel label(CfgLabel::uninitialised());
		if (!label.parse(str, &str) ||
		    !parseThisString(": ", str, &str) ||
		    !parseVexRip(&rip, str, &str))
			return false;
		std::vector<succ> successors;
		if (parseThisString(" -> ", str, &str)) {
			succ l;
			if (!succ::parse(&l, str, &str))
				return false;
			successors.push_back(l);
			while (1) {
				if (!parseThisString(", ", str, &str))
					break;
				if (!succ::parse(&l, str, &str))
					return false;
				successors.push_back(l);
			}
		}
		if (!parseThisChar('\n', str, &str))
			return false;
		CFGNode *work = new CFGNode(-1, label);
		work->rip = rip;
		work->successors.resize(successors.size());
		for (unsigned x = 0; x < successors.size(); x++) {
			work->successors[x].type = successors[x].type;
			work->successors[x].calledFunction = successors[x].l;
			relocations.push_back(std::pair<CFGNode **, CfgLabel>(&work->successors[x].instr, successors[x].label));
		}
		if (cfg_labels.count(label))
			return false;
		cfg_labels[label] = work;
		if (is_root)
			roots.push_back(work);
	}
	for (auto it = relocations.begin(); it != relocations.end(); it++) {
		auto it2 = cfg_labels.find(it->second);
		if (it2 == cfg_labels.end())
			return false;
		*it->first = it2->second;
	}
	*suffix = str;
	return true;
}

bool
StateMachine::parse(StateMachine **out, const char *str, const char **suffix)
{
	std::vector<std::pair<unsigned, VexRip> > origin;
	if (!parseThisString("Machine for ", str, &str))
		return false;
	while (1) {
		if (parseThisChar(':', str, &str))
			break;
		std::pair<unsigned, VexRip> e;
		if (!parseVexRip(&e.second, str, &str) ||
		    !parseThisChar(':', str, &str) ||
		    !parseDecimalUInt(&e.first, str, &str))
			return false;
		parseThisChar(' ', str, &str);
		origin.push_back(e);
	}
	if (!parseThisChar('\n', str, &str))
		return false;
	StateMachineState *root;

	/* Shut the compiler up: it can't tell that
	   parseStateMachine() will always initialise root if it
	   returns true. */
	root = (StateMachineState *)0xf001deadbeeful; 

	std::vector<const CFGNode *> cfg_roots;
	if (!parseThisString("CFG:\n", str, &str) ||
	    !parseCFG(cfg_roots, str, &str) ||
	    !parseStateMachine(&root, str, suffix))
		return false;
	*out = new StateMachine(root, origin, cfg_roots);
	return true;
}
bool
parseStateMachine(StateMachine **out, const char *str, const char **suffix)
{
	return StateMachine::parse(out, str, suffix);
}

StateMachine *
readStateMachine(int fd)
{
	char *content = readfile(fd);
	const char *end;
	StateMachine *res;
	if (!parseStateMachine(&res, content, &end) || *end)
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

void
StateMachineState::findLoadedAddresses(std::set<IRExpr *> &out, const AllowableOptimisations &opt)
{
	std::vector<StateMachineState *> edges;
	targets(edges);
	/* It might look like we can do this by just calling
	   findLoadedAddresses on the @out set for each edge in turn.
	   Not so: the edge operations can also remove items from the
	   loaded set, if we find a store which definitely satisfies
	   the load.  We need a true union here, so have to go for
	   this double iteration. */
	for (auto it = edges.begin(); it != edges.end(); it++) {
		std::set<IRExpr *> t;
		(*it)->findLoadedAddresses(t, opt);
		for (auto it = t.begin(); it != t.end(); it++)
			out.insert(*it);
	}
	if (type == SideEffecting) {
		StateMachineSideEffect *se = ((StateMachineSideEffecting *)this)->sideEffect;
		if (se)
			se->updateLoadedAddresses(out, opt);
	}
}

#ifndef NDEBUG
void
StateMachine::assertSSA() const
{
	std::set<const StateMachineSideEffecting *> states;
	enumStates(this, &states);
	std::set<threadAndRegister, threadAndRegister::fullCompare> discoveredAssignments;
	for (auto it = states.begin(); it != states.end(); it++) {
		StateMachineSideEffect *smse = (*it)->sideEffect;
		if (!smse)
			continue;
		threadAndRegister tr(threadAndRegister::invalid());
		if (smse->definesRegister(tr)) {
			assert(tr.gen() != 0);
			assert(tr.gen() != (unsigned)-1);
			if (!discoveredAssignments.insert(tr).second)
				abort();
		}
	}

	struct : public StateMachineTransformer {
		IRExpr *transformIex(IRExprGet *ieg) {
			assert(ieg->reg.gen() != 0);
			return NULL;
		}
		bool rewriteNewStates() const { return false; }
	} checkForNonSSAVars;
	checkForNonSSAVars.transform(const_cast<StateMachine *>(this));
}
#endif

#if 0
StateMachineEdge::StateMachineEdge(const std::vector<StateMachineSideEffect *> &sideEffects,
				   const VexRip &vr,
				   StateMachineState *target)
{
	if (sideEffects.size() == 0) {
		this->target = target;
		return;
	}
	if (sideEffects.size() == 1) {
		this->sideEffect = sideEffects[0];
		this->target = target;
		return;
	}
	StateMachineState **cursor;
	StateMachineState *root;
	cursor = &root;
	for (unsigned x = 1; x < sideEffects.size(); x++) {
		StateMachineEdge *t = new StateMachineEdge(sideEffects[x], NULL);
		StateMachineProxy *p = new StateMachineProxy(vr, t);
		*cursor = p;
		cursor = &t->target;
	}
	*cursor = target;
	this->target = root;
}

void
StateMachineEdge::prependSideEffect(const VexRip &vr, StateMachineSideEffect *smse,
				    StateMachineState ***endOfTheLine)
{
	assert(endOfTheLine || target);
	if (!sideEffect) {
		if (endOfTheLine)
			assert(*endOfTheLine == &target);
		sideEffect = smse;
	} else {
		StateMachineProxy *smp = new StateMachineProxy(vr, target);
		smp->target->sideEffect = sideEffect;
		target = smp;
		sideEffect = smse;
		if (endOfTheLine && *endOfTheLine == &target)
			*endOfTheLine = &smp->target->target;
	}
}
#endif

void
StateMachineSideEffecting::prependSideEffect(StateMachineSideEffect *se)
{
	if (sideEffect)
		target = new StateMachineSideEffecting(origin, sideEffect, target);
	sideEffect = se;
}

StateMachineState *
StateMachineSideEffecting::optimise(const AllowableOptimisations &opt, bool *done_something)
{
	if (!sideEffect) {
		*done_something = true;
		return target->optimise(opt, done_something);
	}

	if (target == StateMachineUnreached::get()) {
		*done_something = true;
		return target;
	}
	if (sideEffect->type == StateMachineSideEffect::Unreached) {
		*done_something = true;
		return StateMachineUnreached::get();
	}
	sideEffect = sideEffect->optimise(opt, done_something);
	target = target->optimise(opt, done_something);
	if (!sideEffect) {
		assert(*done_something);
		return target;
	}

	if (sideEffect->type == StateMachineSideEffect::StartAtomic &&
	    target->type == StateMachineState::SideEffecting) {
		StateMachineSideEffecting *t = (StateMachineSideEffecting *)target;
		assert(t->sideEffect);
		if (t->sideEffect->type == StateMachineSideEffect::EndAtomic) {
			/* Remove empty atomic section */
			*done_something = true;
			return t->target;
		}
		
		if (t->target->type == StateMachineState::SideEffecting) {
			StateMachineSideEffecting *t2 = (StateMachineSideEffecting *)t->target;
			assert(t2->sideEffect);
			if (t2->sideEffect->type == StateMachineSideEffect::EndAtomic) {
				/* Individual side effects are always
				   atomic, so an atomic block with a
				   single side effect in is a bit
				   pointless. */
				*done_something = true;
				return (new StateMachineSideEffecting(
						t->origin,
						t->sideEffect,
						t2->target))->optimise(opt, done_something);
			}
		}
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
StateMachine::sanityCheck() const
{
	/* These are expensive enough that we don't want them on
	   unconditionally even in !NDEBUG builds. */
	if (!debug_state_machine_sanity_checks)
		return;

	std::map<const StateMachineState *, std::set<threadAndRegister, threadAndRegister::fullCompare> > definedAtTopOfState;
	std::set<threadAndRegister, threadAndRegister::fullCompare> allDefinedRegisters;
	std::set<const StateMachineState *> allStates;

	enumStates(this, &allStates);
	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		const StateMachineSideEffect *se = (*it)->getSideEffect();
		threadAndRegister r(threadAndRegister::invalid());
		if (se && se->definesRegister(r))
			allDefinedRegisters.insert(r);
	}
	for (auto it = allStates.begin(); it != allStates.end(); it++)
		definedAtTopOfState[*it] = allDefinedRegisters;
	definedAtTopOfState[root].clear();

	bool progress = true;
	while (progress && !TIMEOUT) {
		progress = false;
		for (auto it = definedAtTopOfState.begin();
		     it != definedAtTopOfState.end();
		     it++) {
			std::set<threadAndRegister, threadAndRegister::fullCompare> *definedAtEndOfState = &it->second;
			std::set<threadAndRegister, threadAndRegister::fullCompare> ts;
			const StateMachineSideEffect *se = it->first->getSideEffect();
			threadAndRegister definedHere(threadAndRegister::invalid());
			if (se && se->definesRegister(definedHere)) {
				ts = *definedAtEndOfState;
				ts.insert(definedHere);
				definedAtEndOfState = &ts;
			}

			std::vector<const StateMachineState *> exits;
			it->first->targets(exits);
			for (auto it = exits.begin(); it != exits.end(); it++) {
				std::set<threadAndRegister, threadAndRegister::fullCompare> &other(definedAtTopOfState[*it]);
				if (intersectSets(other, *definedAtEndOfState))
					progress = true;
			}
		}
	}

	for (auto it = definedAtTopOfState.begin();
	     it != definedAtTopOfState.end();
	     it++)
		it->first->sanityCheck(&definedAtTopOfState[it->first]);

	struct : public StateMachineTransformer {
		std::set<CfgLabel> neededLabels;
		IRExpr *transformIex(IRExprHappensBefore *hb) {
			neededLabels.insert(hb->before.where);
			neededLabels.insert(hb->after.where);
			return hb;
		}
		StateMachineSideEffectLoad *transformOneSideEffect(
			StateMachineSideEffectLoad *smse, bool *done_something)
		{
			neededLabels.insert(smse->rip.where);
			return StateMachineTransformer::transformOneSideEffect(smse, done_something);
		}
		StateMachineSideEffectStore *transformOneSideEffect(
			StateMachineSideEffectStore *smse, bool *done_something)
		{
			neededLabels.insert(smse->rip.where);
			return StateMachineTransformer::transformOneSideEffect(smse, done_something);
		}
		bool rewriteNewStates() const { return false; }
	} findNeededLabels;
	findNeededLabels.transform(const_cast<StateMachine *>(this));
	std::queue<const CFGNode *> pending;
	for (auto it = cfg_roots.begin(); it != cfg_roots.end(); it++)
		pending.push(*it);
	while (!pending.empty()) {
		const CFGNode *n = pending.front();
		pending.pop();
		findNeededLabels.neededLabels.erase(n->label);
		for (auto it = n->successors.begin(); it != n->successors.end(); it++)
			if (it->instr)
				pending.push(it->instr);
	}
	assert(findNeededLabels.neededLabels.empty());
}
#endif

MemoryAccessIdentifier
MemoryAccessIdentifierAllocator::operator()(const CfgLabel &node, int tid)
{
	auto it_did_insert = ids.insert(std::pair<std::pair<int, CfgLabel>, unsigned>(std::pair<int, CfgLabel>(tid, node), -1));
	auto it = it_did_insert.first;
	it->second++;
	return MemoryAccessIdentifier(node, tid, it->second);
}

IRExpr *
MemoryAccessIdentifierAllocator::freeVariable(IRType ty, int tid, const CfgLabel &node, bool isUnique)
{
	return IRExpr_FreeVariable((*this)(node, tid), ty, isUnique);
}
