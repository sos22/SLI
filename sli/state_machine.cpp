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

#ifndef NDEBUG
#define debug_state_machine_sanity_checks 0
#else
static int debug_state_machine_sanity_checks = 0;
#endif

VexPtr<StateMachineSideEffectUnreached, &ir_heap> StateMachineSideEffectUnreached::_this;
VexPtr<StateMachineUnreached, &ir_heap> StateMachineUnreached::_this;
VexPtr<StateMachineCrash, &ir_heap> StateMachineCrash::_this;
VexPtr<StateMachineNoCrash, &ir_heap> StateMachineNoCrash::_this;
AllowableOptimisations AllowableOptimisations::defaultOptimisations(7.3);

StateMachine *
StateMachine::optimise(const AllowableOptimisations &opt, bool *done_something)
{
	bool b = false;
	std::set<StateMachineState *> done;
	StateMachineState *new_root = root->optimise(opt, &b, done);
	if (b) {
		*done_something = true;
		return new StateMachine(new_root, origin);
	} else {
		return this;
	}
}

StateMachineState *
StateMachineBifurcate::optimise(const AllowableOptimisations &opt, bool *done_something,
				std::set<StateMachineState *> &done)
{
	if (done.count(this))
		return this;
	done.insert(this);
	if (trueTarget == StateMachineUnreached::get()) {
		*done_something = true;
		if (falseTarget == StateMachineUnreached::get())
			return StateMachineUnreached::get();
		else
			return falseTarget->optimise(opt, done_something, done);
	}
	if (falseTarget == StateMachineUnreached::get()) {
		*done_something = true;
		return trueTarget->optimise(opt, done_something, done);
	}
	if (trueTarget == falseTarget) {
		*done_something = true;
		return trueTarget;
	}
	condition = optimiseIRExprFP(condition, opt, done_something);
	if (condition->tag == Iex_Const) {
		*done_something = true;
		if (((IRExprConst *)condition)->con->Ico.U1)
			return trueTarget->optimise(opt, done_something, done);
		else
			return falseTarget->optimise(opt, done_something, done);
	}
	trueTarget = trueTarget->optimise(opt, done_something, done);
	falseTarget = falseTarget->optimise(opt, done_something, done);

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

void
printStateMachine(const StateMachine *sm, FILE *f, std::map<const StateMachineState *, int> &labels)
{
	std::vector<const StateMachineState *> states;

	fprintf(f, "Machine for ");
	for (auto it = sm->origin.begin(); it != sm->origin.end(); it++) {
		if (it != sm->origin.begin())
			fprintf(f, ", ");
		fprintf(f, "%s:%d", it->second.name(), it->first);
	}
	fprintf(f, ":\n");
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
	if (smse1 == NULL && smse2 == NULL)
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
	}
	abort();
}

bool
parseStateMachineSideEffect(StateMachineSideEffect **out,
			    const char *str,
			    const char **suffix)
{
	const char *str2;
	if (parseThisString("<unreached>", str, suffix)) {
		*out = StateMachineSideEffectUnreached::get();
		return true;
	}
	IRExpr *addr;
	IRExpr *data;
	MemoryAccessIdentifier where(MemoryAccessIdentifier::uninitialised());
	if (parseThisString("*(", str, &str2) &&
	    parseIRExpr(&addr, str2, &str2) &&
	    parseThisString(") <- ", str2, &str2) &&
	    parseIRExpr(&data, str2, &str2) &&
	    parseThisString(" @ ", str2, &str2) &&
	    parseMemoryAccessIdentifier(&where, str2, suffix)) {
		*out = new StateMachineSideEffectStore(addr, data, where);
		return true;
	}
	threadAndRegister key(threadAndRegister::invalid());
	IRType type;
	if (parseThisString("LOAD ", str, &str2) &&
	    parseThreadAndRegister(&key, str2, &str2) &&
	    parseThisString(":", str2, &str2) &&
	    parseIRType(&type, str2, &str2) &&
	    parseThisString(" <- *(", str2, &str2) &&
	    parseIRExpr(&addr, str2, &str2) &&
	    parseThisString(")@", str2, &str2) &&
	    parseMemoryAccessIdentifier(&where, str2, suffix)) {
		*out = new StateMachineSideEffectLoad(key, addr, where, type);
		return true;
	}
	if (parseThisString("COPY ", str, &str2) &&
	    parseThreadAndRegister(&key, str2, &str2) &&
	    parseThisString(" = ", str2, &str2) &&
	    parseIRExpr(&data, str2, suffix)) {
		*out = new StateMachineSideEffectCopy(key, data);
		return true;
	}
	if (parseThisString("Assert !(", str, &str2) &&
	    parseIRExpr(&data, str2, &str2) &&
	    parseThisChar(')', str2, &str2)) {
		bool isReal;
		if (parseThisString(" REAL", str2, suffix)) {
			isReal = true;
		} else if (parseThisString(" FAKE", str2, suffix)) {
			isReal = false;
		} else {
			return false;
		}
		*out = new StateMachineSideEffectAssertFalse(data, isReal);
		return true;
	}
	if (parseThisString("Phi", str, &str2) &&
	    parseThreadAndRegister(&key, str2, &str2) &&
	    parseThisString("(", str2, &str2)) {
		std::vector<unsigned> generations;
		while (1) {
			int x;
			if (!parseDecimalInt(&x, str2, &str2) ||
			    !parseThisString(", ", str2, &str2))
				break;
			generations.push_back(x);
		}
		if (!parseThisString(")", str2, suffix))
			return false;
		*out = new StateMachineSideEffectPhi(key, generations);
		return true;
	}
	return false;
}

/* State machine parser.  We cheat a little bit and stash the edge
 * labels in the target fields of state machine states until we have
 * find the state we're actually supposed to point at. */
static bool
parseStateMachineState(StateMachineState **out,
		       const char *str,
		       const char **suffix)
{
	if (parseThisString("<unreached>", str, suffix)) {
		*out = StateMachineUnreached::get();
		return true;
	}
	if (parseThisString("<crash>", str, suffix)) {
		*out = StateMachineCrash::get();
		return true;
	}
	if (parseThisString("<survive>", str, suffix)) {
		*out = StateMachineNoCrash::get();
		return true;
	}
	VexRip origin;
	VexRip target;
	const char *str2;
	if (parseThisChar('<', str, &str2) &&
	    parseVexRip(&origin, str2, &str2) &&
	    parseThisString(": jmp ", str2, &str2) &&
	    parseVexRip(&target, str2, &str2) &&
	    parseThisChar('>', str2, suffix)) {
		*out = new StateMachineStub(origin, target);
		return true;
	}
	int target1;
	StateMachineSideEffect *sme;
	if (parseThisString("{:", str, &str2) &&
	    parseVexRip(&origin, str2, &str2) &&
	    parseThisChar(':', str2, &str2) &&
	    parseStateMachineSideEffect(&sme, str2, &str2) &&
	    parseThisString(" then l", str2, &str2) &&
	    parseDecimalInt(&target1, str2, &str2) &&
	    parseThisChar('}', str2, &str2)) {
		*out = new StateMachineSideEffecting(origin, sme, (StateMachineState *)target1);
		return true;
	}
	IRExpr *condition;
	int target2;
	if (parseVexRip(&origin, str, &str2) &&
	    parseThisString(": if (", str2, &str2) &&
	    parseIRExpr(&condition, str2, &str2) &&
	    parseThisString(") then l", str2, &str2) &&
	    parseDecimalInt(&target1, str2, &str2) &&
	    parseThisString(" else l", str2, &str2) &&
	    parseDecimalInt(&target2, str2, suffix)) {
		*out = new StateMachineBifurcate(origin, condition,
						 (StateMachineState *)target1,
						 (StateMachineState *)target2);
		return true;
	}

	if (parseVexRip(&origin, str, &str2) &&
	    parseThisString(": ND {", str2, &str2)) {
		std::vector<StateMachineState *> successors;
		while (1) {
			if (parseThisChar('}', str2, suffix))
				break;
			if (successors.size() != 0 && !parseThisString(", ", str2, &str2))
				return false;
			if (!parseThisChar('l', str2, &str2))
				return false;
			int l;
			if (!parseDecimalInt(&l, str2, &str2))
				return false;
			successors.push_back((StateMachineState *)l);
		}
		*out = new StateMachineNdChoice(origin, successors);
		return true;
	}

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
parseStateMachine(StateMachineState **out, const char *str, const char **suffix)
{
	StateMachineState *root;
	if (!parseStateMachineState(&root, str, &str))
		return false;
	if (!parseThisChar('\n', str, &str))
		return false;

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
				**it = labelToState[(int)(unsigned long)*it];
				if (!**it)
					return false;
			}
			return true;
		}
	} doOneState(labelToState);
	if (!doOneState(root))
		return false;
	for (auto it = labelToState.begin(); it != labelToState.end(); it++)
		if (!doOneState(it->second))
			return false;
	*suffix = str;
	*out = root;
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

	if (!parseStateMachine(&root, str, suffix))
		return false;
	*out = new StateMachine(root, origin);
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
#endif
}

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
StateMachineState::enumerateMentionedMemoryAccesses(std::set<VexRip> &instrs)
{
	std::vector<StateMachineState *> targ;
	if (type == SideEffecting) {
		StateMachineSideEffecting *se = (StateMachineSideEffecting *)this;
		if (se->sideEffect) {
			StateMachineSideEffectMemoryAccess *smse =
				dynamic_cast<StateMachineSideEffectMemoryAccess *>(se->sideEffect);
			if (smse)
				instrs.insert(smse->rip.rip.rip);
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
ppStateMachineSideEffectMemoryAccess(StateMachineSideEffectMemoryAccess *smsema, FILE *f)
{
	fprintf(f, "{%s}", smsema->rip.name());
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
		switch (smse->type) {
		case StateMachineSideEffect::Load: {
			StateMachineSideEffectLoad *smsel = (StateMachineSideEffectLoad *)smse;
			assert(smsel->target.gen() != 0);
			assert(smsel->target.gen() != (unsigned)-1);
			if (!discoveredAssignments.insert(smsel->target).second)
				abort();
			break;
		}
		case StateMachineSideEffect::Copy: {
			StateMachineSideEffectCopy *smsec = (StateMachineSideEffectCopy *)smse;
			assert(smsec->target.gen() != 0);
			assert(smsec->target.gen() != (unsigned)-1);
			if (!discoveredAssignments.insert(smsec->target).second)
				abort();
			break;
		}
		case StateMachineSideEffect::Phi: {
			StateMachineSideEffectPhi *smsep = (StateMachineSideEffectPhi *)smse;
			assert(smsep->reg.gen() != 0);
			assert(smsep->reg.gen() != (unsigned)-1);
			if (!discoveredAssignments.insert(smsep->reg).second)
					abort();
			break;
		}
		case StateMachineSideEffect::Store:
		case StateMachineSideEffect::AssertFalse:
		case StateMachineSideEffect::Unreached:
			break;
		}
	}

	struct : public StateMachineTransformer {
		IRExpr *transformIex(IRExprGet *ieg) {
			assert(ieg->reg.gen() != 0);
			return NULL;
		}
		IRExpr *transformIex(IRExprPhi *phi) {
			for (auto it = phi->generations.begin(); it != phi->generations.end(); it++)
				assert(*it != 0);
			return IRExprTransformer::transformIex(phi);
		}
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
StateMachineSideEffecting::optimise(const AllowableOptimisations &opt, bool *done_something,
				    std::set<StateMachineState *> &done)
{
	if (done.count(this))
		return this;
	done.insert(this);

	if (!sideEffect) {
		*done_something = true;
		return target->optimise(opt, done_something, done);
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
	target = target->optimise(opt, done_something, done);
	if (!sideEffect) {
		assert(*done_something);
		return target;
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
}

StateMachineState *
StateMachineNdChoice::optimise(const AllowableOptimisations &opt,
			       bool *done_something,
			       std::set<StateMachineState *> &memo)
{
	if (successors.size() == 0) {
		*done_something = true;
		return StateMachineUnreached::get();
	}
	successors[0] = successors[0]->optimise(opt, done_something, memo);

	/* Remove duplicates.  Note that we don't want to sort
	   successors here, since that would involve a dependency on
	   pointer ordering, which causes problems for determinacy. */
	for (auto it1 = successors.begin(); it1 != successors.end(); ) {
		if ((*it1)->type == StateMachineState::Unreached) {
			/* Unreached nodes can be safely removed */
			it1 = successors.erase(it1);
			*done_something = true;
			continue;
		}
		for (auto it2 = it1 + 1; it2 != successors.end(); ) {
			if ( *it1 == *it2 ) {
				*done_something = true;
				it2 = successors.erase(it2);
			} else if ( it1 == successors.begin() ) {
				*it2 = (*it2)->optimise(opt, done_something, memo);
				if ( *it1 == *it2 ) {
					*done_something = true;
					it2 = successors.erase(it2);
				} else {
					it2++;
				}
			} else {
				it2++;
			}
		}
		it1++;
	}
	if (successors.size() == 0) {
		*done_something = true;
		return StateMachineUnreached::get();
	}
	if (successors.size() == 1) {
		*done_something = true;
		return successors[0]->optimise(opt, done_something, memo);
	}
	return this;
}

MemoryAccessIdentifier
MemoryAccessIdentifierAllocator::operator()(const ThreadRip &rip)
{
	/* I'm not sure why, but inlining the definition of dflt into
	   its only use leads to a link error. */
	unsigned dflt = MemoryAccessIdentifier::first_dynamic_generation;
	auto it_and_did_something = ids.insert(std::pair<ThreadRip, unsigned>(rip, dflt));
	auto it = it_and_did_something.first;
	unsigned gen = it->second;
	it->second++;
	return MemoryAccessIdentifier(rip, gen);
}

IRExpr *
MemoryAccessIdentifierAllocator::freeVariable(IRType ty, const ThreadRip &rip)
{
	return IRExpr_FreeVariable((*this)(rip), ty);
}
