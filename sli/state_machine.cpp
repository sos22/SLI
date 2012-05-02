#include <err.h>

#include <map>

#include "sli.h"
#include "state_machine.hpp"
#include "oracle.hpp"
#include "simplify_irexpr.hpp"
#include "offline_analysis.hpp"

#include "libvex_parse.h"

static void findUsedRegisters(IRExpr *e, std::set<threadAndRegister, threadAndRegister::fullCompare> &, const AllowableOptimisations &);

VexPtr<StateMachineSideEffectUnreached, &ir_heap> StateMachineSideEffectUnreached::_this;
VexPtr<StateMachineUnreached, &ir_heap> StateMachineUnreached::_this;
VexPtr<StateMachineCrash, &ir_heap> StateMachineCrash::_this;
VexPtr<StateMachineNoCrash, &ir_heap> StateMachineNoCrash::_this;
AllowableOptimisations AllowableOptimisations::defaultOptimisations(7.3);

StateMachine *
StateMachine::optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something)
{
	bool b = false;
	std::set<StateMachineState *> done;
	StateMachineState *new_root = root->optimise(opt, oracle, &b, freeVariables, done);
	FreeVariableMap fv(freeVariables);
	fv.optimise(opt, &b);
	if (b) {
		*done_something = true;
		StateMachine *sm = new StateMachine(*this);
		sm->root = new_root;
		sm->freeVariables = fv;
		return sm;
	} else {
		return this;
	}
}

StateMachineState *
StateMachineProxy::optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something, FreeVariableMap &fv,
			    std::set<StateMachineState *> &done)
{
	if (done.count(this))
		return this;
	done.insert(this);

	if (target->target == StateMachineUnreached::get()) {
		*done_something = true;
		return target->target;
	}
	if (target->noSideEffects()) {
		*done_something = true;
		return target->target->optimise(opt, oracle, done_something, fv, done);
	}
	target = target->optimise(opt, oracle, done_something, fv, done);
	return this;
}

StateMachineState *
StateMachineBifurcate::optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something, FreeVariableMap &fv,
				std::set<StateMachineState *> &done)
{
	if (done.count(this))
		return this;
	done.insert(this);
	if (trueTarget->target == StateMachineUnreached::get()) {
		*done_something = true;
		if (falseTarget->target == StateMachineUnreached::get())
			return StateMachineUnreached::get();
		else
			return new StateMachineProxy(origin, falseTarget->optimise(opt, oracle, done_something, fv, done));
	}
	if (falseTarget->target == StateMachineUnreached::get()) {
		*done_something = true;
		return new StateMachineProxy(origin, trueTarget->optimise(opt, oracle, done_something, fv, done));
	}
	if (trueTarget == falseTarget) {
		*done_something = true;
		return new StateMachineProxy(origin, trueTarget->optimise(opt, oracle, done_something, fv, done));
	}
	condition = optimiseIRExprFP(condition, opt, done_something);
	if (condition->tag == Iex_Const) {
		*done_something = true;
		if (((IRExprConst *)condition)->con->Ico.U1)
			return new StateMachineProxy(origin, trueTarget->optimise(opt, oracle, done_something, fv, done));
		else
			return new StateMachineProxy(origin, falseTarget->optimise(opt, oracle, done_something, fv, done));
	}
	trueTarget = trueTarget->optimise(opt, oracle, done_something, fv, done);
	falseTarget = falseTarget->optimise(opt, oracle, done_something, fv, done);

	if (trueTarget->noSideEffects() && trueTarget->target->type == StateMachineState::Proxy) {
		StateMachineProxy *smp = (StateMachineProxy *)trueTarget->target;
		*done_something = true;
		trueTarget = smp->target;
	}

	if (falseTarget->noSideEffects() && falseTarget->target->type == StateMachineState::Proxy) {
		StateMachineProxy *smp = (StateMachineProxy *)falseTarget->target;
		*done_something = true;
		falseTarget = smp->target;
	}

	if (falseTarget->noSideEffects() && trueTarget->noSideEffects()) {
		if (trueTarget->target == falseTarget->target) {
			*done_something = true;
			return trueTarget->target;
		}

		if (falseTarget->target->type == StateMachineState::Bifurcate) {
			StateMachineBifurcate *falseBifur = (StateMachineBifurcate *)falseTarget->target;
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
		if (trueTarget->target->type == StateMachineState::Bifurcate) {
			StateMachineBifurcate *trueBifur = (StateMachineBifurcate *)trueTarget->target;
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
	}
	return this;
}

void
StateMachineBifurcate::findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &s, const AllowableOptimisations &opt)
{
	trueTarget->findUsedRegisters(s, opt);
	falseTarget->findUsedRegisters(s, opt);
	::findUsedRegisters(condition, s, opt);
}

StateMachineSideEffect *
StateMachineSideEffectStore::optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something)
{
	addr = optimiseIRExprFP(addr, opt, done_something);
	data = optimiseIRExprFP(data, opt, done_something);
	if (isBadAddress(addr, opt, oracle) ||
	    definitelyUnevaluatable(data, opt, oracle)) {
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
void
StateMachineSideEffectStore::findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &s, const AllowableOptimisations &opt)
{
	::findUsedRegisters(addr, s, opt);
	::findUsedRegisters(data, s, opt);
}

void
StateMachineSideEffectLoad::constructed()
{
	if (addr) {
		bool ign;
		addr = optimiseIRExprFP(addr, AllowableOptimisations::defaultOptimisations, &ign);
	}
}
StateMachineSideEffect *
StateMachineSideEffectLoad::optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something)
{
	addr = optimiseIRExprFP(addr, opt, done_something);
	if (isBadAddress(addr, opt, oracle)) {
		*done_something = true;
		return StateMachineSideEffectUnreached::get();
	}
	constructed();
	return this;
}
void
StateMachineSideEffectLoad::findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &s, const AllowableOptimisations &opt)
{
	s.erase(target);
	::findUsedRegisters(addr, s, opt);
}

StateMachineSideEffect *
StateMachineSideEffectCopy::optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something)
{
	value = optimiseIRExprFP(value, opt, done_something);
	if (definitelyUnevaluatable(value, opt, oracle)) {
		*done_something = true;
		return StateMachineSideEffectUnreached::get();
	}
	return this;
}
void
StateMachineSideEffectCopy::findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &s, const AllowableOptimisations &opt)
{
	s.erase(target);
	::findUsedRegisters(value, s, opt);
}

StateMachineSideEffect *
StateMachineSideEffectAssertFalse::optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something)
{
	value = optimiseIRExprFP(value, opt, done_something);
	if ((value->tag == Iex_Const && ((IRExprConst *)value)->con->Ico.U1) ||
	    definitelyUnevaluatable(value, opt, oracle)) {
		*done_something = true;
		return StateMachineSideEffectUnreached::get();
	}
	return this;
}
void
StateMachineSideEffectAssertFalse::findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &s, const AllowableOptimisations &opt)
{
	::findUsedRegisters(value, s, opt);
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
StateMachineEdge *
StateMachineEdge::optimise(const AllowableOptimisations &opt,
			   Oracle *oracle,
			   bool *done_something,
			   FreeVariableMap &freeVariables,
			   std::set<StateMachineState *> &done)
{
	target = target->optimise(opt, oracle, done_something, freeVariables, done);
	if (TIMEOUT)
		return this;

	if (sideEffect) {
		if (sideEffect->type == StateMachineSideEffect::Unreached) {
			*done_something = true;
			target = StateMachineUnreached::get();
			return this;
		}
		sideEffect = sideEffect->optimise(opt, oracle, done_something);
	}

	return this;
}

static void
findUsedRegisters(IRExpr *e, std::set<threadAndRegister, threadAndRegister::fullCompare> &out, const AllowableOptimisations &opt)
{
	class _ : public IRExprTransformer {
	public:
		std::set<threadAndRegister, threadAndRegister::fullCompare> &out;
		_(std::set<threadAndRegister, threadAndRegister::fullCompare> &_out)
			: out(_out)
		{}
		IRExpr *transformIex(IRExprGet *e) {
			out.insert(e->reg);
			return IRExprTransformer::transformIex(e);
		}
	} t(out);
	t.doit(e);
}

static void
buildEdgeLabelTable(const StateMachineState *sm,
		    std::map<const StateMachineEdge *, int> &table,
		    std::vector<const StateMachineEdge *> &states)
{
	std::vector<const StateMachineEdge *> toEmit;
	int next_label;

	sm->targets(toEmit);
	next_label = 1;
	while (!toEmit.empty()) {
		const StateMachineEdge *sme = toEmit.back();
		toEmit.pop_back();
		if (!sme || table.count(sme))
			continue;
		states.push_back(sme);
		table[sme] = next_label;
		next_label++;
		sme->target->targets(toEmit);
	}
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
printStateMachine(const StateMachineState *sm, FILE *f, std::map<const StateMachineEdge *, int> &labels)
{
	std::vector<const StateMachineEdge *> edges;

	buildEdgeLabelTable(sm, labels, edges);
	sm->prettyPrint(f, labels);
	fprintf(f, "\n");
	for (auto it = edges.begin(); it != edges.end(); it++) {
		fprintf(f, "l%d: ", labels[*it]);
		(*it)->prettyPrint(f, labels);
		fprintf(f, "\n");
	}
}

void
printStateMachine(const StateMachineState *sm, FILE *f)
{
	std::map<const StateMachineEdge *, int> labels;
	printStateMachine(sm, f, labels);
}

void
printStateMachine(const StateMachine *sm, FILE *f, std::map<const StateMachineEdge *, int> &labels)
{
	fprintf(f, "Machine for %s:%d\n", sm->origin.name(), sm->tid);
	printStateMachine(sm->root, f, labels);
	sm->freeVariables.print(f);
}

void
printStateMachine(const StateMachine *sm, FILE *f)
{
	std::map<const StateMachineEdge *, int> labels;
	printStateMachine(sm, f, labels);
}

bool
sideEffectsBisimilar(StateMachineSideEffect *smse1,
		     StateMachineSideEffect *smse2,
		     const AllowableOptimisations &opt)
{
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
	    parseThisChar(')', str2, suffix)) {
		*out = new StateMachineSideEffectAssertFalse(data);
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
	if (parseThisChar('{', str, &str2) &&
	    parseVexRip(&origin, str2, &str2) &&
	    parseThisString(":l", str2, &str2) &&
	    parseDecimalInt(&target1, str2, &str2) &&
	    parseThisChar('}', str2, suffix)) {
		*out = new StateMachineProxy(origin, (StateMachineEdge *)(unsigned long)target1);
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
						 (StateMachineEdge *)(int)target1,
						 (StateMachineEdge *)(int)target2);
		return true;
	}
	return false;
}

static bool
parseStateMachineEdge(StateMachineEdge **out,
		      const char *str,
		      const char **suffix)
{
	StateMachineSideEffect *se;
	if (parseStateMachineSideEffect(&se, str, &str))
		parseThisChar('\n', str, &str);
	StateMachineState *target;
	if (!parseStateMachineState(&target, str, suffix))
		return false;
	*out = new StateMachineEdge(se, target);
	return true;
}

static bool
parseOneEdge(std::map<int, StateMachineEdge *> &out,
	     const char *str,
	     const char **suffix)
{
	int label;
	StateMachineEdge *res;

	res = (StateMachineEdge *)0xf001; /* shut the compiler up */

	if (!parseThisChar('l', str, &str) ||
	    !parseDecimalInt(&label, str, &str) ||
	    !parseThisString(": ", str, &str) ||
	    !parseStateMachineEdge(&res, str, &str) ||
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

	std::map<int, StateMachineEdge *> labelToEdge;
	while (*str) {
		if (!parseOneEdge(labelToEdge, str, &str))
			break;
	}
	class _ {
	public:
		std::map<int, StateMachineEdge *> &labelToEdge;
		_(std::map<int, StateMachineEdge *> &_labelToEdge)
			: labelToEdge(_labelToEdge)
		{}
		bool operator()(StateMachineState *s) {
			switch (s->type) {
			case StateMachineState::Proxy: {
				StateMachineProxy *smp = (StateMachineProxy *)s;
				smp->target = labelToEdge[(int)(unsigned long)smp->target];
				if (!smp->target)
					return false;
				return true;
			}
			case StateMachineState::Bifurcate: {
				StateMachineBifurcate *smb = (StateMachineBifurcate *)s;
				smb->trueTarget = labelToEdge[(int)(unsigned long)smb->trueTarget];
				smb->falseTarget = labelToEdge[(int)(unsigned long)smb->falseTarget];
				if (!smb->trueTarget || !smb->falseTarget)
					return false;
				return true;
			}
			case StateMachineState::Crash:
			case StateMachineState::NoCrash:
			case StateMachineState::Stub:
			case StateMachineState::Unreached:
				return true;
			}
			abort();
		}
	} doOneState(labelToEdge);
	if (!doOneState(root))
		return false;
	for (auto it = labelToEdge.begin(); it != labelToEdge.end(); it++)
		if (!doOneState(it->second->target))
			return false;
	*suffix = str;
	*out = root;
	return true;
}

bool
StateMachine::parse(StateMachine **out, const char *str, const char **suffix)
{
	VexRip origin;
	int tid;
	if (!parseThisString("Machine for ", str, &str) ||
	    !parseVexRip(&origin, str, &str) ||
	    !parseThisChar(':', str, &str) ||
	    !parseDecimalInt(&tid, str, &str) ||
	    !parseThisChar('\n', str, &str))
		return false;
	StateMachineState *root;

	/* Shut the compiler up: it can't tell that
	   parseStateMachine() will always initialise root if it
	   returns true. */
	root = (StateMachineState *)0xf001deadbeeful; 

	if (!parseStateMachine(&root, str, &str))
		return false;
	*out = new StateMachine(root, origin, tid);
	if (!(*out)->freeVariables.parse(str, suffix))
		return false;
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

void
StateMachineEdge::assertAcyclic(std::vector<const StateMachineEdge *> &stack,
				std::set<const StateMachineEdge *> &clean) const
{
#ifndef NDEBUG
	if (clean.count(this))
		return;
	if (std::find(stack.begin(), stack.end(), this) != stack.end())
		goto found_cycle;
	stack.push_back(this);
	{
		std::vector<const StateMachineEdge *> targ;
		target->targets(targ);
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
	std::map<const StateMachineEdge *, int> labels;
	prettyPrint(stdout, labels);
	printf("Path: \n");
	for (auto it = stack.begin(); it != stack.end(); it++)
		printf("\t%d\n", labels[*it]);
	printf("End\n");
	assert(0);
#endif
}

void
StateMachineEdge::assertAcyclic() const
{
#ifndef NDEBUG
	std::vector<const StateMachineEdge *> stack;
	std::set<const StateMachineEdge *> clean;
	assertAcyclic(stack, clean);
#endif
}

void
StateMachineState::enumerateMentionedMemoryAccesses(std::set<VexRip> &instrs)
{
	std::vector<StateMachineEdge *> targ;
	targets(targ);
	for (auto it = targ.begin(); it != targ.end(); it++)
		(*it)->enumerateMentionedMemoryAccesses(instrs);
}

void
StateMachineEdge::enumerateMentionedMemoryAccesses(std::set<VexRip> &instrs)
{
	if (sideEffect) {
		StateMachineSideEffect *smse = sideEffect;
		if (StateMachineSideEffectLoad *smsel =
		    dynamic_cast<StateMachineSideEffectLoad *>(smse)) {
			instrs.insert(smsel->rip.rip.rip);
		} else if (StateMachineSideEffectStore *smses =
			   dynamic_cast<StateMachineSideEffectStore *>(smse)) {
			instrs.insert(smses->rip.rip.rip);
		}
	}
	target->enumerateMentionedMemoryAccesses(instrs);
}

StateMachineState::RoughLoadCount
StateMachineEdge::roughLoadCount(StateMachineState::RoughLoadCount acc) const
{
	if (acc == StateMachineState::multipleLoads)
		return StateMachineState::multipleLoads;

	if (sideEffect) {
		if (dynamic_cast<StateMachineSideEffectLoad *>(sideEffect)) {
			if (acc == StateMachineState::noLoads)
				acc = StateMachineState::singleLoad;
			else
				return StateMachineState::multipleLoads;
		}
	}
	return target->roughLoadCount(acc);
}

void
ppStateMachineSideEffectMemoryAccess(StateMachineSideEffectMemoryAccess *smsema, FILE *f)
{
	fprintf(f, "{%s}", smsema->rip.name());
}

#ifndef NDEBUG
void
StateMachine::sanityCheck() const
{
	std::vector<const StateMachineEdge *> path;
	std::set<threadAndRegister, threadAndRegister::fullCompare> live;
	root->sanityCheck(&live, path);
}
#endif

void
StateMachineState::targets(std::set<StateMachineState *> &out)
{
	std::vector<StateMachineEdge *> edges;
	targets(edges);
	for (auto it = edges.begin(); it != edges.end(); it++)
		out.insert((*it)->target);
}

void
StateMachineState::targets(std::set<const StateMachineState *> &out) const
{
	std::vector<const StateMachineEdge *> edges;
	targets(edges);
	for (auto it = edges.begin(); it != edges.end(); it++)
		out.insert((*it)->target);
}

void
StateMachineState::targets(std::vector<StateMachineState *> &out)
{
	std::vector<StateMachineEdge *> edges;
	targets(edges);
	out.reserve(out.size() + edges.size());
	for (auto it = edges.begin(); it != edges.end(); it++)
		out.push_back((*it)->target);
}

void
StateMachineState::targets(std::vector<const StateMachineState *> &out) const
{
	std::vector<const StateMachineEdge *> edges;
	targets(edges);
	out.reserve(out.size() + edges.size());
	for (auto it = edges.begin(); it != edges.end(); it++)
		out.push_back((*it)->target);
}

void
StateMachineState::targets(std::queue<StateMachineEdge *> &out)
{
	std::vector<StateMachineEdge *> edges;
	targets(edges);
	for (auto it = edges.begin(); it != edges.end(); it++)
		out.push(*it);
}

void
StateMachineState::findLoadedAddresses(std::set<IRExpr *> &out, const AllowableOptimisations &opt)
{
	std::vector<StateMachineEdge *> edges;
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
}

StateMachineState::RoughLoadCount
StateMachineState::roughLoadCount(RoughLoadCount acc) const
{
	if (acc == multipleLoads)
		return multipleLoads;
	std::vector<const StateMachineEdge *> edges;
	targets(edges);
	for (auto it = edges.begin(); acc != multipleLoads && it != edges.end(); it++)
		acc = (*it)->roughLoadCount(acc);
	return acc;
}

#ifndef NDEBUG
void
StateMachine::assertAcyclic() const
{
	std::vector<const StateMachineEdge *> roots;
	root->targets(roots);
	for (auto it = roots.begin(); it != roots.end(); it++)
		(*it)->assertAcyclic();
}
#endif

#ifndef NDEBUG
void
StateMachine::assertSSA() const
{
	std::set<StateMachineEdge *> edges;
	enumStatesAndEdges<StateMachineState>(const_cast<StateMachine *>(this),
					      (std::set<StateMachineState *> *)NULL,
					      &edges);
	std::set<threadAndRegister, threadAndRegister::fullCompare> discoveredAssignments;
	for (auto it = edges.begin(); it != edges.end(); it++) {
		if ( (*it)->sideEffect ) {
			StateMachineSideEffect *smse = (*it)->sideEffect;
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
			default:
				break;
			}
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
