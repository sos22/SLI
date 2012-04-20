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
AllowableOptimisations AllowableOptimisations::defaultOptimisations(true, false, false, false, false, true, NULL);

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
	if (target->sideEffects.size() == 0) {
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

	if (falseTarget->sideEffects.size() == 0 &&
	    trueTarget->sideEffects.size() == 0) {
		if (trueTarget->target == falseTarget->target) {
			*done_something = true;
			return trueTarget->target;
		}

		if (StateMachineBifurcate *falseBifur = dynamic_cast<StateMachineBifurcate *>(falseTarget->target)) {
			if (trueTarget == falseBifur->trueTarget) {
				falseTarget = falseBifur->falseTarget;
				condition = IRExpr_Binop(
					Iop_Or1,
					condition,
					falseBifur->condition);
				*done_something = true;
				return this;
			}
			if (trueTarget == falseBifur->falseTarget) {
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
		if (StateMachineBifurcate *trueBifur = dynamic_cast<StateMachineBifurcate *>(trueTarget->target)) {
			if (falseTarget == trueBifur->falseTarget) {
				trueTarget = trueBifur->trueTarget;
				condition = IRExpr_Binop(
					Iop_And1,
					condition,
					trueBifur->condition);
				*done_something = true;
				return this;
			}
			if (falseTarget == trueBifur->trueTarget) {
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
 top:
	if (TIMEOUT)
		return this;
	if (StateMachineProxy *smp =
	    dynamic_cast<StateMachineProxy *>(target)) {
		StateMachineEdge *other = smp->target;
		if (other->target != target) {
			/* Can't duplicate Phi side effects. */
			bool havePhi = false;
			for (auto it = other->sideEffects.begin();
			     !havePhi && it != other->sideEffects.end();
			     it++)
				if ((*it)->type == StateMachineSideEffect::Phi)
					havePhi = true;
			if (!havePhi) {
				sideEffects.insert(sideEffects.end(),
						   other->sideEffects.begin(),
						   other->sideEffects.end());
				target = other->target;
				*done_something = true;
				goto top;
			}
		}
	}

	for (auto it = sideEffects.begin(); !TIMEOUT && it != sideEffects.end(); it++) {
		if ((*it)->type == StateMachineSideEffect::Unreached) {
			*done_something = true;
			target = StateMachineUnreached::get();
			return this;
		}
		*it = (*it)->optimise(opt, oracle, done_something);
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
buildStateLabelTable(const StateMachineState *sm, std::map<const StateMachineState *, int> &table,
		     std::vector<const StateMachineState *> &states)
{
	std::vector<const StateMachineState *> toEmit;
	int next_label;

	toEmit.push_back(sm);
	next_label = 1;
	while (!toEmit.empty()) {
		sm = toEmit.back();
		toEmit.pop_back();
		if (!sm || table.count(sm))
			continue;
		states.push_back(sm);
		table[sm] = next_label;
		next_label++;
		sm->targets(toEmit);
	}
}

template <typename cont, void printer(const typename cont::value_type, FILE *)> void
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
printStateMachine(const StateMachineState *sm, FILE *f, std::map<const StateMachineState *, int> &labels)
{
	std::vector<const StateMachineState *> states;

	buildStateLabelTable(sm, labels, states);
	for (std::vector<const StateMachineState *>::iterator it = states.begin();
	     it != states.end();
	     it++) {
		fprintf(f, "l%d: ", labels[*it]);
		(*it)->prettyPrint(f, labels);
		fprintf(f, "\n");
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
	fprintf(f, "Machine for %s:%d\n", sm->origin.name(), sm->tid);
	printStateMachine(sm->root, f, labels);
	sm->freeVariables.print(f);
}

void
printStateMachine(const StateMachine *sm, FILE *f)
{
	std::map<const StateMachineState *, int> labels;
	printStateMachine(sm, f, labels);
}


unsigned long
StateMachineEdge::hashval() const
{
	if (!have_hash) {
		unsigned long h = 0xaabb5697;
		for (unsigned x = 0; x < sideEffects.size(); x++)
			h = h * 65537 + sideEffects[x]->hashval();
		_hashval = h;
		have_hash = true;
	}
	return _hashval;
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
	ThreadVexRip rip;
	if (parseThisString("*(", str, &str2) &&
	    parseIRExpr(&addr, str2, &str2) &&
	    parseThisString(") <- ", str2, &str2) &&
	    parseIRExpr(&data, str2, &str2) &&
	    parseThisString(" @ ", str2, &str2) &&
	    parseThreadRip(&rip, str2, suffix)) {
		*out = new StateMachineSideEffectStore(addr, data, rip);
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
	    parseThreadRip(&rip, str2, suffix)) {
	  *out = new StateMachineSideEffectLoad(key, addr, rip, type);
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

/* State machine parser.  We cheat a little bit and stash the state
 * labels in the target field of state machine edges until we have
 * find the state we're actually supposed to point at. */
static bool
parseStateMachineEdge(StateMachineEdge **out,
		      const char *sep,
		      const char *str,
		      const char **suffix)
{
	int targetLabel;
	std::vector<StateMachineSideEffect *> sideEffects;
	if (parseThisChar('{', str, &str)) {
		while (1) {
			StateMachineSideEffect *se;
			if (!parseStateMachineSideEffect(&se, str, &str))
				return false;
			sideEffects.push_back(se);
			if (parseThisString(sep, str, &str))
				continue;
			if (!parseThisString("} ", str, &str))
				return false;
			break;
		}
	}
	if (!parseThisChar('l', str, &str) ||
	    !parseDecimalInt(&targetLabel, str, suffix))
		return false;
	*out = new StateMachineEdge((StateMachineState *)targetLabel);
	(*out)->sideEffects = sideEffects;
	return true;
}

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
	StateMachineEdge *target1;
	if (parseThisChar('{', str, &str2) &&
	    parseVexRip(&origin, str2, &str2) &&
	    parseThisChar(':', str2, &str2) &&
	    parseStateMachineEdge(&target1, "\n  ", str2, &str2) &&
	    parseThisChar('}', str2, suffix)) {
		*out = new StateMachineProxy(origin, target1);
		return true;
	}
	IRExpr *condition;
	StateMachineEdge *target2;
	if (parseVexRip(&origin, str, &str2) &&
	    parseThisString(": if (", str2, &str2) &&
	    parseIRExpr(&condition, str2, &str2) &&
	    parseThisString(")\n  then {\n\t", str2, &str2) &&
	    parseStateMachineEdge(&target1, "\n\t", str2, &str2) &&
	    parseThisString("}\n  else {\n\t", str2, &str2) &&
	    parseStateMachineEdge(&target2, "\n\t", str2, &str2) &&
	    parseThisChar('}', str2, suffix)) {
		*out = new StateMachineBifurcate(origin, condition, target1, target2);
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
	std::map<int, StateMachineState *> labelToState;

	while (*str) {
		if (!parseOneState(labelToState, str, &str))
			break;
	}
	if (!labelToState.count(1))
		return false;
	for (std::map<int, StateMachineState *>::iterator it = labelToState.begin();
	     it != labelToState.end();
	     it++) {
		if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(it->second)) {
			StateMachineState *t = labelToState[(int)(unsigned long)smp->target->target];
			if (!t)
				return false;
			smp->target->target = t;
		} else if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(it->second)) {
			StateMachineState *t = labelToState[(int)(unsigned long)smb->trueTarget->target];
			StateMachineState *f = labelToState[(int)(unsigned long)smb->falseTarget->target];
			if (!t)
				return false;
			if (!f)
				return false;

			smb->trueTarget->target = t;
			smb->falseTarget->target = f;
		} else {
			assert(dynamic_cast<StateMachineTerminal *>(it->second));
		}
	}
	*suffix = str;
	*out = labelToState[1];
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
StateMachineState::assertAcyclic(std::vector<const StateMachineState *> &stack,
				 std::set<const StateMachineState *> &clean) const
{
#ifndef NDEBUG
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
	//assert(!clean.count(this));
	clean.insert(this);
	return;

found_cycle:
	printf("Unexpected cycle in state machine!\n");
	printf("Found at %p\n", this);
	std::map<const StateMachineState *, int> labels;
	prettyPrint(stdout, labels);
	printf("Path: \n");
	for (std::vector<const StateMachineState *>::const_iterator it = stack.begin();
	     it != stack.end();
	     it++)
		printf("\t%d\n", labels[*it]);
	printf("End\n");
	assert(0);
#endif
}

void
StateMachineState::assertAcyclic() const
{
#ifndef NDEBUG
	std::vector<const StateMachineState *> stack;
	std::set<const StateMachineState *> clean;
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
	for (std::vector<StateMachineSideEffect *>::iterator it = sideEffects.begin();
	     it != sideEffects.end();
	     it++) {
		StateMachineSideEffect *smse = *it;
		if (StateMachineSideEffectLoad *smsel =
		    dynamic_cast<StateMachineSideEffectLoad *>(smse)) {
			instrs.insert(smsel->rip.rip);
		} else if (StateMachineSideEffectStore *smses =
			   dynamic_cast<StateMachineSideEffectStore *>(smse)) {
			instrs.insert(smses->rip.rip);
		}
	}
	target->enumerateMentionedMemoryAccesses(instrs);
}

StateMachineState::RoughLoadCount
StateMachineEdge::roughLoadCount(StateMachineState::RoughLoadCount acc) const
{
	if (acc == StateMachineState::multipleLoads)
		return StateMachineState::multipleLoads;

	for (std::vector<StateMachineSideEffect *>::const_iterator it = sideEffects.begin();
	     it != sideEffects.end();
	     it++) {
		if (dynamic_cast<StateMachineSideEffectLoad *>(*it)) {
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

StateMachine *
StateMachine::clone() const
{
	std::map<const StateMachineState *, StateMachineState *> stateMap;
	std::map<const StateMachineEdge *, StateMachineEdge *> edgeMap;
	return new StateMachine(root->clone(stateMap, edgeMap),
				origin,
				freeVariables,
				tid);
}

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
