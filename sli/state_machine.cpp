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

void
FreeVariableMap::optimise(const AllowableOptimisations &opt, bool *done_something)
{
	for (auto it = content->begin(); it != content->end(); it++)
		it.set_value(optimiseIRExprFP(it.value(), opt, done_something));
}

StateMachine *
StateMachine::optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something)
{
	bool b = false;
	std::set<StateMachineState *> done;
	StateMachineState *new_root = root->optimise(opt, oracle, &b, freeVariables, done);
	FreeVariableMap fv(freeVariables);
	fv.optimise(opt, done_something);
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
StateMachineProxy::optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something, FreeVariableMap &fv,
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
StateMachineBifurcate::optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something, FreeVariableMap &fv,
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
StateMachineSideEffectStore::optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something)
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
StateMachineSideEffectLoad::optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something)
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
StateMachineSideEffectCopy::optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something)
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
StateMachineSideEffectAssertFalse::optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something)
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
			   OracleInterface *oracle,
			   bool *done_something,
			   FreeVariableMap &freeVariables,
			   std::set<StateMachineState *> &done)
{
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
						   smp->target->sideEffects.begin(),
						   smp->target->sideEffects.end());
				target = smp->target->target;
				*done_something = true;
				return optimise(opt, oracle, done_something, freeVariables, done);
			}
		}
	}
	if (TIMEOUT)
		return this;
	target = target->optimise(opt, oracle, done_something, freeVariables, done);

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
	t.transformIRExpr(e);
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
		if (sm->target0())
			toEmit.push_back(sm->target0()->target);
		if (sm->target1())
			toEmit.push_back(sm->target1()->target);
	}
}

void
FreeVariableMap::print(FILE *f) const
{
	for (map_t::iterator it = content->begin();
	     it != content->end();
	     it++) {
		fprintf(f, "free%d -> ", it.key().val);
		ppIRExpr(it.value(), f);
		fprintf(f, "\n");
	}
}

bool
FreeVariableMap::parse(const char *str, const char **succ, char **err)
{
	content = new map_t();
	while (1) {
		FreeVariableKey k;
		IRExpr *val;
		if (!parseThisString("free", str, &str, err) ||
		    !parseDecimalInt(&k.val, str, &str, err) ||
		    !parseThisString(" -> ", str, &str, err) ||
		    !parseIRExpr(&val, str, &str, err) ||
		    !parseThisChar('\n', str, &str, err))
			break;
		content->set(FreeVariableKey(k), val);
	}
	*succ = str;
	return true;
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
printStateMachine(const StateMachineState *sm, FILE *f)
{
	std::map<const StateMachineState *, int> labels;
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
printStateMachine(const StateMachine *sm, FILE *f)
{
	fprintf(f, "Machine for %lx:%d\n", sm->origin, sm->tid);
	printStateMachine(sm->root, f);
	sm->freeVariables.print(f);
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
		return definitelyEqual(smses1->addr, smses2->addr, opt) &&
			definitelyEqual(smses1->data, smses2->data, opt);
	}
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *smsel1 =
			dynamic_cast<StateMachineSideEffectLoad *>(smse1);
		StateMachineSideEffectLoad *smsel2 =
			dynamic_cast<StateMachineSideEffectLoad *>(smse2);
		return threadAndRegister::fullEq(smsel1->target, smsel2->target) &&
			definitelyEqual(smsel1->addr, smsel2->addr, opt);
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec1 =
			dynamic_cast<StateMachineSideEffectCopy *>(smse1);
		StateMachineSideEffectCopy *smsec2 =
			dynamic_cast<StateMachineSideEffectCopy *>(smse2);
		return threadAndRegister::fullEq(smsec1->target, smsec2->target) &&
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
		return threadAndRegister::fullEq(smsep1->reg, smsep2->reg);
	}
	}
	abort();
}

bool
parseStateMachineSideEffect(StateMachineSideEffect **out,
			    const char *str,
			    const char **suffix,
			    char **err)
{
	const char *str2;
	if (parseThisString("<unreached>", str, suffix, err)) {
		*out = StateMachineSideEffectUnreached::get();
		return true;
	}
	IRExpr *addr;
	IRExpr *data;
	ThreadRip rip;
	if (parseThisString("*(", str, &str2, err) &&
	    parseIRExpr(&addr, str2, &str2, err) &&
	    parseThisString(") <- ", str2, &str2, err) &&
	    parseIRExpr(&data, str2, &str2, err) &&
	    parseThisString(" @ ", str2, &str2, err) &&
	    parseThreadRip(&rip, str2, suffix, err)) {
		*out = new StateMachineSideEffectStore(addr, data, rip);
		return true;
	}
	threadAndRegister key(threadAndRegister::invalid());
	if (parseThisString("LOAD ", str, &str2, err) &&
	    parseThreadAndRegister(&key, str2, &str2, err) &&
	    parseThisString(" <- *(", str2, &str2, err) &&
	    parseIRExpr(&addr, str2, &str2, err) &&
	    parseThisString(")@", str2, &str2, err) &&
	    parseThreadRip(&rip, str2, suffix, err)) {
		*out = new StateMachineSideEffectLoad(key, addr, rip);
		return true;
	}
	if (parseThisString("COPY ", str, &str2, err) &&
	    parseThreadAndRegister(&key, str2, &str2, err) &&
	    parseThisString(" = ", str2, &str2, err) &&
	    parseIRExpr(&data, str2, suffix, err)) {
		*out = new StateMachineSideEffectCopy(key, data);
		return true;
	}
	if (parseThisString("Assert !(", str, &str2, err) &&
	    parseIRExpr(&data, str2, &str2, err) &&
	    parseThisChar(')', str2, suffix, err)) {
		*out = new StateMachineSideEffectAssertFalse(data);
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
		      const char **suffix,
		      char **err)
{
	int targetLabel;
	std::vector<StateMachineSideEffect *> sideEffects;
	if (parseThisChar('{', str, &str, err)) {
		while (1) {
			StateMachineSideEffect *se;
			if (!parseStateMachineSideEffect(&se, str, &str, err))
				return false;
			sideEffects.push_back(se);
			if (parseThisString(sep, str, &str, err))
				continue;
			if (!parseThisString("} ", str, &str, err))
				return false;
			break;
		}
	}
	if (!parseThisChar('l', str, &str, err) ||
	    !parseDecimalInt(&targetLabel, str, suffix, err))
		return false;
	*out = new StateMachineEdge((StateMachineState *)targetLabel);
	(*out)->sideEffects = sideEffects;
	return true;
}

static bool
parseStateMachineState(StateMachineState **out,
		       const char *str,
		       const char **suffix,
		       char **err)
{
	if (parseThisString("<unreached>", str, suffix, err)) {
		*out = StateMachineUnreached::get();
		return true;
	}
	if (parseThisString("<crash>", str, suffix, err)) {
		*out = StateMachineCrash::get();
		return true;
	}
	if (parseThisString("<survive>", str, suffix, err)) {
		*out = StateMachineNoCrash::get();
		return true;
	}
	unsigned long origin;
	IRExpr *target;
	const char *str2;
	if (parseThisChar('<', str, &str2, err) &&
	    parseHexUlong(&origin, str2, &str2, err) &&
	    parseIRExpr(&target, str2, &str2, err) &&
	    parseThisChar('>', str2, suffix, err)) {
		*out = new StateMachineStub(origin, target);
		return true;
	}
	StateMachineEdge *target1;
	if (parseThisChar('{', str, &str2, err) &&
	    parseHexUlong(&origin, str2, &str2, err) &&
	    parseThisChar(':', str2, &str2, err) &&
	    parseStateMachineEdge(&target1, "\n  ", str2, &str2, err) &&
	    parseThisChar('}', str2, suffix, err)) {
		*out = new StateMachineProxy(origin, target1);
		return true;
	}
	IRExpr *condition;
	StateMachineEdge *target2;
	if (parseHexUlong(&origin, str, &str2, err) &&
	    parseThisString(": if (", str2, &str2, err) &&
	    parseIRExpr(&condition, str2, &str2, err) &&
	    parseThisString(")\n  then {\n\t", str2, &str2, err) &&
	    parseStateMachineEdge(&target1, "\n\t", str2, &str2, err) &&
	    parseThisString("}\n  else {\n\t", str2, &str2, err) &&
	    parseStateMachineEdge(&target2, "\n\t", str2, &str2, err) &&
	    parseThisChar('}', str2, suffix, err)) {
		*out = new StateMachineBifurcate(origin, condition, target1, target2);
		return true;
	}
	return false;
}

static bool
parseOneState(std::map<int, StateMachineState *> &out,
	      const char *str,
	      const char **suffix,
	      char **err)
{
	int label;
	StateMachineState *res;

	if (!parseThisChar('l', str, &str, err) ||
	    !parseDecimalInt(&label, str, &str, err) ||
	    !parseThisString(": ", str, &str, err) ||
	    !parseStateMachineState(&res, str, &str, err) ||
	    !parseThisChar('\n', str, &str, err))
		return false;
	if (out.count(label)) {
		*err = vex_asprintf("label %d defined multiple times", label);
		return false;
	}
	out[label] = res;
	*suffix = str;
	return true;
}

static bool
parseStateMachine(StateMachineState **out, const char *str, const char **suffix, char **err)
{
	std::map<int, StateMachineState *> labelToState;

	while (*str) {
		if (!parseOneState(labelToState, str, &str, err))
			break;
	}
	if (!labelToState.count(1)) {
		*err = (char *)"label 1 must be defined";
		return false;
	}
	for (std::map<int, StateMachineState *>::iterator it = labelToState.begin();
	     it != labelToState.end();
	     it++) {
		if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(it->second)) {
			StateMachineState *t = labelToState[(int)(unsigned long)smp->target->target];
			if (!t) {
				*err = vex_asprintf("Label %d not defined",
						    (int)(unsigned long)smp->target->target);
				return false;
			}
			smp->target->target = t;
		} else if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(it->second)) {
			StateMachineState *t = labelToState[(int)(unsigned long)smb->trueTarget->target];
			StateMachineState *f = labelToState[(int)(unsigned long)smb->falseTarget->target];
			if (!t) {
				*err = vex_asprintf("Label %d not defined",
						    (int)(unsigned long)smb->trueTarget->target);
				return false;
			}
			if (!f) {
				*err = vex_asprintf("Label %d not defined",
						    (int)(unsigned long)smb->falseTarget->target);
				return false;
			}

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
StateMachine::parse(StateMachine **out, const char *str, const char **suffix, char **err)
{
	unsigned long origin;
	int tid;
	if (!parseThisString("Machine for ", str, &str, err) ||
	    !parseHexUlong(&origin, str, &str, err) ||
	    !parseThisChar(':', str, &str, err) ||
	    !parseDecimalInt(&tid, str, &str, err) ||
	    !parseThisChar('\n', str, &str, err))
		return false;
	StateMachineState *root;

	/* Shut the compiler up: it can't tell that
	   parseStateMachine() will always initialise root if it
	   returns true. */
	root = (StateMachineState *)0xf001deadbeeful; 

	if (!parseStateMachine(&root, str, &str, err))
		return false;
	*out = new StateMachine(root, origin, tid);
	if (!(*out)->freeVariables.parse(str, suffix, err))
		return false;
	return true;
}
bool
parseStateMachine(StateMachine **out, const char *str, const char **suffix, char **err)
{
	return StateMachine::parse(out, str, suffix, err);
}

StateMachine *
readStateMachine(int fd)
{
	char *content = readfile(fd);
	const char *end;
	StateMachine *res;
	char *err;
	if (!parseStateMachine(&res, content, &end, &err) || *end)
		errx(1, "error parsing state machine (%s):\n%s", err, content);
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
	if (target0())
		target0()->target->assertAcyclic(stack, clean);
	if (target1())
		target1()->target->assertAcyclic(stack, clean);
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
StateMachineState::enumerateMentionedMemoryAccesses(std::set<unsigned long> &instrs)
{
	if (target1())
		target1()->enumerateMentionedMemoryAccesses(instrs);
	if (target0())
		target0()->enumerateMentionedMemoryAccesses(instrs);
}

void
StateMachineEdge::enumerateMentionedMemoryAccesses(std::set<unsigned long> &instrs)
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

static void
nrAliasingLoads(StateMachineState *sm,
		StateMachineSideEffectLoad *smsel,
		const Oracle::RegisterAliasingConfiguration &alias,
		const AllowableOptimisations &opt,
		int *out,
		std::set<StateMachineState *> &visited,
		OracleInterface *oracle);
static void
nrAliasingLoads(StateMachineEdge *sme,
		StateMachineSideEffectLoad *smsel,
		const Oracle::RegisterAliasingConfiguration &alias,
		const AllowableOptimisations &opt,
		int *out,
		std::set<StateMachineState *> &visited,
		OracleInterface *oracle)
{
	for (unsigned x = 0; x < sme->sideEffects.size(); x++) {
		StateMachineSideEffectLoad *smsel2 =
			dynamic_cast<StateMachineSideEffectLoad *>(sme->sideEffects[x]);
		if (smsel2 &&
		    alias.ptrsMightAlias(smsel->addr, smsel2->addr, opt.freeVariablesMightAccessStack) &&
		    oracle->memoryAccessesMightAlias(smsel, smsel2) &&
		    definitelyEqual( smsel->addr,
				     smsel2->addr,
				     opt))
			(*out)++;
	}
	nrAliasingLoads(sme->target, smsel, alias, opt, out, visited, oracle);
}
static void
nrAliasingLoads(StateMachineState *sm,
		StateMachineSideEffectLoad *smsel,
		const Oracle::RegisterAliasingConfiguration &alias,
		const AllowableOptimisations &opt,
		int *out,
		std::set<StateMachineState *> &visited,
		OracleInterface *oracle)
{
	if (visited.count(sm))
		return;
	visited.insert(sm);
	if (sm->target0())
		nrAliasingLoads(sm->target0(),
				smsel,
				alias,
				opt,
				out,
				visited,
				oracle);
	if (sm->target1())
		nrAliasingLoads(sm->target1(),
				smsel,
				alias,
				opt,
				out,
				visited,
				oracle);
}
static int
nrAliasingLoads(StateMachine *sm,
		StateMachineSideEffectLoad *smsel,
		const Oracle::RegisterAliasingConfiguration &alias,
		const AllowableOptimisations &opt,
		OracleInterface *oracle)
{
	std::set<StateMachineState *> visited;
	int res = 0;
	nrAliasingLoads(sm->root, smsel, alias, opt, &res, visited, oracle);
	return res;
}
			   
static bool definitelyNoSatisfyingStores(StateMachineState *sm,
					 StateMachineSideEffectLoad *smsel,
					 const Oracle::RegisterAliasingConfiguration &alias,
					 const AllowableOptimisations &opt,
					 bool haveAliasingStore,
					 OracleInterface *oracle);
static bool
definitelyNoSatisfyingStores(StateMachineEdge *sme,
			     StateMachineSideEffectLoad *smsel,
			     const Oracle::RegisterAliasingConfiguration &alias,
			     const AllowableOptimisations &opt,
			     bool haveAliasingStore,
			     OracleInterface *oracle)
{
	for (unsigned x = 0; x < sme->sideEffects.size(); x++) {
		StateMachineSideEffect *smse = sme->sideEffects[x];
		if (smse == smsel) {
			if (haveAliasingStore) {
				return false;
			} else {
				/* The load can't appear twice in one
				   path, and we've not seen a
				   satisfying store yet, so we're
				   fine. */
				return true;
			}
		}
		if (haveAliasingStore)
			continue;
		StateMachineSideEffectStore *smses =
			dynamic_cast<StateMachineSideEffectStore *>(smse);
		if (smses &&
		    alias.ptrsMightAlias(smsel->addr, smses->addr, opt.freeVariablesMightAccessStack) &&
		    oracle->memoryAccessesMightAlias(smsel, smses) &&
		    !definitelyNotEqual( smsel->addr,
					 smses->addr,
					 opt)) {
			/* This store might alias with the load.  If
			   we encounter the load after this, then it
			   might be satisfied. */
			haveAliasingStore = true;
		}
	}
	return definitelyNoSatisfyingStores(sme->target,
					    smsel,
					    alias,
					    opt,
					    haveAliasingStore,
					    oracle);
}
static bool
definitelyNoSatisfyingStores(StateMachineState *sm,
			     StateMachineSideEffectLoad *smsel,
			     const Oracle::RegisterAliasingConfiguration &alias,
			     const AllowableOptimisations &opt,
			     bool haveAliasingStore,
			     OracleInterface *oracle)
{
	if (sm->target0() && !definitelyNoSatisfyingStores(sm->target0(),
							   smsel,
							   alias,
							   opt,
							   haveAliasingStore,
							   oracle))
		return false;
	if (sm->target1() && !definitelyNoSatisfyingStores(sm->target1(),
							   smsel,
							   alias,
							   opt,
							   haveAliasingStore,
							   oracle))
		return false;
	return true;
}
static bool definitelyNoSatisfyingStores(StateMachine *sm,
					 StateMachineSideEffectLoad *smsel,
					 const Oracle::RegisterAliasingConfiguration &alias,
					 const AllowableOptimisations &opt,
					 bool haveAliasingStore,
					 OracleInterface *oracle)
{
	return definitelyNoSatisfyingStores(sm->root, smsel, alias, opt, haveAliasingStore, oracle);
}

/* There are some memory locations which are effectively completely
 * unconstrained by anything which the machine does.  Replace those
 * with freshly allocated free variables.  The idea here is that we
 * can then propagate that through a bit and potentially simplify lots
 * of other bits of the machine by allocating yet more free
 * variables. */
static StateMachineState *introduceFreeVariables(StateMachineState *sm,
						 StateMachine *root_sm,
						 const Oracle::RegisterAliasingConfiguration &alias,
						 const AllowableOptimisations &opt,
						 OracleInterface *oracle,
						 bool *done_something,
						 std::vector<std::pair<FreeVariableKey, IRExpr *> > &fresh);
static StateMachineEdge *
introduceFreeVariables(StateMachineEdge *sme,
		       StateMachine *root_sm,
		       const Oracle::RegisterAliasingConfiguration &alias,
		       const AllowableOptimisations &opt,
		       OracleInterface *oracle,
		       bool *done_something,
		       std::vector<std::pair<FreeVariableKey, IRExpr *> > &fresh)
{
	StateMachineEdge *out = new StateMachineEdge(NULL);
	bool doit = false;
	/* A load results in a free variable if it's local and no
	   stores could potentially alias with it and no other loads
	   could alias with it. */
	for (unsigned idx = 0; idx < sme->sideEffects.size(); idx++) {
		StateMachineSideEffect *smse = sme->sideEffects[idx];
		StateMachineSideEffectLoad *smsel = dynamic_cast<StateMachineSideEffectLoad *>(smse);
		if (!smsel ||
		    !oracle->loadIsThreadLocal(smsel) ||
		    !definitelyNoSatisfyingStores(root_sm, smsel, alias, opt, false, oracle) ||
		    nrAliasingLoads(root_sm, smsel, alias, opt, oracle) != 1) {
			out->sideEffects.push_back(smse);
			continue;
		}
		/* This is a local load from a location which is never
		 * stored.  Remove it. */
		StateMachineSideEffectCopy *smsec = new StateMachineSideEffectCopy(smsel->target, IRExpr_FreeVariable());
		out->sideEffects.push_back(smsec);
		fresh.push_back(std::pair<FreeVariableKey, IRExpr *>
				(((IRExprFreeVariable *)smsec->value)->key,
				 IRExpr_Load(Ity_I64, smsel->addr, smsel->rip)));
		doit = true;
	}
	out->target = introduceFreeVariables(sme->target, root_sm, alias, opt, oracle, &doit, fresh);

	if (doit) {
		*done_something = true;
		return out;
	} else {
		return sme;
	}
}
static StateMachineState *
introduceFreeVariables(StateMachineState *sm,
		       StateMachine *root_sm,
		       const Oracle::RegisterAliasingConfiguration &alias,
		       const AllowableOptimisations &opt,
		       OracleInterface *oracle,
		       bool *done_something,
		       std::vector<std::pair<FreeVariableKey, IRExpr *> > &fresh)
{
	bool doit = false;
	if (dynamic_cast<StateMachineTerminal *>(sm))
		return sm;
	if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm)) {
		StateMachineEdge *e = introduceFreeVariables(smp->target,
							     root_sm,
							     alias,
							     opt,
							     oracle,
							     &doit,
							     fresh);
		if (doit) {
			*done_something = true;
			return new StateMachineProxy(smp->origin, e);
		} else {
			return sm;
		}
	}
	StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(sm);
	assert(smb);
	StateMachineEdge *t = introduceFreeVariables(smb->trueTarget,
						     root_sm,
						     alias,
						     opt,
						     oracle,
						     &doit,
						     fresh);
	StateMachineEdge *f = introduceFreeVariables(smb->falseTarget,
						     root_sm,
						     alias,
						     opt,
						     oracle,
						     &doit,
						     fresh);
	if (doit) {
		*done_something = true;
		return new StateMachineBifurcate(smb->origin,
						 smb->condition,
						 t,
						 f);
	} else {
		return sm;
	}
}
StateMachine *
introduceFreeVariables(StateMachine *sm,
		       const Oracle::RegisterAliasingConfiguration &alias,
		       const AllowableOptimisations &opt,
		       OracleInterface *oracle,
		       bool *done_something)
{
	bool b = false;
	std::vector<std::pair<FreeVariableKey, IRExpr *> > fresh;
	StateMachineState *new_root = introduceFreeVariables(sm->root, sm, alias, opt, oracle, &b, fresh);
	if (b) {
		*done_something = true;
		StateMachine *new_sm =  new StateMachine(sm, fresh);
		new_sm->root = new_root;
		return new_sm;
	} else {
		return sm;
	}
}

class countFreeVariablesVisitor : public StateMachineTransformer {
	IRExpr *transformIex(IRExprFreeVariable *e) {
		counts[e->key]++;
		return StateMachineTransformer::transformIex(e);
	}
public:
	std::map<FreeVariableKey, int> counts;
};
class simplifyFreeVariablesTransformer : public StateMachineTransformer {
public:
	std::map<FreeVariableKey, int> &counts;
	FreeVariableMap &freeVariables;
	IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
		switch (e->tag) {
		case Iex_Const:
		case Iex_Get:
		case Iex_GetI:
		case Iex_Load:
		case Iex_Mux0X:
		case Iex_CCall:
		case Iex_FreeVariable:
		case Iex_ClientCall:
		case Iex_ClientCallFailed:
		case Iex_HappensBefore:
			break;
		case Iex_Qop: {
			IRExprQop *exp = (IRExprQop *)e;
			if (exp->arg1->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg1)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg1)->key,
						IRExpr_Qop(
							exp->op,
							freeVariables.get(((IRExprFreeVariable *)exp->arg1)->key),
							exp->arg2,
							exp->arg3,
							exp->arg4)));
				return exp->arg1;
			}
			if (exp->arg2->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg2)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg2)->key,
						IRExpr_Qop(
							exp->op,
							exp->arg1,
							freeVariables.get(((IRExprFreeVariable *)exp->arg2)->key),
							exp->arg3,
							exp->arg4)));
				return exp->arg2;
			}
			if (exp->arg3->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg3)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg3)->key,
						IRExpr_Qop(
							exp->op,
							exp->arg1,
							exp->arg2,
							freeVariables.get(((IRExprFreeVariable *)exp->arg3)->key),
							exp->arg4)));
				return exp->arg3;
			}
			if (exp->arg4->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg4)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg4)->key,
						IRExpr_Qop(
							exp->op,
							exp->arg1,
							exp->arg2,
							exp->arg3,
							freeVariables.get(((IRExprFreeVariable *)exp->arg4)->key))));
				return exp->arg4;
			}
			break;
		}
		case Iex_Triop: {
			IRExprTriop *exp = (IRExprTriop *)e;
			if (exp->arg1->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg1)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg1)->key,
						IRExpr_Triop(
							exp->op,
							freeVariables.get(((IRExprFreeVariable *)exp->arg1)->key),
							exp->arg2,
							exp->arg3)));
				return exp->arg1;
			}
			if (exp->arg2->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg2)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg2)->key,
						IRExpr_Triop(
							exp->op,
							exp->arg1,
							freeVariables.get(((IRExprFreeVariable *)exp->arg2)->key),
							exp->arg3)));
				return exp->arg2;
			}
			if (exp->arg3->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg3)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg3)->key,
						IRExpr_Triop(
							exp->op,
							exp->arg1,
							exp->arg2,
							freeVariables.get(((IRExprFreeVariable *)exp->arg3)->key))));
				return exp->arg3;
			}
			break;
		}
		case Iex_Binop: {
			IRExprBinop *exp = (IRExprBinop *)e;
			if (exp->arg1->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg1)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg1)->key,
						IRExpr_Binop(
							exp->op,
							freeVariables.get(((IRExprFreeVariable *)exp->arg1)->key),
							exp->arg2)));
				return exp->arg1;
			}
			if (exp->arg2->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg2)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg2)->key,
						IRExpr_Binop(
							exp->op,
							exp->arg1,
							freeVariables.get(((IRExprFreeVariable *)exp->arg2)->key))));
				return exp->arg2;
			}
			break;
		}
		case Iex_Unop: {
			IRExprUnop *exp = (IRExprUnop *)e;
			if (exp->arg->tag == Iex_FreeVariable &&
			    counts[ ((IRExprFreeVariable *)exp->arg)->key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						((IRExprFreeVariable *)exp->arg)->key,
						IRExpr_Unop(
							exp->op,
							freeVariables.get(((IRExprFreeVariable *)exp->arg)->key))));
				return exp->arg;
			}
			break;
		}
		case Iex_Associative: {
			IRExprAssociative *exp = (IRExprAssociative *)e;
			for (int x = 0; x < exp->nr_arguments; x++) {
				IRExpr *_a = exp->contents[x];
				if (_a->tag != Iex_FreeVariable)
					continue;
				IRExprFreeVariable *a = (IRExprFreeVariable *)_a;
				if (counts[a->key] != 1)
					continue;
				*done_something = true;
				IRExprAssociative *b = (IRExprAssociative *)IRExpr_Associative(exp);
				assert(freeVariables.get(a->key));
				b->contents[x] = freeVariables.get(a->key);
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
						a->key, b));
				return a;
			}
			break;
		}
		}
		return StateMachineTransformer::transformIRExpr(e, done_something);
	}
	simplifyFreeVariablesTransformer(std::map<FreeVariableKey, int> &_counts,
					 FreeVariableMap &fv)
		: counts(_counts), freeVariables(fv)
	{}
};

StateMachine *
optimiseFreeVariables(StateMachine *sm, bool *done_something)
{
	countFreeVariablesVisitor cfvv;
	bool ign;
	cfvv.transform(sm, &ign);
	simplifyFreeVariablesTransformer sfvt(cfvv.counts, sm->freeVariables);
	return sfvt.transform(sm, done_something);
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
	fprintf(f, "{%d:0x%lx}", smsema->rip.thread, smsema->rip.rip);
}

void
StateMachine::selectSingleCrashingPath(void)
{
	std::set<StateMachineEdge *> memo;
	root = root->selectSingleCrashingPath(memo);
}

void
FreeVariableMap::applyTransformation(IRExprTransformer &x, bool *done_something)
{
	for (map_t::iterator it = content->begin();
	     it != content->end();
	     it++)
		it.set_value(x.transformIRExpr(it.value(), done_something));
}

