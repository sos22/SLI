#include <stdlib.h>

#include "sli.h"
#include "state_machine.hpp"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"
#include "simplify_irexpr.hpp"
#include "eval_state_machine.hpp"
#include "alloc_mai.hpp"
#include "sat_checker.hpp"
#include "simplify_irexpr.hpp"
#include "timers.hpp"

#include "../VEX/priv/guest_generic_bb_to_IR.h"
#include "../VEX/priv/guest_amd64_defs.h"

#ifndef NDEBUG
static bool debug_gen_contexts = false;
#else
#define debug_gen_contexts false
#endif

#define BAD_PTR_FUZZ 10000000

class evalRes : public Named {
	int val;
	char *mkName() const {
		switch (val) {
		case 0:
			return strdup("unreached");
		case 1:
			return strdup("crash");
		case 2:
			return strdup("survive");
		default:
			abort();
		}
	}
	evalRes(int _val)
		: val(_val)
	{}
public:
	static evalRes unreached() { return evalRes(0); }
	static evalRes crash() { return evalRes(1); }
	static evalRes survive() { return evalRes(2); }
	bool operator==(const evalRes &o) {
		return val == o.val;
	}
	bool operator!=(const evalRes &o) {
		return val != o.val;
	}
};

class evalExprRes : public Named {
	bool _failed;
	unsigned long val;
	char *mkName() const {
		if (_failed)
			return strdup("<failed>");
		else
			return my_asprintf("0x%lx", val);
	}
	evalExprRes()
		: _failed(true), val(0xf001dead)
	{}
	evalExprRes(unsigned long v)
		: _failed(false), val(v)
	{}
public:
	static evalExprRes failed() {
		return evalExprRes();
	}
	static evalExprRes success(unsigned long v) {
		return evalExprRes(v);
	}
	bool unpack(unsigned long *v) {
		if (_failed) {
			return false;
		} else {
			*v = val;
			return true;
		}
	}
	bool valid() { return !_failed; }
	bool operator==(const evalExprRes &o) const {
		if (_failed != o._failed) {
			return false;
		}
		if (_failed) {
			return true;
		}
		return val == o.val;
	}
};

class EvalState {
public:
	EvalState() { clear(); }
	std::map<threadAndRegister, unsigned long> regs;
	std::map<MemoryAccessIdentifier, unsigned long> freeVars;
	std::map<unsigned long, unsigned long> memory;
	std::set<unsigned long> badPtrs;
	std::map<unsigned, CfgLabel> entryPoints;
	std::map<unsigned, std::set<CfgLabel> > nonEntryPoints;
	sane_map<std::pair<unsigned, CfgLabel>, CfgLabel> controlFlow;
	std::map<std::pair<unsigned, CfgLabel>, std::set<CfgLabel> > nonControlFlow;

	/* (a, b) in hbEdges -> a must happen before b */
	std::vector<std::pair<MemoryAccessIdentifier, MemoryAccessIdentifier> > hbEdges;
	bool hasIssuedStore;
	void prettyPrint(FILE *f) const {
		fprintf(f, "Regs:\n");
		for (auto it = regs.begin(); it != regs.end(); it++)
			fprintf(f, "\t%s -> 0x%lx\n", it->first.name(), it->second);
		fprintf(f, "freeVars:\n");
		for (auto it = freeVars.begin(); it != freeVars.end(); it++)
			fprintf(f, "\t%s -> 0x%lx\n", it->first.name(), it->second);
		fprintf(f, "memory:\n");
		for (auto it = memory.begin(); it != memory.end(); it++)
			fprintf(f, "\t0x%lx -> 0x%lx\n", it->first, it->second);
		fprintf(f, "badPtrs:\n");
		for (auto it = badPtrs.begin(); it != badPtrs.end(); it++)
			fprintf(f, "\t0x%lx\n", *it);
		fprintf(f, "entryPoints:\n");
		for (auto it = entryPoints.begin(); it != entryPoints.end(); it++)
			fprintf(f, "\t%d -> %s\n", it->first, it->second.name());
		fprintf(f, "nonEntryPoints:\n");
		for (auto it = nonEntryPoints.begin(); it != nonEntryPoints.end(); it++) {
			fprintf(f, "\t%d -> {", it->first);
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				if (it2 != it->second.begin())
					fprintf(f, ", ");
				fprintf(f, "%s", it2->name());
			}
			fprintf(f, "}\n");
		}
		fprintf(f, "controlFlow:\n");
		for (auto it = controlFlow.begin(); it != controlFlow.end(); it++) {
			fprintf(f, "\t(%d,%s) -> %s\n", it->first.first,
				it->first.second.name(), it->second.name());
		}
		fprintf(f, "nonControlFlow:\n");
		for (auto it = nonControlFlow.begin(); it != nonControlFlow.end(); it++) {
			fprintf(f, "\t(%d,%s) -> {", it->first.first, it->first.second.name());
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				if (it2 != it->second.begin()) {
					fprintf(f, ", ");
				}
				fprintf(f, "%s", it2->name());
			}
			fprintf(f, "}\n");
		}
		fprintf(f, "hbEdges:\n");
		for (auto it = hbEdges.begin(); it != hbEdges.end(); it++)
			fprintf(f, "\t%s <-< %s\n", it->first.name(), it->second.name());
		fprintf(f, "hasIssuedStore: %s\n", hasIssuedStore ? "true" : "false");
	}

	/* Possible return values:

	   -- Definitely a bad pointer.
	   -- Definitely contains a given value.
	   -- Definitely a valid memory location, but unknown value.
	   -- Nothing known */
	enum loadMemoryRes {
		lmr_bad_ptr,
		lmr_known_value,
		lmr_unknown_value,
		lmr_unknown_state
	};
	loadMemoryRes loadMemory(unsigned long addr, unsigned long *value) const {
		if (addr < 4096) {
			return lmr_bad_ptr;
		}
		for (auto it = badPtrs.begin(); it != badPtrs.end(); it++) {
			if (addr + BAD_PTR_FUZZ >= *it &&
			    *it + BAD_PTR_FUZZ >= addr)
				return lmr_bad_ptr;
		}
		auto it_l = memory.find(addr);
		if (it_l != memory.end()) {
			*value = it_l->second;
			return lmr_known_value;
		}
		for (auto it = memory.begin(); it != memory.end(); it++) {
			if (addr + BAD_PTR_FUZZ >= it->first &&
			    it->first + BAD_PTR_FUZZ >= addr)
				return lmr_unknown_value;
		}
		return lmr_unknown_state;
	}
	evalExprRes badPtr(unsigned long addr) const
	{
		unsigned long val;
		switch (loadMemory(addr, &val)) {
		case lmr_bad_ptr:
			return evalExprRes::success(1);
		case lmr_known_value:
		case lmr_unknown_value:
			return evalExprRes::success(0);
		case lmr_unknown_state:
			return evalExprRes::failed();
		}
		abort();
	}

	evalExprRes happensBefore(const MemoryAccessIdentifier &acc1,
				  const MemoryAccessIdentifier &acc2) const
	{
		/* All accesses which might happen before or after the
		   two accesses, include the accesses themselves. */
		std::set<MemoryAccessIdentifier> beforeAcc1, afterAcc1, beforeAcc2, afterAcc2;
		beforeAcc2.insert(acc2);
		afterAcc2.insert(acc2);

		bool progress;
		progress = true;
		beforeAcc1.insert(acc1);
		while (progress) {
			progress = false;
			for (auto it = hbEdges.begin(); it != hbEdges.end(); it++) {
				if (beforeAcc1.count(it->second))
					progress |= beforeAcc1.insert(it->first).second;
			}
			if (beforeAcc1.count(acc2))
				return evalExprRes::success(0);
		}
		progress = true;
		afterAcc1.insert(acc1);
		while (progress) {
			progress = false;
			for (auto it = hbEdges.begin(); it != hbEdges.end(); it++) {
				if (afterAcc1.count(it->first))
					progress |= afterAcc1.insert(it->first).second;
			}
			if (afterAcc1.count(acc2))
				return evalExprRes::success(1);
		}
		progress = true;
		beforeAcc2.insert(acc2);
		while (progress) {
			progress = false;
			for (auto it = hbEdges.begin(); it != hbEdges.end(); it++) {
				if (beforeAcc2.count(it->second))
					progress |= beforeAcc2.insert(it->first).second;
			}
			if (beforeAcc2.count(acc1))
				return evalExprRes::success(1);
		}
		progress = true;
		afterAcc2.insert(acc2);
		while (progress) {
			progress = false;
			for (auto it = hbEdges.begin(); it != hbEdges.end(); it++) {
				if (afterAcc2.count(it->first))
					progress |= afterAcc2.insert(it->second).second;
			}
			if (afterAcc2.count(acc1))
				return evalExprRes::success(0);
		}
		return evalExprRes::failed();
	}
	void clear() {
		regs.clear();
		freeVars.clear();
		memory.clear();
		badPtrs.clear();
		entryPoints.clear();
		nonEntryPoints.clear();
		controlFlow.clear();
		nonControlFlow.clear();
		hbEdges.clear();
		hasIssuedStore = false;
	}
	bool consistent() const {
		/* Not interested in anything where RSP is a bad
		 * pointer. */
		for (auto it = regs.begin(); it != regs.end(); it++) {
			if (it->first.isReg() && it->first.asReg() == OFFSET_amd64_RSP) {
				evalExprRes err(badPtr(it->second));
				unsigned long v;
				if (err.unpack(&v) && v)
					return false;
			}
		}
		return true;
	}
};

struct EvalArgs {
	EvalState *randomAcc;
	VexPtr<OracleInterface, &ir_heap> oracle;
	VexPtr<MaiMap, &ir_heap> decode;
	const AllowableOptimisations *opt;
};

class EvalCtxt : public GcCallback<&ir_heap> {
	EvalCtxt(const EvalCtxt &o);
	void operator =(const EvalCtxt &o);
	void runGc(HeapVisitor &hv) {
		for (auto it = logmsgs.begin(); it != logmsgs.end(); it++)
			hv(it->first);
	}
	evalExprRes eval(IRExpr *e, EvalState *randomAcc);
public:
	EvalState currentState;
	std::vector<threadAndRegister> regOrder;
	std::vector<std::pair<const StateMachineState *, char *> > logmsgs;
	std::map<unsigned long, std::set<StateMachineSideEffectMemoryAccess *> > accesses;

	void reset(const EvalState &s) {
		currentState = s;
		regOrder.clear();
		for (auto it = logmsgs.begin(); it != logmsgs.end(); it++)
			free(it->second);
		logmsgs.clear();
	}
	EvalCtxt(EvalState &_initialState)
		: currentState(_initialState)
	{}
	~EvalCtxt() {
		for (auto it = logmsgs.begin(); it != logmsgs.end(); it++)
			free(it->second);
	}

	evalExprRes eval(exprbdd *, EvalState *randomAcc);
	Maybe<bool> eval(bbdd *, EvalState *randomAcc);
	Maybe<StateMachineRes> eval(smrbdd *, EvalState *randomAcc);

	bool eval(const StateMachineState *, StateMachineSideEffect *effect, const EvalArgs &randomAcc);
	evalRes eval(VexPtr<StateMachineState, &ir_heap> state,
		     GarbageCollectionToken token,
		     const EvalArgs &args);
	void log(const StateMachineState *, const char *fmt, ...) __attribute__((__format__( __printf__, 3, 4)));
	void printLog(FILE *f, const std::map<const StateMachineState *, int> &labels) const;

	void prettyPrint(FILE *f) const;
};

static unsigned long
genRandomUlong()
{
	unsigned long res;
	res = random() + random() * RAND_MAX + random() * RAND_MAX * RAND_MAX;
	return res;
}

static IRExpr *mk_const(unsigned long val, IRType ty)
{
	switch (ty) {
	case Ity_I8:
		return IRExpr_Const_U8(val);
	case Ity_I16:
		return IRExpr_Const_U16(val);
	case Ity_I32:
		return IRExpr_Const_U32(val);
	case Ity_I64:
		return IRExpr_Const_U64(val);
	case Ity_I1:
		return IRExpr_Const_U1(val);
	case Ity_INVALID:
	case Ity_I128:
		break;
	}
	abort();
}

template <typename ty> static void
printNamedContainer(FILE *f, const ty &tr)
{
	fprintf(f, "{");
	for (auto it = tr.begin(); it != tr.end(); it++) {
		if (it == tr.begin()) {
			fprintf(f, ", ");
		}
		fprintf(f, "%s", it->name());
	}
	fprintf(f, "}");
}

void
EvalCtxt::prettyPrint(FILE *f) const
{
	currentState.prettyPrint(f);
	fprintf(f, "regOrder: ");
	printNamedContainer(f, regOrder);
	fprintf(f, "\n");
	fprintf(f, "log:\n");
	for (auto it = logmsgs.begin(); it != logmsgs.end(); it++) {
		fprintf(f, "\t%s\n", it->second);
	}
}

static evalExprRes evalExpr(EvalState &ctxt, IRExpr *what, bool *usedRandom, EvalState *randomAcc);

evalExprRes
EvalCtxt::eval(IRExpr *e, EvalState *randomAcc)
{
	bool b;
	evalExprRes res(evalExpr(currentState, e, &b, randomAcc));
	return res;
}

evalExprRes
EvalCtxt::eval(exprbdd *e, EvalState *randomAcc)
{
	if (e->isLeaf()) {
		return eval(e->leaf(), randomAcc);
	} else {
		evalExprRes r(eval(e->internal().condition, randomAcc));
		unsigned long r2;
		if (!r.unpack(&r2)) {
			auto a = eval(e->internal().trueBranch, randomAcc);
			auto b = eval(e->internal().falseBranch, randomAcc);
			if (a == b) {
				return a;
			} else {
				return evalExprRes::failed();
			}
		} else if (r2) {
			return eval(e->internal().trueBranch, randomAcc);
		} else {
			return eval(e->internal().falseBranch, randomAcc);
		}
	}
}
Maybe<bool>
EvalCtxt::eval(bbdd *e, EvalState *randomAcc)
{
	if (e->isLeaf()) {
		return e->leaf();
	} else {
		evalExprRes r(eval(e->internal().condition, randomAcc));
		unsigned long r2;
		if (!r.unpack(&r2)) {
			auto a = eval(e->internal().trueBranch, randomAcc);
			auto b = eval(e->internal().falseBranch, randomAcc);
			if (a == b) {
				return a;
			} else {
				return Maybe<bool>::nothing();
			}
		} else if (r2) {
			return eval(e->internal().trueBranch, randomAcc);
		} else {
			return eval(e->internal().falseBranch, randomAcc);
		}
	}
}
Maybe<StateMachineRes>
EvalCtxt::eval(smrbdd *e, EvalState *randomAcc)
{
	if (e->isLeaf()) {
		return e->leaf();
	} else {
		evalExprRes r(eval(e->internal().condition, randomAcc));
		unsigned long r2;
		if (!r.unpack(&r2)) {
			auto a = eval(e->internal().trueBranch, randomAcc);
			auto b = eval(e->internal().falseBranch, randomAcc);
			if (a == b) {
				return a;
			} else {
				return Maybe<StateMachineRes>::nothing();
			}
		} else if (r2) {
			return eval(e->internal().trueBranch, randomAcc);
		} else {
			return eval(e->internal().falseBranch, randomAcc);
		}
	}
}

void
EvalCtxt::log(const StateMachineState *state, const char *fmt, ...)
{
	va_list args;
	char *buf;
	va_start(args, fmt);
	if (vasprintf(&buf, fmt, args) < 0)
		errx(1, "formating log msg; fmt %s\n", fmt);
	va_end(args);
	logmsgs.push_back(std::pair<const StateMachineState *, char *>(state, buf));
}

void
EvalCtxt::printLog(FILE *f, const std::map<const StateMachineState *, int> &labels) const
{
	for (auto it = logmsgs.begin(); it != logmsgs.end(); it++) {
		auto it2 = labels.find(it->first);
		assert(it2 != labels.end());
		fprintf(f, "l%d: %s\n", it2->second, it->second);
	}
}

bool
EvalCtxt::eval(const StateMachineState *state, StateMachineSideEffect *effect, const EvalArgs &args)
{
	switch (effect->type) {
	case StateMachineSideEffect::Load: {
		auto *l = (StateMachineSideEffectLoad *)effect;
		evalExprRes addr1(eval(l->addr, args.randomAcc));
		unsigned long addr;
		if (!addr1.unpack(&addr)) {
			return false;
		}

		std::set<StateMachineSideEffectMemoryAccess *> &accesses(this->accesses[addr]);
		for (auto it = accesses.begin(); it != accesses.end(); it++) {
			if (!args.oracle->memoryAccessesMightAlias(*args.decode, *args.opt, *it, l)) {
				return false;
			}
		}
		accesses.insert(l);

		unsigned long res;
		switch (currentState.loadMemory(addr, &res)) {
		case EvalState::lmr_bad_ptr:
			log(state, "load(%lx) -> bad pointer", addr);
			return false;
		case EvalState::lmr_known_value:
			log(state, "load(%lx) -> %lx, already in memory", addr, res);
			break;
		case EvalState::lmr_unknown_value:
		case EvalState::lmr_unknown_state:
			res = genRandomUlong();
			currentState.memory[addr] = res;
			if (args.randomAcc) {
				args.randomAcc->memory[addr] = res;
			}
			log(state, "load(%lx) -> %lx, freshly generated", addr, res);
			break;
		}
		currentState.regs[l->target] = res;
		regOrder.push_back(l->target);
		return true;
	}
	case StateMachineSideEffect::Store: {
		auto *s = (StateMachineSideEffectStore *)effect;
		evalExprRes addr1(eval(s->addr, args.randomAcc));
		unsigned long addr;
		if (!addr1.unpack(&addr)) {
			return false;
		}

		std::set<StateMachineSideEffectMemoryAccess *> &accesses(this->accesses[addr]);
		for (auto it = accesses.begin(); it != accesses.end(); it++) {
			if (!args.oracle->memoryAccessesMightAlias(*args.decode, *args.opt, *it, s)) {
				return false;
			}
		}
		accesses.insert(s);

		evalExprRes err(currentState.badPtr(addr));
		unsigned long isBadPtr;
		if (err.unpack(&isBadPtr) && isBadPtr) {
			log(state, "store to %lx: is a bad pointer", addr);
			/* This should arguably return false, and so
			   flag this execution as reaching an escaping
			   state, but that produces so many false
			   positives that it's not worth it. */
			return true;
		}
		evalExprRes data1(eval(s->data, args.randomAcc));
		unsigned long data;
		if (!data1.unpack(&data)) {
			return false;
		}
		currentState.memory[addr] = data;
		currentState.hasIssuedStore = true;
		log(state, "store %lx -> %lx", data, addr);
		return true;
	}
	case StateMachineSideEffect::Copy: {
		auto *c = (StateMachineSideEffectCopy *)effect;
		evalExprRes val1(eval(c->value, args.randomAcc));
		unsigned long val;
		if (!val1.unpack(&val)) {
			return false;
		}
		currentState.regs[c->target] = val;
		regOrder.push_back(c->target);
		log(state, "copy %lx", val);
		return true;
	}
	case StateMachineSideEffect::Unreached:
		log(state, "unreached side-effect");
		return false;
	case StateMachineSideEffect::AssertFalse: {
		auto *a = (StateMachineSideEffectAssertFalse *)effect;
		Maybe<bool> v = eval(a->value, args.randomAcc);
		log(state, "AssertFalse(%s)", v.valid ? (v.content ? "true" : "false") : "unreached");
		if (v.valid && !v.content)
			return true;
		else
			return false;
	}
	case StateMachineSideEffect::Phi: {
		auto *p = (StateMachineSideEffectPhi *)effect;
		for (auto it = regOrder.rbegin(); it != regOrder.rend(); it++) {
			for (auto it2 = p->generations.begin(); it2 != p->generations.end(); it2++) {
				if (it2->reg == *it) {
					assert(currentState.regs.count(it2->reg));
					currentState.regs[p->reg] = currentState.regs[it2->reg];
					regOrder.push_back(p->reg);
					log(state, "phi satisfied by %s (%lx)",
					    it2->reg.name(),
					    currentState.regs[p->reg]);
					return true;
				}
			}
		}
		/* Okay, so we have no assignments, so it must be an
		 * initial value Phi. */
		for (auto it = p->generations.begin(); it != p->generations.end(); it++) {
			if (it->reg.gen() == (unsigned)-1) {
				if (!currentState.regs.count(it->reg)) {
					currentState.regs[it->reg] = genRandomUlong();
					log(state,
					    "phi satisfied by initial load of %s, randomly generated %lx",
					    it->reg.name(),
					    currentState.regs[it->reg]);
					if (args.randomAcc) {
						args.randomAcc->regs[it->reg] = genRandomUlong();
					}
				} else {
					log(state,
					    "phi satisfied by initial load of %s, already set to %lx",
					    it->reg.name(),
					    currentState.regs[it->reg]);
				}
				currentState.regs[p->reg] = currentState.regs[it->reg];
				regOrder.push_back(p->reg);
				return true;
			}
		}
		log(state, "phi is unsatisfied, using random value");
		currentState.regs[p->reg] = genRandomUlong();
		regOrder.push_back(p->reg);
		return true;
	}
	case StateMachineSideEffect::ImportRegister: {
		auto a = (StateMachineSideEffectImportRegister *)effect;
		threadAndRegister src(threadAndRegister::reg(a->tid, a->vex_offset, (unsigned)-1));
		auto it_did_insert = currentState.regs.insert(std::pair<threadAndRegister, unsigned long>(src, 0xf001beefdeadbabe));
		unsigned long v;
		if (it_did_insert.second) {
			v = genRandomUlong();
			it_did_insert.first->second = v;
			if (args.randomAcc) {
				args.randomAcc->regs[src] = v;
			}
			log(state, "import %s -> generate fresh %lx",
			    src.name(), v);
		} else {
			v = it_did_insert.first->second;
			log(state, "import %s -> %lx", src.name(), v);
		}
		currentState.regs[a->reg] = v;
		regOrder.push_back(a->reg);
		return true;
	}

	case StateMachineSideEffect::StartAtomic:
	case StateMachineSideEffect::EndAtomic:
#if !CONFIG_NO_STATIC_ALIASING
	case StateMachineSideEffect::StartFunction:
	case StateMachineSideEffect::EndFunction:
	case StateMachineSideEffect::StackLayout:
#endif
		log(state, "ignored side effect");
		return true;
	}
	abort();
}

evalRes
EvalCtxt::eval(VexPtr<StateMachineState, &ir_heap> state,
	       GarbageCollectionToken token,
	       const EvalArgs &args)
{
top:
	LibVEX_maybe_gc(token);
	switch (state->type) {
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)state.get();
		Maybe<bool> c(eval(smb->condition, args.randomAcc));
		if (!c.valid) {
			log(state, "condition is uneval");
			return evalRes::unreached();
		}
		if (c.content) {
			log(state, "condition is true");
			state = smb->trueTarget;
		} else {
			log(state, "condition is false");
			state = smb->falseTarget;
		}
		goto top;
	}
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *sme = (StateMachineSideEffecting *)state.get();
		if (sme->sideEffect) {
			if (!eval(state, sme->sideEffect, args)) {
				log(state, "eval side effect failed");
				return evalRes::unreached();
			}
		} else {
			log(state, "no-op");
		}
		state = sme->target;
		goto top;
	}
	case StateMachineState::Terminal: {
		auto smt = (StateMachineTerminal *)state.get();
		Maybe<StateMachineRes> r(eval(smt->res, args.randomAcc));
		if (!r.valid) {
			log(state, "uneval terminal");
			return evalRes::unreached();
		}
		switch (r.content) {
		case smr_unreached:
			log(state, "unreached");
			return evalRes::unreached();
		case smr_crash:
			log(state, "crash");
			if (!currentState.consistent())
				return evalRes::unreached();
			if (args.opt->mustStoreBeforeCrash())
				return evalRes::survive();
			return evalRes::crash();
		case smr_survive:
			log(state, "no-crash");
			if (!currentState.consistent())
				return evalRes::unreached();
			return evalRes::survive();
		}
		abort();
	}
	}
	abort();
}

static evalExprRes
evalExpr(EvalState &ctxt, IRExpr *what, bool *usedRandom, EvalState *randomAcc)
{
	struct : public IRExprTransformer {
		EvalState *ctxt;
		EvalState *randomAcc;
		bool *usedRandom;
		IRExpr *transformIex(IRExprGet *ieg) {
			if (ieg->reg.isReg() &&
			    ieg->reg.gen() == (unsigned)-1 &&
			    !ctxt->regs.count(ieg->reg) &&
			    usedRandom) {
				*usedRandom = true;
				ctxt->regs[ieg->reg] = genRandomUlong();
				if (randomAcc) {
					randomAcc->regs[ieg->reg] = ctxt->regs[ieg->reg];
				}
			}
			if (ctxt->regs.count(ieg->reg)) {
				return mk_const(ctxt->regs[ieg->reg], ieg->type());
			}
			return ieg;
		}
		IRExpr *transformIex(IRExprGetI *) {
			abort();
		}
		IRExpr *transformIex(IRExprLoad *e) {
			IRExpr *addr = transformIRExpr(e->addr);
			addr = simplifyIRExpr(addr, AllowableOptimisations::defaultOptimisations);
			if (addr->tag != Iex_Const)
				return IRExpr_Load(e->ty, addr);
			assert(addr->tag == Iex_Const);
			assert(addr->type() == Ity_I64);
			unsigned long address = ((IRExprConst *)addr)->Ico.content.U64;
			unsigned long val;
			switch (ctxt->loadMemory(address, &val)) {
			case EvalState::lmr_bad_ptr:
				break;
			case EvalState::lmr_known_value:
				return mk_const(val, e->type());
			case EvalState::lmr_unknown_value:
			case EvalState::lmr_unknown_state:
				if (!usedRandom)
					break;
				*usedRandom = true;
				ctxt->memory[address] = genRandomUlong();
				if (randomAcc) {
					randomAcc->memory[address] = ctxt->memory[address];
				}
				return mk_const(ctxt->memory[address], e->type());
			}
			return IRExpr_Load(e->ty, addr);
		}
		IRExpr *transformIex(IRExprHappensBefore *e) {
			auto er(ctxt->happensBefore(e->before, e->after));
			unsigned long res;
			if (er.unpack(&res)) {
				assert(res == 0 || res == 1);
				return mk_const(res, Ity_I1);
			}
			if (usedRandom) {
				*usedRandom = true;
				bool res = random() % 2 == 0;
				if (res) {
					ctxt->hbEdges.push_back(std::pair<MemoryAccessIdentifier, MemoryAccessIdentifier>(e->before, e->after));
					if (randomAcc) {
						randomAcc->hbEdges.push_back(std::pair<MemoryAccessIdentifier, MemoryAccessIdentifier>(e->before, e->after));
					}
				} else {
					ctxt->hbEdges.push_back(std::pair<MemoryAccessIdentifier, MemoryAccessIdentifier>(e->after, e->before));
					if (randomAcc) {
						randomAcc->hbEdges.push_back(std::pair<MemoryAccessIdentifier, MemoryAccessIdentifier>(e->after, e->before));
					}
				}
				return mk_const(res, Ity_I1);
			}
			return e;
		}
		IRExpr *transformIex(IRExprFreeVariable *e) {
			if (ctxt->freeVars.count(e->id))
				return mk_const(ctxt->freeVars[e->id], e->ty);
			if (usedRandom) {
				*usedRandom = true;
				ctxt->freeVars[e->id] = genRandomUlong();
				if (randomAcc) {
					randomAcc->freeVars[e->id] = ctxt->freeVars[e->id];
				}
				return mk_const(ctxt->freeVars[e->id], e->ty);
			}
			return e;
		}
		IRExpr *transformIex(IRExprEntryPoint *e) {
			auto it = ctxt->entryPoints.find(e->thread);
			if (it != ctxt->entryPoints.end())
				return mk_const(it->second == e->label, Ity_I1);
			if (ctxt->nonEntryPoints[e->thread].count(e->label))
				return mk_const(0, Ity_I1);
			if (usedRandom) {
				*usedRandom = true;
				bool res = random() % 2 == 0;
				if (res) {
					assert(!ctxt->entryPoints.count(e->thread));
					ctxt->entryPoints.insert(std::pair<unsigned, CfgLabel>(e->thread, e->label));
					if (randomAcc) {
						randomAcc->entryPoints.insert(std::pair<unsigned, CfgLabel>(e->thread, e->label));
					}
				} else {
					ctxt->nonEntryPoints[e->thread].insert(e->label);
					if (randomAcc) {
						randomAcc->nonEntryPoints[e->thread].insert(e->label);
					}
				}
				return mk_const(res, Ity_I1);
			}
			return e;
		}
		IRExpr *transformIex(IRExprControlFlow *e) {
			std::pair<unsigned, CfgLabel> k(e->thread, e->cfg1);
			auto it = ctxt->controlFlow.find(k);
			if (it != ctxt->controlFlow.end())
				return mk_const(it->second == e->cfg2, Ity_I1);
			if (ctxt->nonControlFlow[k].count(e->cfg2))
				return mk_const(0, Ity_I1);
			if (usedRandom) {
				*usedRandom = true;
				bool res = random() % 2 == 0;
				if (res) {
					assert(!ctxt->controlFlow.count(k));
					ctxt->controlFlow.insert(k, e->cfg2);
					if (randomAcc) {
						randomAcc->controlFlow.insert(k, e->cfg2);
					}
				} else {
					ctxt->nonControlFlow[k].insert(e->cfg2);
					if (randomAcc) {
						randomAcc->nonControlFlow[k].insert(e->cfg2);
					}
				}
				return mk_const(res, Ity_I1);
			}
			return e;
		}
		IRExpr *transformIex(IRExprUnop *e) {
			IRExpr *arg = transformIRExpr(e->arg);
			if (aborted)
				return e;
			if (e->op != Iop_BadPtr)
				return IRExpr_Unop(e->op, arg);
			arg = simplifyIRExpr(arg, AllowableOptimisations::defaultOptimisations);
			if (arg->tag != Iex_Const)
				return IRExpr_Unop(e->op, arg);
			assert(arg->tag == Iex_Const);
			assert(arg->type() == Ity_I64);
			unsigned long address = ((IRExprConst *)arg)->Ico.content.U64;
			evalExprRes err(ctxt->badPtr(address));
			unsigned long res;
			if (err.unpack(&res))
				return mk_const(!!res, Ity_I1);
			if (usedRandom) {
				*usedRandom = true;
				ctxt->memory[address] = genRandomUlong();
				if (randomAcc) {
					randomAcc->memory[address] = ctxt->memory[address];
				}
				return mk_const(0, Ity_I1);
			}
			return IRExpr_Unop(Iop_BadPtr, arg);
		}
		IRExpr *transformIex(IRExprCCall *e) {
			if (!strcmp(e->cee->name, "amd64g_calculate_condition") &&
			    e->args[1]->tag == Iex_Get) {
				/* Special case: make sure we produce
				   something which is nice and easy to
				   constant-fold here. */
				IRExprGet *ieg = (IRExprGet *)e->args[1];
				if (!ctxt->regs.count(ieg->reg))
					ctxt->regs[ieg->reg] = AMD64G_CC_OP_SUBQ;
			}

			return IRExprTransformer::transformIex(e);
		}
	} trans;
	trans.ctxt = &ctxt;
	trans.usedRandom = usedRandom;
	trans.randomAcc = randomAcc;
	IRExpr *a = trans.doit(what);
	a = simplifyIRExpr(a, AllowableOptimisations::defaultOptimisations);
	if (a->tag == Iex_Const)
		return evalExprRes::success(((IRExprConst *)a)->Ico.content.U64);
	else
		return evalExprRes::failed();
}

static bool makeEq(EvalState &res, IRExpr *arg1, IRExpr *arg2, bool wantTrue, bool *usedRandom, EvalState *randomAcc);

/* Returns true on success and false otherwise. */
static bool
makeEqConst(EvalState &res, unsigned long cnst, IRExpr *what, bool wantTrue, bool *usedRandom,
	    EvalState *randomAcc)
{
	switch (what->tag) {
	case Iex_FreeVariable: {
		auto *ief = (IRExprFreeVariable *)what;
		if (res.freeVars.count(ief->id)) {
			if (res.freeVars[ief->id] == cnst)
				return wantTrue;
			else
				return !wantTrue;
		}
		if (wantTrue)
			res.freeVars[ief->id] = cnst;
		else
			res.freeVars[ief->id] = cnst + 128;
		return true;
	}
	case Iex_Get: {
		auto *ieg = (IRExprGet *)what;
		if (!ieg->reg.isReg()) {
			return false;
		}
		if (res.regs.count(ieg->reg)) {
			if (res.regs[ieg->reg] == cnst)
				return wantTrue;
			else
				return !wantTrue;
		}
		if (wantTrue)
			res.regs[ieg->reg] = cnst;
		else
			res.regs[ieg->reg] = cnst + 128;
		return true;
	}
	case Iex_Load: {
		auto *iel = (IRExprLoad *)what;
		evalExprRes addr(evalExpr(res, iel->addr, usedRandom, randomAcc));
		unsigned long addr_c;
		if (!addr.unpack(&addr_c))
			return false;
		unsigned long val;
		switch (res.loadMemory(addr_c, &val)) {
		case EvalState::lmr_bad_ptr:
			return false;
		case EvalState::lmr_known_value:
			return (val == cnst) == wantTrue;
		case EvalState::lmr_unknown_value:
		case EvalState::lmr_unknown_state:
			if (wantTrue)
				res.memory[addr_c] = cnst;
			else
				res.memory[addr_c] = cnst + 128;
			return true;
		}
		abort();
	}
	case Iex_CCall: {
		auto iec = (IRExprCCall *)what;
		if (strcmp(iec->cee->name, "amd64g_calculate_condition"))
			break;
		IRExpr *cond, *cc_op, *dep1, *dep2;
		cond = iec->args[0];
		cc_op = iec->args[1];
		dep1 = iec->args[2];
		dep2 = iec->args[3];
		evalExprRes cond_eval(evalExpr(res, cond, NULL, randomAcc));
		evalExprRes cc_op_eval(evalExpr(res, cc_op, NULL, randomAcc));
		unsigned long cond_c;
		if (!cond_eval.unpack(&cond_c) ||
		    cc_op_eval.valid()) {
			unsigned long cc_op_c;
			/* Shut compiler up: it's only a debug message */
			cc_op_c = -1;
			cc_op_eval.unpack(&cc_op_c);
			printf("CC op %ld\n", cc_op_c);
			break;
		}
		if (!cnst)
			cond_c ^= 1;
		switch (cond_c) {
		case AMD64CondZ:
		case AMD64CondLE:
			return makeEqConst(res, AMD64G_CC_OP_SUBQ, cc_op, true, usedRandom, randomAcc) &&
				makeEq(res, dep1, dep2, wantTrue, usedRandom, randomAcc);
		case AMD64CondNZ:
			return makeEqConst(res, AMD64G_CC_OP_SUBQ, cc_op, true, usedRandom, randomAcc) &&
				makeEq(res, dep1, dep2, !wantTrue, usedRandom, randomAcc);
		case AMD64CondNLE:
			if (wantTrue) {
				return makeEqConst(res, AMD64G_CC_OP_SUBQ, cc_op, true, usedRandom, randomAcc) &&
					makeEqConst(res, 128, dep1, true, usedRandom, randomAcc) &&
					makeEqConst(res, 0, dep2, true, usedRandom, randomAcc);
			} else {
				return makeEqConst(res, AMD64G_CC_OP_SUBQ, cc_op, true, usedRandom, randomAcc) &&
					makeEqConst(res, 128, dep2, true, usedRandom, randomAcc) &&
					makeEqConst(res, 0, dep1, true, usedRandom, randomAcc);
			}
		default:
			break;
		}
		break;
	}
	case Iex_Associative: {
		auto *iea = (IRExprAssociative *)what;
		switch (iea->op) {
		case Iop_Add64: {
			if (iea->nr_arguments != 2)
				break;
			evalExprRes res1(evalExpr(res, iea->contents[0], NULL, randomAcc));
			evalExprRes res2(evalExpr(res, iea->contents[1], NULL, randomAcc));
			unsigned long res1c, res2c;
			if (res1.unpack(&res1c))
				return makeEqConst(res, cnst - res1c, iea->contents[1], wantTrue, usedRandom, randomAcc);
			if (res2.unpack(&res2c))
				return makeEqConst(res, cnst - res2c, iea->contents[0], wantTrue, usedRandom, randomAcc);
			res1 = evalExpr(res, iea->contents[0], usedRandom, randomAcc);
			return makeEqConst(res, cnst, iea->contents[1], wantTrue, usedRandom, randomAcc);
		}
		case Iop_Xor8:
		case Iop_Xor16:
		case Iop_Xor32:
		case Iop_Xor64: {
			if (iea->nr_arguments != 2)
				break;
			evalExprRes res1(evalExpr(res, iea->contents[0], NULL, randomAcc));
			evalExprRes res2(evalExpr(res, iea->contents[1], NULL, randomAcc));
			unsigned long res1c, res2c;
			if (res1.unpack(&res1c))
				return makeEqConst(res, cnst ^ res1c, iea->contents[1], wantTrue, usedRandom, randomAcc);
			if (res2.unpack(&res2c))
				return makeEqConst(res, cnst ^ res2c, iea->contents[0], wantTrue, usedRandom, randomAcc);
			res1 = evalExpr(res, iea->contents[0], usedRandom, randomAcc);
			return makeEqConst(res, cnst, iea->contents[1], wantTrue, usedRandom, randomAcc);
		}
		case Iop_And1: {
			std::vector<IRExpr *> nonConstArgs;
			for (int i = 0; i < iea->nr_arguments; i++) {
				evalExprRes eer(evalExpr(res, iea->contents[i], NULL, randomAcc));
				unsigned long a;
				if (eer.unpack(&a)) {
					if (!a) {
						/* Result is definitely false. */
						return !wantTrue;
					} else {
						/* Ignore it */
					}
				} else {
					nonConstArgs.push_back(iea->contents[i]);
				}
			}
			if (nonConstArgs.empty()) {
				/* Every clause is the constant true
				   -> result is the constant true as
				   well. */
				return wantTrue;
			}
			if (wantTrue == !!cnst) {
				/* We're trying to make this
				   expression evaluate to 1.  That
				   means that every clause has to
				   evaluate to 1. */
				for (auto it = nonConstArgs.begin();
				     it != nonConstArgs.end();
				     it++) {
					if (!makeEqConst(res, 1, *it, true, usedRandom, randomAcc))
						return false;
				}
				return true;
			} else {
				/* We're trying to make it eval to 0.
				   It's sufficient for any of the clauses
				   to be zero. */
				for (unsigned x = 0; x < nonConstArgs.size() - 1; x++) {
					EvalState r2(res);
					bool ur = false;
					if (makeEqConst(r2, 0, nonConstArgs[x], true, usedRandom ? &ur : NULL, randomAcc)) {
						res = r2;
						if (ur) {
							assert(usedRandom);
							*usedRandom = true;
						}
						return true;
					}
				}
				return false;
			}
			abort();
		}
		case Iop_And8:
		case Iop_And16:
		case Iop_And32:
		case Iop_And64: {
			std::vector<IRExpr *> nonConstArgs;
			unsigned long consts = ~0ul;
			for (int i = 0; i < iea->nr_arguments; i++) {
				evalExprRes eer(evalExpr(res, iea->contents[i], NULL, randomAcc));
				unsigned long a;
				if (eer.unpack(&a)) {
					consts &= a;
					if (cnst & ~consts)
						return !wantTrue;
				} else {
					nonConstArgs.push_back(iea->contents[i]);
				}
			}
			cnst &= ~consts;
			if (nonConstArgs.empty())
				return wantTrue == (cnst == consts);
			if (cnst != 0) {
				/* XXX could be more clever here. */
				break;
			}
			for (unsigned x = 0; x < nonConstArgs.size() - 1; x++) {
				EvalState r2(res);
				bool ur = false;
				if (makeEqConst(r2, cnst, nonConstArgs[x], wantTrue, usedRandom ? &ur : NULL, randomAcc)) {
					res = r2;
					if (ur) {
						assert(usedRandom);
						*usedRandom = true;
					}
					return true;
				}
			}
			return makeEqConst(res, cnst, nonConstArgs.back(), wantTrue, usedRandom, randomAcc);
		}
		default:
			break;
		}
		break;
	}
	case Iex_Unop: {
		auto *ieu = (IRExprUnop *)what;
		switch (ieu->op) {
		case Iop_Neg64:
			return makeEqConst(res, -cnst, ieu->arg, wantTrue, usedRandom, randomAcc);
		case Iop_Not1:
			return makeEqConst(res, !cnst, ieu->arg, wantTrue, usedRandom, randomAcc);
		case Iop_16to8:
		case Iop_32to8:
		case Iop_64to8: {
			if (cnst & ~0xfful)
				return !wantTrue;
			return makeEqConst(res, cnst & 0xff, ieu->arg, wantTrue, usedRandom, randomAcc);
		}
		case Iop_32to16:
		case Iop_64to16: {
			if (cnst & ~0xfffful)
				return !wantTrue;
			return makeEqConst(res, cnst & 0xffff, ieu->arg, wantTrue, usedRandom, randomAcc);
		}
		case Iop_64to32: {
			if (cnst & ~0xfffffffful)
				return !wantTrue;
			return makeEqConst(res, cnst & 0xffffffff, ieu->arg, wantTrue, usedRandom, randomAcc);
		}
		case Iop_1Uto64: {
			if (cnst & ~1ul)
				return !wantTrue;
			return makeEqConst(res, cnst & 1, ieu->arg, wantTrue, usedRandom, randomAcc);
		}
		case Iop_8Sto32: {
			if ( (cnst & 0xffffff80) != 0xffffff80 &&
			     (cnst & 0xffffff80) != 0)
				return !wantTrue;
			return makeEqConst(res, cnst & 0xff, ieu->arg, wantTrue, usedRandom, randomAcc);
		}
		default:
			break;
		}
		break;
	}
	case Iex_Binop: {
		auto *ieb = (IRExprBinop *)what;
		switch (ieb->op) {
		case Iop_Shl64: {
			evalExprRes arg1(evalExpr(res, ieb->arg1, NULL, randomAcc));
			evalExprRes arg2(evalExpr(res, ieb->arg2, NULL, randomAcc));
			unsigned long arg1c, arg2c;
			if (arg1.unpack(&arg1c)) {
				if (arg2.unpack(&arg2c)) {
					unsigned long res = arg1c << arg2c;
					return (res == cnst) == wantTrue;
				} else {
					for (arg2c = 0; arg2c < 63; arg2c++) {
						if ( ((arg1c << arg2c) == cnst) == wantTrue )
							return makeEqConst(res, arg2c, ieb->arg2, true, usedRandom, randomAcc);
					}
					return false;
				}
			} else if (arg2.unpack(&arg2c)) {
				arg1c = cnst >> arg2c;
				if ( (arg1c << arg2c) != cnst)
					return !wantTrue;
				return makeEqConst(res, arg1c, ieb->arg1, wantTrue, usedRandom, randomAcc);
			} else {
				return makeEqConst(res, cnst, ieb->arg1, wantTrue, usedRandom, randomAcc) &&
					makeEqConst(res, 0, ieb->arg2, true, usedRandom, randomAcc);
			}
			abort();
		}
		case Iop_CmpEQ64: {
			evalExprRes arg1(evalExpr(res, ieb->arg1, NULL, randomAcc));
			evalExprRes arg2(evalExpr(res, ieb->arg2, NULL, randomAcc));
			unsigned long arg1c, arg2c;
			if (!cnst)
				wantTrue = !wantTrue;
			if (arg1.unpack(&arg1c)) {
				if (arg2.unpack(&arg2c))
					return (arg1c == arg2c) == wantTrue;
				return makeEqConst(res, arg1c, ieb->arg2, wantTrue, usedRandom, randomAcc);
			} else if (arg2.unpack(&arg2c)) {
				return makeEqConst(res, arg2c, ieb->arg1, wantTrue, usedRandom, randomAcc);
			}
			if (usedRandom) {
				arg1c = genRandomUlong();
				*usedRandom = true;
			} else {
				arg1c = 0;
			}
			if (!makeEqConst(res, arg1c, ieb->arg1, true, usedRandom, randomAcc))
				return false;
			return makeEqConst(res, arg1c, ieb->arg2, wantTrue, usedRandom, randomAcc);
		}
		case Iop_CmpLT64U: {
			evalExprRes arg1(evalExpr(res, ieb->arg1, NULL, randomAcc));
			evalExprRes arg2(evalExpr(res, ieb->arg1, NULL, randomAcc));
			unsigned long arg1c, arg2c;
			if (arg1.unpack(&arg1c)) {
				if (arg2.unpack(&arg2c))
					return ((arg1c < arg2c) == cnst) == wantTrue;
				if (arg1c == ~0ul)
					return (0 == cnst) == wantTrue;
			} else {
				if (arg2.unpack(&arg2c)) {
					if (arg2c == 0)
						return (0 == cnst) == wantTrue;
					return makeEqConst(res, arg2c - 1, ieb->arg1, wantTrue, usedRandom, randomAcc);
				}
				if (usedRandom) {
					do {
						arg1c = genRandomUlong();
					} while (arg1c == ~0ul);
					*usedRandom = true;
				} else {
					arg1c = 0;
				}
				if (!makeEqConst(res, arg1c, ieb->arg1, true, usedRandom, randomAcc))
					return false;
			}
			return makeEqConst(res, arg1c + 1, ieb->arg2, wantTrue, usedRandom, randomAcc);
		}
		default:
			break;
		}
		break;
	}
	default:
		break;
	}
	printf("Can't make %s%s equal constant %lx\n", nameIRExpr(what), wantTrue ? "" : " not", cnst);
	return false;
}

static bool
makeEq(EvalState &res, IRExpr *arg1, IRExpr *arg2, bool wantTrue, bool *usedRandom, EvalState *randomAcc)
{
	if (arg1->tag == Iex_Const)
		return makeEqConst(res, ((IRExprConst *)arg1)->Ico.content.U64, arg2, wantTrue, usedRandom, randomAcc);
	else if (arg2->tag == Iex_Const)
		return makeEqConst(res, ((IRExprConst *)arg2)->Ico.content.U64, arg1, wantTrue, usedRandom, randomAcc);
	else
		return makeEqConst(res, 0, arg1, true, usedRandom, randomAcc) &&
			makeEqConst(res, 0, arg2, wantTrue, usedRandom, randomAcc);

}

static bool
makeTrue(EvalState &res, IRExpr *expr, bool wantTrue, bool *usedRandom, EvalState *randomAcc)
{
	switch (expr->tag) {
	case Iex_Binop: {
		auto *ieb = (IRExprBinop *)expr;
		switch (ieb->op) {
		case Iop_CmpEQ8:
		case Iop_CmpEQ16:
		case Iop_CmpEQ32:
		case Iop_CmpEQ64:
			return makeEq(res, ieb->arg1, ieb->arg2, wantTrue, usedRandom, randomAcc);
			/* Cheat a little bit and ignore overflow here */
		case Iop_CmpLT8U:
		case Iop_CmpLT16U:
		case Iop_CmpLT32U:
		case Iop_CmpLT64U:
			return makeTrue(
				res,
				simplifyIRExpr(
					IRExpr_Binop(
						(IROp)(Iop_CmpEQ8 + ieb->op - Iop_CmpLT8U),
						IRExpr_Binop(
							(IROp)(Iop_Sub8 + ieb->op - Iop_CmpLT8U),
							ieb->arg1,
							mk_const(1, ieb->arg1->type())),
						ieb->arg2),
					AllowableOptimisations::defaultOptimisations),
				wantTrue,
				usedRandom,
				randomAcc);
		default:
			break;
		}
		break;
	}
	case Iex_Unop: {
		auto *ieu = (IRExprUnop *)expr;
		switch (ieu->op) {
		case Iop_64to1:
			return makeEqConst(res, wantTrue, ieu->arg, true, usedRandom, randomAcc);
		case Iop_BadPtr: {
			evalExprRes addr(evalExpr(res, ieu->arg, usedRandom, randomAcc));
			unsigned long addr_c;
			if (!addr.unpack(&addr_c))
				return false;
			evalExprRes err(res.badPtr(addr_c));
			unsigned long already_res;
			if (err.unpack(&already_res))
				return !!already_res == wantTrue;
			if (wantTrue) {
				res.badPtrs.insert(addr_c);
				return true;
			} else {
				if (usedRandom) {
					res.memory[addr_c] = genRandomUlong();
					*usedRandom = true;
					return true;
				} else {
					return false;
				}
			}
			abort();
		}
		default:
			break;
		}
		break;
	}
	case Iex_EntryPoint: {
		auto iee = (IRExprEntryPoint *)expr;
		auto it = res.entryPoints.find(iee->thread);
		if (it != res.entryPoints.end())
			return wantTrue == (it->second == iee->label);
		if (res.nonEntryPoints.count(iee->thread)) {
			if (res.nonEntryPoints[iee->thread].count(iee->label))
				return !wantTrue;
		}
		if (wantTrue)
			res.entryPoints.insert(std::pair<unsigned, CfgLabel>(iee->thread, iee->label));
		else
			res.nonEntryPoints[iee->thread].insert(iee->label);
		return true;
	}
	case Iex_ControlFlow: {
		auto iee = (IRExprControlFlow *)expr;
		std::pair<unsigned, CfgLabel> k(iee->thread, iee->cfg1);
		auto it = res.controlFlow.find(k);
		if (it != res.controlFlow.end())
			return wantTrue == (it->second == iee->cfg2);
		if (res.nonControlFlow.count(k)) {
			if (res.nonControlFlow[k].count(iee->cfg2)) {
				return !wantTrue;
			}
		}
		if (wantTrue) {
			res.controlFlow.insert(k, iee->cfg2);
		} else {
			res.nonControlFlow[k].insert(iee->cfg2);
		}
		return true;
	}

	case Iex_HappensBefore: {
		auto ieh = (IRExprHappensBefore *)expr;
		auto er(res.happensBefore(ieh->before, ieh->after));
		unsigned long erl;
		if (er.unpack(&erl))
			return !!erl == wantTrue;
		if (wantTrue)
			res.hbEdges.push_back(std::pair<MemoryAccessIdentifier, MemoryAccessIdentifier>(ieh->before, ieh->after));
		else
			res.hbEdges.push_back(std::pair<MemoryAccessIdentifier, MemoryAccessIdentifier>(ieh->after, ieh->before));
		return true;
	}
	default:
		break;
	}
	return false;
}

template <typename t> static void
shuffle(std::vector<t> &what)
{
	for (unsigned idx1 = 0; idx1 < what.size(); idx1++) {
		unsigned idx2 = random() % (what.size() - idx1) + idx1;
		t tmp(what[idx1]);
		what[idx1] = what[idx2];
		what[idx2] = tmp;
	}
}
	
static bool
generateConcreteSatisfier(EvalState &res, const satisfier &abstract_sat, bool *usedRandom, EvalState *randomAcc)
{
	std::vector<IRExpr *> truePrimaries;
	std::vector<IRExpr *> falsePrimaries;
	std::vector<IRExpr *> trueBadPtrs;
	std::vector<IRExpr *> falseBadPtrs;
	for (auto it = abstract_sat.trueBooleans.begin(); it != abstract_sat.trueBooleans.end(); it++) {
		IRExpr *e = *it;
		if (e->tag == Iex_Unop &&
		    ((IRExprUnop *)e)->op == Iop_BadPtr)
			trueBadPtrs.push_back(e);
		else
			truePrimaries.push_back(e);
	}
	for (auto it = abstract_sat.falseBooleans.begin(); it != abstract_sat.falseBooleans.end(); it++) {
		IRExpr *e = *it;
		if (e->tag == Iex_Unop &&
		    ((IRExprUnop *)e)->op == Iop_BadPtr)
			falseBadPtrs.push_back(e);
		else
			falsePrimaries.push_back(e);
	}

	/* If we're allowed to randomise, take the expressions in
	 * random order. */
	if (usedRandom && (truePrimaries.size() > 1 || falsePrimaries.size() > 1 ||
			   trueBadPtrs.size() > 1 || falseBadPtrs.size() > 1)) {
		*usedRandom = true;
		shuffle(truePrimaries);
		shuffle(falsePrimaries);
		shuffle(trueBadPtrs);
		shuffle(falseBadPtrs);
	}

	/* True primaries tend to be easier to deal with, so do them
	 * first. */
	for (auto it = truePrimaries.begin(); it != truePrimaries.end(); it++) {
		if (!makeTrue(res, *it, true, usedRandom, randomAcc))
			return false;
	}
	for (auto it = falsePrimaries.begin(); it != falsePrimaries.end(); it++) {
		if (!makeTrue(res, *it, false, usedRandom, randomAcc))
			return false;
	}
	/* BadPtr expressions are particularly tricky, so do them
	 * last. */
	for (auto it = trueBadPtrs.begin(); it != trueBadPtrs.end(); it++) {
		if (!makeTrue(res, *it, true, usedRandom, randomAcc))
			return false;
	}
	for (auto it = falseBadPtrs.begin(); it != falseBadPtrs.end(); it++) {
		if (!makeTrue(res, *it, false, usedRandom, randomAcc))
			return false;
	}
	return true;
}

static bool
addSatisfier(std::vector<EvalState> &initialCtxts, IRExpr *a)
{
	bool done = false;
	for (auto sat = sat_enumerator(a, AllowableOptimisations::defaultOptimisations);
	     !done && !sat.finished();
	     sat.advance()) {
		EvalState ctxt;
		bool random = false;
		bool res;
		res = generateConcreteSatisfier(ctxt, sat.get(), &random, NULL);
		if (res) {
			if (debug_gen_contexts) {
				printf("New context:\n");
				ctxt.prettyPrint(stdout);
			}
			initialCtxts.push_back(ctxt);
			done = true;
		} else if (random) {
			for (int i = 0; !done && i < 100; i++) {
				random = false;
				ctxt.clear();
				res = generateConcreteSatisfier(ctxt, sat.get(), &random, NULL);
				assert(random);
				if (res) {
					if (debug_gen_contexts) {
						printf("New random context:\n");
						ctxt.prettyPrint(stdout);
					}
					initialCtxts.push_back(ctxt);
					done = true;
				}
			}
		}
	}
	return done;
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<Oracle> oracle;
	{
		MachineState *ms = MachineState::readELFExec(argv[1]);
		Thread *thr = ms->findThread(ThreadId(1));
		oracle = new Oracle(ms, thr, argv[2]);
	}
	oracle->loadCallGraph(oracle, argv[3], argv[4], ALLOW_GC);

	VexPtr<OracleInterface> oracleI(oracle);
	SMScopes scopes;
	VexPtr<StateMachine, &ir_heap> machine1(readStateMachine(&scopes, argv[5]));
	VexPtr<MaiMap, &ir_heap> mai1(MaiMap::fromFile(machine1, argv[6]));
	SMScopes scopes2;
	VexPtr<StateMachine, &ir_heap> machine2(readStateMachine(&scopes2, argv[7]));
	machine2 = rewriteMachineCrossScope(machine2, &scopes);

	VexPtr<MaiMap, &ir_heap> mai2(MaiMap::fromFile(machine2, argv[8]));
	std::set<DynAnalysisRip> nonLocalLoads;
	std::map<DynAnalysisRip, IRType> interestingStores;
	AllowableOptimisations opt(
		AllowableOptimisations::fromFile(
			&interestingStores,
			&nonLocalLoads,
			oracle->ms->addressSpace,
			argv[9]));

	GcSet<IRExpr, &ir_heap> constraints;
	AllowableOptimisations opt2(
		AllowableOptimisations::defaultOptimisations.
		setAddressSpace(oracle->ms->addressSpace).
		enableassumePrivateStack());

	/* collectConstraints can take a while, especially on
	   unoptimised machines.  Kill it after a ten minute
	   timeout. */
	{
		TimeoutTimer timeoutTimer;
		timeoutTimer.timeoutAfterSeconds(600);
		collectConstraints(&scopes, mai1, machine1, oracleI, opt2, constraints, ALLOW_GC);
	}

	if (TIMEOUT) {
		printf("Timeout!\n");
		return 0;
	}

	/* The rest of of this has no timeout */

	{
		std::set<IRExpr *> constraints2;
		for (auto it = constraints.begin(); it != constraints.end(); it++) {
			IRExpr *e = simplifyIRExpr(*it, AllowableOptimisations::defaultOptimisations);
			if (e->tag != Iex_Const) {
				constraints2.insert(e);
			}
		}
		constraints = constraints2;
	}

	printf("Constraints:\n");
	for (auto it = constraints.begin(); it != constraints.end(); it++)
		printf("\t%s\n", nameIRExpr(*it));

	int failed_generate_satisfier = 0;
	int failed_generate_nonsat = 0;
	int satisfier_contexts = 0;
	int non_satisfier_contexts = 0;
	std::vector<EvalState> initialCtxts;
	for (auto it = constraints.begin(); it != constraints.end(); it++) {
		/* Find some concrete configuration which satisfies
		 * this constraint. */

		if (debug_gen_contexts) {
			printf("Find satisfier for ");
			ppIRExpr(*it, stdout);
			printf("\n");
		}

		/* First check whether we've already got one. */
		bool have_satisfying = false;
		for (auto it2 = initialCtxts.begin();
		     !have_satisfying && it2 != initialCtxts.end();
		     it2++) {
			auto res = evalExpr(*it2, *it, NULL, NULL);
			unsigned long v;
			if (res.unpack(&v) && v) {
				have_satisfying = true;
				if (debug_gen_contexts) {
					ppIRExpr(*it, stdout);
					printf(" is satisfied by:\n");
					it2->prettyPrint(stdout);
				}
			}
		}

		if (have_satisfying) {
			/* No point in doing anything more with this
			 * condition. */
			continue;
		}

		IRExpr *a = *it;
		if (!addSatisfier(initialCtxts, a)) {
			fprintf(stderr, "WARNING: Cannot generate concrete satisfier for %s\n", nameIRExpr(a));
			failed_generate_satisfier++;
		} else {
			satisfier_contexts++;
			if (satisfier_contexts % 100 == 0)
				printf("Generated %d/%zd concrete satisfiers (%d failed)\n",
				       satisfier_contexts + failed_generate_satisfier,
				       constraints.size(),
				       failed_generate_satisfier);
		}
		LibVEX_maybe_gc(ALLOW_GC);
	}

	/* Should also try to make all of the conditions be
	 * non-satisfied at least once. */
	for (auto it = constraints.begin(); it != constraints.end(); it++) {
		IRExpr *a = simplifyIRExpr(IRExpr_Unop(Iop_Not1, *it), AllowableOptimisations::defaultOptimisations);

		bool found_one = false;
		for (auto it2 = initialCtxts.begin();
		     !found_one && it2 != initialCtxts.end();
		     it2++) {
			auto res = evalExpr(*it2, a, NULL, NULL);
			unsigned long v;
			if (res.unpack(&v) && v) {
				if (debug_gen_contexts) {
					ppIRExpr(*it, stdout);
					printf(" is not satisfied by:\n");
					it2->prettyPrint(stdout);

				}
				found_one = true;
			}
		}

		if (found_one)
			continue;

		printf("Need explicit non-satisfier for %s...\n", nameIRExpr(a));
		if (!addSatisfier(initialCtxts, a)) {
			fprintf(stderr, "WARNING: Cannot generate concrete non-satisfier for %s\n", nameIRExpr(a));
			failed_generate_nonsat++;
		} else {
			non_satisfier_contexts++;
		}
		LibVEX_maybe_gc(ALLOW_GC);
	}

	printf("Concrete conditions to consider:\n");
	for (auto it = initialCtxts.begin(); it != initialCtxts.end(); it++) {
		if (it != initialCtxts.begin())
			printf("-----------\n");
		it->prettyPrint(stdout);
	}

	int nr_crash = 0;
	int nr_nocrash = 0;
	int nr_escape = 0;
	int nr_demote_survival = 0;

	int nr_failed = 0;
	int nr_m1_unreached= 0;
	int cntr = 0;
	bool printedMachines = false;
	std::map<const StateMachineState *, int> labels1;
	std::map<const StateMachineState *, int> labels2;
	for (auto it = initialCtxts.begin(); it != initialCtxts.end(); it++) {
		EvalCtxt ctxt1(*it);
		EvalState extended_init_ctxt(*it);
		EvalArgs eval1args;
		eval1args.randomAcc = &extended_init_ctxt;
		eval1args.oracle = oracle;
		eval1args.decode = mai1;
		eval1args.opt = &opt;
		evalRes machine1res = ctxt1.eval(machine1->root, ALLOW_GC, eval1args);
		int i;
		for (i = 0; i < 100 && machine1res == evalRes::unreached(); i++) {
			ctxt1.reset(*it);
			extended_init_ctxt = *it;
			machine1res = ctxt1.eval(machine1->root, ALLOW_GC, eval1args);
		}
		if (machine1res == evalRes::unreached()) {
			nr_m1_unreached++;
			continue;
		}
		EvalCtxt ctxt2(extended_init_ctxt);
		EvalArgs eval2args;
		eval2args.randomAcc = NULL;
		eval2args.oracle = oracle;
		eval2args.decode = mai2;
		eval2args.opt = &opt;
		evalRes machine2res = ctxt2.eval(machine2->root, ALLOW_GC, eval2args);
		for (i = 0; i < 100 && machine2res == evalRes::unreached(); i++) {
			ctxt2.reset(extended_init_ctxt);
			machine2res = ctxt2.eval(machine2->root, ALLOW_GC, eval2args);
		}

		bool failed = machine1res != machine2res;
		if (failed &&
		    machine1res == evalRes::survive() &&
		    machine2res == evalRes::unreached() &&
		    opt.noLocalSurvival()) {
			/* If noLocalSurvival is set then you're
			   allowed to convert <survive> into
			   <unreached> */
			failed = false;
			nr_demote_survival++;
		}

		if (failed) {
			if (!printedMachines) {
				printf("Machine1:\n");
				printStateMachine(machine1, stdout, labels1);
				printf("Machine2:\n");
				printStateMachine(machine2, stdout, labels2);
				printedMachines = true;
			}
			printf("Failed: machine1res(%s) != machine2res(%s)\n", machine1res.name(), machine2res.name());
			printf("Machine 1 log:\n");
			ctxt1.printLog(stdout, labels1);
			printf("Machine 2 log:\n");
			ctxt2.printLog(stdout, labels2);
			printf("Initial state:\n");
			extended_init_ctxt.prettyPrint(stdout);

			printf("Context %zd/%zd\n", it - initialCtxts.begin(),
			       initialCtxts.size());

			dbg_break("Failed");

			nr_failed++;
		} else {
			if (machine1res == evalRes::unreached())
				nr_escape++;
			else if (machine1res == evalRes::crash())
				nr_crash++;
			else if (machine1res == evalRes::survive())
				nr_nocrash++;
			else
				abort();
		}
		cntr++;
	}
	printf("%zd constraints generated, %d contexts total (%d sat, %d non-sat), %d failures to generate contexts (%d sat, %d non-sat)\n",
	       constraints.size(),
	       satisfier_contexts + non_satisfier_contexts,
	       satisfier_contexts,
	       non_satisfier_contexts,
	       failed_generate_satisfier + failed_generate_nonsat,
	       failed_generate_satisfier,
	       failed_generate_nonsat);
	printf("%d survival states demoted to unreached, %d machine 1 unreachable\n", nr_demote_survival, nr_m1_unreached);
	if (nr_failed != 0) {
		printf("Result: failed %d/%d\n", nr_failed, cntr);
		return 1;
	} else {
		printf("Result: passed %d (%d escape, %d survive, %d crash)\n",
		       cntr, nr_escape, nr_nocrash, nr_crash);
		return 0;
	}
}

