/* Another way of comparing two state machines to see if they're
   equivalent.  The idea here is that we use the symbolic execution
   engine to reduce each machine down to a single smrbdd and then
   check whether the two smrbdds are equivalent. */
#include "sli.h"
#include "bdd.hpp"
#include "stacked_cdf.hpp"
#include "oracle.hpp"
#include "alloc_mai.hpp"
#include "allowable_optimisations.hpp"
#include "eval_state_machine.hpp"
#include "timers.hpp"

#include "bdd_tmpl.cpp"

class TimeoutTimer : public Timer {
public:
	void fired() {
		_timed_out = true;
	}
};

class deltasmr {
	StateMachineRes res1;
	StateMachineRes res2;
public:
	bool isSafe() const {
		return res1 == res2 || res1 == smr_unreached;
	}
	void sanity_check() const {
		sanity_check_smr(res1);
		sanity_check_smr(res2);
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "%s -> %s", nameSmr(res1), nameSmr(res2));
	}
	deltasmr(StateMachineRes _res1, StateMachineRes _res2)
		: res1(_res1), res2(_res2)
	{}
	bool operator <(const deltasmr &a) const {
		if (res1 < a.res1) {
			return true;
		} else if (a.res1 < res1) {
			return false;
		} else {
			return res2 < a.res2;
		}
	}
};

class deltasmrbdd : public const_bdd<deltasmr, deltasmrbdd> {
	friend class const_bdd_scope<deltasmrbdd>;
	friend class bdd_scope<deltasmrbdd>;
	friend class _bdd<deltasmr, deltasmrbdd>;

	void _sanity_check(deltasmr a) const { a.sanity_check(); }
	void _prettyPrint(FILE *f, deltasmr a) const {
		a.prettyPrint(f);
	}
	deltasmrbdd(bdd_rank rank, IRExpr *cond, deltasmrbdd *trueB, deltasmrbdd *falseB)
		: const_bdd<deltasmr, deltasmrbdd>(rank, cond, trueB, falseB)
	{}
	deltasmrbdd(const deltasmr &b)
		: const_bdd<deltasmr, deltasmrbdd>(b)
	{}
public:
	static deltasmrbdd *diff(scope *scope, smrbdd *a, smrbdd *b);
};

class dsmr_zip {
	smrbdd *a;
	smrbdd *b;
	deltasmrbdd::scope *scp;
public:
	dsmr_zip(smrbdd *_a, smrbdd *_b, deltasmrbdd::scope *_scp)
		: a(_a), b(_b), scp(_scp)
	{}
	void move(dsmr_zip &o) {
		o = *this;
	}
	bool isLeaf() const {
		return a->isLeaf() && b->isLeaf();
	}
	const bdd_rank &bestCond(IRExpr **cond) const {
		assert(!(a->isLeaf() && b->isLeaf()));
		bool takeA =
			!a->isLeaf() &&
			(b->isLeaf() ||
			 a->internal().rank < b->internal().rank);
		if (takeA) {
			*cond = a->internal().condition;
			return a->internal().rank;
		} else {
			*cond = b->internal().condition;
			return b->internal().rank;
		}
	}
	deltasmrbdd *leafzip() const {
		assert(a->isLeaf() && b->isLeaf());
		return scp->cnst(deltasmr(a->leaf(), b->leaf()));
	}
	dsmr_zip trueSucc(const bdd_rank &cond) const {
		return dsmr_zip(a->trueBranch(cond),
				b->trueBranch(cond),
				scp);
	}
	dsmr_zip falseSucc(const bdd_rank &cond) const {
		return dsmr_zip(a->falseBranch(cond),
				b->falseBranch(cond),
				scp);
	}

	static deltasmrbdd *fixup(deltasmrbdd *what) {
		return what;
	}
	static bool badPtr(deltasmrbdd *) {
		return false;
	}

	bool operator<(const dsmr_zip &o) const {
		assert(scp == o.scp);
		if (a < o.a) {
			return true;
		} else if (o.a < a) {
			return false;
		} else {
			return b < o.b;
		}
	}
};

deltasmrbdd *
deltasmrbdd::diff(scope *scp,
		  smrbdd *smr1,
		  smrbdd *smr2)
{
	dsmr_zip f(smr1, smr2, scp);
	return zip(scp, f);
}

static const char *
strip_suffix(const char *what, const char *suffix)
{
	size_t what_len = strlen(what);
	size_t suffix_len = strlen(suffix);
	if (what_len < suffix_len ||
	    memcmp(what + what_len - suffix_len, suffix, suffix_len)) {
		return what;
	}
	char *res = (char *)malloc(what_len - suffix_len + 1);
	memcpy(res, what, what_len - suffix_len);
	res[what_len-suffix_len] = 0;
	return res;
}

static bbdd *
err_if(bbdd::scope *scp, deltasmrbdd *delta, sane_map<deltasmrbdd *, bbdd *> &memo)
{
	auto it_did_insert = memo.insert(delta, (bbdd *)0xf001);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second;
	}
	if (delta->isLeaf()) {
		it->second = scp->cnst(!delta->leaf().isSafe());
	} else {
		it->second = scp->node(
			delta->internal().condition,
			delta->internal().rank,
			err_if(scp, delta->internal().trueBranch, memo),
			err_if(scp, delta->internal().falseBranch, memo));
	}
	return it->second;
}

static bbdd *
err_if(bbdd::scope *scp, deltasmrbdd *delta)
{
	sane_map<deltasmrbdd *, bbdd *> memo;
	return err_if(scp, delta, memo);
}

int
main(int argc, char *argv[])
{
	const char *bin = argv[1];
	const char *data = argv[2];

	init_sli();

	bdd_use_dereferences = false;

	const char *base = strip_suffix(bin, ".exe");
	
	VexPtr<Oracle> oracle;
	{
		MachineState *ms = MachineState::readELFExec(bin);
		Thread *thr = ms->findThread(ThreadId(1));
		oracle = new Oracle(ms, thr, vex_asprintf("%s.types.canon", base));
	}
	oracle->loadCallGraph(oracle,
			      my_asprintf("%s.bcg", base),
			      my_asprintf("%s.db", base),
			      ALLOW_GC);

	VexPtr<OracleInterface> oracleI(oracle);
	SMScopes scopes;
	if (!scopes.read(vex_asprintf("%s/pre_scopes", data))) {
		errx(1, "reading %s/pre_scopes", data);
	}
	VexPtr<StateMachine, &ir_heap> machine1(readStateMachine(&scopes, vex_asprintf("%s/pre_machine", data)));
	VexPtr<MaiMap, &ir_heap> mai1(MaiMap::fromFile(machine1, vex_asprintf("%s/pre_mai", data)));

	SMScopes scopes2;
	if (!scopes2.read(vex_asprintf("%s/post_scopes", data))) {
		errx(1, "reading %s/post_scopes", data);
	}
	VexPtr<StateMachine, &ir_heap> machine2(readStateMachine(&scopes2, vex_asprintf("%s/post_machine", data)));
	machine2 = rewriteMachineCrossScope(machine2, &scopes);
	VexPtr<MaiMap, &ir_heap> mai2(MaiMap::fromFile(machine2, vex_asprintf("%s/post_mai", data)));

	std::set<DynAnalysisRip> nonLocalLoads;
	sane_map<DynAnalysisRip, IRType> interestingStores;
	AllowableOptimisations opt(
		AllowableOptimisations::fromFile(
			&interestingStores,
			&nonLocalLoads,
			oracle->ms->addressSpace,
			vex_asprintf("%s/opt", data)));

	VexPtr<bbdd, &ir_heap> truth(scopes.bools.cnst(true));

	TimeoutTimer timeoutTimer;
	timeoutTimer.nextDue = now() + 60;
	timeoutTimer.schedule();

	VexPtr<smrbdd, &ir_heap> smr1(compileMachineToBdd(&scopes,
							  mai1,
							  machine1,
							  oracleI,
							  opt,
							  ALLOW_GC));
	if (TIMEOUT) {
		return 0;
	}
	VexPtr<smrbdd, &ir_heap> smr2(compileMachineToBdd(&scopes,
							  mai2,
							  machine2,
							  oracleI,
							  opt,
							  ALLOW_GC));
	if (TIMEOUT) {
		return 0;
	}
	if (smr1 == smr2) {
		printf("Pass.\n");
		return 0;
	}

	smr1 = simplifyBDD<smrbdd, smrbdd::scope>(&scopes.smrs,
						  &scopes.bools,
						  smr1,
						  false,
						  opt);
	if (TIMEOUT) {
		return 0;
	}
	smr2 = simplifyBDD<smrbdd, smrbdd::scope>(&scopes.smrs,
						  &scopes.bools,
						  smr2,
						  false,
						  opt);
	if (TIMEOUT) {
		return 0;
	}
	if (smr1 == smr2) {
		printf("Pass.\n");
		return 0;
	}

	deltasmrbdd::scope dscope(&scopes.ordering);
	deltasmrbdd *delta = deltasmrbdd::diff(&dscope, smr1, smr2);

	bbdd *errorIf = err_if(&scopes.bools, delta);
	if (TIMEOUT) {
		return 0;
	}
	if (errorIf == scopes.bools.cnst(false)) {
		printf("Pass.\n");
		return 0;
	}

	printf("smr1:\n");
	smr1->prettyPrint(stdout);
	printf("\nsmr2:\n");
	smr2->prettyPrint(stdout);
	printf("\nDelta:\n");
	delta->prettyPrint(stdout);

	return 1;
}
