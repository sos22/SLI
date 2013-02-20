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

#include "bdd_tmpl.cpp"

class deltasmr {
	StateMachineRes res1;
	StateMachineRes res2;
public:
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
	std::set<DynAnalysisRip> interestingStores;
	AllowableOptimisations opt(
		AllowableOptimisations::fromFile(
			&interestingStores,
			&nonLocalLoads,
			oracle->ms->addressSpace,
			argv[9]));

	VexPtr<bbdd, &ir_heap> truth(scopes.bools.cnst(true));
	VexPtr<smrbdd, &ir_heap> smr1(enumEvalPaths(&scopes,
						    mai1,
						    machine1,
						    truth,
						    oracleI,
						    opt,
						    smr_unreached,
						    ALLOW_GC));
	VexPtr<smrbdd, &ir_heap> smr2(enumEvalPaths(&scopes,
						    mai2,
						    machine2,
						    truth,
						    oracleI,
						    opt,
						    smr_unreached,
						    ALLOW_GC));
	if (smr1 == smr2) {
		printf("Pass.\n");
		return 0;
	}

	smr1 = simplifyBDD<smrbdd, smrbdd::scope>(&scopes.smrs,
						  &scopes.bools,
						  smr1,
						  false,
						  opt);
	smr2 = simplifyBDD<smrbdd, smrbdd::scope>(&scopes.smrs,
						  &scopes.bools,
						  smr2,
						  false,
						  opt);
	if (smr1 == smr2) {
		printf("Pass.\n");
		return 0;
	}

	deltasmrbdd::scope dscope(&scopes.ordering);
	deltasmrbdd *delta = deltasmrbdd::diff(&dscope, smr1, smr2);

	printf("Delta:\n");
	delta->prettyPrint(stdout);

	return 1;
}
