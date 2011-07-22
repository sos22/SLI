#include <stdio.h>

#include "sli.h"
#include "state_machine.hpp"
#include "pickle.hpp"

typedef std::pair<StateMachineState *, StateMachineState *> st_pair_t;
typedef std::pair<StateMachineEdge *, StateMachineEdge *> st_edge_pair_t;

/* Note that this assumes that bisimilarity reduction, and all the
   other usual optimisations, have already been run! */
static bool stateMachinesBisimilar(StateMachineState *a, StateMachineState *b,
				   std::set<st_edge_pair_t> &bisimilarEdges,
				   std::set<st_pair_t> &bisimilarStates,
				   const AllowableOptimisations &opt);
static bool
stateMachineEdgesBisimilar(StateMachineEdge *a,
			   StateMachineEdge *b,
			   std::set<st_edge_pair_t> &bisimilarEdges,
			   std::set<st_pair_t> &bisimilarStates,
			   const AllowableOptimisations &opt)
{
	if (bisimilarEdges.count(st_edge_pair_t(a, b)))
		return true;
	bisimilarEdges.insert(st_edge_pair_t(a, b));
	if (a->sideEffects.size() != b->sideEffects.size())
		return false;
	for (unsigned x = 0; x < a->sideEffects.size(); x++) {
		if (!sideEffectsBisimilar(a->sideEffects[x],
					  b->sideEffects[x],
					  opt))
			return false;
	}
	return stateMachinesBisimilar(a->target, b->target, bisimilarEdges,
				      bisimilarStates, opt);
}
static bool
stateMachinesBisimilar(StateMachineState *a, StateMachineState *b,
		       std::set<st_edge_pair_t> &bisimilarEdges,
		       std::set<st_pair_t> &bisimilarStates,
		       const AllowableOptimisations &opt)
{
	if (bisimilarStates.count(st_pair_t(a, b)))
		return true;
	/* We advance on the assumption that the states *are*
	 * bisimilar, and rely on the fact that bisimilarity has the
	 * right kind of monotonicity for that to actually work. */
	bisimilarStates.insert(st_pair_t(a, b));
	if (dynamic_cast<StateMachineUnreached *>(a))
		return !!dynamic_cast<StateMachineUnreached *>(b);
	if (dynamic_cast<StateMachineCrash *>(a))
		return !!dynamic_cast<StateMachineCrash *>(b);
	if (dynamic_cast<StateMachineNoCrash *>(a))
		return !!dynamic_cast<StateMachineNoCrash *>(b);
	if (StateMachineProxy *smpA = dynamic_cast<StateMachineProxy *>(a)) {
		StateMachineProxy *smpB = dynamic_cast<StateMachineProxy *>(b);
		if (!smpB)
			return false;
		return stateMachineEdgesBisimilar(smpA->target, smpB->target,
						  bisimilarEdges, bisimilarStates,
						  opt);
	}
	if (StateMachineBifurcate *smbA = dynamic_cast<StateMachineBifurcate *>(a)) {
		StateMachineBifurcate *smbB = dynamic_cast<StateMachineBifurcate *>(b);
		if (!smbB)
			return false;
		if (!definitelyEqual(smbA->condition, smbB->condition, opt))
			return false;
		return stateMachineEdgesBisimilar(smbA->trueTarget, smbB->trueTarget,
						  bisimilarEdges, bisimilarStates, opt) &&
		       stateMachineEdgesBisimilar(smbA->falseTarget, smbB->falseTarget,
						  bisimilarEdges, bisimilarStates, opt);
	}
	abort();
}
static bool
stateMachinesBisimilar(StateMachine *a, StateMachine *b)
{
	std::set<st_edge_pair_t> bisimilarEdges;
	std::set<st_pair_t> bisimilarStates;

	return stateMachinesBisimilar(a->root, b->root, bisimilarEdges, bisimilarStates,
				      AllowableOptimisations::defaultOptimisations);
}

int
main(int argc, char *argv[])
{
	init_sli();
	StateMachine *sm1 = unpickleStateMachine(fopen(argv[1], "r"));
	StateMachine *sm2 = unpickleStateMachine(fopen(argv[2], "r"));
	if (stateMachinesBisimilar(sm1, sm2))
		printf("similar\n");
	else
		printf("not similar\n");
	return 0;
}
