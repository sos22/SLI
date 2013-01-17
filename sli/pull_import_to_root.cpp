#include "sli.h"
#include "offline_analysis.hpp"

namespace _pullImportsToRoot {

struct importT {
	unsigned const thread;
	unsigned const offset;
	PointerAliasingSet const aliasSet;
	importT(unsigned _thread, unsigned _offset, const PointerAliasingSet &_aliasSet)
		: thread(_thread), offset(_offset), aliasSet(_aliasSet)
	{}
	bool operator<(const importT &o) const {
		if (thread < o.thread)
			return true;
		if (thread > o.thread)
			return false;
		if (offset < o.offset)
			return true;
		if (offset > o.offset)
			return false;
		return aliasSet < o.aliasSet;
	}
};

static void
findNeededImports(const StateMachineState *sm,
		  std::set<std::pair<const StateMachineState *, bool> > &visited,
		  std::map<importT, std::set<threadAndRegister> > &out,
		  bool *anyAtNonRoot,
		  bool thisAtNonRoot)
{
	if (!visited.insert(std::pair<const StateMachineState *, bool>(sm, thisAtNonRoot)).second)
		return;
	switch (sm->type) {
	case StateMachineState::Bifurcate:
		findNeededImports( ((const StateMachineBifurcate *)sm)->trueTarget,
				   visited,
				   out,
				   anyAtNonRoot,
				   true );
		findNeededImports( ((const StateMachineBifurcate *)sm)->falseTarget,
				   visited,
				   out,
				   anyAtNonRoot,
				   true );
		return;
	case StateMachineState::Terminal:
		return;
	case StateMachineState::SideEffecting: {
		const StateMachineSideEffecting *sme = (const StateMachineSideEffecting *)sm;
		const StateMachineSideEffectImportRegister *import;
		if (sme->sideEffect && sme->sideEffect->type == StateMachineSideEffect::ImportRegister)
			import = (const StateMachineSideEffectImportRegister *)sme->sideEffect;
		else
			import = NULL;
		if (import) {
			*anyAtNonRoot |= thisAtNonRoot;
			out[importT(import->tid, import->vex_offset, import->set)].insert(import->reg);
		} else {
			thisAtNonRoot = true;
		}
		findNeededImports(sme->target, visited, out, anyAtNonRoot, thisAtNonRoot);
		return;
	}
	}
	abort();
}

static StateMachine *
pullImportsToRoot(SMScopes *scopes, StateMachine *sm, bool *progress)
{
	bool atNonRoot;
	std::map<importT, std::set<threadAndRegister> > neededImports;

	/* Start by finding all imports which aren't already at the
	 * root. */
	atNonRoot = false;
	std::set<std::pair<const StateMachineState *, bool> > visited;
	findNeededImports(sm->root, visited, neededImports, &atNonRoot, false);

	if (!atNonRoot)
		return sm;

	*progress = true;

	StateMachineState *newRoot = sm->root;
	while (newRoot->type == StateMachineState::SideEffecting &&
	       ((StateMachineSideEffecting *)newRoot)->sideEffect &&
	       ((StateMachineSideEffecting *)newRoot)->sideEffect->type == StateMachineSideEffect::ImportRegister) {
		newRoot = ((StateMachineSideEffecting *)newRoot)->target;
	}

	/* Purge any existing imports */
	std::set<StateMachineSideEffecting *> se;
	enumStates(newRoot, &se);
	for (auto it = se.begin(); it != se.end(); it++) {
		if ( (*it)->sideEffect && (*it)->sideEffect->type == StateMachineSideEffect::ImportRegister ) {
			(*it)->sideEffect = NULL;
		}
	}

	/* Emit what we need. */
	for (auto it = neededImports.begin();
	     it != neededImports.end();
	     it++) {
		const importT &imp(it->first);
		const std::set<threadAndRegister> &neededRegs(it->second);
		assert(!neededRegs.empty());
		auto it2 = neededRegs.begin();
		auto endIt = neededRegs.end();
		endIt--;
		const threadAndRegister &canonReg(*endIt);
		auto next = it2;
		next++;
		while (next != neededRegs.end()) {
			newRoot = new StateMachineSideEffecting(
				VexRip(),
				new StateMachineSideEffectCopy(
					*it2,
					exprbdd::var(
						&scopes->exprs,
						&scopes->bools,
						IRExpr_Get(canonReg, Ity_I64))),
				newRoot);
			it2 = next;
			next++;
		}

		newRoot = new StateMachineSideEffecting(
			VexRip(),
			new StateMachineSideEffectImportRegister(
				*it2,
				imp.thread,
				imp.offset,
				imp.aliasSet),
			newRoot);
	}

	sm->root = newRoot;
	return sm;
}

}

/* Rewrite @sm so that all of the ImportRegister side-effects are at
   the root of the machine.  This is always valid for an SSA machine,
   and can sometimes make some other optimisations a bit easier. */
StateMachine *
pullImportsToRoot(SMScopes *scopes, StateMachine *sm, bool *progress)
{
	return _pullImportsToRoot::pullImportsToRoot(scopes, sm, progress);
}
