#include "sli.h"
#include "MachineAliasingTable.hpp"

Oracle::RegisterAliasingConfiguration
MachineAliasingTable::getConfig(StateMachineState *s)
{
	auto it = configs.find(s);
	if (it == configs.end())
		return Oracle::RegisterAliasingConfiguration();
	else
		return it->second;
}

Oracle::ThreadRegisterAliasingConfiguration
MachineAliasingTable::maximalThreadConfig()
{
	Oracle::ThreadRegisterAliasingConfiguration c;
	c.stackInStack = true;
	c.stackInMemory = true;
	for (int i = 0; i < Oracle::NR_REGS; i++)
		c.v[i] = PointerAliasingSet::nothing;
	c.v[OFFSET_amd64_RSP / 8] = PointerAliasingSet::stackPointer;
	return c;
}

void
MachineAliasingTable::setRegister(Oracle::RegisterAliasingConfiguration &config,
				  const threadAndRegister &tr,
				  const PointerAliasingSet &val)
{
	if (tr.asReg() >= Oracle::NR_REGS * 8)
		return;
	if (tr.asReg() == OFFSET_amd64_RSP)
		return;
	for (auto it = config.content.begin();
	     it != config.content.end();
	     it++) {
		if (it->first == tr.tid()) {
			it->second.v[tr.asReg() / 8] = val;
			return;
		}
	}

	Oracle::ThreadRegisterAliasingConfiguration c = maximalThreadConfig();
	c.v[tr.asReg() / 8] = val;
	config.content.push_back(std::pair<unsigned, Oracle::ThreadRegisterAliasingConfiguration>(tr.tid(), c));
}

bool
MachineAliasingTable::updateStateConfig(StateMachineState *s,
					const Oracle::RegisterAliasingConfiguration &newConfig)
{
	auto it_did_insert = configs.insert(std::pair<StateMachineState *, Oracle::RegisterAliasingConfiguration>(s, newConfig));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		return true;
	bool res = false;
	Oracle::RegisterAliasingConfiguration &oldConfig(it->second);
	for (auto newConfigIt = newConfig.content.begin();
	     newConfigIt != newConfig.content.end();
	     newConfigIt++) {
		unsigned tid = newConfigIt->first;
		const Oracle::ThreadRegisterAliasingConfiguration &newConfigElem(newConfigIt->second);
		bool done = false;
		for (auto it = oldConfig.content.begin();
		     !done && it != oldConfig.content.end();
		     it++) {
			if (it->first == tid) {
				if (newConfigElem.stackInStack &&
				    !it->second.stackInStack) {
					it->second.stackInStack = true;
					res = true;
				}
				if (newConfigElem.stackInMemory &&
				    !it->second.stackInMemory) {
					it->second.stackInMemory = true;
					res = true;
				}
				for (int i = 0; i < Oracle::NR_REGS; i++) {
					if (it->second.v[i] |= newConfigElem.v[i])
						res = true;
				}
				done = true;
			}
		}
		if (!done) {
			oldConfig.content.push_back(*newConfigIt);
			res = true;
		}
	}
	return res;
}

void
MachineAliasingTable::initialise(StateMachine *sm)
{
	/* Queue of states whose input configuration has changed. */
	std::queue<StateMachineState *> needsUpdate;
	needsUpdate.push(sm->root);
	while (!needsUpdate.empty()) {
		StateMachineState *s = needsUpdate.front();
		needsUpdate.pop();

		Oracle::RegisterAliasingConfiguration exitConfig;
		exitConfig = getConfig(s);
		StateMachineSideEffect *se = s->getSideEffect();
		if (se) {
			switch (se->type) {
			case StateMachineSideEffect::PointerAliasing: {
				auto sl = (StateMachineSideEffectPointerAliasing *)se;
				setRegister(exitConfig, sl->reg, sl->set);
				break;
			}

				/* This bit of alias analysis only
				   cares about generation -1, so
				   side-effects whose only effect is
				   to modify something which isn't
				   generation -1 are irrelevant. */
			case StateMachineSideEffect::Load:
			case StateMachineSideEffect::Copy:
			case StateMachineSideEffect::Phi:

				/* Here, the current function means
				   the function we were in at the
				   start of the machine, so moving to
				   a different function doesn't do
				   anything. */
			case StateMachineSideEffect::StartFunction:
			case StateMachineSideEffect::EndFunction:
			case StateMachineSideEffect::StackLayout:

			case StateMachineSideEffect::Store:
			case StateMachineSideEffect::Unreached:
			case StateMachineSideEffect::AssertFalse:
			case StateMachineSideEffect::StartAtomic:
			case StateMachineSideEffect::EndAtomic:
				break;
			}
		}

		std::vector<StateMachineState *> succ;
		s->targets(succ);
		for (auto it = succ.begin(); it != succ.end(); it++) {
			if (updateStateConfig(*it, exitConfig))
				needsUpdate.push(*it);
		}
	}
}

bool
MachineAliasingTable::ptrsMightAlias(StateMachineState *where,
				     exprbdd *ptr1,
				     exprbdd *ptr2,
				     const IRExprOptimisations &opt) const
{
	auto it = configs.find(where);
	if (it == configs.end())
		return true;
	return it->second.ptrsMightAlias(ptr1, ptr2, opt);
}

bool
MachineAliasingTable::ptrsMightAlias(StateMachineState *where1,
				     exprbdd *ptr1,
				     StateMachineState *where2,
				     exprbdd *ptr2,
				     const IRExprOptimisations &opt) const
{
	auto it1 = configs.find(where1);
	auto it2 = configs.find(where2);
	if (it1 == configs.end() || it2 == configs.end())
		return true;
	Oracle::RegisterAliasingConfiguration config(it1->second);
	config |= it2->second;
	return config.ptrsMightAlias(ptr1, ptr2, opt);
}

bool
MachineAliasingTable::findConfig(StateMachineState *sms, Oracle::RegisterAliasingConfiguration *rac) const
{
	auto it = configs.find(sms);
	if (it == configs.end())
		return false;
	*rac = it->second;
	return true;
}
