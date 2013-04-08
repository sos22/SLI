#ifndef PATCH_STRATEGY_HPP__
#define PATCH_STRATEGY_HPP__

class Oracle;
class crashEnforcementRoots;
class CrashCfg;

void buildPatchStrategy(crashEnforcementRoots &, CrashCfg &, Oracle *oracle,
			std::set<unsigned long> &patchPoints,
			std::set<unsigned long> &interpretInstrs);

#endif /* !PATCH_STRATEGY_HPP__ */
