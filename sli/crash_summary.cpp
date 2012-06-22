#include <err.h>

#include "sli.h"
#include "inferred_information.hpp"
#include "state_machine.hpp"
#include "oracle.hpp"
#include "allowable_optimisations.hpp"
#include "libvex_parse.h"
#include "offline_analysis.hpp"

void
printCrashSummary(CrashSummary *summary, FILE *f)
{
	fprintf(f, "Load machine:\n");
	printStateMachine(summary->loadMachine, f);

	fprintf(f, "Store machine:\n");
	printStateMachine(summary->storeMachine, f);

	fprintf(f, "Verification condition: ");
	ppIRExpr(summary->verificationCondition, f);
	fprintf(f, "\n");

	if (summary->macroSections.size() == 0) {
		fprintf(f, "No remote macro sections\n");
	} else {
		fprintf(f, "Remote macro sections:\n");
		for (auto it = summary->macroSections.begin();
		     it != summary->macroSections.end();
		     it++) {
			fprintf(f, "\t");
			it->first->prettyPrint(f);
			fprintf(f, " to ");
			if (it->second)
				it->second->prettyPrint(f);
			else
				fprintf(f, "<null>");
			fprintf(f, "\n");
		}
	}
	if (summary->aliasing.size() == 0) {
		fprintf(f, "No aliasing information\n");
	} else {
		fprintf(f, "Aliasing:\n");
		for (auto it = summary->aliasing.begin();
		     it != summary->aliasing.end();
		     it++)
			fprintf(f, "\t%s <-> %s\n", it->first.name(), it->second.name());
	}
}

CrashSummary *
readCrashSummary(int fd)
{
	char *buf = readfile(fd);
	const char *succ;
	CrashSummary *r;
	if (!parseCrashSummary(&r, buf, &succ))
		errx(1, "cannot parse %s as CrashSummary", buf);
	parseThisChar(' ', succ, &succ);
	if (*succ)
		errx(1, "garbage after crash summary: %s", succ);
	free(buf);
	return r;
}

CrashSummary *
readBugReport(const char *name, char **metadata)
{
	int fd = open(name, O_RDONLY);
	if (fd < 0)
		err(1, "opening %s", name);
	char *content = readfile(fd);

	/* First line is metadata */
	char *real_start = strchr(content, '\n');
	if (!real_start)
		errx(1, "%s is empty", name);
	*real_start = 0;
	if (metadata)
		*metadata = strdup(content);

	real_start++;
	/* And use the rest */
	CrashSummary *res;
	if (!parseCrashSummary(&res, real_start, (const char **)&real_start))
		errx(1, "cannot parse %s as crash summary", name);
	free(content);
	close(fd);
	return res;
}

bool
parseCrashSummary(CrashSummary **out, const char *buf,
		  const char **succ)
{
	StateMachine *loadMachine;
	StateMachine *storeMachine;
	IRExpr *verificationCondition;
	if (!parseThisString("Load machine:\n", buf, &buf) ||
	    !parseStateMachine(&loadMachine, buf, &buf) ||
	    !parseThisString("Store machine:\n", buf, &buf) ||
	    !parseStateMachine(&storeMachine, buf, &buf) ||
	    !parseThisString("Verification condition: ", buf, &buf) ||
	    !parseIRExpr(&verificationCondition, buf, &buf) ||
	    !parseThisChar('\n', buf, &buf))
		return false;
	std::vector<CrashSummary::macroSectionT> macros;
	if (parseThisString("No remote macro sections\n", buf, &buf)) {
		/* Nothing */
	} else if (parseThisString("Remote macro sections:\n", buf, &buf)) {
		while (1) {
			StateMachineSideEffect *start, *end;
			const char *m;
			if (!parseThisChar('\t', buf, &m) ||
			    !StateMachineSideEffect::parse(&start, m, &m) ||
			    !parseThisString(" to ", m, &m))
				break;
			if (parseThisString("<null>", m, &m)) {
				end = NULL;
			} else if (!StateMachineSideEffect::parse(&end, m, &m)) {
				break;
			}
			if (!parseThisChar('\n', m, &m))
					break;
			StateMachineSideEffectStore *starts = dynamic_cast<StateMachineSideEffectStore *>(start);
			StateMachineSideEffectStore *ends = dynamic_cast<StateMachineSideEffectStore *>(end);
			if (!starts || (end && !ends) )
				return false;
			buf = m;
			macros.push_back(CrashSummary::macroSectionT(starts, ends));
		}
	} else {
		return false;
	}
	std::vector<std::pair<MemoryAccessIdentifier, MemoryAccessIdentifier> > aliasing;
	if (parseThisString("No aliasing information\n", buf, &buf)) {
		/* Nothing */
	} else if (parseThisString("Aliasing:\n", buf, &buf)) {
		while (1) {
			std::pair<MemoryAccessIdentifier, MemoryAccessIdentifier> thing(
				MemoryAccessIdentifier::uninitialised(),
				MemoryAccessIdentifier::uninitialised())
;
			if (!parseMemoryAccessIdentifier(&thing.first, buf, &buf) ||
			    !parseThisString(" <-> ", buf, &buf) ||
			    !parseMemoryAccessIdentifier(&thing.second, buf, &buf) ||
			    !parseThisChar('\n', buf, &buf))
				break;
			aliasing.push_back(thing);
		}
	} else {
		return false;
	}
	*succ = buf;
	*out = new CrashSummary(loadMachine, storeMachine, verificationCondition, macros, aliasing);
	return true;
}

void
CrashSummary::buildAliasingTable(Oracle *oracle)
{
	std::set<StateMachineSideEffectLoad *> loadLoads;
	std::set<StateMachineSideEffectLoad *> storeLoads;
	std::set<StateMachineSideEffectStore *> loadStores;
	std::set<StateMachineSideEffectStore *> storeStores;
	enumSideEffects(loadMachine, loadLoads);
	enumSideEffects(storeMachine, storeLoads);
	enumSideEffects(loadMachine, loadStores);
	enumSideEffects(storeMachine, storeStores);
	std::set<std::pair<MemoryAccessIdentifier, MemoryAccessIdentifier> > res;

	/* The aliasing table needs to contain complete information for the following
	   interference classes:

	   -- loadLoad vs loadStore
	   -- loadLoad vs storeStore
	   -- loadStore vs storeStore
	   -- storeLoad vs storeStore
	   -- storeStore vs storeStore
	*/
#define do_set(s)							\
	for (auto it2 = s.begin(); it2 != s.end(); it2++) {		\
		if (oracle->memoryAccessesMightAlias(			\
			    AllowableOptimisations::defaultOptimisations, \
			    *it2, *it)) {				\
			if ((*it)->rip < (*it2)->rip)			\
				res.insert(std::pair<MemoryAccessIdentifier, MemoryAccessIdentifier>((*it)->rip, (*it2)->rip)); \
			else if ((*it)->rip != (*it2)->rip)		\
				res.insert(std::pair<MemoryAccessIdentifier, MemoryAccessIdentifier>((*it2)->rip, (*it)->rip)); \
		}							\
	}

	for (auto it = loadStores.begin(); it != loadStores.end(); it++) {
		do_set(loadLoads);
	}
	for (auto it = storeStores.begin(); it != storeStores.end(); it++) {
		do_set(loadLoads);
		do_set(loadStores);
		do_set(storeLoads);
		do_set(storeStores);
	}
#undef do_set
	assert(aliasing.empty());
	aliasing.insert(aliasing.end(), res.begin(), res.end());
}

CrashSummary *
transformCrashSummary(CrashSummary *input, StateMachineTransformer &trans, bool *done_something)
{
	bool b;
	if (!done_something) done_something = &b;
	input->loadMachine = trans.transform(input->loadMachine, done_something);
	input->storeMachine = trans.transform(input->storeMachine, done_something);
	input->verificationCondition = trans.doit(input->verificationCondition, done_something);
	return input;
}
