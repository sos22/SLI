#include <err.h>

#include "sli.h"
#include "inferred_information.hpp"
#include "state_machine.hpp"
#include "oracle.hpp"
#include "allowable_optimisations.hpp"
#include "libvex_parse.h"
#include "offline_analysis.hpp"
#include "intern.hpp"

static void
enumRanks(CrashSummary *summary, std::set<bdd_rank> &ranks)
{
	struct {
		static visit_result visitRank(std::set<bdd_rank> *ctxt, const bdd_rank &what) {
			ctxt->insert(what);
			return visit_continue;
		}
	} foo;
	struct bdd_visitor<std::set<bdd_rank> > visitor = {};
	visitor.rank = foo.visitRank;
	visit_crash_summary<std::set<bdd_rank> >(&ranks, &visitor, summary);
}

void
printCrashSummary(CrashSummary *summary, FILE *f)
{
	std::set<bdd_rank> neededRanks;
	enumRanks(summary, neededRanks);
	fprintf(f, "Scopes:\n");
	summary->scopes->prettyPrint(f, &neededRanks);
	printStateMachinePair("Load Machine:\n",
			      summary->loadMachine,
			      "Store Machine:\n",
			      summary->storeMachine,
			      f);

	fprintf(f, "Inferred assumption: ");
	summary->inferredAssumption->prettyPrint(f);
	fprintf(f, "\n");

	fprintf(f, "Crash condition: ");
	summary->crashCondition->prettyPrint(f);
	fprintf(f, "\n");

	if (summary->aliasing.size() == 0) {
		fprintf(f, "No aliasing information\n");
	} else {
		fprintf(f, "Aliasing:\n");
		for (auto it = summary->aliasing.begin();
		     it != summary->aliasing.end();
		     it++)
			fprintf(f, "\t%s <-> %s\n", it->first.name(), it->second.name());
	}

	summary->mai->print(f);
}

CrashSummary *
readCrashSummary(SMScopes *scopes, int fd)
{
	char *buf = readfile(fd);
	const char *succ;
	CrashSummary *r;
	if (!parseCrashSummary(scopes, &r, buf, &succ))
		errx(1, "cannot parse %s as CrashSummary", buf);
	parseThisChar(' ', succ, &succ);
	if (*succ)
		errx(1, "garbage after crash summary: %s", succ);
	free(buf);
	return r;
}

CrashSummary *
readBugReport(SMScopes *scopes, const char *name, char **metadata)
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
	if (!parseCrashSummary(scopes, &res, real_start, (const char **)&real_start))
		errx(1, "cannot parse %s as crash summary", name);
	free(content);
	close(fd);
	return res;
}

bool
parseCrashSummary(SMScopes *scopes,
		  CrashSummary **out,
		  const char *buf,
		  const char **succ)
{
	StateMachine *loadMachine;
	StateMachine *storeMachine;
	bbdd *inferredAssumption;
	bbdd *crashCondition;
	std::map<CfgLabel, const CFGNode *> labels;
	if (!parseThisString("Scopes:\n", buf, &buf) ||
	    !scopes->parse(buf, &buf) ||
	    !parseThisString("Load Machine:\n", buf, &buf) ||
	    !parseStateMachine(scopes, &loadMachine, buf, &buf, labels) ||
	    !parseThisString("Store Machine:\n", buf, &buf) ||
	    !parseStateMachine(scopes, &storeMachine, buf, &buf, labels) ||
	    !parseThisString("Inferred assumption: ", buf, &buf) ||
	    !bbdd::parse(&scopes->bools, &inferredAssumption, buf, &buf) ||
	    !parseThisString("Crash condition: ", buf, &buf) ||
	    !bbdd::parse(&scopes->bools, &crashCondition, buf, &buf))
		return false;
	if (parseThisString("Remote macro sections:\n", buf, &buf)) {
		/* This is an old version of the format which we no
		 * longer support. */
		return false;
	}

	/* Handle old format */
	parseThisString("No remote macro sections\n", buf, &buf);
	std::vector<CrashSummary::aliasingEntryT> aliasing;
	if (parseThisString("No aliasing information\n", buf, &buf)) {
		/* Nothing */
	} else if (parseThisString("Aliasing:\n", buf, &buf)) {
		while (1) {
			MemoryAccessIdentifier w1(MemoryAccessIdentifier::uninitialised());
			MemoryAccessIdentifier w2(MemoryAccessIdentifier::uninitialised());
			if (!w1.parse(buf, &buf) ||
			    !parseThisString(" <-> ", buf, &buf) ||
			    !w2.parse(buf, &buf) ||
			    !parseThisChar('\n', buf, &buf))
				break;
			aliasing.push_back(CrashSummary::aliasingEntryT(w1, w2));
		}
	} else {
		return false;
	}
	MaiMap *mai = MaiMap::parse(labels, buf, &buf);
	if (!mai)
		return false;
	*succ = buf;
	*out = new CrashSummary(scopes, loadMachine, storeMachine, inferredAssumption, crashCondition, aliasing, mai);
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
	std::set<aliasingEntryT> res;

	/* The aliasing table needs to contain complete information for the following
	   interference classes:

	   -- loadLoad vs loadStore
	   -- loadLoad vs storeStore
	   -- loadStore vs storeStore
	   -- loadStore vs loadStore
	   -- storeLoad vs storeStore
	   -- storeStore vs storeStore

	   If CONFIG_W_ISOLATION is clear, it also contains

	   -- storeLoad vs loadStore
	   -- storeStore vs loadStore
	*/
#define do_set(s)							\
	for (auto it2 = s.begin(); it2 != s.end(); it2++) {		\
		if (oracle->memoryAccessesMightAlias(			\
			    *mai,					\
			    AllowableOptimisations::defaultOptimisations, \
			    *it2, *it)) {				\
			if ((*it)->rip < (*it2)->rip)			\
				res.insert(aliasingEntryT		\
					   ((*it)->rip, (*it2)->rip));	\
			else if ((*it)->rip != (*it2)->rip)		\
				res.insert(aliasingEntryT		\
					   ((*it2)->rip, (*it)->rip));	\
		}							\
	}

	for (auto it = loadStores.begin(); it != loadStores.end(); it++) {
		do_set(loadLoads);
		do_set(loadStores);
		if (!CONFIG_W_ISOLATION) {
			do_set(storeLoads);
			do_set(storeStores);
		}
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
	input->loadMachine = trans.transform(input->scopes, input->loadMachine, done_something);
	input->storeMachine = trans.transform(input->scopes, input->storeMachine, done_something);
	auto ia = trans.transform_bbdd(&input->scopes->bools, input->inferredAssumption);
	if (ia != input->inferredAssumption)
		*done_something = true;
	input->inferredAssumption = ia;

	auto cc = trans.transform_bbdd(&input->scopes->bools, input->crashCondition);
	if (cc != input->crashCondition)
		*done_something = true;
	input->crashCondition = cc;

	return input;
}

CrashSummary *
internCrashSummary(CrashSummary *cs)
{
	internStateMachineTable t;
	cs->loadMachine = internStateMachine(cs->loadMachine, t);
	cs->storeMachine = internStateMachine(cs->storeMachine, t);
	return cs;
}
