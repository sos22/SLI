#include <err.h>

#include "sli.h"
#include "inferred_information.hpp"
#include "state_machine.hpp"
#include "libvex_parse.h"

void
printCrashSummary(CrashSummary *summary, FILE *f)
{
	fprintf(f, "Load machine:\n");
	printStateMachine(summary->loadMachine, f);

	for (std::vector<CrashSummary::StoreMachineData *>::iterator it = summary->storeMachines.begin();
	     it != summary->storeMachines.end();
	     it++) {
		CrashSummary::StoreMachineData *smd = *it;
		fprintf(f, "Store machine:\n");
		printStateMachine(smd->machine, f);
		fprintf(f, "Assumption: ");
		ppIRExpr(smd->assumption, f);
		fprintf(f, "\n");
		if (smd->macroSections.size() == 0) {
			fprintf(f, "No remote macro sections\n");
		} else {
			fprintf(f, "Remote macro sections:\n");
			for (std::vector<CrashSummary::StoreMachineData::macroSectionT>::iterator it2 = 
				     smd->macroSections.begin();
			     it2 != smd->macroSections.end();
			     it2++) {
				fprintf(f, "\t");
				it2->first->prettyPrint(f);
				fprintf(f, " to ");
				if (it2->second)
					it2->second->prettyPrint(f);
				else
					fprintf(f, "<null>");
				fprintf(f, "\n");
			}
		}
	}
}

CrashSummary *
readCrashSummary(int fd)
{
	char *buf = readfile(fd);
	const char *succ;
	char *err;
	CrashSummary *r;
	if (!parseCrashSummary(&r, buf, &succ, &err))
		errx(1, "cannot parse %s as CrashSummary: %s", buf, err);
	parseThisChar(' ', succ, &succ, &err);
	if (*succ)
		errx(1, "garbage after crash summary: %s (%s)", succ, err);
	free(buf);
	return r;
}

bool
parseCrashSummary(CrashSummary **out, const char *buf,
		  const char **succ, char **err)
{
	StateMachine *loadMachine;
	if (!parseThisString("Load machine:\n", buf, &buf, err) ||
	    !parseStateMachine(&loadMachine, buf, &buf, err))
		return false;
	std::vector<CrashSummary::StoreMachineData *> storeMachines;
	while (1) {
		StateMachine *storeMachine;
		IRExpr *assumption;
		if (!parseThisString("Store machine:\n", buf, &buf, err) ||
		    !parseStateMachine(&storeMachine, buf, &buf, err) ||
		    !parseThisString("Assumption: ", buf, &buf, err) ||
		    !parseIRExpr(&assumption, buf, &buf, err) ||
		    !parseThisChar('\n', buf, &buf, err))
			break;
		std::vector<CrashSummary::StoreMachineData::macroSectionT> macros;
		if (parseThisString("No remote macro sections\n", buf, &buf, err)) {
			/* Nothing */
		} else if (parseThisString("Remote macro sections:\n", buf, &buf, err)) {
			while (1) {
				StateMachineSideEffect *start, *end;
				const char *m;
				if (!parseThisChar('\t', buf, &m, err) ||
				    !parseStateMachineSideEffect(&start, m, &m, err) ||
				    !parseThisString(" to ", m, &m, err))
					break;
				if (parseThisString("<null>", m, &m, err)) {
					end = NULL;
				} else if (!parseStateMachineSideEffect(&end, m, &m, err)) {
					break;
				}
				if (!parseThisChar('\n', m, &m, err))
					break;
				StateMachineSideEffectStore *starts = dynamic_cast<StateMachineSideEffectStore *>(start);
				StateMachineSideEffectStore *ends = dynamic_cast<StateMachineSideEffectStore *>(end);
				if (!starts || (end && !ends) ) {
					*err = vex_asprintf("expected macro section to start and end with store side effects");
					return false;
				}
				buf = m;
				macros.push_back(CrashSummary::StoreMachineData::macroSectionT(starts, ends));
			}
		}
		storeMachines.push_back(new CrashSummary::StoreMachineData(
						storeMachine,
						assumption,
						macros));
	}
	if (storeMachines.size() == 0)
		return false;
	*succ = buf;
	*out = new CrashSummary(loadMachine, storeMachines);
	return true;
}
