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
	return res;
}

bool
parseCrashSummary(CrashSummary **out, const char *buf,
		  const char **succ)
{
	StateMachine *loadMachine;
	if (!parseThisString("Load machine:\n", buf, &buf) ||
	    !parseStateMachine(&loadMachine, buf, &buf))
		return false;
	std::vector<CrashSummary::StoreMachineData *> storeMachines;
	while (1) {
		StateMachine *storeMachine;
		IRExpr *assumption;
		if (!parseThisString("Store machine:\n", buf, &buf) ||
		    !parseStateMachine(&storeMachine, buf, &buf) ||
		    !parseThisString("Assumption: ", buf, &buf) ||
		    !parseIRExpr(&assumption, buf, &buf) ||
		    !parseThisChar('\n', buf, &buf))
			break;
		std::vector<CrashSummary::StoreMachineData::macroSectionT> macros;
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
