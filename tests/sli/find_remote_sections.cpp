#include <sys/fcntl.h>
#include <err.h>
#include <unistd.h>

#include "sli.h"
#include "oracle.hpp"
#include "state_machine.hpp"
#include "eval_state_machine.hpp"
#include "allowable_optimisations.hpp"
#include "alloc_mai.hpp"

int
main(int argc, char *argv[])
{
	if (argc < 4)
		errx(1, "not enough arguments");

	init_sli();

	VexPtr<OracleInterface> oracle(new Oracle(NULL, NULL, argv[1]));

	VexPtr<StateMachine, &ir_heap> readMachine(readStateMachine(open(argv[2], O_RDONLY)));
	VexPtr<StateMachine, &ir_heap> writeMachine(readStateMachine(open(argv[3], O_RDONLY)));
	VexPtr<IRExpr, &ir_heap> assumption(readIRExpr(open(argv[4], O_RDONLY)));
	VexPtr<MaiMap, &ir_heap> mai(MaiMap::fromFile(readMachine, writeMachine, argv[5]));

	VexPtr<remoteMacroSectionsT, &ir_heap> remoteMacroSections(new remoteMacroSectionsT());

	if (!findRemoteMacroSections(mai, readMachine, writeMachine, assumption, oracle,
				     AllowableOptimisations::defaultOptimisations,
				     remoteMacroSections, ALLOW_GC)) {
		printf("Cannot find remote macro sections...\n");
		return 1;
	}
	for (remoteMacroSectionsT::iterator it = remoteMacroSections->begin();
	     it != remoteMacroSections->end();
	     it++) {
		printf("\t\tRemote macro section ");
		it->start->prettyPrint(stdout);
		printf(" -> ");
		it->end->prettyPrint(stdout);
		printf("\n");
	}
	if (!fixSufficient(mai, readMachine, writeMachine, assumption, oracle,
			   AllowableOptimisations::defaultOptimisations,
			   remoteMacroSections, ALLOW_GC)) {
		printf("Fix insufficient\n");
		return 1;
	} else {
		printf("Fix sufficient\n");
		return 0;
	}
}
