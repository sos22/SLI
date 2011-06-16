#include <sys/fcntl.h>
#include <unistd.h>

#include "sli.h"
#include "oracle.hpp"
#include "state_machine.hpp"
#include "eval_state_machine.hpp"

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<Oracle> oracle(new Oracle(NULL, NULL, NULL));

	VexPtr<StateMachine, &ir_heap> readMachine(readStateMachine(open(argv[1], O_RDONLY)));
	VexPtr<StateMachine, &ir_heap> writeMachine(readStateMachine(open(argv[2], O_RDONLY)));
	VexPtr<IRExpr, &ir_heap> assumption(readIRExpr(open(argv[3], O_RDONLY)));
	
	VexPtr<remoteMacroSectionsT, &ir_heap> remoteMacroSections(new remoteMacroSectionsT());

	if (!findRemoteMacroSections(readMachine, writeMachine, assumption, oracle, remoteMacroSections, ALLOW_GC)) {
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
	if (!fixSufficient(readMachine, writeMachine, assumption, oracle, remoteMacroSections)) {
		printf("Fix insufficient\n");
		return 1;
	} else {
		printf("Fix sufficient\n");
		return 0;
	}
}
