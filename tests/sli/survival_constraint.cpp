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
	if (argc < 3)
		errx(1, "need to know where to read the state machine and MAI map from");

	init_sli();

	SMScopes scopes;
	if (!scopes.read(argv[3]))
		errx(1, "parsing %s as scopes file", argv[3]);

	VexPtr<OracleInterface> oracle(new Oracle(NULL, NULL, NULL));

	VexPtr<StateMachine, &ir_heap> sm(readStateMachine(&scopes, open(argv[1], O_RDONLY)));
	VexPtr<bbdd, &ir_heap> survive;
	VexPtr<bbdd, &ir_heap> nullBBDD(NULL);

	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack()
		.enableignoreSideEffects();

	VexPtr<MaiMap, &ir_heap> mai(MaiMap::fromFile(sm, argv[2]));

	survive = survivalConstraintIfExecutedAtomically(&scopes, mai, sm, nullBBDD, oracle, false, opt, ALLOW_GC);

	bool ignore;
	survive = simplifyBDD(&scopes.bools, survive, opt, &ignore);

	survive->prettyPrint(stdout);

	return 0;
}
