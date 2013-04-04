#include "sli.h"
#include "enforce_crash.hpp"

static void
loadCrashEnforcementData(SMScopes *scopes, crashEnforcementData &ced, AddressSpace *as, int fd)
{
	char *buf = readfile(fd);
	const char *suffix;
	if (!ced.parse(scopes, as, buf, &suffix))
		errx(1, "cannot parse crash enforcement data");
	if (*suffix)
		errx(1, "junk after crash enforcement data: %s", suffix);
	free(buf);
}

int
main(int argc, char *argv[])
{
	const char *binary = argv[1];
	const char *ced_path = argv[2];
	const char *types = argv[3];
	const char *callgraph = argv[4];
	const char *staticdb = argv[5];
	const char *output = argv[6];

	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(binary));
	VexPtr<Oracle> oracle(new Oracle(ms, ms->findThread(ThreadId(1)), types));
	oracle->loadCallGraph(oracle, callgraph, staticdb, ALLOW_GC);

	int fd = open(ced_path, O_RDONLY);
	if (fd < 0)
		err(1, "open(%s)", ced_path);
	SMScopes scopes;
	crashEnforcementData ced;
	loadCrashEnforcementData(&scopes, ced, ms->addressSpace, fd);
	close(fd);

	return ced_to_cep(ced, output, binary, oracle);
}
