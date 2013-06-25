#include "sli.h"

void MachineState::visit(HeapVisitor &hv)
{
	visit_container<std::vector<Thread *> >(threads, hv);
	hv(addressSpace);
	hv(elfData);
}
