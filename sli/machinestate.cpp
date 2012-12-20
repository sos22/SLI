#include <err.h>

#include "sli.h"

void MachineState::visit(HeapVisitor &hv)
{
	visit_container<std::vector<Thread *> >(threads, hv);
	hv(addressSpace);
	hv(elfData);
}

bool MachineState::crashed() const
{
	unsigned x;
	for (x = 0; x < threads.size(); x++)
		if (threads[x]->crashed)
			return true;
	return false;
}
