#include <err.h>

#include "sli.h"

void MachineState::visit(HeapVisitor &hv)
{
	visit_container<std::vector<Thread *> >(threads, hv);
	hv(addressSpace);
	hv(elfData);
}

MachineState *MachineState::dupeSelf() const
{
	MachineState *work = new MachineState();
	*work = *this;

	work->addressSpace = addressSpace->dupeSelf();
	work->threads.resize(threads.size());
	for (unsigned x = 0; x < threads.size(); x++)
		work->threads[x] = threads[x]->dupeSelf();
	return work;
}

bool MachineState::crashed() const
{
	unsigned x;
	for (x = 0; x < threads.size(); x++)
		if (threads[x]->crashed)
			return true;
	return false;
}
