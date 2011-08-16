#include "sli.h"
#include "enforce_crash.hpp"

#define BASE_MESSAGE_ID 0xaabb
unsigned happensBeforeEdge::next_msg_id = BASE_MESSAGE_ID;

void
EnforceCrashPatchFragment::generateEpilogue(ClientRip exitRip)
{
	Instruction<ClientRip> *i = Instruction<ClientRip>::pseudo(exitRip);
	cfg->registerInstruction(i);
	registerInstruction(i, content.size());

	std::set<unsigned> msg_ids;
	for (std::set<happensBeforeEdge *>::iterator it = edges.begin();
	     it != edges.end();
	     it++) {
		const happensBeforeEdge *hb = *it;
		if (exitRip.origThreads.count(hb->before.thread))
			msg_ids.insert(hb->msg_id);
	}

	if (msg_ids.size() != 0) {
		skipRedZone();
		emitPushQ(RegisterIdx::RBX);
		emitPushQ(RegisterIdx::RDI);
		emitMovQ(RegisterIdx::RBX, 0);
		lateRelocs.push_back(new LateRelocation(content.size() - 8,
							8,
							vex_asprintf("(unsigned long)clearMessage"),
							0,
							false));

		for (std::set<unsigned>::iterator it = msg_ids.begin();
		     it != msg_ids.end();
		     it++) {
			unsigned msg_id = *it;
			emitMovQ(RegisterIdx::RDI, msg_id);
			emitCallReg(RegisterIdx::RBX);
		}
		emitPopQ(RegisterIdx::RDI);
		emitPopQ(RegisterIdx::RBX);
		restoreRedZone();
	}

	emitJmpToRipHost(exitRip.rip);
}

char *
EnforceCrashPatchFragment::asC(const char *ident, std::set<ClientRip> &entryPoints)
{
	std::vector<const char *> fragments;

	fragments.push_back(vex_asprintf("#define MESSAGE_ID_BASE %d\n", BASE_MESSAGE_ID));
	fragments.push_back(vex_asprintf("#define MESSAGE_ID_END %d\n", happensBeforeEdge::next_msg_id));
	for (std::set<happensBeforeEdge *>::iterator it = edges.begin();
	     it != edges.end();
	     it++) {
		happensBeforeEdge *hb = *it;
		for (unsigned x = 0; x < hb->content.size(); x++)
			fragments.push_back(vex_asprintf("static unsigned long __msg_%d_slot_%d;\n", hb->msg_id, x));
	}
	fragments.push_back(PatchFragment<ClientRip>::asC(ident, entryPoints));

	return flattenStringFragments(fragments);
}

