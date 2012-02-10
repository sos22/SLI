#include "sli.h"
#include "enforce_crash.hpp"

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
		emitPushQ(RegisterIdx::RSI);
		emitMovQ(RegisterIdx::RSI, 0);
		lateRelocs.push_back(new LateRelocation(content.size() - 8,
							8,
							vex_asprintf("(unsigned long)clearMessage"),
							0,
							false));

		for (std::set<unsigned>::iterator it = msg_ids.begin();
		     it != msg_ids.end();
		     it++)
			emitPushImm32(*it);
		emitPushQ(RegisterIdx::RDI);
		emitMovQ(RegisterIdx::RDI, msg_ids.size());
		emitCallReg(RegisterIdx::RSI);
		emitPopQ(RegisterIdx::RSI);
		emitPopQ(RegisterIdx::RDI);
		restoreRedZone();
	}

	emitJmpToRipHost(exitRip.rip);
}

char *
EnforceCrashPatchFragment::asC(const char *ident, int max_rx_site_id)
{
	std::vector<const char *> fragments;

	unsigned min_message_id, max_message_id;

	if (edges.empty()) {
		min_message_id = max_message_id = 0;
	} else {
		auto it = edges.begin();
		min_message_id = (*it)->msg_id;
		max_message_id = (*it)->msg_id;
		while (it != edges.end()) {
			unsigned id = (*it)->msg_id;
			if (id < min_message_id)
				min_message_id = id;
			if (id > max_message_id)
				max_message_id = id;
			it++;
		}
	}

	fragments.push_back(vex_asprintf("#define MESSAGE_ID_BASE %d\n", min_message_id));
	fragments.push_back(vex_asprintf("#define MESSAGE_ID_END %d\n", max_message_id + 1));
	fragments.push_back(vex_asprintf("#define MIN_RX_SITE_ID %d\n", 0));
	fragments.push_back(vex_asprintf("#define MAX_RX_SITE_ID %d\n", max_rx_site_id));
	for (std::set<happensBeforeEdge *>::iterator it = edges.begin();
	     it != edges.end();
	     it++) {
		happensBeforeEdge *hb = *it;
		for (unsigned x = 0; x < hb->content.size(); x++)
			fragments.push_back(vex_asprintf("static unsigned long __msg_%d_slot_%d;\n", hb->msg_id, x));
	}
	fragments.push_back(PatchFragment<ClientRip>::asC(ident));

	return flattenStringFragments(fragments);
}

