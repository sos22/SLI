#ifndef CRASH_REASON_HPP__
#define CRASH_REASON_HPP__

class MachineState;
class Thread;
class StateMachine;

/* A VEX RIP combines an ordinary machine code RIP with an offset into
   a VEX IRSB.  An idx of 0 corresponds to just before the start of
   the block, and stmts_used corresponds to just after the end. */
class VexRip : public Named {
protected:
	char *mkName() const { return my_asprintf("%lx:%x", rip, idx); }
public:
	VexRip(unsigned long _rip, unsigned _idx) : rip(_rip), idx(_idx) {}
	unsigned long rip;
	unsigned idx;	
	void changedIdx() { clearName(); }
	unsigned long hash(void) const {
		return rip ^ (idx * 13);
	}
	bool operator<(const VexRip &a) const {
		return rip < a.rip || (rip == a.rip && idx < a.idx);
	}
	bool operator==(const VexRip &a) const {
		return rip == a.rip && idx == a.idx;
	}
};

StateMachine *getProximalCause(MachineState *ms, unsigned long rip, Thread *thr);

#endif /* !CRASH_REASON_HPP */
