#ifndef GENFIX_H__
#define GENFIX_H__

#define MAX_INSTRUCTION_SIZE 15

class CFG;

class Prefixes {
public:
	bool rex_w, rex_r, rex_x, rex_b;
	Prefixes() : rex_w(false),
		     rex_r(false),
		     rex_x(false),
		     rex_b(false)
	{
	}
	void rexByte(unsigned char b) {
		assert(b >= 0x40);
		assert(b < 0x50);
		rex_b = !!(b & 1);
		rex_x = !!(b & 2);
		rex_r = !!(b & 4);
		rex_w = !!(b & 8);
	}
};

class EarlyRelocation;

class Instruction : public GarbageCollected<Instruction > {
	unsigned char byte();
	void emit(unsigned char);
	void modrm(unsigned nrImmediates);
	void immediate(unsigned size);
public:
	unsigned long rip;

	unsigned long defaultNext;
	Instruction *defaultNextI;
	unsigned long branchNext;
	Instruction *branchNextI;

	/* Doesn't really belong here, but it'll do for now. */
	unsigned offsetInPatch;
	bool presentInPatch;

	unsigned char content[MAX_INSTRUCTION_SIZE];
	unsigned len;
	Prefixes pfx;
	unsigned nr_prefixes;
	std::vector<EarlyRelocation *> relocs;

	AddressSpace *as;

	bool useful;

	static Instruction *decode(AddressSpace *as,
				   unsigned long rip,
				   CFG *cfg);
	static Instruction *pseudo(unsigned long rip);

	void visit(HeapVisitor &hv) {
		visit_container(relocs, hv);
		hv(as);
		hv(defaultNextI);
		hv(branchNextI);
	}
	void destruct() { this->~Instruction(); }
	NAMED_CLASS
};

class CFG : public GarbageCollected<CFG> {
	AddressSpace *as;
public:
	static unsigned long __trivial_hash_function(const unsigned long &k) { return k; }
	typedef gc_map<unsigned long, Instruction *, __trivial_hash_function,
		       __default_eq_function, __visit_function_heap> ripToInstrT;
	ripToInstrT *ripToInstr;
private:
	std::vector<std::pair<unsigned long, unsigned> > pendingRips;
	std::vector<unsigned long> neededRips;
	void decodeInstruction(unsigned long rip, unsigned max_depth);
public:
	CFG(AddressSpace *_as) : as(_as), ripToInstr(new ripToInstrT()) {}
	void add_root(unsigned long root, unsigned max_depth)
	{
		pendingRips.push_back(std::pair<unsigned long, unsigned>(root, max_depth));
	}
	void doit();
	void visit(HeapVisitor &hv) {
		hv(ripToInstr);
		hv(as);
	}
	void registerInstruction(Instruction *i) { (*ripToInstr)[i->rip] = i; }
	virtual void destruct() { this->~CFG(); }
	NAMED_CLASS

	/* These can be overriden by derived classes to change the
	 * behaviour a bit. */

	/* Should we bother to explore instructions which follow this
	 * one?  If this returns true, direct followers of this
	 * instruction will be explored; indirect ones will not be
	 * (i.e. we only consider branches whose target is statically
	 * constant). */
	virtual bool exploreInstruction(Instruction *i) { return true; }
	/* We've discovered a direct-called function.  Should we
	 * explore the callee?  Indirect calls are never explored. */
	virtual bool exploreFunction(unsigned long rip) { return false; }
	/* Is this instruction useful?  Once the CFG is built, we do a
	 * post-pass which walks the list of instructions, and uses
	 * this to decide whether instructions are useful.  We then
	 * walk backwards through the CFG and mark any instruction
	 * which can reach a useful instruction as being useful
	 * itself.  Finally, any non-useful instructions are replaced
	 * with branches back into the original code.
	 */
	virtual bool instructionUseful(Instruction *i) { return true; }
};

typedef char *LateRelocation;

class PatchFragment : public GarbageCollected<PatchFragment> {
	std::vector<EarlyRelocation *> relocs;
	std::vector<LateRelocation> lateRelocs;
	std::vector<Instruction *> registeredInstrs;

protected:
	CFG *cfg;
	std::vector<unsigned char> content;

private:
	Instruction *nextInstr(CFG *cfg);
	void emitStraightLine(Instruction *i);

protected:
	/* Emit a jump to an offset in the current fragment. */
	void emitJmpToOffset(unsigned offset);
	void emitJmpToRipClient(unsigned long rip);
	void emitJmpToRipHost(unsigned long rip);
	void emitCallSequence(const char *target, bool allowRedirection);
	void skipRedZone();
	void restoreRedZone();
	void emitPushQ(unsigned);
	void emitPopQ(unsigned);
	void emitMovQ(unsigned, unsigned long);
	void emitCallReg(unsigned);
public:
	void fromCFG(CFG *cfg);
	char *asC() const;

	bool ripToOffset(unsigned long rip, unsigned *res);
	void writeBytes(const void *bytes, unsigned size, unsigned offset);
	void addLateReloc(LateRelocation m) { lateRelocs.push_back(m); }

	void visit(HeapVisitor &hv) {
		visit_container(relocs, hv);
	}
	void destruct() { this->~PatchFragment(); }
	NAMED_CLASS

	/* Can be overridden by derived classes which need to do
	 * something special when we return to untranslated code.
	 * This is only invoked for statically constant branches; if
	 * you want to do anything with non-constant branches then
	 * you'll need to override emitInstruction() as well.
	 */
	virtual bool generateEpilogue(unsigned long exitRip) { return false; }

protected:

	/* Emit a single instruction.  The instruction passed in is as
	 * it was in the original program.  The derived class is at
	 * liberty to generate as many or as few output instructions
	 * as it desires. */
	virtual void emitInstruction(Instruction *i);

	void registerInstruction(Instruction *i, unsigned offset) {
		assert(!i->presentInPatch);
		i->offsetInPatch = offset;
		i->presentInPatch = true;
		registeredInstrs.push_back(i);
	}
};

#endif /* !GENFIX_H__ */
