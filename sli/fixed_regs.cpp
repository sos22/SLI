/* Simple static analysis pass which finds out if some register can be
   expressed as either a constant or another register plus a
   constant. */
#include "sli.h"
#include "oracle.hpp"
#include "offline_analysis.hpp"

#ifndef NDEBUG
static bool debug_fixed_regs = false;
#else
#define debug_fixed_regs false
#endif

#define OFFSET_amd64_DFLAG 160

struct ers : public Named {
	enum {cnst, reg_offset } type;
	threadAndRegister base;
	long offset;

	char *mkName() const {
		switch (type) {
		case cnst:
			return my_asprintf("%ld", offset);
		case reg_offset:
			return my_asprintf("%s%+ld", base.name(), offset);
		}
		abort();
	}
		
	static ers Const(long _val) {
		ers res;
		res.type = cnst;
		res.offset = _val;
		return res;
	}
	static ers Reg(const threadAndRegister &_base) {
		ers res;
		res.type = reg_offset;
		res.base = _base;
		res.offset = 0;
		return res;
	}

	bool operator!=(const ers &o) const {
		if (type != o.type || offset != o.offset) {
			return true;
		}
		if (type == cnst) {
			return false;
		}
		return base != o.base;
	}
};
class extFixedRegs : public Named {
	bool invalid;
	/* Not present -> it's just itself with offset 0 */
	std::map<threadAndRegister, ers> content;

	char *mkName() const {
		if (invalid) {
			return strdup("<invalid>");
		}
		std::vector<const char *> fragments;
		for (auto it = content.begin(); it != content.end(); it++) {
			fragments.push_back(my_asprintf("%s -> %s", it->first.name(), it->second.name()));
		}
		char *res = flattenStringFragmentsMalloc(fragments, ", ", "{", "}");
		for (auto it = fragments.begin(); it != fragments.end(); it++) {
			free((void *)*it);
		}
		return res;
	}
public:
	extFixedRegs() : invalid(false) {}
	void setReg(unsigned offset, const Maybe<ers> &);
	void set(const threadAndRegister &, const Maybe<ers> &);
	void invalidateReg(unsigned offset);
	void invalidate(const threadAndRegister &tr);
	void invalidate() { invalid = true; clearName(); }
	Maybe<ers> ersOfExpr(IRExpr *what);

	bool merge(const extFixedRegs &o);

	Oracle::FixedRegs toFixedRegs() const;
};

bool
extFixedRegs::merge(const extFixedRegs &o)
{
	if (invalid) {
		return false;
	}
	if (o.invalid) {
		invalid = true;
		clearName();
		return true;
	}

	bool changed = false;
	for (auto it = content.begin(); it != content.end(); ) {
		auto it2 = o.content.find(it->first);
		if (it2 == o.content.end() ||
		    it2->second != it->second) {
			content.erase(it++);
			changed = true;
		} else {
			it++;
		}
	}
	if (changed) {
		clearName();
	}
	return changed;
}

void
extFixedRegs::setReg(unsigned offset, const Maybe<ers> &what)
{
	set(threadAndRegister::reg(Oracle::STATIC_THREAD, offset, 0), what);
}

void
extFixedRegs::set(const threadAndRegister &reg, const Maybe<ers> &what)
{
	if (!what.valid) {
		invalidate(reg);
	} else {
		for (auto it = content.begin(); it != content.end(); ) {
			if (it->second.type == ers::cnst ||
			    it->second.base != reg) {
				it++;
				continue;
			}
			if (what.content.type == ers::reg_offset &&
			    what.content.base == reg) {
				it->second.offset -= what.content.offset;
				it->second.clearName();
				it++;
			} else {
				content.erase(it++);
			}
		}
		if (what.content.type == ers::cnst ||
		    what.content.base != reg) {
			content[reg] = what.content;
		}
	}
	clearName();
}

void
extFixedRegs::invalidateReg(unsigned offset)
{
	invalidate(threadAndRegister::reg(Oracle::STATIC_THREAD, offset, 0));
}

void
extFixedRegs::invalidate(const threadAndRegister &r)
{
	for (auto it = content.begin(); it != content.end(); ) {
		if (it->first == r ||
		    (it->second.type == ers::reg_offset &&
		     it->second.base == r)) {
			content.erase(it++);
		} else {
			it++;
		}
	}
	clearName();
}

Maybe<ers>
extFixedRegs::ersOfExpr(IRExpr *what)
{
	if (what->type() != Ity_I64) {
		return Maybe<ers>::nothing();
	}
	switch (what->tag) {
	case Iex_Get: {
		auto g = (IRExprGet *)what;
		auto it = content.find(g->reg);
		if (it == content.end()) {
			return Maybe<ers>::just(ers::Reg( ((IRExprGet *)what)->reg ));
		} else {
			return it->second;
		}
	}
	case Iex_Const:
		return ers::Const( ((IRExprConst *)what)->Ico.content.U64 );
	case Iex_Associative: {
		auto a = (IRExprAssociative *)what;
		if (a->op == Iop_Add64) {
			Maybe<ers> acc(ersOfExpr(a->contents[0]));
			for (int i = 1; acc.valid && i < a->nr_arguments; i++) {
				Maybe<ers> o(ersOfExpr(a->contents[i]));
				if (!o.valid) {
					acc = o;
				} else if (acc.content.type == ers::cnst) {
					acc.content.offset += o.content.offset;
					if (o.content.type == ers::reg_offset) {
						acc.content.type = ers::reg_offset;
						acc.content.base = o.content.base;
					}
				} else if (o.content.type == ers::cnst) {
					acc.content.offset += o.content.offset;
				} else {
					acc = Maybe<ers>::nothing();
				}
			}
			if (acc.valid) {
				acc.content.clearName();
			}
			return acc;
		}
		break;
	}
	default:
		break;
	}
	return Maybe<ers>::nothing();
}

Oracle::FixedRegs
extFixedRegs::toFixedRegs() const
{
	Oracle::FixedRegs res;
	res.dfs = Oracle::FixedRegs::unknown;
	for (int i = 0; i < Oracle::NR_REGS; i++) {
		res.content[i].type = Oracle::FixedRegs::rs::invalid;
	}
	if (!invalid) {
		for (auto it = content.begin(); it != content.end(); it++) {
			if (it->first.isTemp()) {
				continue;
			}
			if (it->first.asReg() == OFFSET_amd64_DFLAG) {
				if (it->second.type == ers::cnst &&
				    (it->second.offset == 1 ||
				     it->second.offset == -1)) {
					if (it->second.offset == 1) {
						res.dfs = Oracle::FixedRegs::plus_one;
					} else {
						res.dfs = Oracle::FixedRegs::minus_one;
					}
				} else {
					res.dfs = Oracle::FixedRegs::unknown;
				}
			} else if (it->first.asReg() < Oracle::NR_REGS * 8) {
				if (it->second.type == ers::cnst) {
					res.content[it->first.asReg() / 8].type =
						Oracle::FixedRegs::rs::cnst;
					res.content[it->first.asReg() / 8].offset_or_cnst =
						it->second.offset;
				} else if (it->second.base.isReg() &&
					   it->second.base.asReg() < Oracle::NR_REGS * 8) {
					res.content[it->first.asReg() / 8].type =
						Oracle::FixedRegs::rs::reg_offset;
					res.content[it->first.asReg() / 8].base_reg =
						it->second.base.asReg() / 8;
					res.content[it->first.asReg() / 8].offset_or_cnst =
						it->second.offset;
				}
			}
		}
	}
	return res;
}

static void
calculateFixedRegsForFunction(Oracle *oracle, const StaticRip &head)
{
	sane_map<StaticRip, extFixedRegs> work;
	std::set<StaticRip> pending;
	pending.insert(head);
	extFixedRegs &root(work[head]);
	/* df is always set at start of function */
	root.setReg(OFFSET_amd64_DFLAG, ers::Const(1));

	if (debug_fixed_regs) {
		printf("%s(%s)\n", __func__, head.name());
	}

	struct {
		sane_map<StaticRip, extFixedRegs> *work;
		std::set<StaticRip> *pending;
		void operator()(const StaticRip &sr, const extFixedRegs &state) {
			auto it_did_insert = work->insert(sr, state);
			auto it = it_did_insert.first;
			auto did_insert = it_did_insert.second;
			if (!did_insert) {
				did_insert |= it->second.merge(state);
			}
			if (did_insert) {
				pending->insert(sr);
				if (debug_fixed_regs) {
					printf("   Update %s -> %s\n",
					       sr.name(), state.name());
				}
			}
		}
	} addIncomingEdge;
	addIncomingEdge.work = &work;
	addIncomingEdge.pending = &pending;

	while (!pending.empty()) {
		StaticRip sr(*pending.begin());
		pending.erase(sr);
		if (!(oracle->functionHeadForInstruction(sr) == head)) {
			if (debug_fixed_regs) {
				printf("Not following branch out of function to %s\n", sr.name());
			}
			continue;
		}
		IRSB *irsb = oracle->getIRSBForRip(oracle->ms->addressSpace, sr, false);

		assert(irsb);

		assert(work.count(sr));
		extFixedRegs state(work[sr]);

		if (debug_fixed_regs) {
			printf("Instruction %s, in state %s\n", sr.name(), state.name());
		}

		int last_instr;
		/* If this block ends in a call instruction then we
		   need to make sure that we ignore the push of the
		   return address, since we'll also ignore its pop and
		   otherwise it screws up the stack alignment. */
		if (irsb->jumpkind == Ijk_Call) {
			for (last_instr = irsb->stmts_used;
			     irsb->stmts[last_instr-1]->tag != Ist_IMark;
			     last_instr--) {
				/* nop */
			}
		} else {
			last_instr = irsb->stmts_used;
		}
		for (int i = 1; i < last_instr; i++) {
			switch (irsb->stmts[i]->tag) {
			case Ist_NoOp:
				break;
			case Ist_IMark:
				sr = StaticRip(((IRStmtIMark *)irsb->stmts[i])->addr.rip);
				addIncomingEdge(sr, state);
				pending.erase(sr);
				state = work[sr];
				if (debug_fixed_regs) {
					printf("Advance to %s, state %s\n",
					       sr.name(), state.name());
				}
				break;
			case Ist_AbiHint:
				break;
			case Ist_Put: {
				auto put = (IRStmtPut *)irsb->stmts[i];
				state.set(put->target, state.ersOfExpr(put->data));
				if (debug_fixed_regs) {
					printf("   Update for ");
					ppIRStmt(put, stdout);
					printf(" -> %s\n", state.name());
				}
				break;
			}
			case Ist_PutI:
				state.invalidate();
				if (debug_fixed_regs) {
					printf("    PutI invalidates everything\n");
				}
				break;
			case Ist_Store:
				break;
			case Ist_CAS: {
				auto cas = (IRStmtCAS *)irsb->stmts[i];
				state.invalidate(cas->details->oldLo);
				if (debug_fixed_regs) {
					printf("   Update for ");
					ppIRStmt(cas, stdout);
					printf(" -> %s\n", state.name());
				}					
				break;
			}
			case Ist_Dirty: {
				auto d = (IRStmtDirty *)irsb->stmts[i];
				state.invalidate(d->details->tmp);
				if (debug_fixed_regs) {
					printf("   Update for ");
					ppIRStmt(d, stdout);
					printf(" -> %s\n", state.name());
				}					
				break;
			}
			case Ist_MBE:
				break;
			case Ist_Exit: {
				auto e = (IRStmtExit *)irsb->stmts[i];
				addIncomingEdge(StaticRip(e->dst.rip), state);
				break;
			}
			case Ist_StartAtomic:
				break;
			case Ist_EndAtomic:
				break;
			}
		}

		if (irsb->jumpkind == Ijk_Call) {
			if (!irsb->next_is_const ||
			    !oracle->functionNeverReturns(StaticRip(irsb->next_const.rip))) {
				if (debug_fixed_regs) {
					printf("Skip over call\n");
				}
				state.invalidateReg(OFFSET_amd64_RAX);
				state.invalidateReg(OFFSET_amd64_RDX);
				state.invalidateReg(OFFSET_amd64_RDX);
				state.invalidateReg(OFFSET_amd64_RSI);
				state.invalidateReg(OFFSET_amd64_RDI);
				state.invalidateReg(OFFSET_amd64_R8);
				state.invalidateReg(OFFSET_amd64_R9);
				state.invalidateReg(OFFSET_amd64_R10);
				state.invalidateReg(OFFSET_amd64_R11);
				state.setReg(OFFSET_amd64_DFLAG, ers::Const(1));
				addIncomingEdge(StaticRip(extract_call_follower(irsb)), state);
			}
		} else if (irsb->jumpkind == Ijk_Ret) {
			/* End of the line */
			if (debug_fixed_regs) {
				printf("Hit end of function\n");
			}
		} else if (irsb->next_is_const) {
			if (debug_fixed_regs) {
				printf("Next is %s\n", irsb->next_const.rip.name());
			}
			addIncomingEdge(StaticRip(irsb->next_const.rip), state);
		} else {
			std::vector<StaticRip> targets;
			Oracle::Function(sr).getInstructionFallThroughs(sr, targets);
			for (auto it = targets.begin(); it != targets.end(); it++) {
				if (debug_fixed_regs) {
					printf("Indirect branch to %s\n", it->name());
				}
				addIncomingEdge(*it, state);
			}
		}
	}

	for (auto it = work.begin(); it != work.end(); it++) {
		if (oracle->functionHeadForInstruction(it->first) == head) {
			oracle->setFixedRegs(it->first, it->second.toFixedRegs());
		}
	}
}

void
Oracle::calculateFixedRegs(VexPtr<Oracle> &ths, GarbageCollectionToken token)
{
	if (!CONFIG_FIXED_REGS) {
		return;
	}
	std::vector<StaticRip> functions;
	ths->getFunctions(functions);
	for (auto it = functions.begin(); it != functions.end(); it++) {
		LibVEX_maybe_gc(token);
		calculateFixedRegsForFunction(ths, *it);
		if ( (it-functions.begin()) % 100 == 0) {
			printf("Fixed regs: %zd/%zd\n",
			       it - functions.begin(),
			       functions.size());
		}
	}
}

Oracle::FixedRegs::FixedRegs()
{
	for (int i = 0; i < NR_REGS; i++) {
		content[i].type = rs::invalid;
	}
	dfs = unknown;
}

char *
Oracle::FixedRegs::mkName() const
{
	std::vector<const char *> fragments;
	for (int i = 0; i < NR_REGS; i++) {
		switch (content[i].type) {
		case rs::invalid:
			break;
		case rs::cnst:
			fragments.push_back(vex_asprintf("r%d->0x%lx", i, content[i].offset_or_cnst));
			break;
		case rs::reg_offset:
			fragments.push_back(vex_asprintf("r%d->r%d+%ld",
							 i,
							 content[i].base_reg,
							 content[i].offset_or_cnst));
			break;
		}
	}
	switch (dfs) {
	case plus_one:
		fragments.push_back("DF=+1");
		break;
	case unknown:
		break;
	case minus_one:
		fragments.push_back("DF=-1");
		break;
	}
	return flattenStringFragmentsMalloc(fragments, ", ", "{", "}");
}

bool
Oracle::FixedRegs::parse(const char *buf, const char **end)
{
	clearName();
	for (int i = 0; i < NR_REGS; i++) {
		content[i].type = rs::invalid;
	}
	dfs = unknown;

	if (!parseThisString("{", buf, &buf)) {
		return false;
	}
	while (!parseThisString("}", buf, end)) {
		int reg;
		if (parseThisChar('r', buf, &buf) &&
		    parseDecimalInt(&reg, buf, &buf) &&
		    parseThisString("->", buf, &buf)) {
			long offset;
			int base;
			if (reg < 0 || reg > NR_REGS) {
				return false;
			}
			if (parseThisString("0x", buf, &buf) &&
			    parseHexLong(&offset, buf, &buf)) {
				content[reg].type = rs::cnst;
				content[reg].offset_or_cnst = offset;
			} else if (parseThisChar('r', buf, &buf) &&
				   parseDecimalInt(&base, buf, &buf) &&
				   parseThisChar('+', buf, &buf) &&
				   parseDecimalLong(&offset, buf, &buf)) {
				if (base < 0 || base > NR_REGS) {
					return false;
				}
				content[reg].type = rs::reg_offset;
				content[reg].base_reg = base;
				content[reg].offset_or_cnst = offset;
			} else {
				return false;
			}
		} else if (parseThisString("DF=+1", buf, &buf)) {
			dfs = plus_one;
		} else if (parseThisString("DF=-1", buf, &buf)) {
			dfs = minus_one;
		} else {
			return false;
		}
		parseThisString(", ", buf, &buf);
	}
	return true;
}

class fr_transformer : public StateMachineTransformer {
	IRExpr *transformIex(IRExprGet *ieg) {
		assert(ieg->reg.gen() == 0);
		if (!ieg->reg.isReg() || ieg->type() != Ity_I64) {
			return ieg;
		}
		if (ieg->reg.asReg() == OFFSET_amd64_DFLAG) {
			if (fr->dfs == Oracle::FixedRegs::plus_one) {
				return IRExpr_Const_U64(1);
			} else if (fr->dfs == Oracle::FixedRegs::minus_one) {
				return IRExpr_Const_U64(-1);
			} else {
				return ieg;
			}
		}
		int idx = ieg->reg.asReg() / 8;
		if (idx >= Oracle::NR_REGS) {
			return ieg;
		}
		switch (fr->content[idx].type) {
		case Oracle::FixedRegs::rs::invalid:
			return ieg;
		case Oracle::FixedRegs::rs::cnst:
			return IRExpr_Const_U64(fr->content[idx].offset_or_cnst);
		case Oracle::FixedRegs::rs::reg_offset:
			return IRExpr_Binop(
				Iop_Add64,
				IRExpr_Get(threadAndRegister::reg(ieg->reg.tid(),
								  fr->content[idx].base_reg * 8,
								  0),
					   Ity_I64),
				IRExpr_Const_U64(fr->content[idx].offset_or_cnst));
		}
		abort();
	}
	bool rewriteNewStates() const { return false; }
public:
	const Oracle::FixedRegs *fr;
};

bbdd *
Oracle::FixedRegs::transform_bbdd(bbdd::scope *scope, bbdd *x) const
{
	if (!CONFIG_FIXED_REGS) {
		return x;
	}
	fr_transformer trans;
	trans.fr = this;
	return trans.transform_bbdd(scope, x);
}

smrbdd *
Oracle::FixedRegs::transform_smrbdd(bbdd::scope *scope1, smrbdd::scope *scope, smrbdd *x) const
{
	if (!CONFIG_FIXED_REGS) {
		return x;
	}
	fr_transformer trans;
	trans.fr = this;
	return trans.transform_smrbdd(scope1, scope, x);
}

StateMachineSideEffect *
Oracle::FixedRegs::transformSideEffect(SMScopes *scopes, StateMachineSideEffect *x) const
{
	if (!CONFIG_FIXED_REGS) {
		return x;
	}
	fr_transformer trans;
	trans.fr = this;
	bool ign;
	auto r = trans.transformSideEffect(scopes, x, &ign);
	if (r) {
		return r;
	} else {
		return x;
	}
}

