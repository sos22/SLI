/* Take a crash enforcement data structure and turn into a crash
   enforcement plan .o file. */
#include <sys/fcntl.h>
#include <unistd.h>
#include "sli.h"
#include "enforce_crash.hpp"

unsigned long
__trivial_hash_function(const VexRip &vr)
{
	return vr.hash();
}

static void
loadCrashEnforcementData(crashEnforcementData &ced, AddressSpace *as, int fd)
{
	char *buf = readfile(fd);
	const char *suffix;
	if (!ced.parse(as, buf, &suffix))
		errx(1, "cannot parse crash enforcement data");
	if (*suffix)
		errx(1, "junk after crash enforcement data: %s", suffix);
	free(buf);
}

class CfgRelabeller {
	int next_label;
public:
	std::map<ThreadCfgLabel, int> content;
	CfgRelabeller()
		: next_label(0)
	{}
	bool label(const ThreadCfgLabel &l)
	{
		auto it_did_insert = content.insert(std::pair<ThreadCfgLabel, int>(l, next_label));
		auto did_insert = it_did_insert.second;
		if (did_insert)
			next_label++;
		return did_insert;
	}
	int operator()(const ThreadCfgLabel &l) const
	{
		auto it = content.find(l);
		assert(it != content.end());
		return it->second;
	}
};

static bool
expressionDependsOn(IRExpr *what, const std::set<IRExpr *> &d, bool includeRegisters)
{
	struct : public IRExprTransformer {
		bool res;
		const std::set<IRExpr *> *d;
		bool includeRegisters;
		IRExpr *transformIex(IRExprGet *e) {
			if (e->reg.isReg() && !includeRegisters)
				return e;
			if (d->count(e)) {
				res = true;
				abortTransform();
			}
			return e;
		}
		IRExpr *transformIex(IRExprEntryPoint *e) {
			if (d->count(e)) {
				res = true;
				abortTransform();
			}
			return e;
		}
		IRExpr *transformIex(IRExprControlFlow *e) {
			if (d->count(e)) {
				res = true;
				abortTransform();
			}
			return e;
		}
	} doit;
	doit.res = false;
	doit.d = &d;
	doit.includeRegisters = includeRegisters;
	doit.doit(what);
	return doit.res;
}

static int
max_simslot(const slotMapT &sm)
{
	int res = 0;
	for (auto it = sm.begin(); it != sm.end(); it++)
		if (it->second.idx > res)
			res = it->second.idx;
	return res;
}

static void
stack_validation_table(Oracle *oracle, FILE *f, const VexRip &vr)
{
	unsigned offset = 0;
	for (unsigned x = 1; x < vr.stack.size(); x++) {
		offset += stack_offset(oracle, vr.stack[vr.stack.size() - x]);
		fprintf(f, "         { .offset = %d, .expected_value = 0x%lx },\n",
			offset, vr.stack[vr.stack.size() - x - 1]);
	}
}

static void
compute_entry_point_list(Oracle *oracle,
			 crashEnforcementData &ced,
			 FILE *f,
			 const CfgRelabeller &cfgLabels,
			 const slotMapT &slotMap,
			 const char *ident)
{
	std::map<ThreadCfgLabel, int> ctxts;
	{
		int next_idx;
		next_idx = 1;
		for (auto it = ced.roots.begin(); !it.finished(); it.advance()) {
			ThreadCfgLabel l(it.get());
			if (!ctxts.count(l))
				ctxts[l] = next_idx++;
		}
	}
	for (auto it = ctxts.begin(); it != ctxts.end(); it++) {
		ThreadCfgLabel l(it->first);
		auto n = ced.crashCfg.findInstr(l);
		const AbstractThread &absThread(n->rip.thread);
		ConcreteThread concThread(ced.roots.lookupAbsThread(absThread));
		ConcreteCfgLabel concCfgLabel(concThread.summary(), n->rip.label);
		const VexRip &v(ced.crashCfg.labelToRip(concCfgLabel));
		fprintf(f, "static struct cep_entry_ctxt entry_ctxt%d = {\n", it->second);
		fprintf(f, "    .cfg_label = %d,\n", cfgLabels(it->first));
		fprintf(f, "    .nr_simslots = %d,\n", max_simslot(slotMap) + 1);
		fprintf(f, "    .nr_stack_slots = %zd,\n", v.stack.size() - 1);
		fprintf(f, "    .stack = {\n");
		stack_validation_table(oracle, f, v);
		fprintf(f, "    },\n");
		fprintf(f, "};\n");
	}
	std::map<unsigned long, std::set<ThreadCfgLabel> > entryPoints;
	for (auto it = ced.roots.begin(); !it.finished(); it.advance()) {
		ThreadCfgLabel l(it.get());
		auto n = ced.crashCfg.findInstr(l);
		const AbstractThread &absThread(n->rip.thread);
		ConcreteThread concThread(ced.roots.lookupAbsThread(absThread));
		ConcreteCfgLabel concCfgLabel(concThread.summary(), n->rip.label);
		const VexRip &v(ced.crashCfg.labelToRip(concCfgLabel));
		entryPoints[v.unwrap_vexrip()].insert(l);
	}
	int next_idx = 0;
	for (auto it = entryPoints.begin(); it != entryPoints.end(); it++) {
		fprintf(f, "static struct cep_entry_point __entry_point%d = {\n", next_idx++);
		fprintf(f, "    .orig_rip = 0x%lx,\n", it->first);
		fprintf(f, "    .nr_entry_ctxts = %zd,\n", it->second.size());
		fprintf(f, "    .ctxts = {\n");
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
			fprintf(f, "        &entry_ctxt%d,\n", ctxts[*it2]);
		fprintf(f, "   },\n");
		fprintf(f, "};\n");
	}

	next_idx = 0;
	fprintf(f, "static struct cep_entry_point *%s[] = {\n", ident);
	for (auto it = entryPoints.begin(); it != entryPoints.end(); it++) {
		fprintf(f, "    &__entry_point%d,\n", next_idx++);
	}
	fprintf(f, "};\n");
}

static void
add_simple_array(FILE *f,
		 const char *prefix,
		 const char *def_name,
		 const char *field,
		 const char *sz_field,
		 int idx)
{
	fprintf(f, "%s.%s = instr_%d_%s,\n", prefix, field, idx, def_name);
	fprintf(f, "%s.%s = sizeof(instr_%d_%s)/sizeof(instr_%d_%s[0]),\n",
		prefix, sz_field, idx, def_name, idx, def_name);
}

static void
add_empty_array(FILE *f,
		const char *prefix,
		const char *field,
		const char *sz_field)
{
	fprintf(f,"%s.%s = NULL,\n", prefix, field);
	fprintf(f,"%s.%s = 0,\n", prefix, sz_field);
}

static const char *
vex_type_to_bytecode_type(IRType ty)
{
	switch (ty) {
	case Ity_INVALID:
		abort();
	case Ity_I1:
		return "bct_bit";
	case Ity_I8:
		return "bct_byte";
	case Ity_I16:
		return "bct_short";
	case Ity_I32:
		return "bct_int";
	case Ity_I64:
		return "bct_long";
	case Ity_I128:
		return "bct_longlong";
	case Ity_F32:
		return "bct_float";
	case Ity_F64:
		return "bct_double";
	case Ity_V128:
		return "bct_v128";
	}
	abort();
}

static void
bytecode_op(FILE *f, const char *op, IRType ty)
{
	fprintf(f, "    (unsigned short)(bcop_%s | (%s << bytecode_type_shift)),\n",
		op,
		vex_type_to_bytecode_type(ty)
		);
}
static void
bytecode_const64(FILE *f, unsigned long val)
{
	fprintf(f, "    %d,\n", (unsigned short)val);
	fprintf(f, "    %d,\n", (unsigned short)(val >> 16));
	fprintf(f, "    %d,\n", (unsigned short)(val >> 32));
	fprintf(f, "    %d,\n", (unsigned short)(val >> 48));
}
static void
bytecode_const32(FILE *f, unsigned val)
{
	fprintf(f, "    %d,\n", (unsigned short)val);
	fprintf(f, "    %d,\n", (unsigned short)(val >> 16));
}
static void
bytecode_const16(FILE *f, unsigned short val)
{
	fprintf(f, "    %d,\n", (unsigned short)val);
}
static void
bytecode_const8(FILE *f, unsigned char val)
{
	/* ``Bytecode'' format actually works in terms of shorts, so
	   just zero-extend the byte to 16 bits. */
	fprintf(f, "    %d,\n", (unsigned short)val);
}
static void
bytecode_const1(FILE *f, bool val)
{
	if (val)
		fprintf(f, "    1,\n");
	else
		fprintf(f, "    0,\n");
}

static void
bytecode_eval_expr(FILE *f, IRExpr *expr, crashEnforcementData &ced, const slotMapT &slots)
{
	switch (expr->tag) {
	case Iex_Const: {
		IRExprConst *iec = (IRExprConst *)expr;
		bytecode_op(f, "push_const", iec->type());
		switch (iec->con->tag) {
		case Ico_U1:
			bytecode_const1(f, iec->con->Ico.U1);
			break;
		case Ico_U8:
			bytecode_const8(f, iec->con->Ico.U8);
			break;
		case Ico_U16:
			bytecode_const16(f, iec->con->Ico.U16);
			break;
		case Ico_U32:
			bytecode_const32(f, iec->con->Ico.U32);
			break;
		case Ico_U64:
			bytecode_const64(f, iec->con->Ico.U64);
			break;
		default:
			abort();
		}
		break;
	}
	case Iex_Get:
	case Iex_ControlFlow:
	case Iex_EntryPoint: {
		simulationSlotT slot = slots(expr);
		bytecode_op(f, "push_slot", expr->type());
		bytecode_const32(f, slot.idx);
		break;
	}

	case Iex_Unop: {
		IRExprUnop *ieu = (IRExprUnop *)expr;
		bytecode_eval_expr(f, ieu->arg, ced, slots);
		switch (ieu->op) {
		case Iop_Not1:
		case Iop_Not8:
		case Iop_Not16:
		case Iop_Not32:
		case Iop_Not64:
			bytecode_op(f, "not", ieu->arg->type());
			break;
		case Iop_Neg8:
		case Iop_Neg16:
		case Iop_Neg32:
		case Iop_Neg64:
			bytecode_op(f, "neg", ieu->arg->type());
			break;
		case Iop_8Sto64:
		case Iop_16Sto64:
		case Iop_32Sto64:
			bytecode_op(f, "sign_extend64", ieu->arg->type());
			break;
		case Iop_8Sto32:
		case Iop_16Sto32:
			bytecode_op(f, "sign_extend32", ieu->arg->type());
			break;
		case Iop_1Uto8:
		case Iop_16to8:
		case Iop_32to8:
		case Iop_64to8:
			bytecode_op(f, "zero_extend8", ieu->arg->type());
			break;
		case Iop_8Uto16:
		case Iop_32to16:
		case Iop_64to16:
			bytecode_op(f, "zero_extend16", ieu->arg->type());
			break;
		case Iop_1Uto32:
		case Iop_8Uto32:
		case Iop_16Uto32:
		case Iop_64to32:
			bytecode_op(f, "zero_extend32", ieu->arg->type());
			break;
		case Iop_1Uto64:
		case Iop_8Uto64:
		case Iop_16Uto64:
		case Iop_32Uto64:
			bytecode_op(f, "zero_extend64", ieu->arg->type());
			break;
		case Iop_BadPtr:
			bytecode_op(f, "badptr", Ity_I64);
			break;
		default:
			abort();
		}
		break;
	}

	case Iex_Binop: {
		IRExprBinop *ieb = (IRExprBinop *)expr;
		bytecode_eval_expr(f, ieb->arg1, ced, slots);
		bytecode_eval_expr(f, ieb->arg2, ced, slots);
		switch (ieb->op) {
		case Iop_CmpEQ8:
		case Iop_CmpEQ16:
		case Iop_CmpEQ32:
		case Iop_CmpEQ64:
			bytecode_op(f, "cmp_eq", ieb->arg1->type());
			break;
		case Iop_Mul8:
		case Iop_Mul16:
		case Iop_Mul32:
		case Iop_Mul64:
			bytecode_op(f, "mul", ieb->arg1->type());
			break;
		case Iop_CmpLT8U:
		case Iop_CmpLT16U:
		case Iop_CmpLT32U:
		case Iop_CmpLT64U:
			bytecode_op(f, "cmp_ltu", ieb->arg1->type());
			break;
		case Iop_CmpLT8S:
		case Iop_CmpLT16S:
		case Iop_CmpLT32S:
		case Iop_CmpLT64S:
			bytecode_op(f, "cmp_lts", ieb->arg1->type());
			break;
		case Iop_Shl64:
			bytecode_op(f, "shl", ieb->arg1->type());
			break;
		case Iop_Shr64:
			bytecode_op(f, "shr", ieb->arg1->type());
			break;
		case Iop_Sar64:
			bytecode_op(f, "sar", ieb->arg1->type());
			break;
		default:
			abort();
		}
		break;
	}

	case Iex_Associative: {
		IRExprAssociative *const iea = (IRExprAssociative *)expr;
		assert(iea->nr_arguments != 0);
		bytecode_eval_expr(f, iea->contents[0], ced, slots);
		for (int i = 1; i < iea->nr_arguments; i++) {
			bytecode_eval_expr(f, iea->contents[i], ced, slots);
			switch (iea->op) {
			case Iop_Add8:
			case Iop_Add16:
			case Iop_Add32:
			case Iop_Add64:
				bytecode_op(f, "add", iea->type());
				break;
			case Iop_And1:
			case Iop_And8:
			case Iop_And16:
			case Iop_And32:
			case Iop_And64:
				bytecode_op(f, "and", iea->type());
				break;
			case Iop_Or1:
			case Iop_Or8:
			case Iop_Or16:
			case Iop_Or32:
			case Iop_Or64:
				bytecode_op(f, "or", iea->type());
				break;
			case Iop_Xor1:
			case Iop_Xor8:
			case Iop_Xor16:
			case Iop_Xor32:
			case Iop_Xor64:
				bytecode_op(f, "xor", iea->type());
				break;
			default:
				abort();
			}
		}
		break;
	}
	case Iex_Load: {
		IRExprLoad *iel = (IRExprLoad *)expr;
		bytecode_eval_expr(f, iel->addr, ced, slots);
		bytecode_op(f, "load", iel->ty);
		break;
	}
	case Iex_Mux0X: {
		IRExprMux0X *m = (IRExprMux0X *)expr;
		bytecode_eval_expr(f, m->exprX, ced, slots);
		bytecode_eval_expr(f, m->expr0, ced, slots);
		bytecode_eval_expr(f, m->cond, ced, slots);
		bytecode_op(f, "mux0x", m->expr0->type());
		break;
	}
	default:
		abort();
	}
}

static void
emit_validation(FILE *f, int ident, const char *name, const std::set<exprEvalPoint> &condition,
		crashEnforcementData &ced, const slotMapT &slots)
{
	fprintf(f, "static const unsigned short instr_%d_%s[] = {\n", ident, name);
	for (auto it = condition.begin();
	     it != condition.end();
	     it++) {
		bytecode_eval_expr(f, it->e, ced, slots);
		if (!it->invert)
			bytecode_op(f, "not", Ity_I1);
		fprintf(f, "    (unsigned short)bcop_fail_if,\n");
	}
	fprintf(f, "    (unsigned short)bcop_succeed\n};\n");
}

struct cfg_annotation_summary {
	bool have_stash;
	unsigned rx_msg;
	unsigned tx_msg;
	unsigned long rip;
	bool has_pre_validate;
	bool has_rx_validate;
	bool has_eval_validate;
	bool has_control_validate;
	const char *id;
};

static unsigned
getRegisterIdx(unsigned vex_offset)
{
	if (vex_offset <= OFFSET_amd64_R15)
		return (vex_offset - OFFSET_amd64_RAX) / 8;
	if (vex_offset == offsetof(VexGuestAMD64State, guest_FS_ZERO))
		return 16;
	abort();
}

static void
dump_annotated_cfg(crashEnforcementData &ced, FILE *f, CfgRelabeller &relabeller,
		   const slotMapT &slots, const char *ident)
{
	{
		std::queue<ThreadCfgLabel> pending;
		for (auto it = ced.roots.begin(); !it.finished(); it.advance())
			pending.push(it.get());
		while (!pending.empty()) {
			ThreadCfgLabel l(pending.front());
			pending.pop();
			if (!relabeller.label(l))
				continue;
			auto n = ced.crashCfg.findInstr(l);
			for (auto it = n->successors.begin(); it != n->successors.end(); it++) {
				if (it->instr)
					pending.push(ThreadCfgLabel(l.thread, it->instr->label));
			}
		}
	}

	std::map<int, cfg_annotation_summary> summaries;
	unsigned next_msg_list_id = 1;

	/* Now go through and generate plan-level representations for those. */
	/* Ancillary data first: the content of the instruction, plus
	 * any necessary annotations. */
	for (auto it = relabeller.content.begin(); it != relabeller.content.end(); it++) {
		ThreadCfgLabel oldLabel(it->first);
		int newLabel(it->second);

		auto instr = ced.crashCfg.findInstr(oldLabel);
		assert(instr);
		assert(instr->len != 0);
		fprintf(f, "static const unsigned char instr_%d_content[] = {", newLabel);
		for (unsigned x = 0; x < instr->len; x++) {
			if (x != 0)
				fprintf(f, ", ");
			fprintf(f, "0x%02x", instr->content[x]);
		}
		fprintf(f, "};\n");

		std::vector<std::pair<int, unsigned long> > successors;
		for (auto it = instr->successors.begin(); it != instr->successors.end(); it++) {
			if (!it->instr)
				continue;
		}
		fprintf(f, "static const cfg_label_t instr_%d_successors[] = {", newLabel);
		for (auto it = instr->successors.begin(); it != instr->successors.end(); it++) {
			if (it->instr) {
				ThreadCfgLabel nextLabel(oldLabel.thread, it->instr->label);
				fprintf(f, "%d, ", relabeller(nextLabel));
			}
		}
		fprintf(f, "};\n");

		struct cfg_annotation_summary summary;
		memset(&summary, 0, sizeof(summary));
		if (ced.exprStashPoints.count(oldLabel)) {
			const std::set<IRExpr *> &toStash(ced.exprStashPoints[oldLabel]);
			fprintf(f, "static const struct cfg_instr_stash instr_%d_stash[] = {\n", newLabel);
			for (auto it2 = toStash.begin(); it2 != toStash.end(); it2++) {
				if ( (*it2)->tag == Iex_Get ) {
					IRExprGet *e = (IRExprGet *)*it2;
					simulationSlotT simSlot(slots(e));
					fprintf(f, "    { .reg = %d, .slot = %d },\n",
						e->reg.isReg() ? getRegisterIdx(e->reg.asReg()) : -1,
						simSlot.idx);
				}
			}
			fprintf(f, "};\n");
			fprintf(f, "static const struct cfg_instr_set_entry instr_%d_set_entry[] = {\n", newLabel);
			for (auto it2 = toStash.begin(); it2 != toStash.end(); it2++) {
				if ( (*it2)->tag == Iex_EntryPoint ) {
					simulationSlotT simSlot(slots(*it2));
					fprintf(f, "    { .slot = %d },\n", simSlot.idx);
				}
			}
			fprintf(f, "};\n");
			fprintf(f, "static const struct cfg_instr_set_control instr_%d_set_control[] = {\n", newLabel);
			for (auto it2 = toStash.begin(); it2 != toStash.end(); it2++) {
				if ( (*it2)->tag == Iex_ControlFlow ) {
					IRExprControlFlow *e = (IRExprControlFlow *)*it2;
					simulationSlotT simSlot(slots(e));
					int goingTo = relabeller(ThreadCfgLabel(oldLabel.thread, e->cfg2));
					fprintf(f, "    { .next_node = %d, .slot = %d },\n", goingTo, simSlot.idx);
				}
			}
			fprintf(f, "};\n");
			summary.have_stash = true;
		}
		if (ced.happensBeforePoints.count(oldLabel)) {
			const std::set<happensBeforeEdge *> &hbEdges(ced.happensBeforePoints[oldLabel]);
			std::set<happensBeforeEdge *> rxMsg;
			std::set<happensBeforeEdge *> txMsg;
			for (auto it2 = hbEdges.begin(); it2 != hbEdges.end(); it2++) {
				happensBeforeEdge *hb = *it2;
				if (hb->after->rip == oldLabel) {
					rxMsg.insert(hb);
				} else {
					assert(hb->before->rip == oldLabel);
					txMsg.insert(hb);
				}
			}
			assert(!(rxMsg.empty() && txMsg.empty()));
			if (!rxMsg.empty()) {
				for (auto it = rxMsg.begin(); it != rxMsg.end(); it++)
					fprintf(f, "static struct msg_template msg_template_%x_rx;\n",
						(*it)->msg_id);
				fprintf(f, "static struct msg_template *msg_list_%d[] = {\n",
					next_msg_list_id);
				for (auto it = rxMsg.begin(); it != rxMsg.end(); it++)
					fprintf(f, "\t&msg_template_%x_rx,\n", (*it)->msg_id);
				fprintf(f, "};\n");
				summary.rx_msg = next_msg_list_id;
				next_msg_list_id++;
			}
			if (!txMsg.empty()) {
				for (auto it = txMsg.begin(); it != txMsg.end(); it++)
					fprintf(f, "static struct msg_template msg_template_%x_tx;\n",
						(*it)->msg_id);
				fprintf(f, "static struct msg_template *msg_list_%d[] = {\n",
					next_msg_list_id);
				for (auto it = txMsg.begin(); it != txMsg.end(); it++)
					fprintf(f, "\t&msg_template_%x_tx,\n", (*it)->msg_id);
				fprintf(f, "};\n");
				summary.tx_msg = next_msg_list_id;
				next_msg_list_id++;
			}
		}
		if (ced.expressionEvalPoints.count(oldLabel)) {
			const std::set<exprEvalPoint> &sideConditions(ced.expressionEvalPoints[oldLabel]);
			std::set<exprEvalPoint> pre_validate, rx_validate, eval_validate, control_validate;
			std::set<IRExpr *> rxed, stashedData, stashedControl;
			if (ced.happensBeforePoints.count(oldLabel)) {
				const std::set<happensBeforeEdge *> &hbEdges(ced.happensBeforePoints[oldLabel]);
				for (auto it2 = hbEdges.begin(); it2 != hbEdges.end(); it2++) {
					happensBeforeEdge *hb = *it2;
					if (hb->after->rip == oldLabel) {
						for (unsigned x = 0; x < hb->content.size(); x++)
							rxed.insert(hb->content[x]);
					}
				}
			}
			if (ced.exprStashPoints.count(oldLabel)) {
				const std::set<IRExpr *> &toStash(ced.exprStashPoints[oldLabel]);
				for (auto it2 = toStash.begin(); it2 != toStash.end(); it2++) {
					IRExpr *e = *it2;
					if ( e->tag == Iex_Get ) {
						stashedData.insert(e);
					} else if ( e->tag == Iex_ControlFlow ) {
						stashedControl.insert(e);
					} else if ( e->tag == Iex_EntryPoint ) {
						/* This is arguably a control-flow stash,
						   but it happens right at the start of the
						   instruction rather than right at the end,
						   so it's available throughout the instruction
						   and doesn't affect where we can do the eval,
						   so we can just ignore it. */
					} else {
						abort();
					}
				}
			}
			/* We need to decide where in the instruction
			   cycle to evaluate this side-condition.  The
			   options are at the very start, during
			   message RX, after performing the data
			   stash, or after performing the control flow
			   stash.  We pick the earliest point at which
			   we have all necessary information. */
			/* (The instruction cycle always does RX
			   before stash.) */
			for (auto it = sideConditions.begin();
			     it != sideConditions.end();
			     it++) {
				if (expressionDependsOn(it->e, stashedControl, false))
					control_validate.insert(*it);
				else if (expressionDependsOn(it->e, stashedData, false))
					eval_validate.insert(*it);
				else if (expressionDependsOn(it->e, rxed, true))
					rx_validate.insert(*it);
				else
					pre_validate.insert(*it);
			}
			assert(!(pre_validate.empty() && rx_validate.empty() && eval_validate.empty() && control_validate.empty()));
			if (!pre_validate.empty()) {
				summary.has_pre_validate = true;
				emit_validation(f, newLabel, "pre_validate", pre_validate, ced, slots);
			}
			if (!rx_validate.empty()) {
				summary.has_rx_validate = true;
				emit_validation(f, newLabel, "rx_validate", rx_validate, ced, slots);
			}
			if (!eval_validate.empty()) {
				summary.has_eval_validate = true;
				emit_validation(f, newLabel, "eval_validate", eval_validate, ced, slots);
			}
			if (!control_validate.empty()) {
				summary.has_control_validate = true;
				emit_validation(f, newLabel, "control_validate", control_validate, ced, slots);
			}
		}

		const AbstractThread &absThread(instr->rip.thread);
		ConcreteThread concThread(ced.roots.lookupAbsThread(absThread));
		ConcreteCfgLabel concCfgLabel(concThread.summary(), instr->rip.label);
		summary.rip = ced.crashCfg.labelToRip(concCfgLabel).unwrap_vexrip();
		summary.id = instr->label.name();
		summaries[newLabel] = summary;
		fprintf(f, "\n");
	}

	/* Now for the message templates. */
	std::set<happensBeforeEdge *> allHbEdges;
	for (auto it = ced.happensBeforePoints.begin(); it != ced.happensBeforePoints.end(); it++)
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
			allHbEdges.insert(*it2);
	for (auto it = allHbEdges.begin(); it != allHbEdges.end(); it++) {
		happensBeforeEdge *hb = *it;
		fprintf(f, "static struct msg_template msg_template_%x_tx;\n", hb->msg_id);
		fprintf(f, "static struct msg_template msg_template_%x_rx = {\n", hb->msg_id);
		fprintf(f, "    .msg_id = 0x%x,\n", hb->msg_id);
		fprintf(f, "    .event_count = 0,\n");
		fprintf(f, "    .pair = &msg_template_%x_tx,\n", hb->msg_id);
		fprintf(f, "    .payload_size = %zd,\n", hb->content.size());
		fprintf(f, "    .payload = {");
		for (unsigned x = 0; x < hb->content.size(); x++) {
			if (x != 0)
				fprintf(f, ", ");
			fprintf(f, "%d", slots(hb->content[x]).idx);
		}
		fprintf(f, "}\n};\n");
		fprintf(f, "static struct msg_template msg_template_%x_tx = {\n", hb->msg_id);
		fprintf(f, "    .msg_id = 0x%x,\n", hb->msg_id);
		fprintf(f, "    .event_count = 0,\n");
		fprintf(f, "    .pair = &msg_template_%x_rx,\n", hb->msg_id);
		fprintf(f, "    .payload_size = %zd,\n", hb->content.size());
		fprintf(f, "    .payload = {");
		for (unsigned x = 0; x < hb->content.size(); x++) {
			if (x != 0)
				fprintf(f, ", ");
			fprintf(f, "%d", slots(hb->content[x]).idx);
		}
		fprintf(f, "}\n};\n");
	}

	/* Now dump out the actual CFG table. */
	fprintf(f, "static struct cfg_instr %s[] = {\n", ident);
	for (auto it = summaries.begin(); it != summaries.end(); it++) {
		if (it == summaries.begin())
			fprintf(f, "    [%d] = {\n", it->first);
		else
			fprintf(f, "    }, [%d] = {\n", it->first);
		fprintf(f, "        .rip = 0x%lx,\n", it->second.rip);
		add_simple_array(f, "        ", "content", "content", "content_sz", it->first);
		add_simple_array(f, "        ", "successors", "successors", "nr_successors", it->first);
		if (it->second.have_stash) {
			add_simple_array(f, "        ", "stash", "stash", "nr_stash", it->first);
			add_simple_array(f, "        ", "set_entry", "set_entry", "nr_set_entry", it->first);
			add_simple_array(f, "        ", "set_control", "set_control", "nr_set_control", it->first);
		} else {
			add_empty_array(f, "        ", "stash", "nr_stash");
			add_empty_array(f, "        ", "set_entry", "nr_set_entry");
			add_empty_array(f, "        ", "set_control", "nr_set_control");
		}
		if (it->second.rx_msg) {
			fprintf(f, "        .nr_rx_msg = sizeof(msg_list_%d)/sizeof(msg_list_%d[0]),\n",
				it->second.rx_msg, it->second.rx_msg);
			fprintf(f, "        .rx_msgs = msg_list_%d,\n", it->second.rx_msg);
		} else {
			fprintf(f, "        .nr_rx_msg = 0,\n");
			fprintf(f, "        .rx_msgs = NULL,\n");
		}
		if (it->second.tx_msg) {
			fprintf(f, "        .nr_tx_msg = sizeof(msg_list_%d)/sizeof(msg_list_%d[0]),\n",
				it->second.tx_msg, it->second.tx_msg);
			fprintf(f, "        .tx_msgs = msg_list_%d,\n", it->second.tx_msg);
		} else {
			fprintf(f, "        .nr_tx_msg = 0,\n");
			fprintf(f, "        .tx_msgs = NULL,\n");
		}
		if (it->second.has_pre_validate)
			fprintf(f, "        .pre_validate = instr_%d_pre_validate,\n", it->first);
		else
			fprintf(f, "        .pre_validate = NULL,\n");
		if (it->second.has_rx_validate)
			fprintf(f, "        .rx_validate = instr_%d_rx_validate,\n", it->first);
		else
			fprintf(f, "        .rx_validate = NULL,\n");
		if (it->second.has_eval_validate)
			fprintf(f, "        .eval_validate = instr_%d_eval_validate,\n", it->first);
		else
			fprintf(f, "        .eval_validate = NULL,\n");
		if (it->second.has_control_validate)
			fprintf(f, "        .control_flow_validate = instr_%d_control_validate,\n", it->first);
		else
			fprintf(f, "        .control_flow_validate = NULL,\n");
		fprintf(f, "        .id = \"%s\",\n", it->second.id);
	}
	fprintf(f, "    }\n};\n");
}

static int
lowest_msg_id(const crashEnforcementData &ced)
{
	unsigned res = 0;
	bool f = false;
	for (auto it = ced.happensBeforePoints.begin();
	     it != ced.happensBeforePoints.end();
	     it++) {
		for (auto it2 = it->second.begin();
		     it2 != it->second.end();
		     it2++) {
			if (!f || (*it2)->msg_id < res)
				res = (*it2)->msg_id;
			f = true;
		}
	}
	return res;
}
static int
highest_msg_id(const crashEnforcementData &ced)
{
	unsigned res = 0;
	bool f = false;
	for (auto it = ced.happensBeforePoints.begin();
	     it != ced.happensBeforePoints.end();
	     it++) {
		for (auto it2 = it->second.begin();
		     it2 != it->second.end();
		     it2++) {
			if (!f || (*it2)->msg_id > res)
				res = (*it2)->msg_id;
			f = true;
		}
	}
	return res;
}

int
main(int argc, char *argv[])
{
	const char *binary = argv[1];
	const char *ced_path = argv[2];
	const char *types = argv[3];
	const char *callgraph = argv[4];
	const char *output = argv[5];

	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(binary));
	VexPtr<Oracle> oracle(new Oracle(ms, ms->findThread(ThreadId(1)), types));
	oracle->loadCallGraph(oracle, callgraph, ALLOW_GC);

	int fd = open(ced_path, O_RDONLY);
	if (fd < 0)
		err(1, "open(%s)", ced_path);
	crashEnforcementData ced;
	loadCrashEnforcementData(ced, ms->addressSpace, fd);
	close(fd);

	FILE *f = fopen(output, "w");
	CfgRelabeller relabeller;

	fprintf(f, "#include \"cep_interpreter.h\"\n");
	fprintf(f, "#include <stddef.h>\n"); /* For NULL */
	fprintf(f, "\n");

	slotMapT slots(ced.exprStashPoints, ced.happensBeforePoints);

	fprintf(f, "/*\n");
	slots.prettyPrint(f);
	fprintf(f, "*/\n");

	dump_annotated_cfg(ced, f, relabeller, slots, "__cfg_nodes");
	compute_entry_point_list(oracle, ced, f, relabeller, slots, "__entry_points");
	fprintf(f, "const unsigned long __patch_points[] = {");
	for (auto it = ced.patchPoints.begin(); it != ced.patchPoints.end(); it++) {
		if (it != ced.patchPoints.begin())
			fprintf(f, ", ");
		fprintf(f, "0x%lxul", *it);
	}
	fprintf(f, "};\n");
	fprintf(f, "const unsigned long __force_interpret[] = {");
	for (auto it = ced.interpretInstrs.begin(); it != ced.interpretInstrs.end(); it++) {
		if (it != ced.interpretInstrs.begin())
			fprintf(f, ", ");
		fprintf(f, "0x%lxul", *it);
	}
	fprintf(f, "};\n");
	fprintf(f, "const struct crash_enforcement_plan plan = {\n");
	fprintf(f, "    .entry_points = __entry_points,\n");
	fprintf(f, "    .nr_entry_points = sizeof(__entry_points)/sizeof(__entry_points[0]),\n");
	fprintf(f, "    .cfg_nodes = __cfg_nodes,\n");
	fprintf(f, "    .nr_cfg_nodes = sizeof(__cfg_nodes)/sizeof(__cfg_nodes[0]),\n");
	fprintf(f, "    .base_msg_id = 0x%x,\n", lowest_msg_id(ced));
	fprintf(f, "    .msg_id_limit = 0x%x,\n", highest_msg_id(ced) + 1);
	fprintf(f, "    .nr_patch_points = sizeof(__patch_points)/sizeof(__patch_points[0]),\n");
	fprintf(f, "    .patch_points = __patch_points,\n");
	fprintf(f, "    .nr_force_interpret = sizeof(__force_interpret)/sizeof(__force_interpret[0]),\n");
	fprintf(f, "    .force_interpret = __force_interpret,\n");
	fprintf(f, "};\n");

	fprintf(f, "\n");
	fprintf(f, "const char program_to_patch[] = \"%s\";\n",	realpath(binary,NULL));
	fclose(f);

	return 0;
}
