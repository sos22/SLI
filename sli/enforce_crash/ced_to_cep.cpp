/* Take a crash enforcement data structure and turn into a crash
   enforcement plan .o file. */
#include <sys/fcntl.h>
#include <unistd.h>
#include "sli.h"
#include "enforce_crash.hpp"
#include "maybe.hpp"
#include "visitor.hpp"

unsigned long
__trivial_hash_function(const VexRip &vr)
{
	return vr.hash();
}

static void
loadCrashEnforcementData(bbdd::scope *scope, crashEnforcementData &ced, AddressSpace *as, int fd)
{
	char *buf = readfile(fd);
	const char *suffix;
	if (!ced.parse(scope, as, buf, &suffix))
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
	Maybe<int> operator()(const ThreadCfgLabel &l) const
	{
		auto it = content.find(l);
		if (it == content.end()) {
			return Maybe<int>::nothing();
		} else {
			return Maybe<int>::just(it->second);
		}
	}
};

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
	/* label -> <idx, rspDelta> */
	std::map<ThreadCfgLabel, std::pair<int, long> > ctxts;
	{
		int next_idx;
		next_idx = 1;
		for (auto it = ced.roots.begin(); !it.finished(); it.advance()) {
			ThreadCfgLabel l(it.threadCfgLabel());
			if (!ctxts.count(l)) {
				ctxts[l] = std::pair<int, long>(next_idx++, it.rspDelta());
			}
		}
	}
	for (auto it = ctxts.begin(); it != ctxts.end(); it++) {
		ThreadCfgLabel l(it->first);
		auto n = ced.crashCfg.findInstr(l);
		const AbstractThread &absThread(n->rip.thread);
		ConcreteThread concThread(ced.roots.lookupAbsThread(absThread));
		ConcreteCfgLabel concCfgLabel(concThread.summary(), n->rip.label);
		const VexRip &v(ced.crashCfg.labelToRip(concCfgLabel));
		Maybe<int> cfg_label(cfgLabels(it->first));
		if (!cfg_label.valid) {
			continue;
		}
		fprintf(f, "static struct cep_entry_ctxt entry_ctxt%d = {\n", it->second.first);
		fprintf(f, "    .cfg_label = %d,\n", cfg_label.content);
		fprintf(f, "    .nr_simslots = %d,\n", max_simslot(slotMap) + 1);
		fprintf(f, "    .nr_stack_slots = %zd,\n", v.stack.size() - 1);
		fprintf(f, "    .rsp_delta = %ldl,\n", it->second.second);
		fprintf(f, "    .stack = {\n");
		stack_validation_table(oracle, f, v);
		fprintf(f, "    },\n");
		fprintf(f, "};\n");
	}
	std::map<unsigned long, std::set<ThreadCfgLabel> > entryPoints;
	for (auto it = ced.roots.begin(); !it.finished(); it.advance()) {
		ThreadCfgLabel l(it.threadCfgLabel());
		auto n = ced.crashCfg.findInstr(l);
		const AbstractThread &absThread(n->rip.thread);
		ConcreteThread concThread(ced.roots.lookupAbsThread(absThread));
		ConcreteCfgLabel concCfgLabel(concThread.summary(), n->rip.label);
		const VexRip &v(ced.crashCfg.labelToRip(concCfgLabel));
		if (cfgLabels(l).valid) {
			entryPoints[v.unwrap_vexrip()].insert(l);
		}
	}
	int next_idx = 0;
	for (auto it = entryPoints.begin(); it != entryPoints.end(); it++) {
		fprintf(f, "static struct cep_entry_point __entry_point%d = {\n", next_idx++);
		fprintf(f, "    .orig_rip = 0x%lx,\n", it->first);
		fprintf(f, "    .nr_entry_ctxts = %zd,\n", it->second.size());
		fprintf(f, "    .ctxts = {\n");
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
			fprintf(f, "        &entry_ctxt%d,\n", ctxts[*it2].first);
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
	}
	abort();
}

static void
emit_bytecode_op(std::vector<const char *> &bytecode,
		 const char *op,
		 IRType ty)
{
	bytecode.push_back(
		my_asprintf("(unsigned short)bcop_%s | ((unsigned short)%s << bytecode_type_shift)",
			    op,
			    vex_type_to_bytecode_type(ty)));
}
static void
bytecode_const64(std::vector<const char *> &bytecode, unsigned long val)
{
	bytecode.push_back(my_asprintf("%d", (unsigned short)val));
	bytecode.push_back(my_asprintf("%d", (unsigned short)(val >> 16)));
	bytecode.push_back(my_asprintf("%d", (unsigned short)(val >> 32)));
	bytecode.push_back(my_asprintf("%d", (unsigned short)(val >> 48)));
}
static void
bytecode_const32(std::vector<const char *> &bytecode, unsigned val)
{
	bytecode.push_back(my_asprintf("%d", (unsigned short)val));
	bytecode.push_back(my_asprintf("%d", (unsigned short)(val >> 16)));
}
static void
bytecode_const16(std::vector<const char *> &bytecode, unsigned short val)
{
	bytecode.push_back(my_asprintf("%d", (unsigned short)val));
}
static void
bytecode_const8(std::vector<const char *> &bytecode, unsigned char val)
{
	/* ``Bytecode'' format actually works in terms of shorts, so
	   just zero-extend the byte to 16 bits. */
	bytecode.push_back(my_asprintf("%d", (unsigned short)val));
}

static void
bytecode_eval_expr(std::vector<const char *> &bytecode, IRExpr *expr, const slotMapT &slots)
{
	switch (expr->tag) {
	case Iex_Const: {
		IRExprConst *iec = (IRExprConst *)expr;
		emit_bytecode_op(bytecode, "push_const", iec->type());
		switch (iec->type()) {
		case Ity_I1:
			abort();
			break;
		case Ity_I8:
			bytecode_const8(bytecode, iec->Ico.content.U8);
			break;
		case Ity_I16:
			bytecode_const16(bytecode, iec->Ico.content.U16);
			break;
		case Ity_I32:
			bytecode_const32(bytecode, iec->Ico.content.U32);
			break;
		case Ity_I64:
			bytecode_const64(bytecode, iec->Ico.content.U64);
			break;
		default:
			abort();
		}
		break;
	}
	case Iex_Get:
	case Iex_ControlFlow:
	case Iex_EntryPoint: {
		simulationSlotT slot = slots(
			expr->tag == Iex_Get ? input_expression::registr((const IRExprGet *)expr) :
			expr->tag == Iex_ControlFlow ? input_expression::control_flow((const IRExprControlFlow *)expr) :
			input_expression::entry_point((const IRExprEntryPoint *)expr));
		emit_bytecode_op(bytecode, "push_slot", expr->type());
		bytecode_const32(bytecode, slot.idx);
		break;
	}

	case Iex_Unop: {
		IRExprUnop *ieu = (IRExprUnop *)expr;
		bytecode_eval_expr(bytecode, ieu->arg, slots);
		switch (ieu->op) {
		case Iop_Not1:
		case Iop_Not8:
		case Iop_Not16:
		case Iop_Not32:
		case Iop_Not64:
			emit_bytecode_op(bytecode, "not", ieu->arg->type());
			break;
		case Iop_Neg8:
		case Iop_Neg16:
		case Iop_Neg32:
		case Iop_Neg64:
			emit_bytecode_op(bytecode, "neg", ieu->arg->type());
			break;
		case Iop_8Sto64:
		case Iop_16Sto64:
		case Iop_32Sto64:
			emit_bytecode_op(bytecode, "sign_extend64", ieu->arg->type());
			break;
		case Iop_8Sto32:
		case Iop_16Sto32:
			emit_bytecode_op(bytecode, "sign_extend32", ieu->arg->type());
			break;
		case Iop_1Uto8:
		case Iop_16to8:
		case Iop_32to8:
		case Iop_64to8:
			emit_bytecode_op(bytecode, "zero_extend8", ieu->arg->type());
			break;
		case Iop_8Uto16:
		case Iop_32to16:
		case Iop_64to16:
			emit_bytecode_op(bytecode, "zero_extend16", ieu->arg->type());
			break;
		case Iop_1Uto32:
		case Iop_8Uto32:
		case Iop_16Uto32:
		case Iop_64to32:
			emit_bytecode_op(bytecode, "zero_extend32", ieu->arg->type());
			break;
		case Iop_1Uto64:
		case Iop_8Uto64:
		case Iop_16Uto64:
		case Iop_32Uto64:
			emit_bytecode_op(bytecode, "zero_extend64", ieu->arg->type());
			break;
		case Iop_BadPtr:
			emit_bytecode_op(bytecode, "badptr", Ity_I64);
			break;
		default:
			abort();
		}
		break;
	}

	case Iex_Binop: {
		IRExprBinop *ieb = (IRExprBinop *)expr;
		bytecode_eval_expr(bytecode, ieb->arg1, slots);
		bytecode_eval_expr(bytecode, ieb->arg2, slots);
		switch (ieb->op) {
		case Iop_CmpEQ8:
		case Iop_CmpEQ16:
		case Iop_CmpEQ32:
		case Iop_CmpEQ64:
			emit_bytecode_op(bytecode, "cmp_eq", ieb->arg1->type());
			break;
		case Iop_Mul8:
		case Iop_Mul16:
		case Iop_Mul32:
		case Iop_Mul64:
			emit_bytecode_op(bytecode, "mul", ieb->arg1->type());
			break;
		case Iop_CmpLT8U:
		case Iop_CmpLT16U:
		case Iop_CmpLT32U:
		case Iop_CmpLT64U:
			emit_bytecode_op(bytecode, "cmp_ltu", ieb->arg1->type());
			break;
		case Iop_CmpLT8S:
		case Iop_CmpLT16S:
		case Iop_CmpLT32S:
		case Iop_CmpLT64S:
			emit_bytecode_op(bytecode, "cmp_lts", ieb->arg1->type());
			break;
		case Iop_Shl64:
			emit_bytecode_op(bytecode, "shl", ieb->arg1->type());
			break;
		case Iop_Shr64:
			emit_bytecode_op(bytecode, "shr", ieb->arg1->type());
			break;
		case Iop_Sar64:
			emit_bytecode_op(bytecode, "sar", ieb->arg1->type());
			break;
		default:
			abort();
		}
		break;
	}

	case Iex_Associative: {
		IRExprAssociative *const iea = (IRExprAssociative *)expr;
		assert(iea->nr_arguments != 0);
		bytecode_eval_expr(bytecode, iea->contents[0], slots);
		for (int i = 1; i < iea->nr_arguments; i++) {
			bytecode_eval_expr(bytecode, iea->contents[i], slots);
			switch (iea->op) {
			case Iop_Add8:
			case Iop_Add16:
			case Iop_Add32:
			case Iop_Add64:
				emit_bytecode_op(bytecode, "add", iea->type());
				break;
			case Iop_And1:
			case Iop_And8:
			case Iop_And16:
			case Iop_And32:
			case Iop_And64:
				emit_bytecode_op(bytecode, "and", iea->type());
				break;
			case Iop_Or1:
			case Iop_Or8:
			case Iop_Or16:
			case Iop_Or32:
			case Iop_Or64:
				emit_bytecode_op(bytecode, "or", iea->type());
				break;
			case Iop_Xor8:
			case Iop_Xor16:
			case Iop_Xor32:
			case Iop_Xor64:
				emit_bytecode_op(bytecode, "xor", iea->type());
				break;
			case Iop_Mul8:
			case Iop_Mul16:
			case Iop_Mul32:
			case Iop_Mul64:
				emit_bytecode_op(bytecode, "mul", iea->type());
				break;
			default:
				abort();
			}
		}
		break;
	}
	case Iex_Load: {
		IRExprLoad *iel = (IRExprLoad *)expr;
		bytecode_eval_expr(bytecode, iel->addr, slots);
		emit_bytecode_op(bytecode, "load", iel->ty);
		break;
	}
	default:
		abort();
	}
}

static void
emit_validation(FILE *f,
		const char *tag,
		int ident,
		const char *name,
		bbdd *condition,
		const slotMapT &slots)
{
	std::vector<const char *> bytecode;
	sane_map<bbdd *, unsigned> validationOffsets;
	std::vector<std::pair<bbdd *, unsigned> > relocs;
	const char *branch = "bcop_branch";
	const char *succeed = "bcop_succeed";
	const char *fail = "bcop_fail";

	assert(!condition->isLeaf());

	bytecode_eval_expr(bytecode, condition->internal().condition, slots);

	bytecode.push_back(branch);
	relocs.push_back(std::pair<bbdd *, unsigned>(condition->internal().trueBranch,
						     bytecode.size()));
	bytecode.push_back((const char *)0xf001);
	relocs.push_back(std::pair<bbdd *, unsigned>(condition->internal().falseBranch,
						     bytecode.size()));
	bytecode.push_back((const char *)0xf002);

	while (!relocs.empty()) {
		auto targ = relocs.back().first;
		auto offset = relocs.back().second;
		relocs.pop_back();

		auto it_did_insert = validationOffsets.insert(targ, 0xcafe);
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (did_insert) {
			it->second = bytecode.size();
			if (targ->isLeaf()) {
				if (targ->leaf()) {
					bytecode.push_back(succeed);
				} else {
					bytecode.push_back(fail);
				}
			} else {
				bytecode_eval_expr(bytecode, targ->internal().condition, slots);
				bytecode.push_back(branch);
				relocs.push_back(std::pair<bbdd *, unsigned>
						 (targ->internal().trueBranch,
						  bytecode.size()));
				bytecode.push_back((const char *)0xf003);
				relocs.push_back(std::pair<bbdd *, unsigned>
						 (targ->internal().falseBranch,
						  bytecode.size()));
				bytecode.push_back((const char *)0xf004);
			}
		}
		bytecode[offset] = my_asprintf("%d", it->second);
	}
	fprintf(f, "static const unsigned short %s_%d_%s[] = {\n", tag, ident, name);
	for (unsigned x = 0; x < bytecode.size(); x++) {
		fprintf(f, "/* %3d */   %s,\n", x, bytecode[x]);
		if (bytecode[x] != branch &&
		    bytecode[x] != succeed &&
		    bytecode[x] != fail) {
			free((void *)bytecode[x]);
		}
	}
	fprintf(f, "};\n");
}

struct cfg_annotation_summary {
	bool have_stash;
	unsigned rx_msg;
	unsigned tx_msg;
	unsigned long rip;
	bool has_after_regs;
	bool has_after_control_flow;
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
		for (auto it = ced.roots.begin(); !it.finished(); it.advance()) {
			pending.push(it.threadCfgLabel());
		}
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
				Maybe<int> nextLabelIdx(relabeller(nextLabel));
				if (nextLabelIdx.valid) {
					fprintf(f, "%d, ", nextLabelIdx.content);
				}
			}
		}
		fprintf(f, "};\n");

		struct cfg_annotation_summary summary;
		memset(&summary, 0, sizeof(summary));
		if (ced.exprStashPoints.count(oldLabel)) {
			const std::set<input_expression> &toStash(ced.exprStashPoints[oldLabel]);
			fprintf(f, "static const struct cfg_instr_stash instr_%d_stash[] = {\n", newLabel);
			for (auto it2 = toStash.begin(); it2 != toStash.end(); it2++) {
				if ( it2->tag == input_expression::inp_register ) {
					simulationSlotT simSlot(slots(*it2));
					fprintf(f, "    { .reg = %d, .slot = %d },\n",
						getRegisterIdx(it2->vex_offset),
						simSlot.idx);
				}
			}
			fprintf(f, "};\n");
			fprintf(f, "static const struct cfg_instr_set_entry instr_%d_set_entry[] = {\n", newLabel);
#warning This isn't quite right: building the CED sets a stash for every entry point expression at every point node, but the interpreter always responds to one of those stashes by storing 1 in the slot. '
			for (auto it2 = toStash.begin(); it2 != toStash.end(); it2++) {
				if ( it2->tag == input_expression::inp_entry_point ) {
					simulationSlotT simSlot(slots(*it2));
					fprintf(f, "    { .slot = %d },\n", simSlot.idx);
				}
			}
			fprintf(f, "};\n");
			fprintf(f, "static const struct cfg_instr_set_control instr_%d_set_control[] = {\n", newLabel);
			for (auto it2 = toStash.begin(); it2 != toStash.end(); it2++) {
				if ( it2->tag == input_expression::inp_control_flow ) {
					simulationSlotT simSlot(slots(*it2));
					Maybe<int> goingTo(relabeller(ThreadCfgLabel(oldLabel.thread, it2->label2)));
					if (goingTo.valid) {
						fprintf(f, "    { .next_node = %d, .slot = %d },\n", goingTo.content, simSlot.idx);
					}
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
			bbdd *after_regs = ced.expressionEvalPoints.after_regs(oldLabel);
			bbdd *after_control_flow = ced.expressionEvalPoints.after_control_flow(oldLabel);

			assert(after_regs || after_control_flow);
			if (after_regs) {
				summary.has_after_regs = true;
				emit_validation(f, "instr", newLabel, "after_regs", after_regs, slots);
			}
			if (after_control_flow) {
				summary.has_after_control_flow = true;
				emit_validation(f, "instr", newLabel, "after_control_flow", after_control_flow, slots);
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
	for (auto it = ced.happensBeforePoints.begin(); it != ced.happensBeforePoints.end(); it++) {
		allHbEdges |= it->second;
	}
	for (auto it = allHbEdges.begin(); it != allHbEdges.end(); it++) {
		happensBeforeEdge *hb = *it;
		if (hb->sideCondition) {
			emit_validation(f, "msg_filter", hb->msg_id, "filt",
					hb->sideCondition, slots);
		}
		fprintf(f, "static struct msg_template msg_template_%x_tx;\n", hb->msg_id);
		fprintf(f, "static struct msg_template msg_template_%x_rx = {\n", hb->msg_id);
		fprintf(f, "    .msg_id = 0x%x,\n", hb->msg_id);
		fprintf(f, "    .event_count = 0,\n");
		fprintf(f, "    .pair = &msg_template_%x_tx,\n", hb->msg_id);
		if (hb->sideCondition) {
			fprintf(f, "    .side_condition = msg_filter_%d_filt,\n",
				hb->msg_id);
		}
		fprintf(f, "    .payload_size = %zd,\n", hb->content.size());
		fprintf(f, "    .payload = {");
		for (auto it = hb->content.begin(); !it.finished(); it.advance()) {
			if (it.started()) {
				fprintf(f, ", ");
			}
			fprintf(f, "%d", slots(it.get()).idx);
		}
		fprintf(f, "}\n};\n");
		fprintf(f, "static struct msg_template msg_template_%x_tx = {\n", hb->msg_id);
		fprintf(f, "    .msg_id = 0x%x,\n", hb->msg_id);
		fprintf(f, "    .event_count = 0,\n");
		fprintf(f, "    .pair = &msg_template_%x_rx,\n", hb->msg_id);
		fprintf(f, "    .payload_size = %zd,\n", hb->content.size());
		fprintf(f, "    .payload = {");
		for (auto it = hb->content.begin(); !it.finished(); it.advance()) {
			if (it.started()) {
				fprintf(f, ", ");
			}
			fprintf(f, "%d", slots(it.get()).idx);
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
		if (it->second.has_after_regs)
			fprintf(f, "        .after_regs = instr_%d_after_regs,\n", it->first);
		else
			fprintf(f, "        .after_regs = NULL,\n");
		if (it->second.has_after_control_flow)
			fprintf(f, "        .after_control_flow = instr_%d_after_control_flow,\n", it->first);
		else
			fprintf(f, "        .after_control_flow = NULL,\n");
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
	loadCrashEnforcementData(&scopes.bools, ced, ms->addressSpace, fd);
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

/* For reasons which aren't terribly clear, the linker won't pick up
   nf.o unless there's a reference to it in this file.  Make sure
   there is one. */
void
force_linkage()
{
	NF_Term foo;
	foo.prettyPrint(stdout, "");
}
