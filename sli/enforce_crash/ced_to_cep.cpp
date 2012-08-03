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
expressionDependsOn(IRExpr *what, const std::set<IRExprGet *> &d, bool includeRegisters)
{
	struct : public IRExprTransformer {
		bool res;
		const std::set<IRExprGet *> *d;
		bool includeRegisters;
		IRExpr *transformIex(IRExprGet *e) {
			if (e->reg.isReg() && !includeRegisters)
				return e;
			if (d->count(e))
				res = true;
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
max_simslot(const AbstractThread &tid, const slotMapT &sm)
{
	int res = 0;
	for (auto it = sm.begin(); it != sm.end(); it++)
		if (it->first.first == tid &&
		    it->second.idx > res)
			res = it->second.idx;
	return res;
}

static void
compute_entry_point_list(crashEnforcementData &ced, FILE *f, const CfgRelabeller &cfgLabels, const char *ident)
{
	std::map<ThreadCfgLabel, int> ctxts;
	{
		int next_idx;
		next_idx = 1;
		for (auto it = ced.roots.begin();
		     it != ced.roots.end();
		     it++) {
			ThreadCfgLabel l(*it);
			if (!ctxts.count(l))
				ctxts[l] = next_idx++;
		}
	}
	for (auto it = ctxts.begin(); it != ctxts.end(); it++) {
		ThreadCfgLabel l(it->first);
		CFGNode *n = ced.crashCfg.findInstr(l);
		VexRip v(n->rip);
		fprintf(f, "static const struct cep_entry_ctxt entry_ctxt%d = {\n", it->second);
		fprintf(f, "    .cfg_label = %d,\n", cfgLabels(it->first));
		fprintf(f, "    .nr_simslots = %d,\n", max_simslot(l.thread, ced.exprsToSlots) + 1);
		fprintf(f, "    .nr_stack_slots = %zd,\n", v.stack.size() - 1);
		fprintf(f, "    .stack = {\n");
#warning need to actually calculate the offsets for stack validation
		for (unsigned x = 1; x < v.stack.size(); x++)
			fprintf(f,
				"        { .offset = 99, .expected_value = 0x%lx },\n",
				v.stack[x]);
		fprintf(f, "    },\n");
		fprintf(f, "};\n");
	}
	std::map<unsigned long, std::set<ThreadCfgLabel> > entryPoints;
	for (auto it = ced.roots.begin(); it != ced.roots.end(); it++) {
		ThreadCfgLabel l(*it);
		CFGNode *n = ced.crashCfg.findInstr(l);
		VexRip v(n->rip);
		entryPoints[v.unwrap_vexrip()].insert(l);
	}
	int next_idx = 0;
	for (auto it = entryPoints.begin(); it != entryPoints.end(); it++) {
		fprintf(f, "static const struct cep_entry_point __entry_point%d = {\n", next_idx++);
		fprintf(f, "    .orig_rip = 0x%lx,\n", it->first);
		fprintf(f, "    .nr_entry_ctxts = %zd,\n", it->second.size());
		fprintf(f, "    .ctxts = {\n");
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
			fprintf(f, "        &entry_ctxt%d,\n", ctxts[*it2]);
		fprintf(f, "   },\n");
		fprintf(f, "};\n");
	}

	next_idx = 0;
	fprintf(f, "static const struct cep_entry_point *%s[] = {\n", ident);
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
bytecode_eval_expr(FILE *f, IRExpr *expr, const AbstractThread &thread, crashEnforcementData &ced)
{
	switch (expr->tag) {
	case Iex_Const: {
		IRExprConst *iec = (IRExprConst *)expr;
		switch (iec->con->tag) {
		case Ico_U32:
			bytecode_op(f, "push_const", Ity_I32);
			bytecode_const32(f, iec->con->Ico.U32);
			break;
		case Ico_U64:
			bytecode_op(f, "push_const", Ity_I64);
			bytecode_const64(f, iec->con->Ico.U64);
			break;
		default:
			abort();
		}
		break;
	}
	case Iex_Get: {
		IRExprGet *ieg = (IRExprGet *)expr;
		simulationSlotT slot = ced.exprsToSlots(thread, ieg);
		bytecode_op(f, "push_slot", ieg->ty);
		bytecode_const32(f, slot.idx);
		break;
	}

	case Iex_Binop: {
		IRExprBinop *ieb = (IRExprBinop *)expr;
		bytecode_eval_expr(f, ieb->arg1, thread, ced);
		bytecode_eval_expr(f, ieb->arg2, thread, ced);
		switch (ieb->op) {
		case Iop_CmpEQ32:
			bytecode_op(f, "cmp_eq", Ity_I32);
			break;
		case Iop_CmpEQ64:
			bytecode_op(f, "cmp_eq", Ity_I64);
			break;
		default:
			abort();
		}
		break;
	}

	case Iex_Associative: {
		IRExprAssociative *iea = (IRExprAssociative *)expr;
		assert(iea->nr_arguments != 0);
		bytecode_eval_expr(f, iea->contents[0], thread, ced);
		for (int i = 1; i < iea->nr_arguments; iea++) {
			bytecode_eval_expr(f, iea->contents[i], thread, ced);
			switch (iea->op) {
			case Iop_Add64:
				bytecode_op(f, "add", iea->type());
				break;
			default:
				abort();
			}
		}
		break;
	}
	case Iex_Load: {
		IRExprLoad *iel = (IRExprLoad *)expr;
		bytecode_eval_expr(f, iel->addr, thread, ced);
		bytecode_op(f, "load", iel->ty);
		break;
	}
	default:
		abort();
	}
}

static void
emit_validation(FILE *f, int ident, const char *name, const std::set<exprEvalPoint> &condition, const AbstractThread &thread, crashEnforcementData &ced)
{
	fprintf(f, "static const unsigned short instr_%d_%s[] = {\n", ident, name);
	for (auto it = condition.begin();
	     it != condition.end();
	     it++) {
		bytecode_eval_expr(f, it->e, thread, ced);
		if (!it->invert)
			bytecode_op(f, "not", Ity_I1);
		fprintf(f, "    (unsigned short)bcop_fail_if,\n");
	}
	fprintf(f, "    (unsigned short)bcop_succeed\n};\n");
}

struct cfg_annotation_summary {
	bool have_stash;
	unsigned tx_msg;
	unsigned rx_msg;
	unsigned long rip;
	bool has_pre_validate;
	bool has_rx_validate;
	bool has_eval_validate;
};

static void
dump_annotated_cfg(crashEnforcementData &ced, FILE *f, CfgRelabeller &relabeller, const char *ident)
{
	{
		std::queue<ThreadCfgLabel> pending;
		for (auto it = ced.roots.begin(); it != ced.roots.end(); it++)
			pending.push(*it);
		while (!pending.empty()) {
			ThreadCfgLabel l(pending.front());
			pending.pop();
			if (!relabeller.label(l))
				continue;
			CFGNode *n = ced.crashCfg.findInstr(l);
			for (auto it = n->successors.begin(); it != n->successors.end(); it++) {
				if (it->instr)
					pending.push(ThreadCfgLabel(l.thread, it->instr->label));
			}
		}
	}

	std::map<int, cfg_annotation_summary> summaries;

	/* Now go through and generate plan-level representations for those. */
	/* Ancillary data first: the content of the instruction, plus
	 * any necessary annotations. */
	for (auto it = relabeller.content.begin(); it != relabeller.content.end(); it++) {
		ThreadCfgLabel oldLabel(it->first);
		int newLabel(it->second);

		CFGNode *instr = ced.crashCfg.findInstr(oldLabel);
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
			const std::set<IRExprGet *> &toStash(ced.exprStashPoints[oldLabel]);
			fprintf(f, "static const struct cfg_instr_stash instr_%d_stash[] = {\n", newLabel);
			for (auto it2 = toStash.begin(); it2 != toStash.end(); it2++) {
				IRExprGet *e = *it2;
				simulationSlotT simSlot(ced.exprsToSlots(oldLabel.thread, e));
				fprintf(f, "    { .reg = %d, .slot = %d },\n",
					e->reg.isReg() ? RegisterIdx::fromVexOffset(e->reg.asReg()).idx : -1,
					simSlot.idx);
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
				if (hb->after == oldLabel) {
					rxMsg.insert(hb);
				} else {
					assert(hb->before == oldLabel);
					txMsg.insert(hb);
				}
			}
			assert(!(rxMsg.empty() && txMsg.empty()));
			if (!rxMsg.empty()) {
				assert(rxMsg.size() == 1);
				summary.rx_msg = (*rxMsg.begin())->msg_id;
			}
			if (!txMsg.empty()) {
				assert(txMsg.size() == 1);
				summary.tx_msg = (*txMsg.begin())->msg_id;
			}
		}
		if (ced.expressionEvalPoints.count(oldLabel)) {
			const std::set<exprEvalPoint> &sideConditions(ced.expressionEvalPoints[oldLabel]);
			std::set<exprEvalPoint> pre_validate, rx_validate, eval_validate;
			std::set<IRExprGet *> rxed, stashed;
			if (ced.happensBeforePoints.count(oldLabel)) {
				const std::set<happensBeforeEdge *> &hbEdges(ced.happensBeforePoints[oldLabel]);
				for (auto it2 = hbEdges.begin(); it2 != hbEdges.end(); it2++) {
					happensBeforeEdge *hb = *it2;
					if (hb->after == oldLabel) {
						for (unsigned x = 0; x < hb->content.size(); x++)
							rxed.insert(hb->content[x]);
					}
				}
			}
			if (ced.exprStashPoints.count(oldLabel)) {
				const std::set<IRExprGet *> &toStash(ced.exprStashPoints[oldLabel]);
				for (auto it2 = toStash.begin(); it2 != toStash.end(); it2++)
					stashed.insert(*it2);
			}
			/* We need to decide where in the instruction
			   cycle to evaluate this side-condition.  The
			   options are at the very start, during
			   message RX, or after performing the stash,
			   and we pick the earliest point at which we
			   have all necessary information. */
			/* (The instruction cycle always does RX
			   before stash.) */
			for (auto it = sideConditions.begin();
			     it != sideConditions.end();
			     it++) {
				if (expressionDependsOn(it->e, stashed, false))
					eval_validate.insert(*it);
				else if (expressionDependsOn(it->e, rxed, true))
					rx_validate.insert(*it);
				else
					pre_validate.insert(*it);
			}
			assert(!(pre_validate.empty() && rx_validate.empty() && eval_validate.empty()));
			if (!pre_validate.empty()) {
				summary.has_pre_validate = true;
				emit_validation(f, newLabel, "pre_validate", pre_validate, oldLabel.thread, ced);
			}
			if (!rx_validate.empty()) {
				summary.has_rx_validate = true;
				emit_validation(f, newLabel, "rx_validate", rx_validate, oldLabel.thread, ced);
			}
			if (!eval_validate.empty()) {
				summary.has_eval_validate = true;
				emit_validation(f, newLabel, "eval_validate", eval_validate, oldLabel.thread, ced);
			}
		}

		summary.rip = instr->rip.unwrap_vexrip();
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
		AbstractThread beforeTid = hb->before.thread;
		AbstractThread afterTid = hb->after.thread;
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
			fprintf(f, "%d", ced.exprsToSlots(afterTid, hb->content[x]).idx);
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
			fprintf(f, "%d", ced.exprsToSlots(beforeTid, hb->content[x]).idx);
		}
		fprintf(f, "}\n};\n");
	}

	/* Now dump out the actual CFG table. */
	fprintf(f, "static const struct cfg_instr %s[] = {\n", ident);
	for (auto it = summaries.begin(); it != summaries.end(); it++) {
		if (it == summaries.begin())
			fprintf(f, "    [%d] = {\n", it->first);
		else
			fprintf(f, "    }, [%d] = {\n", it->first);
		fprintf(f, "        .rip = 0x%lx,\n", it->second.rip);
		add_simple_array(f, "        ", "content", "content", "content_sz", it->first);
		add_simple_array(f, "        ", "successors", "successors", "nr_successors", it->first);
		if (it->second.have_stash)
			add_simple_array(f, "        ", "stash", "stash", "nr_stash", it->first);
		else
			add_empty_array(f, "        ", "stash", "nr_stash");
		if (it->second.rx_msg)
			fprintf(f, "        .rx_msg = &msg_template_%x_rx,\n", it->second.rx_msg);
		else
			fprintf(f, "        .rx_msg = NULL,\n");
		if (it->second.tx_msg)
			fprintf(f, "        .tx_msg = &msg_template_%x_tx,\n", it->second.tx_msg);
		else
			fprintf(f, "        .tx_msg = NULL,\n");
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
	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(binary));

	int fd = open(ced_path, O_RDONLY);
	if (fd < 0)
		err(1, "open(%s)", ced_path);
	crashEnforcementData ced(false);
	loadCrashEnforcementData(ced, ms->addressSpace, fd);
	close(fd);

	CfgRelabeller relabeller;

	fprintf(stdout, "#include \"cep_interpreter.h\"\n");
	fprintf(stdout, "#include <stddef.h>\n"); /* For NULL */
	fprintf(stdout, "\n");
	dump_annotated_cfg(ced, stdout, relabeller, "__cfg_nodes");
	compute_entry_point_list(ced, stdout, relabeller, "__entry_points");
	fprintf(stdout, "const struct crash_enforcement_plan plan = {\n");
	fprintf(stdout, "    .entry_points = __entry_points,\n");
	fprintf(stdout, "    .nr_entry_points = sizeof(__entry_points)/sizeof(__entry_points[0]),\n");
	fprintf(stdout, "    .cfg_nodes = __cfg_nodes,\n");
	fprintf(stdout, "    .nr_cfg_nodes = sizeof(__cfg_nodes)/sizeof(__cfg_nodes[0]),\n");
	fprintf(stdout, "    .base_msg_id = 0x%x,\n", lowest_msg_id(ced));
	fprintf(stdout, "    .msg_id_limit = 0x%x,\n", highest_msg_id(ced) + 1);
	fprintf(stdout, "};\n");

	fprintf(stdout, "\n");
	fprintf(stdout,
		"const char program_to_patch[] = \"%s\";\n",
		realpath(binary,NULL));
	return 0;
}
