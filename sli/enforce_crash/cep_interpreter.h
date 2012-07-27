#ifndef CED_INTERPRETER_H__
#define CED_INTERPRETER_H__

typedef int cfg_label_t;

typedef int simslot_t;
struct cfg_instr_msg {
	int msg_id;
	unsigned payload_size;
	const simslot_t payload[];
};

struct cfg_instr_stash {
	int reg;
	simslot_t slot;
};

struct cfg_instr {
	unsigned long rip;
	const unsigned char *content;
	unsigned content_sz;
	const cfg_label_t *successors;
	int nr_successors;
	const struct cfg_instr_stash *stash;
	int nr_stash;
	const struct cfg_instr_msg *rx_msg;
	int nr_rx_msg;
	const struct cfg_instr_msg *tx_msg;
	int nr_tx_msg;
};

struct cep_entry_ctxt {
	cfg_label_t cfg_label;
	unsigned nr_stack_slots;
	struct {
		unsigned offset;
		unsigned long expected_value;
	} stack[];
};
struct cep_entry_point {
	unsigned long orig_rip;
	unsigned nr_entry_ctxts;
	const struct cep_entry_ctxt *ctxts[];
};
struct crash_enforcement_plan {
	int nr_entry_points;
	const struct cep_entry_point **entry_points;
	int nr_cfg_nodes;
	const struct cfg_instr *cfg_nodes;
};

extern const struct crash_enforcement_plan plan;
extern const char program_to_patch[];

#endif /* !CED_INTERPRETER_H__ */
