#ifndef CED_INTERPRETER_H__
#define CED_INTERPRETER_H__

typedef int cfg_label_t;
typedef int simslot_t;

/* Top four bits of a byte code op are a type tag, the rest are the
   operation to perform. */
#define bytecode_type_shift 12
#define bytecode_op(x) ((x) & 0xfff)
#define bytecode_type(x) (((x) >> bytecode_type_shift) & 0xf)
enum byte_code_type {
	bct_bit,
	bct_byte,
	bct_short,
	bct_int,
	bct_long,
	bct_longlong,
};
enum byte_code_op {
	bcop_push_const,
	bcop_push_slot,

	/* Binary ops */
	bcop_cmp_eq,
	bcop_cmp_ltu,
	bcop_cmp_lts,
	bcop_add,
	bcop_and,
	bcop_or,
	bcop_xor,
	bcop_mul,
	bcop_shl,
	bcop_shr,
	bcop_sar,

	bcop_divS,
	bcop_modS,
	bcop_divU,
	bcop_modU,

	bcop_mullU64,

	/* Unary ops */
	bcop_not,
	bcop_neg,
	bcop_sign_extend32,
	bcop_sign_extend64,
	/* Zero extend ops are somewhat misnamed: they convert the
	   argument the appropriate number of bits.  If that's an
	   upcast then they zero extend, but they also work for
	   downcasts, which aren't really extends at all. */
	bcop_zero_extend8,
	bcop_zero_extend16,
	bcop_zero_extend32,
	bcop_zero_extend64,

	bcop_discard,

	bcop_swap,
	bcop_dupe,

	/* Specials */
	bcop_load,
	bcop_badptr,

	/* Two-way conditional branch.  Takes the top thing on the
	   stack, which must be a bct_bit, and two immediate
	   arguments.  The immediate arguments are offsets into the
	   current bytecode program.  If the bit is one we jump to the
	   first offset and if the bit is zero we jump to the second
	   one. */
	bcop_branch,
	bcop_fail,
	bcop_succeed,
};

struct msg_template {
	int msg_id;

	/* The number of times this message has been sent (for TX
	   templates) or received (for RX templates).  This isn't
	   really part of the CEP, since it's run-time rather than
	   compile-time, but this is the most convenient place to
	   stash it. */
	int event_count;

	/* A flag saying whether anyone is currently waiting for this
	   message, since we probably want to avoid adding more
	   threads to it. */
	int busy;

	const unsigned short *side_condition;

	/* For RX templates, this is the matching TX template.  For TX
	   templates, it's the matching RX one. */
	struct msg_template *pair;
};

struct cfg_instr_stash {
	int reg;
	simslot_t slot;
};

struct cfg_instr_set_entry {
	simslot_t slot;
	int set; /* 1 to set, 0 to clear */
};

struct cfg_instr_set_control {
	int next_node;
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
	const struct cfg_instr_set_entry *set_entry;
	int nr_set_entry;
	const struct cfg_instr_set_control *set_control;
	int nr_set_control;
	int nr_rx_msg;
	struct msg_template **rx_msgs;
	int nr_tx_msg;
	struct msg_template **tx_msgs;

	/* Side condition checking points */
	const unsigned short *after_regs;
	const unsigned short *after_control_flow;

	const char *id; /* Just for debug */
	int cntr;
};

struct cep_entry_ctxt {
	cfg_label_t cfg_label;
	unsigned nr_simslots;
	unsigned nr_stack_slots;
	int cntr;
	long rsp_delta;
	struct {
		unsigned offset;
		unsigned long expected_value;
	} stack[];
};
struct cep_entry_point {
	unsigned long orig_rip;
	unsigned nr_entry_ctxts;
	struct cep_entry_ctxt *ctxts[];
};
struct crash_enforcement_plan {
	int nr_entry_points;
	struct cep_entry_point **entry_points;
	int nr_cfg_nodes;
	struct cfg_instr *cfg_nodes;
	int base_msg_id;
	int msg_id_limit;
	int nr_patch_points;
	const unsigned long *patch_points;
	int nr_force_interpret;
	const unsigned long *force_interpret;
};

#define mk_flex_array(name)						\
	struct name ## _array {						\
		int sz;							\
		int allocated;						\
		struct name **content;					\
	};								\
	static void name ## _push(struct name ## _array *arr,		\
				  struct name *elem)			\
	{								\
		if (arr->sz == arr->allocated) {			\
			arr->allocated += 8;				\
			arr->content = cep_realloc(			\
				arr->content,				\
				sizeof(arr->content[0])*arr->allocated); \
		}							\
		arr->content[arr->sz] = elem;				\
		arr->sz++;						\
	}								\
	static void name ## _erase_first(struct name ## _array *arr,	\
					 struct name *elem)		\
	{								\
		int i;							\
		for (i = 0; i < arr->sz; i++) {				\
			if (arr->content[i] == elem) {			\
				memmove(arr->content + i,		\
					arr->content + i + 1,		\
					sizeof(arr->content[0]) * (arr->sz - i - 1)); \
				arr->sz--;				\
				return;					\
			}						\
		}							\
		abort();						\
	}								\
	static void name ## _erase_idx(struct name ## _array *arr,	\
				       int idx)				\
	{								\
		assert(idx < arr->sz);					\
		assert(idx >= 0);					\
		memmove(arr->content + idx,				\
			arr->content + idx + 1,				\
			sizeof(arr->content[0]) * (arr->sz - idx - 1));	\
		arr->sz--;						\
	}								\
	static void name ## _arr_cleanup(struct name ## _array *arr)	\
	{								\
		cep_free(arr->content);					\
	}								\
	static void name ## _arr_swizzle(struct name ## _array *dest,	\
					 struct name ## _array *src)	\
	{								\
		int i;							\
		for (i = 0; i < dest->sz; i++)				\
			assert(dest->content[i] == NULL);		\
		cep_free(dest->content);				\
		*dest = *src;						\
		memset(src, 0, sizeof(*src));				\
	}

extern const struct crash_enforcement_plan plan;
extern const char program_to_patch[];

#endif /* !CED_INTERPRETER_H__ */
