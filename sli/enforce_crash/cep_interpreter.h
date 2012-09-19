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
	bct_float,
	bct_double,
	bct_v128
};
enum byte_code_op {
	bcop_push_const,
	bcop_push_slot,

	/* Binary ops */
	bcop_cmp_eq,
	bcop_cmp_ltu,
	bcop_add,
	bcop_shl,

	/* Unary ops */
	bcop_not,
	bcop_sign_extend64,

	/* Specials */
	bcop_load,
	bcop_badptr,

	bcop_fail_if,
	bcop_succeed,
};

struct msg_template {
	int msg_id;
	unsigned payload_size;

	/* The number of times this message has been sent (for TX
	   templates) or received (for RX templates).  This isn't
	   really part of the CEP, since it's run-time rather than
	   compile-time, but this is the most convenient place to
	   stash it. */
	int event_count;

	/* For RX templates, this is the matching TX template.  For TX
	   templates, it's the matching RX one. */
	struct msg_template *pair;
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
	struct msg_template *rx_msg;
	struct msg_template *tx_msg;
	/* Side conditions can be evaluated at one of three points:

	   -- At the very beginning of the instruction.
	   -- Just after receiving a message.
	   -- Just after evaluating the original instruction.
	*/
	const unsigned short *pre_validate;
	const unsigned short *rx_validate;
	const unsigned short *eval_validate;

	const char *id; /* Just for debug */
};

struct cep_entry_ctxt {
	cfg_label_t cfg_label;
	unsigned nr_simslots;
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
	int base_msg_id;
	int msg_id_limit;
};

#define mk_flex_array(name)						\
	struct name ## _array {						\
		int sz;							\
		int allocated;						\
		struct name **content;					\
	};								\
	void name ## _push(struct name ## _array *arr,			\
			   struct name *elem)				\
	{								\
		if (arr->sz == arr->allocated) {			\
			arr->allocated += 8;				\
			arr->content = realloc(				\
				arr->content,				\
				sizeof(arr->content[0])*arr->allocated); \
		}							\
		arr->content[arr->sz] = elem;				\
		arr->sz++;						\
	}								\
	void name ## _erase_first(struct name ## _array *arr,		\
				  struct name *elem)			\
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
			abort();					\
		}							\
	}								\
	void name ## _erase_idx(struct name ## _array *arr,		\
				int idx)				\
	{								\
		assert(idx < arr->sz);					\
		assert(idx >= 0);					\
		memmove(arr->content + idx,				\
			arr->content + idx + 1,				\
			sizeof(arr->content[0]) * (arr->sz - idx - 1));	\
		arr->sz--;						\
	}								\
	void name ## _arr_cleanup(struct name ## _array *arr)		\
	{								\
		free(arr->content);					\
	}								\
	void name ## _arr_swizzle(struct name ## _array *dest,		\
				  struct name ## _array *src)		\
	{								\
		int i;							\
		for (i = 0; i < dest->sz; i++)				\
			assert(dest->content[i] == NULL);		\
		free(dest->content);					\
		*dest = *src;						\
		memset(src, 0, sizeof(*src));				\
	}

extern const struct crash_enforcement_plan plan;
extern const char program_to_patch[];

#endif /* !CED_INTERPRETER_H__ */
