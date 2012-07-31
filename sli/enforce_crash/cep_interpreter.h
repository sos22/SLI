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
		free(dest->content);					\
		*dest = *src;						\
		memset(src, 0, sizeof(*src));				\
	}

extern const struct crash_enforcement_plan plan;
extern const char program_to_patch[];

#endif /* !CED_INTERPRETER_H__ */
