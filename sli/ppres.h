#define FOOTSTEP_REG_0_NAME XMM0
#define FOOTSTEP_REG_0_OFFSET 200
#define FOOTSTEP_REG_1_NAME XMM1
#define FOOTSTEP_REG_1_OFFSET 216
#define FOOTSTEP_REG_2_NAME XMM0b
#define FOOTSTEP_REG_2_OFFSET 208
#define FOOTSTEP_REG_3_NAME CC_NDEP
#define FOOTSTEP_REG_3_OFFSET 152
#define FOOTSTEP_REG_4_NAME RAX
#define FOOTSTEP_REG_4_OFFSET 0

#ifndef FOOTSTEP_REGS_ONLY

#define RECORD_BLOCK_SIZE 16384
#define MAX_RECORD_SIZE 4096

struct record_header {
	unsigned cls;
	unsigned size;
	unsigned tid;
};

template<typename ait>
struct footstep_record {
#define RECORD_footstep 1
	ait rip;
	ait FOOTSTEP_REG_0_NAME;
	ait FOOTSTEP_REG_1_NAME;
	ait FOOTSTEP_REG_2_NAME;
	ait FOOTSTEP_REG_3_NAME;
	ait FOOTSTEP_REG_4_NAME;
};

template<typename ait>
struct syscall_record {
#define RECORD_syscall 2
	ait syscall_nr;
	SysRes syscall_res;
	ait arg1;
	ait arg2;
	ait arg3;
};

template<typename ait>
struct memory_record {
#define RECORD_memory 3
	ait ptr;
	/* Followed by lots more data */
};

template<typename ait>
struct rdtsc_record {
#define RECORD_rdtsc 4
	ait stashed_tsc;
};

template<typename ait>
struct mem_read_record {
#define RECORD_mem_read 5
	ait ptr;
	/* Followed by the data */
};

template<typename ait>
struct mem_write_record {
#define RECORD_mem_write 6
	ait ptr;
	/* Followed by the data */
};

/* No payload data */
#define RECORD_new_thread 7

/* No payload */
#define RECORD_thread_blocking 8

/* No payload */
#define RECORD_thread_unblocked 9

template<typename ait>
struct client_req_record {
#define RECORD_client 10
	ait flavour;
};

template<typename ait>
struct signal_record {
#define RECORD_signal 11
	ait rip;
	Int signo;
	ait err;
	ait virtaddr;
};

template<typename ait>
struct allocate_memory_record {
#define RECORD_allocate_memory 12
	ait start;
	ait size;
	ait prot;
	UWord flags;
};

/* Uses VexGuestAMD64State as payload */
#define RECORD_initial_registers 13

template<typename ait>
struct initial_brk_record {
#define RECORD_initial_brk 14
	ait initial_brk;
};

template<typename ait>
struct initial_sighandlers_record {
#define RECORD_initial_sighandlers 15
	sigaction_t handlers[64];
};

template<typename ait>
struct vex_thread_state_record_1 {
#define RECORD_vex_thread_state_1 16
	unsigned statement_nr;
	ait temporaries[0];
};

template<typename ait>
struct vex_thread_state_record_2 {
#define RECORD_vex_thread_state_2 17
	unsigned statement_nr;
	ait translation_origin;
	ait temporaries[0];
};

#define RECORD_MAX_CLASS RECORD_vex_thread_state_2


struct index_record {
	unsigned long record_nr;
	unsigned long offset_in_file;
};

static inline int
IS_STACK(const void *ptr, unsigned long rsp)
{
	if ((unsigned long)ptr < (unsigned long)rsp - 128 ||
	    (unsigned long)ptr > (unsigned long)rsp + 16384)
		return False;
	else
		return True;
}

#endif /* !FOOTSTEP_REGS_ONLY */
