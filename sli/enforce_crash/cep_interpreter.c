/* An interpreter for crash enforcement plans.  This gets loaded into
   the target program andis then responsible for driving the program
   along the CEP. */
#include "cep_interpreter.h"

#include <asm/prctl.h>
#include <linux/futex.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/mman.h>
#include <assert.h>
#include <err.h>
#include <errno.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* Define _PAGE_SIZE and _STACK_SIZE which don't include the ul
 * suffix, because that makes it easier to use them in inline
 * assembly. */
#define _PAGE_SIZE 4096
#define _STACK_SIZE (_PAGE_SIZE * 4)
#define PAGE_SIZE 4096ul
#define STACK_SIZE (PAGE_SIZE * 4)
#define PAGE_MASK (~(PAGE_SIZE - 1))
#define MAX_DELAY_US (100000)

extern void clone(void);
static void (*__GI__exit)(int res);
void arch_prctl(int, unsigned long);
static void clone_hook_c(int (*fn)(void *), void *fn_arg) __attribute__((unused));

/* For some reason, if this is non-static, gcc generates a very odd
   relocation for it, and we fail.  I don't understand why, or why the
   other things defined in assembly aren't affected, so just accept it
   for now and ignore the compiler warnings. */
static void clone_hook_asm();

typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
typedef unsigned long uint64_t;

#define BOUND_LLS_EXITED ((struct low_level_state *)1)

struct low_level_state {
	int refcount; /* HLS holds a reference. */

	cfg_label_t cfg_node;

	int nr_simslots;

	int last_operation_is_send;
	int await_bound_lls_exit;

	struct high_level_state *hls;

	/* Once we've received a message from an LLS, we become bound
	 * to that LLS and in future will only receive messages from
	 * them.  Can be BOUND_LLS_EXITED if we've bound to a thread
	 * which has since exited, in which case all message receives
	 * will fail. */
	struct low_level_state *bound_lls;

	struct msg_template *bound_sending_message;
	struct msg_template *unbound_sending_message;
	struct msg_template *bound_receiving_message;
	struct msg_template *unbound_receiving_message;

	unsigned long simslots[];
};
mk_flex_array(low_level_state);

struct high_level_state {
	struct low_level_state_array ll_states;
};

#define __DECL_REG(name) union {		\
		uint64_t r ## name, e ## name;	\
		uint32_t _e ## name;		\
	}
struct reg_struct {
	__DECL_REG(ip);
	__DECL_REG(ax);
	__DECL_REG(dx);
	__DECL_REG(cx);
	__DECL_REG(bx);
	__DECL_REG(bp);
	__DECL_REG(si);
	__DECL_REG(di);
	unsigned long r8;
	unsigned long r9;
	unsigned long r10;
	unsigned long r11;
	unsigned long r12;
	unsigned long r13;
	unsigned long r14;
	unsigned long r15;
	__DECL_REG(flags);
	__DECL_REG(sp);
};

/* All of the state which we need to maintain for each physical client
 * thread.  Pointed to by GS_BASE. */
struct per_thread_state {
	/* The initial interpreter rsp is the rsp field of
	   client_regs.  The trampoline will transition to this stack,
	   push all the other registers, and then jump into the
	   interpreter proper, so we end up with the interpreter
	   running on the interpreter stack and the client regs
	   stashed in client_regs. */
	unsigned long initial_interpreter_rsp;
	/* -16 rather than the more obvious -8 because that gives us
            better stack alignment. */
	unsigned char interpreter_stack[STACK_SIZE - 16 - sizeof(struct reg_struct)];
	struct reg_struct client_regs;
};

static struct low_level_state_array message_senders;
static struct low_level_state_array message_receivers;

typedef void exit_routine_t(struct reg_struct *);
static exit_routine_t *find_exit_stub(unsigned long rip);

static int
have_cloned;

static int
big_lock;

#define debug(fmt, ...) printf("%d:%f: " fmt, gettid(), now(), ##__VA_ARGS__)

static int
gettid(void)
{
	return syscall(__NR_gettid);
}
static double
now(void)
{
	static double start;
	struct timeval t;
	double res;
	gettimeofday(&t, NULL);
	res = t.tv_sec + t.tv_usec * 1e-06;
	if (start == 0)
		start = res;
	return res - start;
}

static void
sanity_check_low_level_state(const struct low_level_state *lls, int expected_present)
{
	int i;
	int present;
	assert(lls->refcount > 0);
	assert(lls->hls);
	if (lls->bound_lls && lls->bound_lls != BOUND_LLS_EXITED) {
		assert(lls->bound_lls->bound_lls == lls);
		assert(lls->bound_lls->hls != lls->hls);
	}
	present = 0;
	for (i = 0; i < lls->hls->ll_states.sz; i++)
		if (lls->hls->ll_states.content[i] == lls)
			present++;
	assert(present == expected_present);
}

static void
sanity_check_high_level_state(const struct high_level_state *hls)
{
	int i;
	assert(hls->ll_states.sz >= 0);
	assert(hls->ll_states.sz <= hls->ll_states.allocated);
	for (i = 0; i < hls->ll_states.sz; i++) {
		assert(hls->ll_states.content[i]);
		sanity_check_low_level_state(hls->ll_states.content[i], 1);
	}
}

/* Allocate some memory which can be both written and executed.  Used
 * to build trampolines and so forth. */
static void *
alloc_executable(size_t sz)
{
	static void *cur_region;
	static size_t region_avail;
	void *ptr;

	assert(sz <= PAGE_SIZE);
	if (region_avail < sz) {
		cur_region =
			mmap(NULL,
			     PAGE_SIZE,
			     PROT_READ|PROT_WRITE|PROT_EXEC,
			     MAP_PRIVATE|MAP_32BIT|MAP_ANONYMOUS|MAP_EXECUTABLE,
			     -1,
			     0);
		region_avail = PAGE_SIZE;
	}
	ptr = cur_region;
	cur_region += sz;
	region_avail -= sz;
	return ptr;
}

static int
__fetch_guest(size_t sz, void *dst, unsigned long addr)
{
#warning should catch the fault here...
	memcpy(dst, (const void *)addr, sz);
	return 1;
}
#define fetch_guest(host_ptr, guest_ptr) __fetch_guest(sizeof(*host_ptr), (void *)host_ptr, guest_ptr)

/* Check whether the current stack matches up with the a CEP entry
 * point. */
static int
ctxt_matches(const struct cep_entry_ctxt *ctxt, const struct reg_struct *regs)
{
	unsigned x;
	for (x = 0; x < ctxt->nr_stack_slots; x++) {
		unsigned long guest_val;
		if (!fetch_guest(&guest_val, regs->rsp + ctxt->stack[x].offset))
			return 0;
		if (guest_val != ctxt->stack[x].expected_value)
			return 0;
	}
	return 1;
}

static struct low_level_state *
new_low_level_state(struct high_level_state *hls, int nr_simslots)
{
	struct low_level_state *lls = calloc(sizeof(struct low_level_state) + nr_simslots * sizeof(lls->simslots[0]), 1);
	lls->refcount = 1;
	lls->nr_simslots = nr_simslots;
	lls->hls = hls;
	sanity_check_low_level_state(lls, 0);
	return lls;
}

static void
start_low_level_thread(struct high_level_state *hls, cfg_label_t starting_label, int nr_simslots)
{
	struct low_level_state *lls = new_low_level_state(hls, nr_simslots);
	lls->cfg_node = starting_label;
	low_level_state_push(&hls->ll_states, lls);
	sanity_check_low_level_state(lls, 1);
}

static void
init_high_level_state(struct high_level_state *hls)
{
	memset(hls, 0, sizeof(*hls));
}

#define cpu_user_regs reg_struct
#include "x86_emulate.h"
#include "x86_emulate.c"
#undef cpu_user_regs

struct cep_emulate_ctxt {
	struct x86_emulate_ctxt ctxt;
	struct high_level_state *hls;
};

static int
emulator_read(enum x86_segment seg,
	      unsigned long offset,
	      void *p_data,
	      unsigned int bytes,
	      struct x86_emulate_ctxt *_ctxt)
{
	/* This is where we'd do load stashes, if we were doing load
	 * stashes. */
	/* XXX should trap any faults here, so that we can set up a
	   correct signal frame. XXX */
	struct cep_emulate_ctxt *ctxt = (struct cep_emulate_ctxt *)_ctxt;
	struct high_level_state *hls = ctxt->hls;
	int i, j;

	assert(seg == x86_seg_ds || seg == x86_seg_ss);
	memcpy(p_data, (const void *)offset, bytes);
	for (i = 0; i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		const struct cfg_instr *instr = &plan.cfg_nodes[lls->cfg_node];
		for (j = 0; j < instr->nr_stash; j++) {
			if (instr->stash[j].reg == -1) {
				assert(bytes <= 8);
				lls->simslots[instr->stash[j].slot] = 0;
				memcpy(&lls->simslots[instr->stash[j].slot],
				       p_data,
				       bytes);
				break;
			}
		}
	}
	return X86EMUL_OKAY;
}

static int
emulator_insn_fetch(enum x86_segment seg,
		    unsigned long offset,
		    void *p_data,
		    unsigned int bytes,
		    struct x86_emulate_ctxt *_ctxt)
{
	struct cep_emulate_ctxt *ctxt = (struct cep_emulate_ctxt *)_ctxt;
	struct high_level_state *hls = ctxt->hls;
	const struct cfg_instr *current_cfg_node;
	int to_copy;
	int i;
	current_cfg_node = NULL;
	for (i = 0; i < hls->ll_states.sz; i++) {
		if (current_cfg_node)
			assert(current_cfg_node->rip == plan.cfg_nodes[hls->ll_states.content[i]->cfg_node].rip);
		else
			current_cfg_node = &plan.cfg_nodes[hls->ll_states.content[i]->cfg_node];
	}
	assert(offset >= current_cfg_node->rip && offset < current_cfg_node->rip + current_cfg_node->content_sz);
	to_copy = current_cfg_node->content_sz - (offset - current_cfg_node->rip);
	if (to_copy > bytes)
		to_copy = bytes;
	memcpy(p_data, current_cfg_node->content + offset - current_cfg_node->rip, to_copy);
	if (to_copy < bytes)
		memset(p_data + to_copy, 0x90, bytes - to_copy);
	return X86EMUL_OKAY;
}

static int
emulator_write(enum x86_segment seg,
	       unsigned long offset,
	       void *p_data,
	       unsigned int bytes,
	       struct x86_emulate_ctxt *ctxt)
{
	/* XXX should trap any faults */
	assert(seg == x86_seg_ds || seg == x86_seg_ss);
	memcpy((void *)offset, (const void *)p_data, bytes);
	return X86EMUL_OKAY;
}

static int
emulator_cmpxchg(enum x86_segment seg,
		 unsigned long offset,
		 void *p_old,
		 void *p_new,
		 unsigned int bytes,
		 struct x86_emulate_ctxt *ctxt)
{
	assert(seg == x86_seg_ds);
	switch (bytes) {
	case 1: {
		unsigned char prev;
		asm("lock cmpxchg %2, %3\n"
		    : "=a" (prev)
		    : "0" (*(unsigned char *)p_old),
		      "r" (*(unsigned char *)p_new),
		      "m" (*(unsigned char *)offset)
		    : "memory"
			);
	}
	default:
		abort();
	}
	return 0;
}

static const struct x86_emulate_ops
emulator_ops = {
	.read = emulator_read,
	.insn_fetch = emulator_insn_fetch,
	.write = emulator_write,
	.cmpxchg = emulator_cmpxchg,
};

static int
cmpxchg(int *what, int oldval, int newval)
{
	int seen;
	if (*what != oldval)
		return *what;
	asm ("lock cmpxchg %3, %1\n"
	     : "=a" (seen), "+m" (*what)
	     : "0" (oldval),
	       "r" (newval)
	     : "memory");
	return seen;
}

static void
store_release(int *what, int val)
{
	*(volatile int *)what = val;
}

static void
acquire_big_lock(void)
{
	while (cmpxchg(&big_lock, 0, 1) != 0)
		;
}
static void
release_big_lock(void)
{
	store_release(&big_lock, 0);
}

static void
release_lls(struct low_level_state *lls)
{
	lls->refcount--;
	if (!lls->refcount)
		free(lls);
}

static struct per_thread_state *
find_pts(void)
{
	unsigned long initial_interpreter_stack;
	struct per_thread_state *res;
	asm("movq %%gs:0, %0\n"
	    : "=r" (initial_interpreter_stack)
		);
	res = (struct per_thread_state *)(initial_interpreter_stack - offsetof(struct per_thread_state, client_regs.rsp));
	assert(res->initial_interpreter_rsp == initial_interpreter_stack);
	return res;
}

static void
exit_interpreter(void)
{
	struct per_thread_state *pts = find_pts();
	exit_routine_t *exit_routine;

	exit_routine = find_exit_stub(pts->client_regs.rip);
	debug("Exit to %lx, rax %lx, rbp %lx\n",
	      pts->client_regs.rip,
	      pts->client_regs.rax,
	      pts->client_regs.rbp);
	release_big_lock();
	exit_routine(&pts->client_regs);
	/* shouldn't get here */
	abort();
}

static void
exit_thread(struct low_level_state *ll)
{
	debug("Exit thread %d\n", ll->cfg_node);
	sanity_check_low_level_state(ll, 0);
	if (ll->bound_lls && ll->bound_lls != BOUND_LLS_EXITED) {
		assert(ll->bound_lls->bound_lls == ll);
		ll->bound_lls->bound_lls = BOUND_LLS_EXITED;
	}
	release_lls(ll);
}

/* Clone an LLS, including duplicating any bound thread. */
static struct low_level_state *
clone_lls(struct low_level_state *lls)
{
	struct low_level_state *new_lls = new_low_level_state(lls->hls, lls->nr_simslots);
	sanity_check_low_level_state(lls, 1);
	new_lls->cfg_node = lls->cfg_node;
	memcpy(new_lls->simslots, lls->simslots, sizeof(new_lls->simslots[0]) * new_lls->nr_simslots);
	new_lls->bound_lls = lls->bound_lls;
	assert(!lls->bound_sending_message);
	assert(!lls->bound_receiving_message);
	assert(!lls->unbound_sending_message);
	assert(!lls->unbound_receiving_message);

	if (lls->bound_lls && lls->bound_lls != BOUND_LLS_EXITED) {
		struct low_level_state *new_bound_lls = new_low_level_state(lls->hls, lls->bound_lls->nr_simslots);
		new_bound_lls->cfg_node = lls->bound_lls->cfg_node;
		new_bound_lls->bound_lls = new_lls;
		new_lls->bound_lls = new_bound_lls;
		memcpy(new_bound_lls->simslots, lls->bound_lls->simslots, sizeof(new_bound_lls->simslots[0]) * new_bound_lls->nr_simslots);
		new_bound_lls->bound_receiving_message = lls->bound_lls->bound_receiving_message;
		new_bound_lls->bound_sending_message = lls->bound_lls->bound_sending_message;

		/* We don't clone unbound_*_messages, or register with
		 * the global sender and receiver arrays, because the
		 * new LLS is bound. */

		low_level_state_push(&new_bound_lls->hls->ll_states, new_bound_lls);
	}

	low_level_state_push(&new_lls->hls->ll_states, new_lls);
	return new_lls;
}

static void
discharge_message(struct low_level_state *tx_lls,
		  struct msg_template *tx_template,
		  struct low_level_state *rx_lls,
		  struct msg_template *rx_template)
{
	int x;

	tx_lls->last_operation_is_send = 1;
	assert(tx_template->pair == rx_template);
	assert(rx_template->pair == tx_template);
	assert(rx_template->payload_size == tx_template->payload_size);
	for (x = 0; x < rx_template->payload_size; x++) {
		assert(rx_template->payload[x] < rx_lls->nr_simslots);
		assert(tx_template->payload[x] < tx_lls->nr_simslots);
		rx_lls->simslots[rx_template->payload[x]] = tx_lls->simslots[tx_template->payload[x]];
	}
}

static void
rendezvous_threads(struct low_level_state_array *llsa,
		   int tx_is_local,
		   struct low_level_state *tx_lls,
		   struct low_level_state *rx_lls)
{
	struct msg_template *rx_template;
	struct msg_template *tx_template;
	int x;

	assert(rx_lls->unbound_receiving_message);
	assert(!rx_lls->unbound_sending_message);
	assert(tx_lls->unbound_sending_message);
	assert(!tx_lls->unbound_receiving_message);

	assert(!rx_lls->bound_receiving_message);
	assert(!rx_lls->bound_sending_message);
	assert(!tx_lls->bound_sending_message);
	assert(!tx_lls->bound_receiving_message);

	rx_template = rx_lls->unbound_receiving_message;
	tx_template = tx_lls->unbound_sending_message;
	assert(rx_template == tx_template->pair);
	assert(tx_template == rx_template->pair);

	/* Note that we don't dupe the message send and receive state
	   here.  That's because we're about to discharge the message
	   operation in both LLSs. */
	/* Possibly slightly surprising: we allow re-binding of
	   threads which have been bound to exited threads.  That's
	   valid because the thread we're binding to is in a message
	   send or receive state, and if it's bound to a dead thread
	   in one of those states it will itself exit shortly.  Given
	   that, there's no point in duplicating it again, and we can
	   just rescue the original thread by re-binding it to
	   ourselves. */
	if (tx_lls->bound_lls || tx_lls->bound_lls == BOUND_LLS_EXITED) {
		/* The transmitting LLS is already bound, so dupe it
		   and bind to the dupe instead. */
		struct low_level_state *dupe_tx_lls;

		assert(tx_lls->bound_lls != rx_lls);

		dupe_tx_lls = new_low_level_state(tx_lls->hls, tx_lls->nr_simslots);
		dupe_tx_lls->cfg_node = tx_lls->cfg_node;
		memcpy(dupe_tx_lls->simslots, tx_lls->simslots, sizeof(dupe_tx_lls->simslots[0]) * tx_lls->nr_simslots);

		tx_lls = dupe_tx_lls;
		if (!tx_is_local)
			low_level_state_push(&tx_lls->hls->ll_states, tx_lls);
		else
			low_level_state_push(llsa, tx_lls);
	}
	if (rx_lls->bound_lls || rx_lls->bound_lls == BOUND_LLS_EXITED) {
		/* We are already bound, so dupe ourselves and have
		   the dupe bind instead. */
		struct low_level_state *dupe_rx_lls;

		assert(rx_lls->bound_lls != tx_lls);

		dupe_rx_lls = new_low_level_state(rx_lls->hls, rx_lls->nr_simslots);
		dupe_rx_lls->cfg_node = rx_lls->cfg_node;
		memcpy(dupe_rx_lls->simslots, rx_lls->simslots, sizeof(dupe_rx_lls->simslots[0]) * rx_lls->nr_simslots);

		rx_lls = dupe_rx_lls;
		if (tx_is_local)
			low_level_state_push(&rx_lls->hls->ll_states, rx_lls);
		else
			low_level_state_push(llsa, rx_lls);
	}

	/* Both LLSs are now unbound, so we can safely bind them
	 * together. */
	rx_lls->bound_lls = tx_lls;
	tx_lls->bound_lls = rx_lls;

	assert(rx_template->payload_size == tx_template->payload_size);
	for (x = 0; x < rx_template->payload_size; x++) {
		assert(rx_template->payload[x] < rx_lls->nr_simslots);
		assert(tx_template->payload[x] < tx_lls->nr_simslots);
		rx_lls->simslots[rx_template->payload[x]] = tx_lls->simslots[tx_template->payload[x]];
	}

	discharge_message(tx_lls, tx_template, rx_lls, rx_template);
}

static void
rendezvous_threads_tx(struct low_level_state_array *llsa,
		      struct low_level_state *tx_lls,
		      struct low_level_state *rx_lls)
{
	sanity_check_low_level_state(rx_lls, 1);
	sanity_check_low_level_state(tx_lls, 1);
	rendezvous_threads(llsa, 1, tx_lls, rx_lls);
}
static void
rendezvous_threads_rx(struct low_level_state_array *llsa,
		      struct low_level_state *rx_lls,
		      struct low_level_state *tx_lls)
{
	sanity_check_low_level_state(rx_lls, 1);
	sanity_check_low_level_state(tx_lls, 1);
	rendezvous_threads(llsa, 0, tx_lls, rx_lls);
}

/* This is quite fiddly.  We have a bunch of low-level threads, some
 * of which want to perform message receive operations.  The threads
 * which don't want to receive anything are unchanged, so ignore them
 * for now and only consider the threads which do need to perform
 * receive operations.
 *
 * There will be at most one receive in each thread.  A receive should
 * define an interval of time (t0, t1) and receive *any* acceptable
 * messages sent in that interval.  If there are no such messages then
 * the thread fails and exits.  If there are multiple such messages
 * the the thread forks so that it can receive all of them.
 *
 * The interval of time is implemented by just checking for acceptable
 * messages at t0, subscribing to them, then delaying for t1-t0,
 * arranging to receive anything which arrives in that time.
 */
/* Caution: this drops the big lock while it's waiting.  The lock is
 * always help when we return, and we require it to be held when we
 * start. */
static void
receive_messages(struct high_level_state *hls)
{
	int i;
	int j;
	int need_delay;
	int have_rx;
	struct low_level_state_array new_llsa;

	/* Quick escape if we don't have anything to receive. */
	have_rx = 0;
	for (i = 0; !have_rx && i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		const struct cfg_instr *instr = &plan.cfg_nodes[lls->cfg_node];
		sanity_check_low_level_state(lls, 1);
		if (!lls->await_bound_lls_exit && instr->rx_msg)
			have_rx = 1;
	}
	if (!have_rx)
		return;

	memset(&new_llsa, 0, sizeof(new_llsa));
	need_delay = 0;
	have_rx = 0;
	for (i = 0; i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		const struct cfg_instr *instr = &plan.cfg_nodes[lls->cfg_node];
		struct msg_template *msg;
		int delay_this_side;

		if (lls->await_bound_lls_exit || !instr->rx_msg) {
			/* Threads which don't receive any messages
			 * don't need to do anything. */
			low_level_state_push(&new_llsa, lls);
			hls->ll_states.content[i] = NULL;
			continue;
		}

		msg = instr->rx_msg;

		if (msg->event_count < msg->pair->event_count) {
			debug("%p: RX %x, delay is on RX side (%d < %d)\n",
			      lls, msg->msg_id, msg->event_count, msg->pair->event_count);
			delay_this_side = 1;
		} else {
			debug("%p: RX %x, delay is on TX side (%d >= %d)\n",
			      lls, msg->msg_id, msg->event_count, msg->pair->event_count);
			delay_this_side = 0;
		}
		msg->event_count++;

		if (lls->bound_lls == BOUND_LLS_EXITED) {
			debug("Receiving from an exited thread -> fail\n");
			hls->ll_states.content[i] = NULL;
			exit_thread(lls);
		} else if (lls->bound_lls != NULL) {
			assert(lls->bound_lls->bound_lls == lls);
			if (lls->bound_lls->bound_sending_message == msg->pair) {
				debug("%p: Receive from bound thread %p\n", lls, lls->bound_lls);
#warning apply message filter here and fail out if the message doesn't match. '
				discharge_message(lls->bound_lls, lls->bound_lls->bound_sending_message,
						  lls, msg);
				lls->bound_lls->bound_sending_message = NULL;
				hls->ll_states.content[i] = NULL;
				low_level_state_push(&new_llsa, lls);
			} else if (lls->bound_lls->bound_sending_message != NULL) {
				debug("%p: Bound thread sent wrong message\n", lls);
				hls->ll_states.content[i] = NULL;
				exit_thread(lls);
			} else {
				debug("%p: Bound thread %p with nothing outstanding; go to RX state\n",
				      lls, lls->bound_lls);
				lls->bound_receiving_message = msg;
				need_delay = 1;
				have_rx = 1;
			}
		} else {
			/* Gather up all of the messages which have
			   already been sent which might be
			   relevant. */
			lls->unbound_receiving_message = msg;
			for (j = 0; j < message_senders.sz; j++) {
				struct low_level_state *tx_lls = message_senders.content[j];
#warning apply message filter here and discard anything which doesn't match. '
				assert(tx_lls->unbound_sending_message);
				if (tx_lls->unbound_sending_message == msg->pair)
					rendezvous_threads_rx(&new_llsa, lls, tx_lls);
			}
			/* And tell any future senders that we're
			 * available. */
			low_level_state_push(&message_receivers, lls);
			have_rx = 1;
			need_delay |= delay_this_side;
		}
	}

	if (!have_rx) {
		/* All receives completed fast.  Yay. */
		debug("All receives completed fast\n");
		low_level_state_arr_swizzle(&hls->ll_states, &new_llsa);
		return;
	}

	if (!need_delay) {
		/* Some receives failed, but we're not allowed to
		 * delay here.  Fail the relevant threads. */
		debug("Received failed, but no delays here\n");
		for (i = 0; i < hls->ll_states.sz; i++) {
			struct low_level_state *lls = hls->ll_states.content[i];
			if (!lls)
				continue;
			hls->ll_states.content[i] = NULL;
			/* Bound receives always either succeed or set
			   need_delay, and in either case we won't get
			   here. */
			assert(!lls->bound_receiving_message);
			/* ... so we must be doing an unbound receive. */
			assert(lls->unbound_receiving_message);
			low_level_state_erase_first(&message_receivers, lls);
			/* Success of an unbound receive is indicated
			   by binding the LLS. */
			if (lls->bound_lls) {
				debug("%p: unbound RX from %p\n", lls, lls->bound_lls);
				assert(lls->bound_lls != BOUND_LLS_EXITED);
				low_level_state_push(&new_llsa, lls);
			} else {
				debug("%p: unbound RX failed\n", lls);
				exit_thread(lls);
			}
		}
		low_level_state_arr_swizzle(&hls->ll_states, &new_llsa);
		return;
	}

	/* Some states require a delay.  Do it. */
	debug("Delay for RX\n");
	release_big_lock();
	/* XXX could be more cunning here */
	usleep(MAX_DELAY_US);
	acquire_big_lock();
	debug("Back from RX delay\n");

	for (i = 0; i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		if (!lls)
			continue;
		sanity_check_low_level_state(lls, 1);
		hls->ll_states.content[i] = NULL;
		if (lls->unbound_receiving_message) {
			lls->unbound_receiving_message = NULL;
			low_level_state_erase_first(&message_receivers, lls);
		}
		if (lls->bound_receiving_message) {
			debug("Bound receive failed\n");
			exit_thread(lls);
		} else if (!lls->bound_lls) {
			debug("Unbound receive failed\n");
			exit_thread(lls);
		} else {
			debug("Receive succeeded.\n");
			low_level_state_push(&new_llsa, lls);
		}
	}

	low_level_state_arr_swizzle(&hls->ll_states, &new_llsa);
}

static void
advance_through_cfg(struct high_level_state *hls, unsigned long rip)
{
	int i, j, r;
	debug("Next instr %lx\n", rip);
	r = hls->ll_states.sz;
	for (i = 0; i < r; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		cfg_label_t cur_label = lls->cfg_node;
		const struct cfg_instr *current_cfg_node = &plan.cfg_nodes[cur_label];
		int preserve = 0;
		debug("Consider successors of %d\n", i);
		for (j = 0; j < current_cfg_node->nr_successors; j++) {
			if (rip == plan.cfg_nodes[current_cfg_node->successors[j]].rip) {
				struct low_level_state *newLls;
				if (!preserve) {
					/* The common case is that we
					 * have precisely one
					 * successor.  Avoid
					 * malloc()/free() in that
					 * case. */
					newLls = lls;
					low_level_state_push(&hls->ll_states, newLls);
					preserve = 1;
				} else {
					/* low-level state fork ->
					 * need to malloc() */
					newLls = clone_lls(lls);
				}
				newLls->cfg_node = current_cfg_node->successors[j];
				debug("Accept %d:%lx\n", current_cfg_node->successors[j], rip);
			} else {
				debug("Reject %d:%lx != %lx\n",
				       current_cfg_node->successors[j],
				       plan.cfg_nodes[current_cfg_node->successors[j]].rip,
				       rip);
			}
		}
		if (!preserve) {
			debug("%d has no viable successors\n", i);
			hls->ll_states.content[i] = NULL;
			if (current_cfg_node->nr_successors == 0) {
				if (lls->last_operation_is_send) {
					/* If the last operation in a
					   thread is a send, that
					   means, pretty much, that
					   the last instruction is a
					   store, and we need the
					   receiving thread to read
					   the value which was stored.
					   That means that we
					   shouldn't allow this
					   physical thread to execute
					   any more instructions until
					   the receiving thread
					   executes that load.  Easy
					   way of implementing that is
					   simply to stall until the
					   bound LLS exits. */
					debug("successfully finished this CFG with a send\n");
					assert(lls->bound_lls);
					lls->await_bound_lls_exit = 1;
					low_level_state_push(&hls->ll_states, lls);
				} else {
					debug("successfully finished this CFG; didn't end with a send\n");
					exit_thread(lls);
				}
			} else {
				exit_thread(lls);
			}
		}
	}
	hls->ll_states.sz -= r;
	memmove(hls->ll_states.content, hls->ll_states.content + r, sizeof(hls->ll_states.content[0]) * hls->ll_states.sz);
}

static void
check_for_ll_thread_start(struct high_level_state *hls, const struct reg_struct *regs)
{
	int i, j;
	for (i = 0; i < plan.nr_entry_points; i++) {
		if (plan.entry_points[i]->orig_rip != regs->rip)
			continue;
		for (j = 0; j < plan.entry_points[i]->nr_entry_ctxts; j++) {
			if (ctxt_matches(plan.entry_points[i]->ctxts[j], regs))
				start_low_level_thread(
					hls,
					plan.entry_points[i]->ctxts[j]->cfg_label,
					plan.entry_points[i]->ctxts[j]->nr_simslots);
		}
	}
}

static void
emulate_underlying_instruction(struct high_level_state *hls, struct reg_struct *regs)
{
	struct cep_emulate_ctxt emul_ctxt = {
		.ctxt = {
			.regs = regs,
			.addr_size = 64,
			.sp_size = 64,
			.force_writeback = 0,
		},
	};
	int r;

	debug("Emulate from %lx\n", regs->rip);
	emul_ctxt.hls = hls;
	r = x86_emulate(&emul_ctxt.ctxt, &emulator_ops);
	assert(r == X86EMUL_OKAY);
}

static void
send_messages(struct high_level_state *hls)
{
	struct low_level_state_array new_llsa;
	int i;
	int have_sends;
	int need_delay;
	int j;

	have_sends = 0;
	for (i = 0; !have_sends && i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		if (plan.cfg_nodes[lls->cfg_node].tx_msg)
			have_sends = 1;
	}
	if (!have_sends)
		return;

	debug("start tx\n");
	memset(&new_llsa, 0, sizeof(new_llsa));
	have_sends = 0;
	need_delay = 0;
	for (i = 0; i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		const struct cfg_instr *instr = &plan.cfg_nodes[lls->cfg_node];
		struct msg_template *msg;
		int delay_this_side;

		if (!instr->tx_msg) {
			low_level_state_push(&new_llsa, lls);
			hls->ll_states.content[i] = NULL;
			continue;
		}

		msg = instr->tx_msg;

		if (msg->event_count <= msg->pair->event_count) {
			debug("%p: Send %x, delay is on TX side (%d <= %d)\n",
			      lls, msg->msg_id, msg->event_count, msg->pair->event_count);
			delay_this_side = 1;
		} else {
			debug("%p: Send %x, delay is on RX side (%d > %d)\n",
			      lls, msg->msg_id, msg->event_count, msg->pair->event_count);
			delay_this_side = 0;
		}
		msg->event_count++;

		if (lls->bound_lls == BOUND_LLS_EXITED) {
			debug("Send when bound to a dead thread; doomed\n");
			hls->ll_states.content[i] = NULL;
			exit_thread(lls);
		} else if (lls->bound_lls) {
			if (lls->bound_lls->bound_receiving_message) {
				debug("Transmit to bound thread %p which is already waiting\n",
				      lls->bound_lls);
#warning apply message filter here and fail out if it doesn't match. '
				discharge_message(lls, msg,
						  lls->bound_lls, lls->bound_lls->bound_receiving_message);
				lls->bound_lls->bound_receiving_message = NULL;
				low_level_state_push(&new_llsa, lls);
				hls->ll_states.content[i] = NULL;
			} else {
				debug("Transmit to bound thread %p which isn't yet ready\n",
				      lls->bound_lls);
				lls->bound_sending_message = msg;
				have_sends = 1;
				need_delay = 1;
			}
		} else {
			/* Perform a general send. */
			lls->unbound_sending_message = msg;
			for (j = 0; j < message_receivers.sz; j++) {
				struct low_level_state *rx_lls = message_receivers.content[j];
#warning apply message filter here and discard anything which doesn't match. '
				assert(rx_lls->unbound_receiving_message);
				if (rx_lls->unbound_receiving_message == msg->pair) {
					debug("inject message into remote LLS %p\n", rx_lls);
					rendezvous_threads_tx(&new_llsa, lls, rx_lls);
				}
			}
			/* And tell any future receivers that we're
			 * available. */
			low_level_state_push(&message_senders, lls);
			have_sends = 1;
			need_delay |= delay_this_side;
		}
	}

	if (!have_sends) {
		debug("All sends completed without delaying\n");
		low_level_state_arr_swizzle(&hls->ll_states, &new_llsa);
		return;
	}

	if (!need_delay) {
		/* Sends failed, but we don't want to delay, so fail
		 * them all. */
		debug("Sends outstanding, but no delays here.\n");
		for (i = 0; i < hls->ll_states.sz; i++) {
			struct low_level_state *lls = hls->ll_states.content[i];
			if (!lls)
				continue;
			hls->ll_states.content[i] = NULL;
			/* Bound sends always either succeed or set
			   need_delay, so we shouldn't see any
			   incomplete ones here. */
			assert(!lls->bound_sending_message);
			/* Since we weren't doing a bound send, we
			   must have been doing an unbound one. */
			assert(lls->unbound_sending_message);
			low_level_state_erase_first(&message_senders, lls);
			/* If we're now bound then the send succeeded.
			   Otherwise, it failed and we should exit. */
			if (lls->bound_lls) {
				debug("%p: Unbound TX to %p; bind.\n",
				      lls, lls->bound_lls);
				assert(lls->bound_lls != BOUND_LLS_EXITED);
				low_level_state_push(&new_llsa, lls);
			} else {
				debug("%p: TX failed\n", lls);
				exit_thread(lls);
			}
		}
		low_level_state_arr_swizzle(&hls->ll_states, &new_llsa);
		return;
	}

	debug("Delay for TX.\n");
	release_big_lock();
	usleep(MAX_DELAY_US);
	acquire_big_lock();
	debug("Back from TX delay.\n");

	for (i = 0; i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		if (!lls)
			continue;
		hls->ll_states.content[i] = NULL;
		if (lls->unbound_sending_message) {
			lls->unbound_sending_message = NULL;
			low_level_state_erase_first(&message_senders, lls);
		}
		if (lls->bound_sending_message) {
			debug("Bound send failed\n");
			exit_thread(lls);
		} else if (!lls->bound_lls) {
			debug("Unbound send failed\n");
			hls->ll_states.content[i] = NULL;
			exit_thread(lls);
		} else {
			debug("Send succeeded\n");
			low_level_state_push(&new_llsa, lls);
		}
	}

	low_level_state_arr_swizzle(&hls->ll_states, &new_llsa);
}

static void
wait_for_bound_exits(struct high_level_state *hls)
{
	int i;
	int waiting_for_bound_exit;

	while (1) {
		waiting_for_bound_exit = 0;
		for (i = 0; !waiting_for_bound_exit && i < hls->ll_states.sz; i++) {
			struct low_level_state *lls = hls->ll_states.content[i];
			if (lls->await_bound_lls_exit) {
				if (lls->bound_lls == BOUND_LLS_EXITED) {
					low_level_state_erase_idx(&hls->ll_states, i);
					exit_thread(lls);
					i--;
				} else {
					assert(lls->bound_lls);
					assert(!lls->bound_lls->await_bound_lls_exit);
					waiting_for_bound_exit++;
				}
			}
		}
		if (!waiting_for_bound_exit)
			break;
		debug("Waiting for %d bound exits\n", waiting_for_bound_exit);
		release_big_lock();
		usleep(100);
		acquire_big_lock();
	}
	return;
}

static void
stash_registers(struct high_level_state *hls, struct reg_struct *regs)
{
	int i, j;

	for (i = 0; i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		const struct cfg_instr *instr = &plan.cfg_nodes[lls->cfg_node];
		for (j = 0; j < instr->nr_stash; j++) {
			if (instr->stash[j].reg != -1) {
				simslot_t *slot = &lls->simslots[instr->stash[j].slot];
				switch (instr->stash[j].reg) {
#define do_case(idx, r)							\
					case idx:			\
						*slot = regs-> r;	\
						break
					do_case(0, rax);
					do_case(1, rcx);
					do_case(2, rdx);
					do_case(3, rbx);
					do_case(4, rsp);
					do_case(5, rbp);
					do_case(6, rsi);
					do_case(7, rdi);
					do_case(8, r8);
					do_case(9, r9);
					do_case(10, r10);
					do_case(11, r11);
					do_case(12, r12);
					do_case(13, r13);
					do_case(14, r14);
					do_case(15, r15);
#undef do_case
				default:
					abort();
				}
			}
		}
	}
}

static void
advance_hl_interpreter(struct high_level_state *hls, struct reg_struct *regs)
{
	int i;

	sanity_check_high_level_state(hls);

	for (i = 0; i < hls->ll_states.sz; i++)
		hls->ll_states.content[i]->last_operation_is_send = 0;

	check_for_ll_thread_start(hls, regs);
	if (hls->ll_states.sz == 0)
		exit_interpreter();
	sanity_check_high_level_state(hls);

	stash_registers(hls, regs);

	receive_messages(hls);
	if (hls->ll_states.sz == 0)
		exit_interpreter();
	sanity_check_high_level_state(hls);

	wait_for_bound_exits(hls);
	if (hls->ll_states.sz == 0)
		exit_interpreter();

	emulate_underlying_instruction(hls, regs);
	sanity_check_high_level_state(hls);

	send_messages(hls);
	if (hls->ll_states.sz == 0)
		exit_interpreter();
	sanity_check_high_level_state(hls);

	advance_through_cfg(hls, regs->rip);
	sanity_check_high_level_state(hls);
}

static void
start_interpreting(int entrypoint_idx)
{
	const struct cep_entry_point *entry_point = plan.entry_points[entrypoint_idx];
	struct per_thread_state *pts = find_pts();
	struct high_level_state hls;

	debug("Start interpreting idx %d, pts at %p, regs at %p\n",
	      entrypoint_idx,
	      pts,
	      &pts->client_regs);
	init_high_level_state(&hls);
	pts->client_regs.rip = entry_point->orig_rip;
	while (1) {
		acquire_big_lock();
		advance_hl_interpreter(&hls, &pts->client_regs);
		release_big_lock();
	}
	abort();
}

#define str2(x) # x
#define str(x) str2(x)

/* We have two types of trampolines, one for transitioning from client
   code into the interpreter and one for going from the interpreter to
   client code. */
asm(
"__trampoline_client_to_interp_start:\n"
"    mov %rsp, %gs:(" str(_STACK_SIZE) " - 16)\n" /* Stash client RSP */
"    mov %gs:0, %rsp\n"    /* Switch to interpreter stack */
"    pushf\n"              /* Save other client registers */
"    push %r15\n"
"    push %r14\n"
"    push %r13\n"
"    push %r12\n"
"    push %r11\n"
"    push %r10\n"
"    push %r9\n"
"    push %r8\n"
"    push %rdi\n"
"    push %rsi\n"
"    push %rbp\n"
"    push %rbx\n"
"    push %rcx\n"
"    push %rdx\n"
"    push %rax\n"
"    push %rax\n"          /* Leave space for rip */
"__trampoline_client_to_interp_load_edi:\n"
"    mov $0x11223344, %edi\n"
"__trampoline_client_to_interp_load_rdx:\n"
"    movq $0x1122334455667788, %rdx\n"
"    jmp *%rdx\n"
"__trampoline_client_to_interp_end:\n"
"\n"
"__trampoline_interp_to_client_start:\n"
"    movq %rdi, %rsp\n"
"    popq %rax\n"          /* RIP, but we have another plan for restoring that */
"    popq %rax\n"
"    popq %rdx\n"
"    popq %rcx\n"
"    popq %rbx\n"
"    popq %rbp\n"
"    popq %rsi\n"
"    popq %rdi\n"
"    popq %r8\n"
"    popq %r9\n"
"    popq %r10\n"
"    popq %r11\n"
"    popq %r12\n"
"    popq %r13\n"
"    popq %r14\n"
"    popq %r15\n"
"    popf\n"
"    popq %rsp\n"
"__trampoline_interp_to_client_jmp_client:\n"
".byte 0xe9\n"
".byte 0\n"
".byte 0\n"
".byte 0\n"
".byte 0\n"
"__trampoline_interp_to_client_end:\n"
"\n");
void __trampoline_client_to_interp_start(void) __attribute__((visibility ("hidden")));
void __trampoline_client_to_interp_load_edi(void) __attribute__((visibility ("hidden")));
void __trampoline_client_to_interp_load_rdx(void) __attribute__((visibility ("hidden")));
void __trampoline_client_to_interp_end(void) __attribute__((visibility ("hidden")));
void __trampoline_interp_to_client_start(void) __attribute__((visibility ("hidden")));
void __trampoline_interp_to_client_jmp_client(void) __attribute__((visibility ("hidden")));
void __trampoline_interp_to_client_end(void) __attribute__((visibility ("hidden")));
static unsigned long
alloc_trampoline(int idx)
{
	size_t tramp_size = (unsigned long)&__trampoline_client_to_interp_end - (unsigned long)&__trampoline_client_to_interp_start;
	unsigned char *buffer;

	debug("tramp start %p, end %p, size %zx\n", &__trampoline_client_to_interp_end, &__trampoline_client_to_interp_start, tramp_size);
	buffer = alloc_executable(tramp_size);
	memcpy(buffer, &__trampoline_client_to_interp_start, tramp_size);
	*(int *)(buffer +
		 (unsigned long)&__trampoline_client_to_interp_load_edi -
		 (unsigned long)&__trampoline_client_to_interp_start +
		 1) = idx;
	*(long *)(buffer +
		  (unsigned long)&__trampoline_client_to_interp_load_rdx -
		  (unsigned long)&__trampoline_client_to_interp_start +
		  2) = (unsigned long)start_interpreting;
	debug("Trampoline at %p\n", buffer);
	return (unsigned long)buffer;
}

struct exit_trampoline {
	struct exit_trampoline *next;
	unsigned long rip;
};
static exit_routine_t *
find_exit_stub(unsigned long rip)
{
	static struct exit_trampoline *head_exit_trampoline;
	struct exit_trampoline *cursor;
	size_t tramp_size;
	void *trampoline;
	long delta;
	void *jmp_instr;

	for (cursor = head_exit_trampoline; cursor; cursor = cursor->next) {
		if (cursor->rip == rip)
			return (exit_routine_t *)(cursor + 1);
	}
	tramp_size = (unsigned long)__trampoline_interp_to_client_end -
		(unsigned long)__trampoline_interp_to_client_start;
	cursor = alloc_executable(sizeof(*cursor) + tramp_size);
	cursor->rip = rip;
	trampoline = cursor + 1;
	memcpy(trampoline, (const void *)__trampoline_interp_to_client_start, tramp_size);
	jmp_instr = trampoline +
		(unsigned long)__trampoline_interp_to_client_jmp_client -
		(unsigned long)__trampoline_interp_to_client_start;
	delta = rip - ((unsigned long)jmp_instr + 5);
	assert(delta == (int)delta);
	*(int *)((unsigned long)jmp_instr + 1) = delta;
	cursor->next = head_exit_trampoline;
	head_exit_trampoline = cursor;
	return (exit_routine_t *)(cursor + 1);
}

static void
alloc_thread_state_area(void)
{
	struct per_thread_state *pts;
	pts = mmap(NULL, PAGE_SIZE * 1024, PROT_READ|PROT_WRITE,
		     MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
	pts->initial_interpreter_rsp =
		(unsigned long)&pts->client_regs.rsp;
	arch_prctl(ARCH_SET_GS, (unsigned long)pts);
}
/* This is hooked into clone() so that we're called instead of the
   usual child thread function.  The child thread function and its
   sole argument are passed in as @fn and @fn_arg.  Create our
   per-thread state area and then run the user function.  Note that we
   have to call __GI__exit ourselves, because of the way we're patched
   in. */
static void
clone_hook_c(int (*fn)(void *), void *fn_arg)
{
	int res;

	alloc_thread_state_area();

	have_cloned = 1;

	res = fn(fn_arg);

	__GI__exit(res);
}

/* We need to hook the clone() call in glibc to catch creation of new
 * threads early enough.  This is a hideous, hideous hack.  Meh. */
static void
hook_clone(void)
{
	unsigned char *clone_addr = (unsigned char *)clone;
	void *mprotect_start, *mprotect_end;
	int idx;

	mprotect_start = (void *)((unsigned long)clone_addr & ~(PAGE_SIZE - 1));
	mprotect_end = (void *)(((unsigned long)clone_addr + 64 + PAGE_SIZE - 1) & ~(PAGE_SIZE - 1));

	if (mprotect(mprotect_start, mprotect_end - mprotect_start, PROT_READ|PROT_WRITE|PROT_EXEC) == -1)
		err(1, "mprotect() before hooking clone");
	__GI__exit =
		(void (*)(int))
		(*(int *)(clone_addr + 113) + (unsigned long)clone_addr + 117);

	idx = 105;
#define byte(x) clone_addr[idx++] = ((x) & 0xff)
#define word(x) byte(x); byte((x) >> 8)
#define dword(x) word(x); word((x) >> 16)
#define qword(x) dword(x); dword((x) >> 32)
	/* movq $clone_hook_asm, %r10 */
	byte(0x49); byte(0xba); qword((unsigned long)clone_hook_asm);
	/* jmp *%r10 */
	byte(0x41); byte(0xff); byte(0xe2);
#undef byte
#undef qword
	if (mprotect(mprotect_start, mprotect_end - mprotect_start, PROT_READ|PROT_EXEC) == -1)
		err(1, "mprotect() after hooking clone");
}

asm(
/* This hooks in to a bit of glibc's clone function which would normally go:

>    0x00007fc62cce2709 <+105>:   pop    %rax
>    0x00007fc62cce270a <+106>:   pop    %rdi
>    0x00007fc62cce270b <+107>:   callq  *%rax
>    0x00007fc62cce270d <+109>:   mov    %rax,%rdi
>    0x00007fc62cce2710 <+112>:   callq  0x7fc62cca66f0 <*__GI__exit>

the call is the top of the user-supplied thread function.  We need to
call into our bits before doing basically the same thing. */
"clone_hook_asm:\n"
"pop %rdi\n"
"pop %rsi\n"
"call clone_hook_c\n"
	);

static void
activate(void)
{
	unsigned x;
	long delta;
	char buf[4096];
	ssize_t s;

	s = readlink("/proc/self/exe", buf, sizeof(buf)-1);
	if (s == -1) {
		printf("Can't access /proc/self/exe; patch disabled\n");
		return;
	}
	buf[s] = 0;
	if (strcmp(buf, program_to_patch)) {
		printf("This is a patch for %s, but we were invoked on %s; disabling.\n",
		       program_to_patch, buf);
		return;
	}

	alloc_thread_state_area();

	/* We need to patch each entry point so that it turns into a
	   jump instruction which targets the patch.  Do so. */
	for (x = 0; x < plan.nr_entry_points; x++) {
		mprotect((void *)(plan.entry_points[x]->orig_rip & PAGE_MASK),
			 PAGE_SIZE * 2,
			 PROT_READ|PROT_WRITE|PROT_EXEC);
		*(unsigned char *)plan.entry_points[x]->orig_rip = 0xe9; /* jmp rel32 opcode */
		delta = alloc_trampoline(x) - (plan.entry_points[x]->orig_rip + 5);
		assert(delta == (int)delta);
		*(int *)(plan.entry_points[x]->orig_rip + 1) = delta;
		mprotect((void *)(plan.entry_points[x]->orig_rip & PAGE_MASK),
			 PAGE_SIZE * 2,
			 PROT_READ|PROT_EXEC);
	}

	hook_clone();
}

static void (*__init_activate)(void) __attribute__((section(".ctors"), unused, used)) = activate;
