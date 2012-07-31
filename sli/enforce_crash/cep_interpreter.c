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

#define PAGE_SIZE 4096ul
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
	int refcount; /* HLS holds a reference, and so do all outgoing
		       * messages. */

	struct high_level_state *hls;

	cfg_label_t cfg_node;

	int nr_simslots;

	/* Once we've received a message from an LLS, we become bound
	 * to that LLS and in future will only receive messages from
	 * them.  Can be BOUND_LLS_EXITED if we've bound to a thread
	 * which has since exited, in which case all message receives
	 * will fail. */
	struct low_level_state *bound_lls;

	/* True if we're currently trying to receive from @bound_lls. */
	int bound_rx;

	/* Used by receiving LLSs to indicate to a transmitting LLS
	   that the TX has succeeded and that the the transmitting LLS
	   shouldn't exit. */
	int done_tx;

	struct message *incoming_msg;
	struct message *outgoing_msg;

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

/* One of the messages which is actually sent. */
struct message {
	int refcount;
	unsigned id;
	struct low_level_state *sender;
	unsigned payload_sz;
	unsigned long payload[];
};
mk_flex_array(message);

/* A thing which can receive messages.  When a high-level interpreter
 * wants to perform a receive it figures out what it might possibly
 * want to receive and then arranges for all of the
 * potentially-relevant messages to get routed to one of these, and
 * then performs the low-level receives on that message pool. */
struct msg_rx_struct {
	/* The messages which have been received so far. */
	struct message_array messages;
};
mk_flex_array(msg_rx_struct);

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
	unsigned char interpreter_stack[PAGE_SIZE - 16 - sizeof(struct reg_struct)];
	struct reg_struct client_regs;
};

/* Rendezvous points for unbound low-level threads.  When an unbound
 * thread wants to send or receive a message it will register itself
 * in a message slot.  Any matching operation which comes along later
 * will notice it in the slot and rendezvous from there. */
struct msg_slot {
	struct message_array outstanding_send;
	struct msg_rx_struct_array receivers;
};
static struct msg_slot *msg_slots;

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
new_low_level_state(int nr_simslots)
{
	struct low_level_state *lls = calloc(sizeof(struct low_level_state) + nr_simslots * sizeof(lls->simslots[0]), 1);
	lls->refcount = 1;
	lls->nr_simslots = nr_simslots;
	return lls;
}

static struct message *
new_message(struct low_level_state *lls, const struct msg_template *template)
{
	struct message *res = malloc(sizeof(*res) + template->payload_size * sizeof(res->payload[0]));
	res->refcount = 1;
	res->id = template->msg_id;
	res->sender = lls;
	res->payload_sz = template->payload_size;
	lls->refcount++;
	return res;
}

static void
start_low_level_thread(struct high_level_state *hls, cfg_label_t starting_label, int nr_simslots)
{
	struct low_level_state *lls = new_low_level_state(nr_simslots);
	lls->cfg_node = starting_label;
	lls->hls = hls;
	low_level_state_push(&hls->ll_states, lls);
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
	const struct cfg_instr *current_cfg_node;
};

static int
emulator_read(enum x86_segment seg,
	      unsigned long offset,
	      void *p_data,
	      unsigned int bytes,
	      struct x86_emulate_ctxt *ctxt)
{
	/* This is where we'd do load stashes, if we were doing load
	 * stashes. */
	/* XXX should trap any faults here, so that we can set up a
	   correct signal frame. XXX */
	assert(seg == x86_seg_ds || seg == x86_seg_ss);
	memcpy(p_data, (const void *)offset, bytes);
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
	int to_copy = ctxt->current_cfg_node->content_sz - offset + ctxt->current_cfg_node->rip;
	assert(offset >= ctxt->current_cfg_node->rip && offset < ctxt->current_cfg_node->rip + ctxt->current_cfg_node->content_sz);
	if (to_copy > bytes)
		to_copy = bytes;
	memcpy(p_data, ctxt->current_cfg_node->content + offset - ctxt->current_cfg_node->rip, to_copy);
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

static void
release_message(struct message *msg)
{
	msg->refcount--;
	if (!msg->refcount) {
		release_lls(msg->sender);
		free(msg);
	}
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
	struct low_level_state *new_lls = new_low_level_state(lls->nr_simslots);
	new_lls->hls = lls->hls;
	new_lls->cfg_node = lls->cfg_node;
	memcpy(new_lls->simslots, lls->simslots, sizeof(new_lls->simslots[0]) * new_lls->nr_simslots);
	assert(!lls->bound_rx);
	assert(!lls->outgoing_msg);
	assert(!lls->incoming_msg);

	if (lls->bound_lls && lls->bound_lls != BOUND_LLS_EXITED) {
		struct low_level_state *new_bound_lls = new_low_level_state(lls->bound_lls->nr_simslots);
		new_bound_lls->hls = lls->bound_lls->hls;
		new_bound_lls->cfg_node = lls->bound_lls->cfg_node;
		new_bound_lls->bound_lls = new_lls;
		new_bound_lls->bound_rx = lls->bound_lls->bound_rx;
		new_bound_lls->done_tx = lls->bound_lls->done_tx;
		memcpy(new_bound_lls->simslots, lls->bound_lls->simslots, sizeof(new_bound_lls->simslots[0]) * new_bound_lls->nr_simslots);
		if (lls->bound_lls->incoming_msg) {
			/* Old bound LLS was in the process of
			   receiving a message from the old LLS -> new
			   bound LLS is in the process if receiving a
			   message from the new LLS */
			struct message *msg = malloc(sizeof(*msg) + lls->bound_lls->incoming_msg->payload_sz * sizeof(msg->payload[0]));
			msg->refcount = 1;
			msg->id = lls->bound_lls->incoming_msg->id;
			msg->sender = new_lls;
			new_lls->refcount++;
			memcpy(msg->payload,
			       lls->bound_lls->incoming_msg->payload,
			       lls->bound_lls->incoming_msg->payload_sz * 8);
			new_bound_lls->incoming_msg = msg;
		}
		if (lls->bound_lls->outgoing_msg) {
			/* Likewise, if the old bound LLS was sending
			   a message, the new bound LLS must be as
			   well. */
			struct message *msg = malloc(sizeof(*msg) + lls->bound_lls->outgoing_msg->payload_sz * sizeof(msg->payload[0]));
			msg->refcount = 1;
			msg->id = lls->bound_lls->outgoing_msg->id;
			msg->sender = new_bound_lls;
			new_bound_lls->refcount++;
			memcpy(msg->payload,
			       lls->bound_lls->outgoing_msg->payload,
			       lls->bound_lls->outgoing_msg->payload_sz * 8);
			new_bound_lls->outgoing_msg = msg;
		}
		/* We know that the old bound LLS isn't currently
		   sending any unbound messages, because it's a bound
		   LLS, and so there can't be any messages in the
		   message slots. */
#ifndef NDEBUG
		{
			int i, j;
			for (i = 0; i < plan.msg_id_limit - plan.base_msg_id; i++) {
				for (j = 0; j < msg_slots[i].outstanding_send.sz; j++)
					assert(msg_slots[i].outstanding_send.content[j]->sender != lls->bound_lls);
			}
		}
#endif
		low_level_state_push(&new_bound_lls->hls->ll_states, new_bound_lls);
	}

	low_level_state_push(&new_lls->hls->ll_states, new_lls);
	return new_lls;
}

/* @lls is now going to receive message @msg.  Bind the threads
   together and unpack the message. */
/* Thread binding is, like most of the message passing logic, a bit
   fiddly.  The key idea is that we need to set lls->bound_lls ==
   msg->sender and msg->sender->bound_lls == lls, except that we're
   not allowed to un-bind any LLSs in order to do so. The workaround
   is to just duplicate any LLSs which are already bound. */
static void
rendezvous_threads_rx(struct low_level_state_array *llsa,
		      struct low_level_state *rx_lls,
		      struct message *msg,
		      const struct msg_template *template)
{
	struct low_level_state *tx_lls = msg->sender;
	int x;

	assert(tx_lls);

	if (tx_lls->bound_lls && tx_lls->bound_lls != rx_lls) {
		/* The transmitting LLS is already bound, so dupe it
		   and bind to the dupe instead. */

		struct low_level_state *dupe_tx_lls;

		assert(tx_lls->bound_lls != BOUND_LLS_EXITED);

		/* Because the TX LLS is supposed to be in the middle
		   of send_message(), which can't receive messages. */
		assert(!tx_lls->incoming_msg);

		dupe_tx_lls = new_low_level_state(tx_lls->nr_simslots);
		dupe_tx_lls->hls = tx_lls->hls;
		dupe_tx_lls->cfg_node = tx_lls->cfg_node;
		memcpy(dupe_tx_lls->simslots, tx_lls->simslots, sizeof(dupe_tx_lls->simslots[0]) * tx_lls->nr_simslots);

		tx_lls = dupe_tx_lls;
		low_level_state_push(&tx_lls->hls->ll_states, tx_lls);
	}

	if (rx_lls->bound_lls && rx_lls->bound_lls != tx_lls) {
		/* We are already bound, so dupe ourselves and have
		   the dupe bind instead. */

		struct low_level_state *dupe_rx_lls;
		assert(rx_lls->bound_lls != BOUND_LLS_EXITED);
		dupe_rx_lls = new_low_level_state(rx_lls->nr_simslots);
		dupe_rx_lls->hls = rx_lls->hls;
		dupe_rx_lls->cfg_node = rx_lls->cfg_node;
		memcpy(dupe_rx_lls->simslots, rx_lls->simslots, sizeof(dupe_rx_lls->simslots[0]) * rx_lls->nr_simslots);

		/* Note that rx_lls is not registered with an HLS at
		   this point. */
	}

	/* Both LLSs are now unbound, so we can safely bind them
	 * together. */
	if (tx_lls->bound_lls != rx_lls) {
		assert(!tx_lls->bound_lls);
		assert(!rx_lls->bound_lls);
		rx_lls->bound_lls = tx_lls;
		tx_lls->bound_lls = rx_lls;
	} else {
		assert(rx_lls->bound_lls == tx_lls);
	}

	tx_lls->done_tx = 1;

	assert(msg->payload_sz == template->payload_size);
	for (x = 0; x < msg->payload_sz; x++) {
		assert(template->payload[x] < rx_lls->nr_simslots);
		rx_lls->simslots[template->payload[x]] = msg->payload[x];
	}

	low_level_state_push(llsa, rx_lls);
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
	struct msg_rx_struct msg_rx;
	int need_delay;
	int have_bound_rx;
	int have_unbound_rx;
	struct low_level_state_array new_llsa;

	memset(&msg_rx, 0, sizeof(msg_rx));
	need_delay = 0;
	have_unbound_rx = 0;
	have_bound_rx = 0;
	for (i = 0; i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		const struct cfg_instr *instr = &plan.cfg_nodes[lls->cfg_node];
		const struct msg_template *msg;
		struct msg_slot *slot;
		struct message *rxed_msg;

		if (!instr->rx_msg) {
			/* Threads which don't receive any messages
			 * don't need to do anything. */
			continue;
		}

		msg = instr->rx_msg;

		debug("Trying to receive %x\n", msg->msg_id);
		if (lls->bound_lls) {
			if (lls->bound_lls == BOUND_LLS_EXITED) {
				/* This should fail slightly further
				 * down. */
			} else {
				assert(lls->bound_lls->bound_lls == lls);
				if (lls->bound_lls->outgoing_msg) {
#warning apply message filter here
					debug("Receive from bound thread\n");
					lls->incoming_msg = lls->bound_lls->outgoing_msg;
					lls->bound_lls->outgoing_msg = NULL;
				} else {
					debug("Bound thread with nothing outstanding; go to RX state\n");
					lls->bound_rx = 1;
					need_delay = 1;
				}
			}
			have_bound_rx = 1;
		} else {
			slot = &msg_slots[msg->msg_id - plan.base_msg_id];
			/* Gather up all of the messages which have
			   already been sent which might be
			   relevant. */
			for (j = 0; j < slot->outstanding_send.sz; j++) {
				rxed_msg = slot->outstanding_send.content[j];
				rxed_msg->refcount++;
#warning apply message filter here
				rxed_msg->sender->done_tx = 1;
				debug("Picked up msg %p (%d/%d)\n",
				       rxed_msg,
				       j,
				       slot->outstanding_send.sz);
				message_push(&msg_rx.messages, rxed_msg);
			}
			/* And tell any future senders that we're
			 * available. */
			/* Note that we might end up attaching the
			 * msg_rx structure to the same slot multiple
			 * times.  That's fine; it just means we'll
			 * receive each message multiple times, and
			 * then ignore all but one of them later. */
			msg_rx_struct_push(&slot->receivers, &msg_rx);
			have_unbound_rx = 1;
			need_delay = 1;
		}
	}

	if (!have_bound_rx && !have_unbound_rx) {
		/* No receive operations needed. */
		return;
	}

	if (need_delay) {
		debug("Delay for RX\n");
		release_big_lock();
		/* XXX could be more cunning here */
		usleep(MAX_DELAY_US);
		acquire_big_lock();
		debug("Back from RX delay\n");
	}

	memset(&new_llsa, 0, sizeof(new_llsa));

	for (i = 0; i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		const struct cfg_instr *instr = &plan.cfg_nodes[lls->cfg_node];
		const struct msg_template *msg;
		struct msg_slot *slot;

		if (!instr->rx_msg) {
			low_level_state_push(&new_llsa, lls);
			hls->ll_states.content[i] = NULL;
			continue;
		}

		msg = &instr->rx_msg[0];
		if (lls->bound_lls) {
			lls->bound_rx = 0;
		} else {
			debug("Stop trying to receive ID %x\n", msg->msg_id);
			slot = &msg_slots[msg->msg_id - plan.base_msg_id];
			/* We are no longer waiting for further messages. */
			msg_rx_struct_erase_first(&slot->receivers, &msg_rx);
		}
	}

	/* We've now collected all of the possibly-relevant messages
	   together.  Match them up to low-level threads and perform
	   the receive. */
	for (i = 0; i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		const struct cfg_instr *instr;
		const struct msg_template *msg;
		int rx_succeeded;

		if (!lls)
			continue;
		instr = &plan.cfg_nodes[lls->cfg_node];

		msg = &instr->rx_msg[0];
		rx_succeeded = 0;
		if (lls->bound_lls) {
			if (lls->incoming_msg) {
				struct message *rxed_msg = lls->incoming_msg;
				debug("Bound rendezvous via %p\n", rxed_msg);
#warning apply message filter here
				lls->incoming_msg = NULL;
				rendezvous_threads_rx(&new_llsa, lls, rxed_msg, msg);
				release_message(rxed_msg);
				rx_succeeded = 1;
			}
		} else {
			for (j = 0; j < msg_rx.messages.sz; j++) {
				struct message *rxed_msg = msg_rx.messages.content[j];
				if (rxed_msg->id == msg->msg_id &&
				    (lls->bound_lls == rxed_msg->sender || lls->bound_lls == NULL)) {
#warning apply message filter here
					debug("Rendezvousing via message %p (%d, %d/%d)\n",
					       rxed_msg, i, j, msg_rx.messages.sz);
					rendezvous_threads_rx(&new_llsa, lls, rxed_msg, msg);
					rx_succeeded = 1;
				}
			}
		}
		if (!rx_succeeded) {
			debug("rx failed\n");
			exit_thread(lls);
		}
	}

	/* And now we're done. */
	for (i = 0; i < msg_rx.messages.sz; i++)
		release_message(msg_rx.messages.content[i]);
	message_arr_cleanup(&msg_rx.messages);

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
			if (current_cfg_node->nr_successors == 0)
				debug("successfully finished this CFG\n");
			exit_thread(lls);
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
	emul_ctxt.current_cfg_node = &plan.cfg_nodes[hls->ll_states.content[0]->cfg_node];
	r = x86_emulate(&emul_ctxt.ctxt, &emulator_ops);
	assert(r == X86EMUL_OKAY);
}

static void
send_messages(struct high_level_state *hls)
{
	struct message_array sent_msgs;
	int i;
	int have_sends;
	int need_delay;
	int j;

	memset(&sent_msgs, 0, sizeof(sent_msgs));
	have_sends = 0;
	need_delay = 0;
	for (i = 0; i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		const struct cfg_instr *instr = &plan.cfg_nodes[lls->cfg_node];
		const struct msg_template *msg;
		struct message *tx_msg;

		if (!instr->tx_msg)
			continue;

		have_sends = 1;
		lls->done_tx = 0;
		if (lls->bound_lls == BOUND_LLS_EXITED) {
			debug("Send when bound to a dead thread; doomed\n");
			continue;
		}

		msg = instr->tx_msg;
		tx_msg = new_message(lls, msg);
		debug("Send %x via %p\n", tx_msg->id, tx_msg);
		for (j = 0; j < msg->payload_size; j++) {
			assert(msg->payload[j] < lls->nr_simslots);
			tx_msg->payload[j] = lls->simslots[msg->payload[j]];
		}
		if (lls->bound_lls) {
			if (lls->bound_lls->bound_rx) {
				assert(!lls->bound_lls->incoming_msg);
				lls->bound_lls->incoming_msg = tx_msg;
				tx_msg->refcount++;
				debug("Bound to a live thread which is in RX state\n");
			} else {
				debug("Bound to a live thread not in the RX state\n");
				lls->outgoing_msg = tx_msg;
				tx_msg->refcount++;
				need_delay = 1;
			}
		} else {
			struct msg_slot *slot = &msg_slots[msg->msg_id - plan.base_msg_id];
			debug("Send when %p not bound; %d known receivers\n",
			       tx_msg, slot->receivers.sz);
			for (j = 0; j < slot->receivers.sz; j++) {
				tx_msg->refcount++;
				message_push(&slot->receivers.content[j]->messages,
					     tx_msg);
			}
			message_push(&slot->outstanding_send, tx_msg);
			tx_msg->refcount++;
			message_push(&sent_msgs, tx_msg);
			need_delay = 1;
		}
	}

	if (!have_sends) {
		debug("Nothing to send\n");
		return;
	}

	if (need_delay) {
		debug("Delay.\n");
		release_big_lock();
		usleep(MAX_DELAY_US);
		acquire_big_lock();
	}

	for (i = 0; i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		const struct cfg_instr *instr = &plan.cfg_nodes[lls->cfg_node];

		if (instr->tx_msg && !lls->done_tx) {
			debug("Send failed\n");
			exit_thread(lls);
			low_level_state_erase_idx(&hls->ll_states, i);
			i--;
		}
	}

	/* If we went any unbound messages then we need to erase them
	   from the slot's outstanding send list. */
	for (i = 0; i < sent_msgs.sz; i++) {
		struct message *msg = sent_msgs.content[i];
		struct msg_slot *slot = &msg_slots[msg->id - plan.base_msg_id];
		message_erase_first(&slot->outstanding_send, msg);
		release_message(msg);
	}

	message_arr_cleanup(&sent_msgs);
}

static void
advance_hl_interpreter(struct high_level_state *hls, struct reg_struct *regs)
{
	check_for_ll_thread_start(hls, regs);
	if (hls->ll_states.sz == 0)
		exit_interpreter();

	receive_messages(hls);
	if (hls->ll_states.sz == 0)
		exit_interpreter();

	emulate_underlying_instruction(hls, regs);

	send_messages(hls);
	if (hls->ll_states.sz == 0)
		exit_interpreter();

	advance_through_cfg(hls, regs->rip);
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

/* We have two types of trampolines, one for transitioning from client
   code into the interpreter and one for going from the interpreter to
   client code. */
asm(
"__trampoline_client_to_interp_start:\n"
"    mov %rsp, %gs:4080\n" /* Stash client RSP */
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

	msg_slots = calloc(sizeof(msg_slots[0]), plan.msg_id_limit - plan.base_msg_id);

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
