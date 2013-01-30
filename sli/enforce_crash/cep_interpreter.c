#define _GNU_SOURCE
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
#include <sys/ucontext.h>
#include <assert.h>
#include <dlfcn.h>
#include <err.h>
#include <errno.h>
#include <limits.h>
#include <math.h>
#include <signal.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ucontext.h>
#include <unistd.h>

#include "../../config.h"

#define KEEP_LLS_HISTORY 0
#define LLS_HISTORY 8
#define USE_STATS 1
#define VERY_LOUD 0
#define USE_CUSTOM_MALLOC 1
#define SANITY_CHECK_ALLOCATOR 0

/* Define _PAGE_SIZE and _STACK_SIZE which don't include the ul
 * suffix, because that makes it easier to use them in inline
 * assembly. */
#define _PAGE_SIZE 4096
#define _STACK_SIZE (_PAGE_SIZE * 4)
#define PAGE_SIZE 4096ul
#define STACK_SIZE (PAGE_SIZE * 4)
#define PAGE_MASK (~(PAGE_SIZE - 1))
#define MAX_DELAY_US (100000)

static unsigned long prng_state = 0xe6b16c0386053e31;
static int disable_sideconditions;
static int force_delay; /* -1 -> on send, 0 -> use rebalancer, 1 -> on receive */
static int skip_context_check;

extern void clone(void);
static void (*__GI__exit)(int res);
void arch_prctl(int, unsigned long);
static void clone_hook_c(int (*fn)(void *), void *fn_arg) __attribute__((unused));

static void *cep_realloc(void *ptr, size_t new_sz);
static void *cep_malloc(size_t sz);
static void cep_free(const void *what);

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

#if USE_STATS
static struct {
#define enum_stats(iter)			\
	iter(lls_created)			\
	iter(hls_created)			\
	iter(bytecode_evaluated)		\
	iter(restart_interpreter)		\
	iter(exit_emulate)			\
	iter(exit_interpreter)			\
	iter(ll_clone)				\
	iter(discharge_message)			\
	iter(message_filter_failed)		\
	iter(rx_from_exited)			\
	iter(rx_bound)				\
	iter(rx_bound_fast)			\
	iter(rx_bound_failed)			\
	iter(rx_bound_wait)			\
	iter(rx_unbound_early)			\
	iter(rx_unbound)			\
	iter(rx_fast)				\
	iter(rx_slow)				\
	iter(rx_delay)				\
	iter(rx_futex)				\
	iter(rx_futex_timeout)			\
	iter(rx_bound_failed_late)		\
	iter(rx_unbound_failed)			\
	iter(rx_success)			\
	iter(adv_no_malloc)			\
	iter(adv_malloc)			\
	iter(adv_reject)			\
	iter(adv_dead)				\
	iter(adv_fail_side_condition)		\
	iter(emul_underlying)			\
	iter(tx_bound_exited)			\
	iter(tx_bound_fast)			\
	iter(tx_bound_failed)			\
	iter(tx_bound_wrong_message)		\
	iter(tx_bound_slow)			\
	iter(tx_unbound)			\
	iter(tx_unbound_early)			\
	iter(tx_fast)				\
	iter(tx_slow)				\
	iter(tx_delay)				\
	iter(tx_futex)				\
	iter(tx_futex_timeout)			\
	iter(tx_bound_failed_late)		\
	iter(tx_unbound_failed)			\
	iter(tx_success)			\
	iter(wait_bound_exit)			\
	iter(stash_reg)				\
	iter(condition_failed)			\
	iter(condition_passed)			\
	iter(dummy_entry_point)			\
	iter(enter_interpreter)			\
	iter(finish_send)			\
	iter(finish_non_send)

#define mk_stat(name)				\
	long name;
	enum_stats(mk_stat)
#undef mk_stat
} stats;

#define EVENT(x) do { stats. x ++; } while (0)
#else
#define EVENT(x) do {} while (0)
#endif

struct low_level_state {
	cfg_label_t cfg_node;

	int nr_simslots;

	int last_operation_is_send;
	int await_bound_lls_exit;

	struct high_level_state *hls;

	int *mbox; /* Futex mbox */

	long rsp_delta;

	/* Once we've received a message from an LLS, we become bound
	 * to that LLS and in future will only receive messages from
	 * them.  Can be BOUND_LLS_EXITED if we've bound to a thread
	 * which has since exited, in which case all message receives
	 * will fail. */
	struct low_level_state *bound_lls;

	int nr_bound_sending_messages;
	struct msg_template **bound_sending_messages;
	int nr_unbound_sending_messages;
	struct msg_template **unbound_sending_messages;
	int nr_bound_receiving_messages;
	struct msg_template **bound_receiving_messages;
	int nr_unbound_receiving_messages;
	struct msg_template **unbound_receiving_messages;

#ifdef KEEP_LLS_HISTORY
	cfg_label_t history[LLS_HISTORY];
#endif
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
	/* If non-zero, the interpreter is currently making a memory
	   access on behalf of the guest and we should jump to this
	   address if the access fails. */
	unsigned long fault_recovery_addr;
	void *sigstack;
	unsigned char interpreter_stack[STACK_SIZE - 32 - sizeof(struct reg_struct)];
	struct reg_struct client_regs;
};

/* Each of these represents a bit of the underlying program which
   we've modified to include our entry branches.  Exiting back to a
   RIP in one of these is bad, so we just interpret for a bit longer
   if it looks like we're going to have to. */
struct entry_patch {
	unsigned long start;
	unsigned size;
	/* As it happens, the largest patch we ever put down is 5
	   bytes, but pad to 13 so as to get better alignment. */
#define MAX_PATCH_SIZE 13
	unsigned char content[MAX_PATCH_SIZE];
};
static int nr_entry_patches;
static struct entry_patch *entry_patches;

static struct low_level_state_array message_senders;
static struct low_level_state_array message_receivers;

typedef void exit_routine_t(struct reg_struct *);
static exit_routine_t *find_exit_stub(unsigned long rip);

static int
have_cloned;

static int
nr_queued_wakes;
#define MAX_QUEUED_WAKES 8
static int *
queued_wakes[8];

#if VERY_LOUD
#define debug(fmt, ...) dbg_msg("%d:%f: " fmt, gettid(), now(), ##__VA_ARGS__)
#else
#define debug(...) do {} while (0)
#endif

/* Bit of a hack: the last-freed address is nominally in unaccessible
   memory.  Just shadow it here. */
static unsigned long last_freed;

static void
futex(int *ptr, int op, int val, struct timespec *timeout)
{
	syscall(__NR_futex, (unsigned long)ptr, (unsigned long)op, (unsigned long)val, (unsigned long)timeout);
}

#ifndef NDEBUG
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
#endif

static void
safe_write(int fd, const void *buf, size_t buf_size)
{
	ssize_t s;
	while (buf_size != 0) {
		s = write(fd, buf, buf_size);
		if (s < 0) {
			err(1,
			    "writing %zd bytes to fd %d",
			    buf_size, fd);
		}
		if (s == 0) {
			errx(1, "EOF on fd %d while writing?", fd);
		}
		buf += s;
		buf_size -= s;
	}
}

#if VERY_LOUD
static void
reverse(char *start_ptr, char *end_ptr)
{
	while (start_ptr <= end_ptr) {
		char t = *start_ptr;
		*start_ptr = *end_ptr;
		*end_ptr = t;
		start_ptr++;
		end_ptr--;
	}
}

static void dbg_msg(const char *fmt, ...) __attribute__((format (printf, 1, 2)));
static void
dbg_msg(const char *fmt, ...)
{
	/* We're under the big lock, so no need to worry about
	 * synchronisation. */
	static char buf[1024];
	static const char fmt_int_chars[] = "0123456789abcdefZZZ";
	unsigned prod_idx;
	unsigned cons_idx;
	va_list args;

	int flags;
	unsigned long arg_ulong;
	int arg_int;
	const char *arg_str;
	double arg_double;
	int start_idx;
	char fmt_char;
	int arg_idx;
	unsigned base;

	va_start(args, fmt);

#define FLAG_L 1
#define FLAG_Z 2
	prod_idx = 0;
	cons_idx = 0;
	while (1) {
		/* Make sure that there's always enough space for
		   ``simple'' escapes. */
		if (prod_idx >= sizeof(buf) - 32) {
			safe_write(1, buf, prod_idx);
			prod_idx = 0;
		}

		if (fmt[cons_idx] == 0) {
			/* Messages should be \n terminated. */
			assert(prod_idx == 0);
			va_end(args);
			return;
		}
		if (fmt[cons_idx] == '\n') {
			buf[prod_idx++] = '\n';
			safe_write(1, buf, prod_idx);
			prod_idx = 0;
			cons_idx++;
			continue;
		}
		if (fmt[cons_idx] != '%') {
			buf[prod_idx++] = fmt[cons_idx++];
			continue;
		}
		/* Okay, we have a percento.  Deal with it. */
		cons_idx++;
		/* Formats which we need to handle:

		   %lx
		   %p
		   %s
		   %d
		   %x
		   %ld
		   %zx
		   %f
		*/
		flags = 0;
		while (1) {
			if (fmt[cons_idx] == 'l') {
				flags |= FLAG_L;
				cons_idx++;
			} else if (fmt[cons_idx] == 'z') {
				flags |= FLAG_Z;
				cons_idx++;
			} else {
				break;
			}
		}
		fmt_char = fmt[cons_idx++];
		if (fmt_char == 'p') {
			/* %p == 0x%lx */
			buf[prod_idx++] = '0';
			buf[prod_idx++] = 'x';
			flags = FLAG_L;
			fmt_char = 'x';
		}
		switch (fmt_char) {
		case 'x':
		case 'd':
			switch (flags & (FLAG_L | FLAG_Z)) {
			case 0:
				arg_int = va_arg(args, int);
				if (fmt_char == 'd' && arg_int < 0) {
					buf[prod_idx++] = '-';
					arg_ulong = -arg_int;
				} else {
					arg_ulong = (unsigned)arg_int;
				}
				break;
			case FLAG_L:
				arg_ulong = va_arg(args, unsigned long);
				if (fmt_char == 'd' && (long)arg_ulong < 0) {
					buf[prod_idx++] = '-';
					arg_ulong = -arg_ulong;
				}
				break;
			case FLAG_Z:
				arg_ulong = va_arg(args, size_t);
				break;
			default:
				abort();
			}
			if (arg_ulong == 0) {
				buf[prod_idx++] = '0';
				break;
			}
			if (fmt_char == 'x') {
				base = 16;
			} else {
				base = 10;
			}
			start_idx = prod_idx;
			while (arg_ulong != 0) {
				buf[prod_idx++] = fmt_int_chars[arg_ulong % base];
				arg_ulong /= base;
			}
			reverse(buf + start_idx, buf + prod_idx - 1);
			break;
		case 's':
			arg_str = va_arg(args, const char *);
			for (arg_idx = 0; arg_str[arg_idx]; arg_idx++) {
				buf[prod_idx++] = arg_str[arg_idx];
				if (prod_idx == sizeof(buf)) {
					safe_write(1, buf, prod_idx);
					prod_idx = 0;
				}
			}
			break;
		case 'f':
			arg_double = va_arg(args, double);
			if (isnan(arg_double)) {
				buf[prod_idx++] = 'N';
				buf[prod_idx++] = 'a';
				buf[prod_idx++] = 'N';
				break;
			}
			if (arg_double < 0) {
				buf[prod_idx++] = '-';
				arg_double = -arg_double;
			}
			if (isinf(arg_double)) {
				buf[prod_idx++] = 'i';
				buf[prod_idx++] = 'n';
				buf[prod_idx++] = 'f';
				break;
			}
			arg_ulong = (unsigned long)arg_double;
			arg_double -= arg_ulong;
			if (arg_ulong == 0) {
				buf[prod_idx++] = '0';
			} else {
				start_idx = prod_idx;
				while (arg_ulong >= 1) {
					buf[prod_idx++] = fmt_int_chars[arg_ulong % 10];
					arg_ulong /= 10;
				}
				reverse(buf + start_idx, buf + prod_idx - 1);
			}
			buf[prod_idx++] = '.';
			for (arg_idx = 0; arg_idx < 6; arg_idx++) {
				assert(arg_double < 1);
				arg_double *= 10;
				buf[prod_idx++] = fmt_int_chars[(int)arg_double];
				arg_double -= (int)arg_double;
			}
			break;
		default:
			abort();
		}
	}
#undef FLAG_L
#undef FLAG_Z
}
#endif

#if USE_CUSTOM_MALLOC
/* Simple malloc() implementation.  We don't really want to call into
   libc's malloc because that makes figuring out what's going on with
   double free bugs kind of tricky. */
struct alloc_hdr {
#define ALLOC_FLAG_FREE 1ul
#define ALLOC_FLAG_PREV_FREE 2ul
#define ALLOC_FLAG_FIRST 4ul
#define ALLOC_FLAG_LAST 8ul
/* Size includes header and padding. */
#define ALLOC_SIZE_MASK (~15ul)

	size_t sz_and_flags;
};

struct free_chunk {
	struct free_chunk *next;
	struct free_chunk **pprev;
};

struct alloc_arena {
	size_t sz; /* Min size of chunks in this arena */
	struct free_chunk free_chunks;
};

#define NR_ARENAS 8
#define MIN_ALLOC_SIZE (sizeof(struct free_chunk) + sizeof(struct alloc_hdr))
#define ALLOC_CHUNK_SIZE 4194304ul

static struct alloc_arena malloc_arenas[NR_ARENAS];

static void
sanity_check_allocator(void)
{
	int i;
	const struct free_chunk *fc;

	if (!SANITY_CHECK_ALLOCATOR) {
		return;
	}
	for (i = 0; i < NR_ARENAS; i++) {
		assert(malloc_arenas[i].sz >= MIN_ALLOC_SIZE);
		if (i != 0) {
			assert(malloc_arenas[i].sz > malloc_arenas[i-1].sz);
		}
		for (fc = malloc_arenas[i].free_chunks.next;
		     fc != &malloc_arenas[i].free_chunks;
		     fc = fc->next) {
			const struct alloc_hdr *hdr = (const struct alloc_hdr *)fc - 1;
			const struct alloc_hdr *footer;
			size_t sz;
			assert(hdr->sz_and_flags & ALLOC_FLAG_FREE);
			assert(!(hdr->sz_and_flags & ALLOC_FLAG_PREV_FREE));
			sz = hdr->sz_and_flags & ALLOC_SIZE_MASK;
			assert(sz >= malloc_arenas[i].sz);
			footer = (const struct alloc_hdr *)((unsigned long)hdr + sz - sizeof(struct alloc_hdr));
			assert(footer->sz_and_flags == hdr->sz_and_flags);
			if (!(hdr->sz_and_flags & ALLOC_FLAG_LAST)) {
				const struct alloc_hdr *next = footer + 1;
				assert(!(next->sz_and_flags & ALLOC_FLAG_FREE));
				assert(!(next->sz_and_flags & ALLOC_FLAG_FIRST));
				assert(next->sz_and_flags & ALLOC_FLAG_PREV_FREE);
			}
			if (hdr->sz_and_flags & ALLOC_FLAG_FIRST) {
				assert( ((unsigned long)hdr & ~PAGE_MASK) == 0);
			}
		}
	}
}

static void
init_allocator(void)
{
	int i;
	for (i = 0; i < NR_ARENAS; i++) {
		malloc_arenas[i].free_chunks.next = &malloc_arenas[i].free_chunks;
		malloc_arenas[i].free_chunks.pprev = &malloc_arenas[i].free_chunks.next;
	}

	malloc_arenas[0].sz = 32;
	malloc_arenas[1].sz = 64;
	malloc_arenas[2].sz = 128;
	malloc_arenas[3].sz = 256;
	malloc_arenas[4].sz = 512;
	malloc_arenas[5].sz = 1024;
	malloc_arenas[6].sz = 2048;
	malloc_arenas[7].sz = 4096;

	sanity_check_allocator();
}

static void
unregister_free_chunk(struct alloc_hdr *hdr)
{
	struct free_chunk *fc = (struct free_chunk *)(hdr + 1);
	size_t sz = hdr->sz_and_flags & ALLOC_SIZE_MASK;
	struct alloc_hdr *footer = (struct alloc_hdr *)((unsigned long)hdr + sz) - 1;

	assert(footer->sz_and_flags == hdr->sz_and_flags);
	assert(hdr->sz_and_flags & ALLOC_FLAG_FREE);
	assert(!(hdr->sz_and_flags & ALLOC_FLAG_PREV_FREE));
	fc->next->pprev = fc->pprev;
	*fc->pprev = fc->next;
}
static void
register_free_chunk(struct alloc_hdr *hdr)
{
	/* This is responsible for creating the footer */
	struct free_chunk *fc = (struct free_chunk *)(hdr + 1);
	size_t sz = hdr->sz_and_flags & ALLOC_SIZE_MASK;
	struct alloc_hdr *footer = (struct alloc_hdr *)((unsigned long)hdr + sz) - 1;
	int arena_idx;

#ifndef NDEBUG
	memset(hdr + 1, 0xab, sz - sizeof(*hdr));
#endif

	assert(hdr->sz_and_flags & ALLOC_FLAG_FREE);
	assert(!(hdr->sz_and_flags & ALLOC_FLAG_PREV_FREE));
	footer->sz_and_flags = hdr->sz_and_flags;
	for (arena_idx = 0; arena_idx < NR_ARENAS; arena_idx++) {
		if (arena_idx == NR_ARENAS - 1 ||
		    malloc_arenas[arena_idx+1].sz > sz) {
			malloc_arenas[arena_idx].free_chunks.next->pprev = &fc->next;
			fc->next = malloc_arenas[arena_idx].free_chunks.next;
			fc->pprev = &malloc_arenas[arena_idx].free_chunks.next;
			*fc->pprev = fc;
			return;
		}
	}
	abort();
}
static void *
cep_realloc(void *ptr, size_t new_sz)
{
	size_t orig_sz = new_sz;
	struct alloc_hdr *hdr;
	size_t old_sz;
	void *n;

	if (new_sz == 0) {
		cep_free(ptr);
		return NULL;
	}

	if (!ptr) {
		return cep_malloc(new_sz);
	}

	/* Add space for the header and round up size. */
	new_sz += sizeof(struct alloc_hdr);
	new_sz = (new_sz + ~ALLOC_SIZE_MASK) & ALLOC_SIZE_MASK;
	if (new_sz < MIN_ALLOC_SIZE) {
		new_sz = MIN_ALLOC_SIZE;
	}

	hdr = ptr;
	hdr--;
	assert(!(hdr->sz_and_flags & ALLOC_FLAG_FREE));
	old_sz = hdr->sz_and_flags & ALLOC_SIZE_MASK;
	if ( old_sz >= new_sz ) {
		/* We never trim blocks during realloc, so shrinking
		 * is a no-op. */
		debug("realloc(%p, %zd) -> %p (shrink from %zd)\n",
		       ptr, new_sz, ptr, old_sz);
		return ptr;
	}
	/* Can we satisfy the request by taking the next chunk? */
	if ( !(hdr->sz_and_flags & ALLOC_FLAG_LAST) ) {
		struct alloc_hdr *next = (struct alloc_hdr *)((unsigned long)hdr + old_sz);
		if (next->sz_and_flags & ALLOC_FLAG_FREE) {
			size_t next_sz = next->sz_and_flags & ALLOC_SIZE_MASK;
			size_t slop;
			if (old_sz + next_sz >= new_sz) {
				sanity_check_allocator();

				/* We can satisfy the realloc by
				 * expanding the current chunk into
				 * the next one. */
				unregister_free_chunk(next);

				slop = old_sz + next_sz - new_sz;
				assert(!(slop & ~ALLOC_SIZE_MASK));
				if (slop < 64) {
					if (!(next->sz_and_flags & ALLOC_FLAG_LAST)) {
						struct alloc_hdr *nextnext =
							(struct alloc_hdr *)((unsigned long)next + next_sz);
						assert(nextnext->sz_and_flags & ALLOC_FLAG_PREV_FREE);
						assert(!(nextnext->sz_and_flags & ALLOC_FLAG_FREE));
						nextnext->sz_and_flags &= ~ALLOC_FLAG_PREV_FREE;
					}
					new_sz = old_sz + next_sz;
				} else {
					struct alloc_hdr *slophdr =
						(struct alloc_hdr *)((unsigned long)hdr + new_sz);
					slophdr->sz_and_flags =
						slop |
						ALLOC_FLAG_FREE |
						(next->sz_and_flags & ALLOC_FLAG_LAST);
					register_free_chunk(slophdr);
				}
				hdr->sz_and_flags &= ~ALLOC_SIZE_MASK;
				assert(!(new_sz & ALLOC_SIZE_MASK));
				hdr->sz_and_flags |= new_sz;
				debug("realloc(%p, %zd) -> %p (merge up)\n",
				       ptr, new_sz, ptr);
				sanity_check_allocator();
				return ptr;
			}
		}
	}

	debug("realloc(%p, %zd) -> via malloc\n", ptr, new_sz);
	/* Can't do it by expanding this chunk.  Allocate a new
	 * one. */
	n = cep_malloc(orig_sz);
	if (orig_sz < old_sz) {
		memcpy(n, ptr, orig_sz);
	} else {
		memcpy(n, ptr, old_sz);
	}
	cep_free(ptr);
	return n;
}
static void *
cep_malloc(size_t sz)
{
	int arena_idx;
	struct alloc_hdr *hdr;
	struct free_chunk *fc;
	size_t chunk_size;
	size_t slop;

	sanity_check_allocator();

	/* Add space for the header and round up size. */
	sz += sizeof(struct alloc_hdr);
	sz = (sz + ~ALLOC_SIZE_MASK) & ALLOC_SIZE_MASK;
	if (sz < MIN_ALLOC_SIZE) {
		sz = MIN_ALLOC_SIZE;
	}

	assert(sz <= ALLOC_CHUNK_SIZE);

	/* Find the arena. */
	for (arena_idx = 0;
	     arena_idx < NR_ARENAS &&
		     (malloc_arenas[arena_idx].sz < sz ||
		      malloc_arenas[arena_idx].free_chunks.next ==
		          &malloc_arenas[arena_idx].free_chunks);
	     arena_idx++) {
		/* nop */
	}

	if (arena_idx == NR_ARENAS) {
		/* No sufficiently large free chunks, so invent one. */
		void *new_chunk = mmap(NULL, ALLOC_CHUNK_SIZE, PROT_READ | PROT_WRITE,
				       MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
		struct alloc_hdr *new_hdr = new_chunk;
		new_hdr->sz_and_flags =
			ALLOC_CHUNK_SIZE |
			ALLOC_FLAG_FREE |
			ALLOC_FLAG_FIRST |
			ALLOC_FLAG_LAST;
		register_free_chunk(new_hdr);
		arena_idx = NR_ARENAS - 1;
	}

	fc = malloc_arenas[arena_idx].free_chunks.next;
	assert(fc != &malloc_arenas[arena_idx].free_chunks);
	hdr = (struct alloc_hdr *)fc - 1;

	assert(hdr->sz_and_flags & ALLOC_FLAG_FREE);
	chunk_size = hdr->sz_and_flags & ALLOC_SIZE_MASK;
	assert(chunk_size >= malloc_arenas[arena_idx].sz);
	assert(chunk_size >= sz);

	unregister_free_chunk(hdr);
	hdr->sz_and_flags &= ~ALLOC_FLAG_FREE;
	slop = chunk_size - sz;
	if (slop >= 64) {
		struct alloc_hdr *slophdr = (struct alloc_hdr *)((unsigned long)hdr + sz);
		slophdr->sz_and_flags =
			slop |
			ALLOC_FLAG_FREE |
			(hdr->sz_and_flags & ALLOC_FLAG_LAST);
		register_free_chunk(slophdr);
		hdr->sz_and_flags &= ~ALLOC_SIZE_MASK;
		hdr->sz_and_flags |= sz;
	} else if (!(hdr->sz_and_flags & ALLOC_FLAG_LAST)) {
		struct alloc_hdr *nexthdr = (struct alloc_hdr *)((unsigned long)hdr + chunk_size);
		assert(nexthdr->sz_and_flags & ALLOC_FLAG_PREV_FREE);
		assert(!(nexthdr->sz_and_flags & ALLOC_FLAG_FREE));
		nexthdr->sz_and_flags &= ~ALLOC_FLAG_PREV_FREE;
	}

	sanity_check_allocator();
	debug("malloc(%zd) -> %p\n", sz, hdr + 1);
	return hdr + 1;
}
static void
cep_free(const void *ptr)
{
	struct alloc_hdr *hdr;
	size_t sz;

	hdr = (struct alloc_hdr *)ptr;
	hdr--;

	sanity_check_allocator();

	assert(!(hdr->sz_and_flags & ALLOC_FLAG_FREE));
	sz = hdr->sz_and_flags & ALLOC_SIZE_MASK;
	assert(sz >= MIN_ALLOC_SIZE);

	debug("free(%p), sz %zd\n", ptr, sz);

	if (!(hdr->sz_and_flags & ALLOC_FLAG_LAST)) {
		struct alloc_hdr *nexthdr = (struct alloc_hdr *)((unsigned long)hdr + sz);
		assert(!(nexthdr->sz_and_flags & ALLOC_FLAG_PREV_FREE));
		if (nexthdr->sz_and_flags & ALLOC_FLAG_FREE) {
			unregister_free_chunk(nexthdr);
			sz += nexthdr->sz_and_flags & ALLOC_SIZE_MASK;
		} else {
			nexthdr->sz_and_flags |= ALLOC_FLAG_PREV_FREE;
		}
	}
	if (hdr->sz_and_flags & ALLOC_FLAG_PREV_FREE) {
		struct alloc_hdr *footer = (struct alloc_hdr *)(hdr - 1);
		struct alloc_hdr *prevhdr;
		assert(!(hdr->sz_and_flags & ALLOC_FLAG_FIRST));
		assert(footer->sz_and_flags & ALLOC_FLAG_FREE);
		assert(!(footer->sz_and_flags & ALLOC_FLAG_PREV_FREE));
		assert(!(footer->sz_and_flags & ALLOC_FLAG_LAST));
		prevhdr = (struct alloc_hdr *)((unsigned long)hdr - (footer->sz_and_flags & ALLOC_SIZE_MASK));
		assert(prevhdr->sz_and_flags == footer->sz_and_flags);
		unregister_free_chunk(prevhdr);
		sz += prevhdr->sz_and_flags & ALLOC_SIZE_MASK;
		prevhdr->sz_and_flags |= hdr->sz_and_flags & ALLOC_FLAG_LAST;
		hdr = prevhdr;
	}

	hdr->sz_and_flags |= ALLOC_FLAG_FREE;
	assert(!(hdr->sz_and_flags & ALLOC_FLAG_PREV_FREE));
	hdr->sz_and_flags &= ~ALLOC_SIZE_MASK;
	assert(!(sz & ~ALLOC_SIZE_MASK));
	hdr->sz_and_flags |= sz;
	register_free_chunk(hdr);

	sanity_check_allocator();
}
#else
static void
sanity_check_allocator(void)
{
}
static void
init_allocator(void)
{
}
static void *
cep_malloc(size_t sz)
{
	return malloc(sz);
}
static void *
cep_realloc(void *what, size_t sz)
{
	return realloc(what, sz);
}
static void
cep_free(const void *what)
{
	free((void *)what);
}
#endif

static void
sanity_check_low_level_state(const struct low_level_state *lls, int expected_present)
{
	int i;
	int present;
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
	int res;
	switch (sz) {
#define do_sz(size, type)						\
		case size: {						\
			unsigned type tmp;				\
			unsigned long t2;				\
			asm (						\
				"lea 1f(%%rip), %[t2]\n"		\
				"movq %[t2], %%gs:8\n"			\
				"mov %[addr], %[tmpreg]\n"		\
				"mov %[tmpreg], %[dst]\n"		\
				"movq $0, %%gs:8\n"			\
				"mov $1, %[res]\n"			\
				"2:\n"					\
				".section .text.fault_handlers\n"	\
				"1: mov $0, %[res]\n"			\
				"jmp 2b\n"				\
				".previous\n"				\
				: [tmpreg] "=r" (tmp),			\
				  [t2] "=r" (t2),			\
				  [dst] "=m" (*(unsigned type *)dst),	\
				  [res] "=r" (res)			\
				: [addr] "m" ( *(unsigned type *)addr)	\
				);					\
			return res;					\
		}
		do_sz(1, char)
		do_sz(2, short)
		do_sz(4, int)
		do_sz(8, long)
#undef do_sz
	case 16: {
		unsigned long tmp;
		asm (
			"leaq 1f(%%rip), %[tmpreg]\n"
			"movq %[tmpreg], %%gs:8\n"
			"mov (%[addr]), %[tmpreg]\n"
			"mov %[tmpreg], (%[dst])\n"
			"mov 8(%[addr]), %[tmpreg]\n"
			"mov %[tmpreg], 8(%[dst])\n"
			"movq $0, %%gs:8\n"
			"mov $1, %[res]\n"
			"2:\n"
			".section .text.fault_handlers\n"
			"1: mov $0, %[res]\n"
			"jmp 2b\n"
			".previous\n"
			: [tmpreg] "=r" (tmp),
			  [res] "=r" (res)
			: [addr] "r" (addr),
			  [dst] "r" (dst)
			: "memory"
			);
		return res;
	}
	default:
		abort();
	}
}
#define fetch_guest(host_ptr, guest_ptr) __fetch_guest(sizeof(*host_ptr), (void *)host_ptr, guest_ptr)

/* Check whether the current stack matches up with the a CEP entry
 * point. */
static int
ctxt_matches(const struct cep_entry_ctxt *ctxt, const struct reg_struct *regs)
{
	unsigned x;
	if (skip_context_check)
		return 1;
	for (x = 0; x < ctxt->nr_stack_slots; x++) {
		unsigned long guest_val;
		if (!fetch_guest(&guest_val, regs->rsp + ctxt->stack[x].offset))
			return 0;
		if (guest_val != ctxt->stack[x].expected_value) {
			debug("Context mismatch: %lx != %lx\n",
			      guest_val, ctxt->stack[x].expected_value);
			return 0;
		}
	}
	return 1;
}

static struct low_level_state *
new_low_level_state(struct high_level_state *hls, int nr_simslots)
{
	struct low_level_state *lls = cep_malloc(sizeof(*lls) + nr_simslots * sizeof(lls->simslots[0]));
	memset(lls, 0, sizeof(*lls) + nr_simslots * sizeof(lls->simslots[0]));
	lls->nr_simslots = nr_simslots;
	lls->hls = hls;
	sanity_check_low_level_state(lls, 0);
	EVENT(lls_created);
	return lls;
}

static void
start_low_level_thread(struct high_level_state *hls, cfg_label_t starting_label, long rsp_delta, int nr_simslots)
{
	struct low_level_state *lls = new_low_level_state(hls, nr_simslots);
	int i;

	lls->cfg_node = starting_label;
	lls->rsp_delta = rsp_delta;
	low_level_state_push(&hls->ll_states, lls);
	sanity_check_low_level_state(lls, 1);
#ifdef KEEP_LLS_HISTORY
	lls->history[LLS_HISTORY-1] = starting_label;
#endif
	debug("%p(%s): Start new LLS\n",
	      lls,
	      plan.cfg_nodes[starting_label].id);
	for (i = 0; i < plan.cfg_nodes[starting_label].nr_set_entry; i++)
		lls->simslots[plan.cfg_nodes[starting_label].set_entry[i].slot] = 1;
}

static void
init_high_level_state(struct high_level_state *hls)
{
	memset(hls, 0, sizeof(*hls));
	EVENT(hls_created);
}

#define cpu_user_regs reg_struct
#define STATIC static
#include "x86_emulate.h"
#include "../x86_emulate.c"
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
	assert(hls);
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
	assert(hls);
	current_cfg_node = NULL;
	for (i = 0; i < hls->ll_states.sz; i++) {
		if (current_cfg_node)
			assert(current_cfg_node->rip == plan.cfg_nodes[hls->ll_states.content[i]->cfg_node].rip);
		else
			current_cfg_node = &plan.cfg_nodes[hls->ll_states.content[i]->cfg_node];
	}
	assert(current_cfg_node);
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
	seen = *what;
	if (seen != oldval)
		return seen;
	asm ("lock cmpxchg %3, %1\n"
	     : "=a" (seen), "+m" (*what)
	     : "0" (oldval),
	       "r" (newval)
	     : "memory");
	return seen;
}

static int
xchg(int *what, int newval)
{
	int seen;
	asm ("xchg %0, %1\n"
	     : "=r" (seen), "=m" (*what)
	     : "0" (newval)
	     : "memory");
	return seen;
}

/* Note that this is non-atomic!  That's okay, because all of the
 * callers are under the big lock. */
static int
na_xchg(int *val, int newval)
{
	int oldval = *val;
	*val = newval;
	return oldval;
}

static void
store_release(int *what, int val)
{
	*(volatile int *)what = val;
}

/* Arrange that we will perform a futex wake on @ptr the next time we
 * release the big lock. */
static void
queue_wake(int *ptr)
{
	if (nr_queued_wakes == MAX_QUEUED_WAKES) {
		/* Too much stuff queued -> do it immediately, even if
		   that does mean forcing some other poor thread to
		   spin waiting for the big lock. */
		debug("Immediate wake on %p\n", ptr);
		futex(ptr, FUTEX_WAKE, 1, NULL);
	} else {
		debug("Queue wake on %p\n", ptr);
		queued_wakes[nr_queued_wakes] = ptr;
		nr_queued_wakes++;
	}
}

union big_lock_t {
	int word;
	struct {
		short prod;
		short cons;
	};
} big_lock;

static void
acquire_big_lock(void)
{
	union big_lock_t old;
	union big_lock_t new;
	union big_lock_t seen;
	short ticket;
	old = big_lock;
	while (1) {
		new = old;
		new.prod++;
		seen.word = cmpxchg(&big_lock.word, old.word, new.word);
		if (seen.word == old.word) {
			break;
		}
		old = seen;
	}
	ticket = new.prod - 1;
	while (1) {
		old = big_lock;
		if (old.cons == ticket) {
			break;
		}
		futex(&big_lock.word, FUTEX_WAIT, old.word, NULL);
	}
}
static void
release_big_lock(void)
{
	/* Release the big lock, and issue a futex wake if
	 * appropriate.  We only do one wake each time we release the
	 * lock, because whoever we wake will immediately acquire the
	 * lock, and so there's no point in having lots of people wake
	 * up just to contend for the lock. */
	union big_lock_t old;
	union big_lock_t new;
	union big_lock_t seen;
	int *wake;

	if (nr_queued_wakes != 0) {
		nr_queued_wakes--;
		wake = queued_wakes[nr_queued_wakes];
	} else {
		wake = NULL;
	}

	old = big_lock;
	while (1) {
		new = old;
		new.cons++;
		seen.word = cmpxchg(&big_lock.word, old.word, new.word);
		if (seen.word != old.word) {
			old = seen;
			continue;
		}
		if (new.cons != new.prod) {
			futex(&big_lock.word, FUTEX_WAKE, INT_MAX, NULL);
		}
		if (wake) {
			futex(wake, FUTEX_WAKE, 1, NULL);
		}
		return;
	}
}

static void
release_lls(struct low_level_state *lls)
{
	cep_free(lls);
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

static unsigned long
bytecode_fetch_const(const unsigned short **bytecode,
		     enum byte_code_type type)
{
	unsigned long res;

	switch (type) {
	case bct_bit:
		res = (*bytecode)[0] & 1;
		(*bytecode)++;
		break;
	case bct_byte:
		res = (*bytecode)[0] & 0xff;
		(*bytecode)++;
		break;
	case bct_short:
		res = (*bytecode)[0];
		(*bytecode)++;
		break;
	case bct_int:
		res = (*bytecode)[0] | ((unsigned)(*bytecode)[1] << 16);
		(*bytecode) += 2;
		break;
	case bct_long:
		res = (*bytecode)[0] |
			((unsigned long)(*bytecode)[1] << 16) |
			((unsigned long)(*bytecode)[2] << 32) |
			((unsigned long)(*bytecode)[3] << 48);
		(*bytecode) += 4;
		break;
	case bct_longlong:
		/* Can't just return these as longs */
		abort();
	}
	return res;
}

static unsigned long
bytecode_mask(unsigned long val, enum byte_code_type type)
{
	switch (type) {
	case bct_bit:
		return val & 1;
	case bct_byte:
		return val & 0xff;
	case bct_short:
		return val & 0xffff;
	case bct_int:
		return val & 0xffffffff;
	case bct_long:
		return val;
	case bct_longlong:
		/* Can't just return these as longs */
		abort();
	}
	abort();
}

static unsigned long
bytecode_fetch_slot(const unsigned short **bytecode,
		    enum byte_code_type type,
		    const struct low_level_state *lls,
		    const struct msg_template *rx_template,
		    const struct msg_template *tx_template,
		    const struct low_level_state *tx_lls)
{
	simslot_t idx = bytecode_fetch_const(bytecode, bct_int);
	int msg_slot;

	assert(idx < lls->nr_simslots);
	/* Is the slot overridden by the message? */
	if (rx_template) {
		assert(tx_lls);
		assert(rx_template->payload_size == tx_template->payload_size);
		for (msg_slot = 0; msg_slot < rx_template->payload_size; msg_slot++) {
			if (rx_template->payload[msg_slot] == idx) {
				/* Yes */
				assert(tx_template->payload[msg_slot] < tx_lls->nr_simslots);
				return bytecode_mask(
					tx_lls->simslots[tx_template->payload[msg_slot]],
					type);
			}
		}
	}
	return bytecode_mask(lls->simslots[idx], type);
}

/* malloc()ed bytecode stack regions */
/* Make each overflow area be one page */
#define NR_STACK_SLOTS_PER_OVERFLOW 128
struct stack_overflow {
	struct stack_overflow *prev;
	struct stack_overflow *next;
	unsigned long base[NR_STACK_SLOTS_PER_OVERFLOW];
};
/* The part of the bytecode stack which is allocated on the
 * interpreter stack. */
#define NR_STACK_SLOTS_INLINE 16
struct bytecode_stack {
	unsigned long *ptr;
	unsigned long *overflow_limit;
	unsigned long *underflow_limit;
	unsigned long inlne[NR_STACK_SLOTS_INLINE];
	struct stack_overflow *overflow;
};

static void
init_bytecode_stack(struct bytecode_stack *stack)
{
#ifndef NDEBUG
	memset(stack, 0xab, sizeof(*stack));
#endif
	stack->ptr = stack->inlne;
	stack->underflow_limit = stack->inlne;
	stack->overflow_limit = stack->inlne + NR_STACK_SLOTS_INLINE;
	stack->overflow = NULL;
}

static void
cleanup_stack(const struct bytecode_stack *_stack)
{
	struct bytecode_stack *stack = (struct bytecode_stack *)_stack;
	struct stack_overflow *a, *b;
	for (a = stack->overflow; a; a = b) {
		b = a->next;
		cep_free(a);
	}
}

static void
bytecode_push(struct bytecode_stack *stack, unsigned long val, enum byte_code_type type)
{
	if (stack->ptr == stack->overflow_limit) {
		struct stack_overflow *o;
		if (stack->ptr == stack->inlne + NR_STACK_SLOTS_INLINE) {
			/* Transition from inline stack to overflow
			 * stack. */
			if (stack->overflow) {
				o = stack->overflow;
			} else {
				o = cep_malloc(sizeof(*o));
				o->next = NULL;
				o->prev = NULL;
				stack->overflow = o;
			}
		} else {
			/* Just overflowed an overflow stack */
			struct stack_overflow *old_o =
				(struct stack_overflow *)((unsigned long)stack->ptr - sizeof(*old_o));
			if (old_o->next) {
				o = old_o->next;
			} else {
				o = cep_malloc(sizeof(*o));
				o->next = NULL;
				o->prev = old_o;
				old_o->next = o;
			}
		}
		stack->ptr = o->base;
		stack->overflow_limit = o->base + NR_STACK_SLOTS_PER_OVERFLOW;
		stack->underflow_limit = o->base;
	}
	*stack->ptr = bytecode_mask(val, type);
	stack->ptr++;
}

static void
bytecode_push_longlong(struct bytecode_stack *stack, const unsigned char *bytes)
{
	const unsigned long *words = (const unsigned long *)bytes;
	bytecode_push(stack, words[0], bct_long);
	bytecode_push(stack, words[1], bct_long);
}

static unsigned long
bytecode_pop(struct bytecode_stack *stack, enum byte_code_type type)
{
	unsigned long res;

	if (stack->ptr == stack->underflow_limit) {
		struct stack_overflow *old_o;
		assert(stack->ptr != stack->inlne); /* otherwise the
						     * stack really
						     * has
						     * underflowed. */
		old_o = (struct stack_overflow *)((unsigned long)stack->ptr -
						  offsetof(struct stack_overflow, base[0]));
		if (old_o->prev) {
			/* Underflowed from one overflow stack to another. */
			struct stack_overflow *o = old_o->prev;
			stack->ptr = o->base + NR_STACK_SLOTS_PER_OVERFLOW;
			stack->underflow_limit = o->base;
		} else {
			/* Underflowed from an overflow stack to the inline stack. */
			stack->ptr = stack->inlne + NR_STACK_SLOTS_INLINE;
			stack->underflow_limit = stack->inlne;
		}
		stack->overflow_limit = stack->ptr;
	}

	stack->ptr--;
	res = *stack->ptr;
	return bytecode_mask(res, type);
}

static size_t
bct_size(enum byte_code_type type)
{
	switch (type) {
	case bct_bit:  abort();
	case bct_byte: return 1;
	case bct_short: return 2;
	case bct_int: return 4;
	case bct_long: return 8;
	case bct_longlong: return 16;
	}
	abort();
}

/* Returns 1 if the bytecode finishes with bcop_succeed and 0
 * otherwise. */
static int
eval_bytecode(const unsigned short *bytecode,
	      const struct low_level_state *lls,
	      const struct msg_template *rx_template,
	      const struct msg_template *tx_message,
	      const struct low_level_state *tx_lls)
{
	struct bytecode_stack stack;
	enum byte_code_op op;
	enum byte_code_type type;
	int res;

	if (disable_sideconditions || !bytecode)
		return 1;

	EVENT(bytecode_evaluated);

	init_bytecode_stack(&stack);
	while (1) {
		op = bytecode_op(*bytecode);
		type = bytecode_type(*bytecode);
		bytecode++;
		switch (op) {
		case bcop_push_const:
			bytecode_push(&stack, bytecode_fetch_const(&bytecode, type), type);
			break;
		case bcop_push_slot:
			bytecode_push(&stack, bytecode_fetch_slot(&bytecode, type, lls, rx_template, tx_message, tx_lls), type);
			break;

		case bcop_cmp_eq:
			bytecode_push(&stack, bytecode_pop(&stack, type) == bytecode_pop(&stack, type), bct_bit);
			break;
		case bcop_cmp_ltu: {
			unsigned long arg1 = bytecode_pop(&stack, type);
			unsigned long arg2 = bytecode_pop(&stack, type);
			bytecode_push(&stack, arg2 < arg1, bct_bit);
			debug("bcop_cmpltu: %lx < %lx -> %d\n", arg1, arg2, arg2 < arg1);
			break;
		}
		case bcop_cmp_lts: {
			unsigned res;
			switch (type) {
#define do_type(bct_type, c_type, fmt)					\
				case bct_type: {			\
					c_type arg1 = bytecode_pop(&stack, bct_type); \
					c_type arg2 = bytecode_pop(&stack, bct_type); \
					res = arg2 < arg1;		\
					debug("bcop_cmplts: %"fmt" < %"fmt" -> %d\n", arg1, arg2, res); \
					break;				\
				}
				do_type(bct_byte, char, "x");
				do_type(bct_short, short, "x");
				do_type(bct_int, int, "x");
				do_type(bct_long, long, "lx");
#undef do_type
			default:
				abort();
			}
			bytecode_push(&stack, res, bct_bit);
			break;
		}
		case bcop_add: {
			unsigned long arg1 = bytecode_pop(&stack, type);
			unsigned long arg2 = bytecode_pop(&stack, type);
			bytecode_push(&stack, arg1 + arg2, type);
			debug("bcop_add: %lx + %lx -> %lx\n", arg1, arg2, arg1 + arg2);
			break;
		}
		case bcop_and: {
			unsigned long arg1 = bytecode_pop(&stack, type);
			unsigned long arg2 = bytecode_pop(&stack, type);
			bytecode_push(&stack, arg1 & arg2, type);
			debug("bcop_and: %lx & %lx -> %lx\n", arg1, arg2, arg1 & arg2);
			break;
		}
		case bcop_or: {
			unsigned long arg1 = bytecode_pop(&stack, type);
			unsigned long arg2 = bytecode_pop(&stack, type);
			bytecode_push(&stack, arg1 | arg2, type);
			debug("bcop_and: %lx | %lx -> %lx\n", arg1, arg2, arg1 | arg2);
			break;
		}
		case bcop_xor: {
			unsigned long arg1 = bytecode_pop(&stack, type);
			unsigned long arg2 = bytecode_pop(&stack, type);
			bytecode_push(&stack, arg1 & arg2, type);
			debug("bcop_xor: %lx ^ %lx -> %lx\n", arg1, arg2, arg1 ^ arg2);
			break;
		}
		case bcop_mul: {
			unsigned long arg1 = bytecode_pop(&stack, type);
			unsigned long arg2 = bytecode_pop(&stack, type);
			bytecode_push(&stack, arg1 * arg2, type);
			debug("bcop_mul: %lx * %lx -> %lx\n", arg1, arg2, arg1 * arg2);
			break;
		}
		case bcop_shl: {
			unsigned long arg1 = bytecode_pop(&stack, type);
			unsigned long arg2 = bytecode_pop(&stack, bct_byte);
			debug("bcop_shl: %lx << %lx -> %lx\n", arg1, arg2, arg2 << arg1);
			bytecode_push(&stack, arg2 << arg1, type);
			break;
		}
		case bcop_shr: {
			unsigned long arg1 = bytecode_pop(&stack, type);
			unsigned long arg2 = bytecode_pop(&stack, bct_byte);
			debug("bcop_shr: %lx >> %lx -> %lx\n", arg1, arg2, arg2 >> arg1);
			bytecode_push(&stack, arg2 >> arg1, type);
			break;
		}
		case bcop_sar: {
			unsigned long arg1 = bytecode_pop(&stack, type);
			long arg2 = bytecode_pop(&stack, bct_byte);
			unsigned long res;
			switch (type) {
			case bct_byte:
				res = (char)arg2 >> arg1;
				break;
			case bct_short:
				res = (short)arg2 >> arg1;
				break;
			case bct_int:
				res = (int)arg2 >> arg1;
				break;
			case bct_long:
				res = (long)arg2 >> arg1;
				break;
			default:
				abort();
			}
			debug("bcop_sar: %lx >> %lx -> %lx\n", arg1, arg2, res);
			bytecode_push(&stack, res, type);
			break;
		}

		case bcop_not:
			bytecode_push(&stack, ~bytecode_pop(&stack, type), type);
			break;
		case bcop_neg: {
			unsigned long inp = bytecode_pop(&stack, type);
			unsigned long res;
			switch (type) {
			case bct_bit:
				if (inp)
					res = 0;
				else
					res = ~0ul;
				break;
			case bct_byte:
				res = -(char)inp;
				break;
			case bct_short:
				res = -(short)inp;
				break;
			case bct_int:
				res = -(int)inp;
				break;
			case bct_long:
				res = -(long)inp;
				break;
			default:
				abort();
			}
			bytecode_push(&stack, res, type);
			debug("bcop_neg: -%lx -> %lx\n", inp, res);
			break;
		}
		case bcop_sign_extend64: {
			unsigned long inp = bytecode_pop(&stack, type);
			unsigned long res;
			switch (type) {
			case bct_bit:
				res = ((long)inp << 63) >> 63;
				break;
			case bct_byte:
				res = ((long)inp << 56) >> 56;
				break;
			case bct_short:
				res = ((long)inp << 48) >> 48;
				break;
			case bct_int:
				res = ((long)inp << 32) >> 32;
				break;
			case bct_long:
				res = inp;
				break;
			default:
				abort();
			}
			bytecode_push(&stack, res, bct_long);
			break;
		}
		case bcop_sign_extend32: {
			unsigned long inp = bytecode_pop(&stack, type);
			unsigned long res;
			switch (type) {
			case bct_bit:
				res = ((int)inp << 31) >> 31;
				break;
			case bct_byte:
				res = ((int)inp << 24) >> 24;
				break;
			case bct_short:
				res = ((int)inp << 16) >> 16;
				break;
			default:
				abort();
			}
			bytecode_push(&stack, res, bct_int);
			break;
		}
		case bcop_zero_extend64: {
			unsigned long inp = bytecode_pop(&stack, type);
			bytecode_push(&stack, inp, bct_long);
			break;
		}
		case bcop_zero_extend32: {
			unsigned long inp = bytecode_pop(&stack, type);
			bytecode_push(&stack, inp, bct_int);
			break;
		}
		case bcop_zero_extend16: {
			unsigned long inp = bytecode_pop(&stack, type);
			bytecode_push(&stack, inp, bct_short);
			break;
		}
		case bcop_zero_extend8: {
			unsigned long inp = bytecode_pop(&stack, type);
			bytecode_push(&stack, inp, bct_byte);
			break;
		}

		case bcop_load: {
			unsigned long addr = bytecode_pop(&stack, bct_long);
			unsigned char buf[16];
			if (addr == CONFIG_LASTFREE_ADDR) {
				memcpy(buf, &last_freed, 8);
			} else {
				if (!__fetch_guest(bct_size(type), buf, addr)) {
					debug("fault fetching from %lx!\n", addr);
					res = 0;
					goto out;
				}
			}
			if (type == bct_longlong) {
				bytecode_push_longlong(&stack, buf);
			} else {
				unsigned long data = bytecode_mask(*(unsigned long *)buf, type);
				debug("%p(%s): load(%lx) -> %lx\n", lls, plan.cfg_nodes[lls->cfg_node].id, addr, data);
				bytecode_push(&stack, data, type);
			}
			break;
		}

		case bcop_badptr: {
			unsigned long addr = bytecode_pop(&stack, bct_long);
			unsigned char buf;
			int res;
			res = !fetch_guest(&buf, addr);
			bytecode_push(&stack, res, bct_bit);
			break;
		}

		case bcop_mux0x: {
			unsigned cond = bytecode_pop(&stack, bct_bit);
			unsigned long zero = bytecode_pop(&stack, type);
			unsigned long nzero = bytecode_pop(&stack, type);
			unsigned long res = cond ? nzero : zero;
			bytecode_push(&stack, res, type);
			debug("bcop_mux0x: %d ? %lx : %lx -> %lx\n", cond,
			      nzero, zero, res);
			break;
		}

		case bcop_fail_if: {
			if (bytecode_pop(&stack, bct_bit)) {
				res = 0;
				goto out;
			}
			break;
		}
		case bcop_succeed: {
			res = 1;
			goto out;
		}
		}
	}

out:
	cleanup_stack(&stack);
	return res;
}

static unsigned long
fetch_fs_base(void)
{
	unsigned long res;
	arch_prctl(ARCH_GET_FS, (unsigned long)&res);
	return res;
}

struct exit_emulation_ctxt {
	struct x86_emulate_ctxt ctxt;
	struct entry_patch *patch;
};

static int
exit_emulator_read(enum x86_segment seg,
		   unsigned long offset,
		   void *p_data,
		   unsigned int bytes,
		   struct x86_emulate_ctxt *_ctxt)
{
	unsigned long base;
	/* XXX should trap any faults here, so that we can set up a
	   correct signal frame. XXX */
	switch (seg) {
	case x86_seg_ds:
	case x86_seg_ss:
		base = 0;
		break;
	case x86_seg_fs:
		base = fetch_fs_base();
		break;
	default:
		abort();
	}
	memcpy(p_data, (const void *)offset + base, bytes);
	return X86EMUL_OKAY;
}

static int
exit_emulator_insn_fetch(enum x86_segment seg,
			 unsigned long offset,
			 void *p_data,
			 unsigned int bytes,
			 struct x86_emulate_ctxt *_ctxt)
{
	struct exit_emulation_ctxt *ctxt = (struct exit_emulation_ctxt *)_ctxt;
	struct entry_patch *patch = ctxt->patch;
	int from_patch;
	if (!patch || offset >= patch->start + patch->size) {
		memcpy(p_data, (const void *)offset, bytes);
	} else {
		from_patch = patch->size - (offset - patch->start);
		if (from_patch > bytes)
			from_patch = bytes;
		memcpy(p_data, patch->content + offset - patch->start, from_patch);
		if (from_patch < bytes)
			memcpy(p_data + from_patch, (const void *)(offset + from_patch), bytes - from_patch);
	}
	return X86EMUL_OKAY;
}

static const struct x86_emulate_ops
exit_emulator_ops = {
	.read = exit_emulator_read,
	.insn_fetch = exit_emulator_insn_fetch,
	.write = emulator_write,
	.cmpxchg = emulator_cmpxchg,
};

static void
restart_interpreter(void)
{
	/* We tried to exit the interpreter and then trod on another
	 * entry point.  Try that again. */
	debug("Restart interpreter at %lx (stack %lx).\n",
	      find_pts()->client_regs.rip,
	      find_pts()->initial_interpreter_rsp);
	EVENT(restart_interpreter);
	release_big_lock();
	asm volatile (
		"    mov %%gs:0, %%rsp\n"      /* Reset the stack */
		"    subq %0, %%rsp\n"         /* Make sure we don't tread on stashed registers */
		"    jmp start_interpreting\n" /* Restart the interpreter */
		:
		: "i" (sizeof(struct reg_struct) + 8)
		);
	debug("Huh?  Restart interpreter didn't work\n");
	abort();
}

/* Emulate a single instruction in a patch epilogue. */
static void
exit_emul(struct entry_patch *patch)
{
	struct exit_emulation_ctxt ctxt = {
		.ctxt = {
			.regs = &find_pts()->client_regs,
			.addr_size = 64,
			.sp_size = 64,
			.force_writeback = 0,
		}
	};
	int r;
	ctxt.patch = patch;
	EVENT(exit_emulate);
	r = x86_emulate(&ctxt.ctxt, &exit_emulator_ops);
	assert(r == X86EMUL_OKAY);
}

static void
exit_interpreter(void)
{
	struct per_thread_state *pts = find_pts();
	exit_routine_t *exit_routine;
	int i;
	int j;
	int hit_patch;
	debug("Exit to %lx, rax %lx, rbp %lx\n",
	      pts->client_regs.rip,
	      pts->client_regs.rax,
	      pts->client_regs.rbp);
	hit_patch = 1;
	while (hit_patch) {
		hit_patch = 0;
		/* Check whether we've hit another entry point. */
		for (j = 0; j < plan.nr_entry_points; j++) {
			if (plan.entry_points[j]->orig_rip == pts->client_regs.rip) {
				restart_interpreter();
			}
		}
		for (i = 0; i < nr_entry_patches; i++) {
			if (pts->client_regs.rip >= entry_patches[i].start &&
			       pts->client_regs.rip < entry_patches[i].start + entry_patches[i].size) {
				/* We're in danger of exiting into the
				   middle of an instruction which we
				   patched.  That's basically never a
				   good idea, so interpret for another
				   couple of instructions. */
				debug("Destination RIP %lx is in the middle of entry point patch [%lx,%lx); interpret.\n",
				      pts->client_regs.rip,
				      entry_patches[i].start,
				      entry_patches[i].start + entry_patches[i].size);
				hit_patch = 1;
				exit_emul(&entry_patches[i]);
				break;
			}
		}
		if (hit_patch)
			continue;
		for (i = 0; i < plan.nr_force_interpret; i++) {
			if (plan.force_interpret[i] == pts->client_regs.rip) {
				/* This instruction hasn't been
				   patched, but for some reason the
				   plan requires us to interpret it
				   anyway.  Do so. */
				debug("Destination RIP %lx matches force_interpret slot %d\n",
				      pts->client_regs.rip, i);
				hit_patch = 1;
				exit_emul(NULL);
				break;
			}
		}
	}
	exit_routine = find_exit_stub(pts->client_regs.rip);
	EVENT(exit_interpreter);
	release_big_lock();
	exit_routine(&pts->client_regs);
	/* shouldn't get here */
	abort();
}

static void
exit_thread(struct low_level_state *ll)
{
	debug("Exit thread %p(%s)\n", ll, plan.cfg_nodes[ll->cfg_node].id);
	sanity_check_low_level_state(ll, 0);
	if (ll->bound_lls && ll->bound_lls != BOUND_LLS_EXITED) {
		assert(ll->bound_lls->bound_lls == ll);
		ll->bound_lls->bound_lls = BOUND_LLS_EXITED;
		if (ll->bound_lls->mbox &&
		    !na_xchg(ll->bound_lls->mbox, 1))
			queue_wake(ll->bound_lls->mbox);
	}
	release_lls(ll);
}

/* Clone an LLS, including duplicating any bound thread. */
static struct low_level_state *
clone_lls(struct low_level_state *lls)
{
	struct low_level_state *new_lls = new_low_level_state(lls->hls, lls->nr_simslots);
	new_lls->cfg_node = lls->cfg_node;
	memcpy(new_lls->simslots, lls->simslots, sizeof(new_lls->simslots[0]) * new_lls->nr_simslots);
	new_lls->bound_lls = lls->bound_lls;
	assert(!lls->bound_sending_messages);
	assert(!lls->bound_receiving_messages);
	assert(!lls->unbound_sending_messages);
	assert(!lls->unbound_receiving_messages);

#ifdef KEEP_LLS_HISTORY
	memcpy(new_lls->history, lls->history, sizeof(lls->history));
#endif
	if (lls->bound_lls && lls->bound_lls != BOUND_LLS_EXITED) {
		struct low_level_state *new_bound_lls = new_low_level_state(lls->hls, lls->bound_lls->nr_simslots);
		new_bound_lls->cfg_node = lls->bound_lls->cfg_node;
		new_bound_lls->bound_lls = new_lls;
		new_lls->bound_lls = new_bound_lls;
		memcpy(new_bound_lls->simslots, lls->bound_lls->simslots, sizeof(new_bound_lls->simslots[0]) * new_bound_lls->nr_simslots);
		new_bound_lls->nr_bound_receiving_messages = lls->bound_lls->nr_bound_receiving_messages;
		new_bound_lls->nr_bound_sending_messages = lls->bound_lls->nr_bound_sending_messages;
		new_bound_lls->bound_receiving_messages = lls->bound_lls->bound_receiving_messages;
		new_bound_lls->bound_sending_messages = lls->bound_lls->bound_sending_messages;

		/* We don't clone unbound_*_messages, or register with
		 * the global sender and receiver arrays, because the
		 * new LLS is bound. */

#ifdef KEEP_LLS_HISTORY
		memcpy(new_bound_lls->history, lls->bound_lls->history, sizeof(lls->bound_lls->history));
#endif

		low_level_state_push(&new_bound_lls->hls->ll_states, new_bound_lls);
	}

	low_level_state_push(&new_lls->hls->ll_states, new_lls);

	EVENT(ll_clone);

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
	EVENT(discharge_message);

	if (rx_lls->mbox) {
		int x = na_xchg(rx_lls->mbox, 1);
		debug("rx_lls has an mbox %p; value %d\n", rx_lls->mbox, x);
		if (!x)
			queue_wake(rx_lls->mbox);
	}
	if (tx_lls->mbox) {
		int x = na_xchg(tx_lls->mbox, 1);
		debug("tx_lls has an mbox %p; value %d\n", tx_lls->mbox, x);
		if (!x)
			queue_wake(tx_lls->mbox);
	}
}

static struct low_level_state *
dupe_lls(struct low_level_state *input)
{
	struct low_level_state *old_bound;
	struct low_level_state *new_bound;
	struct low_level_state *output;

	assert(input);
	assert(input->bound_lls);
	assert(input->bound_lls->bound_lls);
	assert(input->bound_lls->bound_lls == input);

	old_bound = input->bound_lls;

	assert(!input->unbound_sending_messages);
	assert(!old_bound->unbound_receiving_messages);
	assert(!input->await_bound_lls_exit);
	assert(!old_bound->await_bound_lls_exit);

	assert(!input->mbox);

	new_bound = new_low_level_state(old_bound->hls, old_bound->nr_simslots);
	new_bound->cfg_node = old_bound->cfg_node;
#ifdef KEEP_LLS_HISTORY
	memcpy(new_bound->history, old_bound->history, sizeof(new_bound->history));
#endif
	memcpy(new_bound->simslots, old_bound->simslots, sizeof(new_bound->simslots[0]) * new_bound->nr_simslots);
	new_bound->last_operation_is_send = old_bound->last_operation_is_send;
	new_bound->mbox = old_bound->mbox;
	new_bound->nr_bound_sending_messages = old_bound->nr_bound_sending_messages;
	new_bound->bound_sending_messages = old_bound->bound_sending_messages;
	new_bound->nr_bound_receiving_messages = old_bound->nr_bound_receiving_messages;
	new_bound->bound_receiving_messages = old_bound->bound_receiving_messages;

	output = new_low_level_state(input->hls, input->nr_simslots);
	output->cfg_node = input->cfg_node;
#ifdef KEEP_LLS_HISTORY
	memcpy(output->history, input->history, sizeof(output->history));
#endif
	memcpy(output->simslots, input->simslots, sizeof(output->simslots[0]) * output->nr_simslots);
	output->last_operation_is_send = input->last_operation_is_send;
	output->nr_bound_sending_messages   = input->nr_bound_sending_messages;
	output->bound_sending_messages      = input->bound_sending_messages;
	output->nr_bound_receiving_messages = input->nr_bound_receiving_messages;
	output->bound_receiving_messages    = input->bound_receiving_messages;

	new_bound->bound_lls = output;
	output->bound_lls = new_bound;

	low_level_state_push(&new_bound->hls->ll_states, new_bound);

	return output;
}

static void
rendezvous_threads(struct low_level_state_array *llsa,
		   int tx_is_local,
		   struct msg_template *tx_template,
		   struct low_level_state *tx_lls,
		   struct msg_template *rx_template,
		   struct low_level_state *rx_lls)
{
	int x;

	assert(rx_template == tx_template->pair);
	assert(tx_template == rx_template->pair);

	assert(!rx_lls->unbound_sending_messages);
	assert(!tx_lls->unbound_receiving_messages);

	assert(!rx_lls->bound_receiving_messages);
	assert(!rx_lls->bound_sending_messages);
	assert(!tx_lls->bound_sending_messages);
	assert(!tx_lls->bound_receiving_messages);

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
#ifdef KEEP_LLS_HISTORY
		memcpy(dupe_tx_lls->history, tx_lls->history, sizeof(tx_lls->history));
#endif
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
#ifdef KEEP_LLS_HISTORY
		memcpy(dupe_rx_lls->history, rx_lls->history, sizeof(rx_lls->history));
#endif

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
		      struct msg_template *tx_msg,
		      struct low_level_state *tx_lls,
		      struct msg_template *rx_msg,
		      struct low_level_state *rx_lls)
{
	sanity_check_low_level_state(rx_lls, 1);
	sanity_check_low_level_state(tx_lls, 1);
	rendezvous_threads(llsa, 1, tx_msg, tx_lls, rx_msg, rx_lls);
}
static void
rendezvous_threads_rx(struct low_level_state_array *llsa,
		      struct msg_template *rx_msg,
		      struct low_level_state *rx_lls,
		      struct msg_template *tx_msg,
		      struct low_level_state *tx_lls)
{
	sanity_check_low_level_state(rx_lls, 1);
	sanity_check_low_level_state(tx_lls, 1);
	rendezvous_threads(llsa, 0, tx_msg, tx_lls, rx_msg, rx_lls);
}

static int
rx_message_filter(struct low_level_state *rx_lls,
		  struct msg_template *rx_msg,
		  struct low_level_state *tx_lls,
		  struct msg_template *tx_msg)
{
	const unsigned short *filter = plan.cfg_nodes[rx_lls->cfg_node].rx_validate;
	int res;
	res = eval_bytecode(filter, rx_lls, rx_msg,
			    tx_msg, tx_lls);
	if (!res) {
		debug("%p: failed RX message filter!\n", rx_lls);
		EVENT(message_filter_failed);
	}
	return res;
}

static void
get_max_wait_time(struct timeval *end_wait)
{
	gettimeofday(end_wait, NULL);
	end_wait->tv_usec += MAX_DELAY_US * 2;
	while (end_wait->tv_usec >= 1000000) {
		end_wait->tv_sec++;
		end_wait->tv_usec -= 1000000;
	}
}

static int
get_timeout(const struct timeval *end_wait, struct timespec *timeout)
{
	struct timeval now;
	gettimeofday(&now, NULL);
	timeout->tv_sec = end_wait->tv_sec - now.tv_sec;
	timeout->tv_nsec = (end_wait->tv_usec - now.tv_usec) * 1000;
	while (timeout->tv_nsec < 0) {
		timeout->tv_sec--;
		timeout->tv_nsec += 1000000000;
	}
	/* Delays of less than 10us get treated as an instant wakeup,
	   just because you'd probably spend that long going to sleep
	   and waking up again. */
	if (timeout->tv_sec < 0 ||
	    (timeout->tv_sec == 0 && timeout->tv_nsec < 10000))
		return -1;
	return 0;
}

static long
delay_bias(const struct cfg_instr *instr, int is_tx)
{
	struct msg_template **msgs = is_tx ? instr->tx_msgs : instr->rx_msgs;
	int nr = is_tx ? instr->nr_tx_msg : instr->nr_rx_msg;
	long res;
	int j;
	if (force_delay) {
		if (force_delay == -1) {
			if (is_tx)
				return -1;
			else
				return 1;
		} else {
			if (is_tx)
				return 1;
			else
				return -1;
		}
	}
	res = 0;
	for (j = 0; j < nr; j++) {
		res += msgs[j]->event_count;
		res -= msgs[j]->pair->event_count;
		msgs[j]->event_count++;
	}
	return res;
}

static unsigned
gen_random(void)
{
	/* The MMIX PRNG */
	unsigned long next_state = prng_state * 6364136223846793005ul + 1442695040888963407ul;
	unsigned res = next_state >> 33;
	prng_state = next_state;
	return res;
}

static void
random_delay(void)
{
	usleep((gen_random() % MAX_DELAY_US) + MAX_DELAY_US);
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
	int need_futex;
	int have_rx;
	struct low_level_state_array new_llsa;
	int mbox;

	/* Quick escape if we don't have anything to receive. */
	have_rx = 0;
	for (i = 0; !have_rx && i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		const struct cfg_instr *instr = &plan.cfg_nodes[lls->cfg_node];
		sanity_check_low_level_state(lls, 1);
		if (!lls->await_bound_lls_exit && instr->nr_rx_msg != 0)
			have_rx = 1;
	}
	if (!have_rx)
		return;

	debug("start rx\n");
	memset(&new_llsa, 0, sizeof(new_llsa));
	need_delay = 0;
	have_rx = 0;
	need_futex = 0;
	mbox = 0;
	for (i = 0; i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		const struct cfg_instr *instr = &plan.cfg_nodes[lls->cfg_node];
		long db;
		int delay_this_side;

		if (lls->await_bound_lls_exit || instr->nr_rx_msg == 0) {
			/* Threads which don't receive any messages
			 * don't need to do anything. */
			low_level_state_push(&new_llsa, lls);
			hls->ll_states.content[i] = NULL;
			debug("%p(%s): nothing to receive\n", lls, instr->id);
			continue;
		}

		db = delay_bias(instr, 0);
		if (db < 0) {
			debug("%p(%s): RX, delay is on RX side (bias %ld)\n",
			      lls, instr->id, db);
			delay_this_side = 1;
		} else {
			debug("%p(%s): RX, delay is on TX side (bias %ld)\n",
			      lls, instr->id, db);
			delay_this_side = 0;
		}

		if (lls->bound_lls == BOUND_LLS_EXITED) {
			debug("%p(%s): Receiving from an exited thread -> fail\n",
			      lls, instr->id);
			hls->ll_states.content[i] = NULL;
			EVENT(rx_from_exited);
			exit_thread(lls);
		} else if (lls->bound_lls != NULL) {
			assert(lls->bound_lls->bound_lls == lls);
			if (lls->bound_lls->nr_bound_sending_messages != 0) {
				int tx_idx;
				int rx_idx;
				struct msg_template *rx_msg;
				struct msg_template *tx_msg;
				int keep = 0;
				hls->ll_states.content[i] = NULL;
				for (tx_idx = 0; tx_idx < lls->bound_lls->nr_bound_sending_messages; tx_idx++) {
					tx_msg = lls->bound_lls->bound_sending_messages[tx_idx];
					for (rx_idx = 0; rx_idx < instr->nr_rx_msg; rx_idx++) {
						rx_msg = instr->rx_msgs[rx_idx];
						if (rx_msg->pair == tx_msg &&
						    rx_message_filter(lls, rx_msg, lls->bound_lls, tx_msg)) {
							debug("%p(%s): Receive from bound thread %p\n", lls, instr->id, lls->bound_lls);
							if (keep)
								lls = dupe_lls(lls);
							discharge_message(lls->bound_lls, tx_msg,
									  lls, rx_msg);
							lls->bound_lls->bound_sending_messages = NULL;
							lls->bound_lls->nr_bound_sending_messages = 0;
							low_level_state_push(&new_llsa, lls);
							keep = 1;
							EVENT(rx_bound_fast);
						}
					}
				}

				if (!keep) {
					debug("%p(%s): Bound thread sent wrong message\n", lls, instr->id);
					exit_thread(lls);
					EVENT(rx_bound_failed);
				}
			} else {
				debug("%p(%s): Bound thread %p with nothing outstanding; go to RX state\n",
				      lls, instr->id, lls->bound_lls);
				lls->nr_bound_receiving_messages = instr->nr_rx_msg;
				lls->bound_receiving_messages = instr->rx_msgs;
				lls->mbox = &mbox;
				need_futex = 1;
				have_rx = 1;
				EVENT(rx_bound_wait);
			}
		} else {
			/* Gather up all of the messages which have
			   already been sent which might be
			   relevant. */
			lls->nr_unbound_receiving_messages = instr->nr_rx_msg;
			lls->unbound_receiving_messages = instr->rx_msgs;
			for (j = 0; j < message_senders.sz; j++) {
				struct low_level_state *tx_lls = message_senders.content[j];
				int tx_idx;
				assert(tx_lls->nr_unbound_sending_messages != 0);
				for (tx_idx = 0; tx_idx < tx_lls->nr_unbound_sending_messages; tx_idx++) {
					struct msg_template *tx_msg = tx_lls->unbound_sending_messages[tx_idx];
					int rx_idx;
					for (rx_idx = 0; rx_idx < instr->nr_rx_msg; rx_idx++) {
						struct msg_template *rx_msg = instr->rx_msgs[rx_idx];
						if (tx_msg == rx_msg->pair &&
						    rx_message_filter(lls, rx_msg, tx_lls, tx_msg)) {
							debug("%p(%s): late rx from remote LLS %p\n", lls,
							      instr->id, tx_lls);
							rendezvous_threads_rx(&new_llsa, rx_msg, lls, tx_msg, tx_lls);
							EVENT(rx_unbound_early);
						}
					}
				}
			}
			/* And tell any future senders that we're
			 * available. */
			low_level_state_push(&message_receivers, lls);
			have_rx = 1;
			need_delay |= delay_this_side;
			EVENT(rx_unbound);
		}
	}

	if (!have_rx) {
		/* All receives completed fast.  Yay. */
		debug("All receives completed fast\n");
		low_level_state_arr_swizzle(&hls->ll_states, &new_llsa);
		EVENT(rx_fast);
		return;
	}
	EVENT(rx_slow);

	if (need_delay) {
		/* Some states require a delay e.g. an unbound
		   receive, which always waits for a fixed amount of
		   time, even if someone arrives before the wait is
		   finished. */
		debug("Delay for RX\n");
		EVENT(rx_delay);
		release_big_lock();
		random_delay();
		acquire_big_lock();
		debug("Back from RX delay\n");
	} else if (need_futex) {
		/* We have bound receives and no delayable unbound
		 * ones.  That means waiting until the bound messages
		 * arrive, but no longer. */
		struct timeval end_wait;
		struct timespec timeout;
		EVENT(rx_futex);
		get_max_wait_time(&end_wait);
		while (1) {
			if (get_timeout(&end_wait, &timeout) < 0) {
				EVENT(rx_futex_timeout);
				break;
			}
			debug("RX delay via futex %p\n", &mbox);
			release_big_lock();
			futex(&mbox, FUTEX_WAIT, 0, &timeout);
			acquire_big_lock();
			debug("Back from futex RX delay\n");
			int x = na_xchg(&mbox, 0);
			if (x) {
				/* One of our receives has completed.
				 * Process it and check if it was the
				 * last one. */
				int have_more_bound_rx = 0;
				for (i = 0; i < hls->ll_states.sz; i++) {
					struct low_level_state *lls = hls->ll_states.content[i];
					if (!lls)
						continue;
					if (lls->nr_unbound_receiving_messages != 0) {
						/* We allow unbound
						   receives to keep
						   trying while we're
						   waiting for bound
						   ones, but don't try
						   to complete them
						   until all the bound
						   ones have
						   finished. */
						continue;
					}
					if (lls->bound_lls == BOUND_LLS_EXITED) {
						debug("%p(%s): Unbound receive: peer exited\n",
						      lls,
						      plan.cfg_nodes[lls->cfg_node].id);
						lls->mbox = NULL;
						hls->ll_states.content[i] = NULL;
						exit_thread(lls);
					} else if (lls->nr_bound_receiving_messages != 0) {
						have_more_bound_rx = 1;
					} else {
						debug("%p(%s): Unbound receive succeeded\n",
						      lls,
						      plan.cfg_nodes[lls->cfg_node].id);
						hls->ll_states.content[i] = NULL;
						lls->mbox = NULL;
						low_level_state_push(&new_llsa, lls);
					}
				}
				if (!have_more_bound_rx)
					break;
			}
		}
	}

	/* That's all the delaying we're allowed.  Process all of the
	   receive operations we have in one go. */
	for (i = 0; i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		if (!lls)
			continue;
		sanity_check_low_level_state(lls, 1);
		hls->ll_states.content[i] = NULL;
		lls->mbox = NULL;
		if (lls->nr_unbound_receiving_messages != 0) {
			lls->unbound_receiving_messages = NULL;
			lls->nr_unbound_receiving_messages = 0;
			low_level_state_erase_first(&message_receivers, lls);
		}
		if (lls->nr_bound_receiving_messages != 0) {
			debug("%p(%s): Bound receive failed\n", lls, plan.cfg_nodes[lls->cfg_node].id);
			exit_thread(lls);
			EVENT(rx_bound_failed_late);
		} else if (!lls->bound_lls) {
			debug("%p(%s): Unbound receive failed\n", lls, plan.cfg_nodes[lls->cfg_node].id);
			exit_thread(lls);
			EVENT(rx_unbound_failed);
		} else {
			debug("%p(%s): Receive succeeded.\n", lls, plan.cfg_nodes[lls->cfg_node].id);
			low_level_state_push(&new_llsa, lls);
			EVENT(rx_success);
		}
	}

	low_level_state_arr_swizzle(&hls->ll_states, &new_llsa);
}

static void
advance_through_cfg(struct high_level_state *hls, unsigned long rip)
{
	int i, j, k, r;
	debug("Next instr %lx\n", rip);
	r = hls->ll_states.sz;
	for (i = 0; i < r; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		cfg_label_t cur_label = lls->cfg_node;
		struct cfg_instr *current_cfg_node = &plan.cfg_nodes[cur_label];
		current_cfg_node->cntr++;
		sanity_check_low_level_state(lls, 1);
		int preserve = 0;
		debug("%p(%s): advance\n", lls, current_cfg_node->id);
		for (j = 0; j < current_cfg_node->nr_successors; j++) {
			if (rip == plan.cfg_nodes[current_cfg_node->successors[j]].rip) {
				struct low_level_state *newLls;
				for (k = 0; k < current_cfg_node->nr_set_control; k++) {
					if (current_cfg_node->set_control[k].next_node ==
					    current_cfg_node->successors[j])
						lls->simslots[current_cfg_node->set_control[k].slot] = 1;
				}
				if (current_cfg_node->control_flow_validate &&
				    !eval_bytecode(current_cfg_node->control_flow_validate,
						   lls, NULL, NULL, NULL)) {
					debug("%p(%s): Reject %s due to control-flow side condition\n",
					      lls, current_cfg_node->id,
					      plan.cfg_nodes[current_cfg_node->successors[j]].id);
					EVENT(adv_fail_side_condition);
					continue;
				}
				if (!preserve) {
					/* The common case is that we
					 * have precisely one
					 * successor.  Avoid
					 * malloc()/free() in that
					 * case. */
					newLls = lls;
					low_level_state_push(&hls->ll_states, newLls);
					preserve = 1;
					EVENT(adv_no_malloc);
				} else {
					/* low-level state fork ->
					 * need to malloc() */
					newLls = clone_lls(lls);
					EVENT(adv_malloc);
				}
				newLls->cfg_node = current_cfg_node->successors[j];
#ifdef KEEP_LLS_HISTORY
				memmove(newLls->history, newLls->history + 1, sizeof(newLls->history[0]) * (LLS_HISTORY-1));
				newLls->history[LLS_HISTORY-1] = current_cfg_node->successors[j];
#endif
				debug("%p(%s): Accept %p(%s)\n",
				      lls,
				      current_cfg_node->id,
				      newLls,
				      plan.cfg_nodes[newLls->cfg_node].id);
			} else {
				EVENT(adv_reject);
				debug("%p(%s): Reject %s(%d): %lx != %lx\n",
				      lls,
				      current_cfg_node->id,
				      plan.cfg_nodes[current_cfg_node->successors[j]].id,
				      current_cfg_node->successors[j],
				      plan.cfg_nodes[current_cfg_node->successors[j]].rip,
				      rip);
			}
		}
		if (!preserve) {
			EVENT(adv_dead);
			debug("%p(%s): no viable successors\n", lls, current_cfg_node->id);
			hls->ll_states.content[i] = NULL;
			if (current_cfg_node->nr_successors == 0) {
				safe_write(1,
					   "Completed enforcement plan!\n",
					   sizeof("Completed enforcement plan!"));
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
					debug("%p(%s): successfully finished this CFG with a send\n",
					      lls, current_cfg_node->id);
					assert(lls->bound_lls);
					lls->await_bound_lls_exit = 1;
					low_level_state_push(&hls->ll_states, lls);
					EVENT(finish_send);
				} else {
					debug("%p(%s): successfully finished this CFG; didn't end with a send\n",
					      lls, current_cfg_node->id);
					exit_thread(lls);
					EVENT(finish_non_send);
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
check_for_ll_thread_start(struct high_level_state *hls, struct reg_struct *regs)
{
	int i, j;
	for (i = 0; i < plan.nr_entry_points; i++) {
		if (plan.entry_points[i]->orig_rip != regs->rip)
			continue;
		assert(plan.entry_points[i]->nr_entry_ctxts > 0);
		for (j = 0; j < plan.entry_points[i]->nr_entry_ctxts; j++) {
			if (ctxt_matches(plan.entry_points[i]->ctxts[j], regs)) {
				plan.entry_points[i]->ctxts[j]->cntr++;
				start_low_level_thread(
					hls,
					plan.entry_points[i]->ctxts[j]->cfg_label,
					plan.entry_points[i]->ctxts[j]->rsp_delta,
					plan.entry_points[i]->ctxts[j]->nr_simslots);
			}
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
		.hls = hls
	};
	int r;

	debug("Emulate from %lx\n", regs->rip);
	EVENT(emul_underlying);
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
	int need_futex;
	int mbox;

	have_sends = 0;
	for (i = 0; !have_sends && i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		if (plan.cfg_nodes[lls->cfg_node].nr_tx_msg != 0)
			have_sends = 1;
	}
	if (!have_sends)
		return;

	debug("start tx %d\n", hls->ll_states.sz);
	memset(&new_llsa, 0, sizeof(new_llsa));
	have_sends = 0;
	need_delay = 0;
	need_futex = 0;
	mbox = 0;
	for (i = 0; i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		const struct cfg_instr *instr = &plan.cfg_nodes[lls->cfg_node];
		int delay_this_side;
		long bias;

		if (instr->nr_tx_msg == 0) {
			low_level_state_push(&new_llsa, lls);
			hls->ll_states.content[i] = NULL;
			debug("%p(%s): nothing to send\n", lls, instr->id);
			continue;
		}

		bias = delay_bias(instr, 1);
		if (bias < 0) {
			debug("%p(%s): TX, delay is on TX side (bias %ld)\n",
			      lls, instr->id, bias);
			delay_this_side = 1;
		} else {
			debug("%p(%s): TX, delay is on RX side (bias %ld)\n",
			      lls, instr->id, bias);
			delay_this_side = 0;
		}

		if (lls->bound_lls == BOUND_LLS_EXITED) {
			debug("%p(%s): Send when bound to a dead thread; doomed\n",
			      lls, instr->id);
			hls->ll_states.content[i] = NULL;
			exit_thread(lls);
			EVENT(tx_bound_exited);
		} else if (lls->bound_lls) {
			if (lls->bound_lls->nr_bound_receiving_messages != 0) {
				int tx_idx;
				int rx_idx;
				struct msg_template *rx_msg;
				struct msg_template *tx_msg;
				int keep = 0;
				hls->ll_states.content[i] = NULL;
				for (rx_idx = 0; rx_idx < lls->bound_lls->nr_bound_receiving_messages; rx_idx++) {
					rx_msg = lls->bound_lls->bound_receiving_messages[rx_idx];
					for (tx_idx = 0; tx_idx < instr->nr_tx_msg; tx_idx++) {
						tx_msg = instr->tx_msgs[tx_idx];
						if (tx_msg->pair == rx_msg &&
						    rx_message_filter(lls->bound_lls, rx_msg, lls, tx_msg)) {
							debug("%p(%s): Transmit to bound thread %p which is already waiting\n",
							      lls,
							      instr->id,
							      lls->bound_lls);
							if (keep)
								lls = dupe_lls(lls);
							discharge_message(lls, tx_msg, lls->bound_lls, rx_msg);
							lls->bound_lls->bound_receiving_messages = NULL;
							lls->bound_lls->nr_bound_receiving_messages = 0;
							low_level_state_push(&new_llsa, lls);
							keep = 1;
							EVENT(tx_bound_fast);
						}
					}
				}

				if (!keep) {
					debug("%p(%s): Bound thread received wrong message\n", lls, instr->id);
					exit_thread(lls);
					EVENT(tx_bound_failed);
				}
			} else {
				debug("%p(%s): Transmit to bound thread %p which isn't yet ready\n",
				      lls,
				      instr->id,
				      lls->bound_lls);
				lls->nr_bound_sending_messages = instr->nr_tx_msg;
				lls->bound_sending_messages = instr->tx_msgs;
				have_sends = 1;
				need_futex = 1;
				lls->mbox = &mbox;
				EVENT(tx_bound_slow);
			}
		} else {
			/* Perform a general send. */
			lls->nr_unbound_sending_messages = instr->nr_tx_msg;
			lls->unbound_sending_messages = instr->tx_msgs;
			for (j = 0; j < message_receivers.sz; j++) {
				struct low_level_state *rx_lls = message_receivers.content[j];

				int rx_idx;
				assert(rx_lls->nr_unbound_receiving_messages != 0);
				for (rx_idx = 0; rx_idx < rx_lls->nr_unbound_receiving_messages; rx_idx++) {
					struct msg_template *rx_msg = rx_lls->unbound_receiving_messages[rx_idx];
					int tx_idx;
					for (tx_idx = 0; tx_idx < instr->nr_tx_msg; tx_idx++) {
						struct msg_template *tx_msg = instr->tx_msgs[tx_idx];
						if (rx_msg == tx_msg->pair &&
						    rx_message_filter(rx_lls, rx_msg, lls, tx_msg)) {
							debug("%p(%s): inject message into remote LLS %p\n",
							      lls, instr->id, rx_lls);
							rendezvous_threads_tx(&new_llsa, tx_msg, lls, rx_msg, rx_lls);
							EVENT(tx_unbound_early);
						}
					}
				}
			}
			/* And tell any future receivers that we're
			 * available. */
			low_level_state_push(&message_senders, lls);
			have_sends = 1;
			need_delay |= delay_this_side;
			EVENT(tx_unbound);
		}
	}

	if (!have_sends) {
		debug("All sends completed without delaying\n");
		low_level_state_arr_swizzle(&hls->ll_states, &new_llsa);
		EVENT(tx_fast);
		return;
	}

	EVENT(tx_slow);

	if (need_delay) {
		/* We have delay-able unbound transmits.  Those always
		   stall for a fixed amount of time, even if something
		   arrives to complete them before the delay is
		   finished, because they need to bind to *everything*
		   which arrives during the delay, and not just the
		   first thing. */
		EVENT(tx_delay);
		debug("Delay for TX.\n");
		release_big_lock();
		random_delay();
		acquire_big_lock();
		debug("Back from TX delay.\n");
	} else if (need_futex) {
		struct timeval end_wait;
		struct timespec timeout;
		EVENT(tx_futex);
		get_max_wait_time(&end_wait);
		while (1) {
			if (get_timeout(&end_wait, &timeout) < 0) {
				EVENT(tx_futex_timeout);
				break;
			}
			debug("TX delay via futex %p\n", &mbox);
			release_big_lock();
			futex(&mbox, FUTEX_WAIT, 0, &timeout);
			acquire_big_lock();
			debug("Back from futex TX delay\n");
			int x = na_xchg(&mbox, 0);
			if (x) {
				int have_more_bound_tx = 0;
				for (i = 0; i < hls->ll_states.sz; i++) {
					struct low_level_state *lls = hls->ll_states.content[i];
					if (!lls)
						continue;
					if (lls->nr_unbound_sending_messages != 0)
						continue;
					if (lls->bound_lls == BOUND_LLS_EXITED) {
						debug("%p(%s): Unbound transmit, peer exited\n",
						      lls,
						      plan.cfg_nodes[lls->cfg_node].id);
						hls->ll_states.content[i] = NULL;
						lls->mbox = NULL;
						exit_thread(lls);
					} else if (lls->nr_bound_sending_messages != 0) {
						have_more_bound_tx = 1;
					} else {
						debug("%p(%s): Unbound transmit succeeded early\n",
						      lls,
						      plan.cfg_nodes[lls->cfg_node].id);
						hls->ll_states.content[i] = NULL;
						lls->mbox = NULL;
						low_level_state_push(&new_llsa, lls);
					}
				}
				if (!have_more_bound_tx)
					break;
			}
		}
	}

	for (i = 0; i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		if (!lls)
			continue;
		hls->ll_states.content[i] = NULL;
		if (lls->nr_unbound_sending_messages != 0) {
			lls->unbound_sending_messages = NULL;
			lls->nr_unbound_sending_messages = 0;
			low_level_state_erase_first(&message_senders, lls);
		}
		if (lls->nr_bound_sending_messages != 0) {
			debug("%p(%s): Bound send failed\n", lls, plan.cfg_nodes[lls->cfg_node].id);
			exit_thread(lls);
			EVENT(tx_bound_failed_late);
		} else if (!lls->bound_lls) {
			debug("%p(%s): Unbound send failed\n", lls, plan.cfg_nodes[lls->cfg_node].id);
			hls->ll_states.content[i] = NULL;
			exit_thread(lls);
			EVENT(tx_unbound_failed);
		} else {
			debug("%p(%s): Send succeeded\n", lls, plan.cfg_nodes[lls->cfg_node].id);
			low_level_state_push(&new_llsa, lls);
			EVENT(tx_success);
		}
	}

	low_level_state_arr_swizzle(&hls->ll_states, &new_llsa);
}

static void
wait_for_bound_exits(struct high_level_state *hls)
{
	int i;
	int waiting_for_bound_exit;
	int mbox;

	while (1) {
		waiting_for_bound_exit = 0;
		mbox = 0;
		for (i = 0; !waiting_for_bound_exit && i < hls->ll_states.sz; i++) {
			struct low_level_state *lls = hls->ll_states.content[i];
			if (lls->await_bound_lls_exit) {
				if (lls->bound_lls == BOUND_LLS_EXITED) {
					debug("%p's was waiting for bound exit, but that has now happened\n",
					      lls);
					low_level_state_erase_idx(&hls->ll_states, i);
					exit_thread(lls);
					i--;
				} else {
					assert(lls->bound_lls);
					assert(!lls->bound_lls->await_bound_lls_exit);
					waiting_for_bound_exit++;
					lls->mbox = &mbox;
				}
			}
		}
		if (!waiting_for_bound_exit)
			break;
		EVENT(wait_bound_exit);
		debug("Waiting for %d bound exits on %p\n", waiting_for_bound_exit, &mbox);
		release_big_lock();
		futex(&mbox, FUTEX_WAIT, 0, NULL);
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
			EVENT(stash_reg);
			if (instr->stash[j].reg != -1) {
				unsigned long *slot = &lls->simslots[instr->stash[j].slot];
				switch (instr->stash[j].reg) {
#define do_case(idx, r)							\
					case idx:			\
						*slot = regs-> r;	\
						break
					do_case(0, rax);
					do_case(1, rcx);
					do_case(2, rdx);
					do_case(3, rbx);
					/* rsp is special */
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
					/* Apply the delta to RSP */
				case 4:
					*slot = regs->rsp - lls->rsp_delta;
					break;
				case 16:
					*slot = fetch_fs_base();
					break;
				default:
					abort();
				}
				debug("%p(%s) stashed r%d = %lx in slot %d\n",
				      lls, instr->id, instr->stash[j].reg,
				      *slot, instr->stash[j].slot);
			}
		}
	}
}

static void
check_conditions(struct high_level_state *hls, const char *message, unsigned offset)
{
	int i;
	int j;
	int killed;

	killed = 0;
	for (i = 0; i < hls->ll_states.sz; i++) {
		struct low_level_state *lls = hls->ll_states.content[i];
		const struct cfg_instr *cfg = &plan.cfg_nodes[lls->cfg_node];
		const unsigned short *condition = *(const unsigned short **)((unsigned long)cfg + offset);
		if (!eval_bytecode(condition, lls, NULL, NULL, NULL)) {
			debug("%p(%s) failed a %s side-condition\n", lls, cfg->id, message);
			hls->ll_states.content[i] = NULL;
			exit_thread(lls);
			killed = 1;
			EVENT(condition_failed);
		}
		EVENT(condition_passed);
	}
	if (killed) {
		i = 0;
		j = 0;
		while (i < hls->ll_states.sz) {
			if (hls->ll_states.content[i]) {
				hls->ll_states.content[j] = hls->ll_states.content[i];
				j++;
			}
			i++;
		}
		hls->ll_states.sz = j;
	}
}
static void
check_pre_conditions(struct high_level_state *hls)
{
	check_conditions(hls, "pre", offsetof(struct cfg_instr, pre_validate));
}
static void
check_eval_conditions(struct high_level_state *hls)
{
	check_conditions(hls, "eval", offsetof(struct cfg_instr, eval_validate));
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
	sanity_check_high_level_state(hls);

	check_pre_conditions(hls);
	if (hls->ll_states.sz == 0)
		exit_interpreter();
	sanity_check_high_level_state(hls);

	receive_messages(hls);
	if (hls->ll_states.sz == 0)
		exit_interpreter();
	sanity_check_high_level_state(hls);

	wait_for_bound_exits(hls);
	if (hls->ll_states.sz == 0)
		exit_interpreter();

	emulate_underlying_instruction(hls, regs);
	sanity_check_high_level_state(hls);

	check_eval_conditions(hls);
	if (hls->ll_states.sz == 0)
		exit_interpreter();
	sanity_check_high_level_state(hls);

	send_messages(hls);
	if (hls->ll_states.sz == 0)
		exit_interpreter();
	sanity_check_high_level_state(hls);

	advance_through_cfg(hls, regs->rip);
	sanity_check_high_level_state(hls);
}

static void
start_interpreting(void)
{
	struct per_thread_state *pts = find_pts();
	const struct cep_entry_point *entry_point;
	struct high_level_state hls;
	int entrypoint_idx;

	for (entrypoint_idx = 0; entrypoint_idx < plan.nr_entry_points; entrypoint_idx++)
		if (plan.entry_points[entrypoint_idx]->orig_rip == pts->client_regs.rip)
			break;

	if (entrypoint_idx == plan.nr_entry_points) {
		acquire_big_lock();
		debug("Start with a dummy entry point\n");
		EVENT(dummy_entry_point);
		exit_interpreter();
	}

	EVENT(enter_interpreter);

	entry_point = plan.entry_points[entrypoint_idx];
	init_high_level_state(&hls);
	pts->client_regs.rip = entry_point->orig_rip;
	acquire_big_lock();
	debug("Start interpreting idx %d, pts at %p, regs at %p\n",
	      entrypoint_idx,
	      pts,
	      &pts->client_regs);
	while (1) {
		advance_hl_interpreter(&hls, &pts->client_regs);
		release_big_lock();
		acquire_big_lock();
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
"__trampoline_client_to_interp_load_rip:\n"
"    movq $0x1122334455667788, %rax\n"
"    push %rax\n"
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
void __trampoline_client_to_interp_load_rdx(void) __attribute__((visibility ("hidden")));
void __trampoline_client_to_interp_load_rip(void) __attribute__((visibility ("hidden")));
void __trampoline_client_to_interp_end(void) __attribute__((visibility ("hidden")));
void __trampoline_interp_to_client_start(void) __attribute__((visibility ("hidden")));
void __trampoline_interp_to_client_jmp_client(void) __attribute__((visibility ("hidden")));
void __trampoline_interp_to_client_end(void) __attribute__((visibility ("hidden")));
static unsigned long
alloc_trampoline(unsigned long rip)
{
	size_t tramp_size = (unsigned long)&__trampoline_client_to_interp_end - (unsigned long)&__trampoline_client_to_interp_start;
	unsigned char *buffer;

	debug("tramp start %p, end %p, size %zx\n", &__trampoline_client_to_interp_end, &__trampoline_client_to_interp_start, tramp_size);
	buffer = alloc_executable(tramp_size);
	memcpy(buffer, &__trampoline_client_to_interp_start, tramp_size);
	*(long *)(buffer +
		  (unsigned long)&__trampoline_client_to_interp_load_rip -
		  (unsigned long)&__trampoline_client_to_interp_start +
		  2) = rip;
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

/* This gets invoked only for segvs generated by our infrastructure,
 * so all it needs to do is fix up the RIP and get out. */
#if 0
static void segv_sigaction_c(int signum, siginfo_t *info, ucontext_t *ctxt,
			     unsigned long recovery_addr) __attribute__((used, unused));
#endif
static void
segv_sigaction_c(int signum, siginfo_t *info, ucontext_t *ctxt, unsigned long recovery_addr)
{
	ctxt->uc_mcontext.gregs[REG_RIP] = recovery_addr;
}

/* This gets invoked if we receive a signal but then need to send it
 * back to the client.  Trickier */
#if 0
static void deliver_signal_client(int signum, siginfo_t *info, ucontext_t *ctxt,
				  unsigned long delivery_rsp) __attribute__((used, unused));
#endif
static void
deliver_signal_client(int signum, siginfo_t *info, ucontext_t *ctxt, unsigned long delivery_rsp)
{
	abort();
}

/* This is also used for sigbus.  Needs to be in assembly so that we
 * can do the stack rewinding trick if we need to invoke a user signal
 * handler. */
asm (
"segv_sigaction:\n"
/* signum == rdi, siginfo_t == rsi, ucontext_t == rdx.  Otherwise,
 * usual call clobbered registers and so forth. */
"    movq %gs:8, %rcx\n"
"    testq %rcx, %rcx\n"
"    jz not_ours\n"
"    jmp segv_sigaction_c\n"
"not_ours:\n"
"    movq %rsp, %rcx\n"
"    jmp deliver_signal_client\n"
);
static void segv_sigaction(int, siginfo_t *, void *);

static void
alloc_thread_state_area(void)
{
	struct per_thread_state *pts;
	stack_t stack;

	pts = mmap(NULL, STACK_SIZE, PROT_READ|PROT_WRITE,
		     MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
	pts->initial_interpreter_rsp =
		(unsigned long)&pts->client_regs.rsp;
	arch_prctl(ARCH_SET_GS, (unsigned long)pts);

	/* Set up an alternative signal stack.  This gets a bit messy
	   if the client also sets up an alt signal stack, but it
	   ought to just about work provided nobody does anything
	   crazy. */
	pts->sigstack = mmap(NULL, PAGE_SIZE, PROT_READ|PROT_WRITE,
			     MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
	stack.ss_sp = pts->sigstack;
	stack.ss_flags = 0;
	stack.ss_size = PAGE_SIZE;
	sigaltstack(&stack, NULL);
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
patch_entry_point(unsigned long rip, unsigned long trampoline)
{
	static int nr_entry_patches_alloced = 0;
	long delta;
	if (nr_entry_patches_alloced == nr_entry_patches) {
		nr_entry_patches_alloced += 8;
		entry_patches = realloc(entry_patches, sizeof(entry_patches[0]) * nr_entry_patches_alloced);
	}
	entry_patches[nr_entry_patches].start = rip;
	entry_patches[nr_entry_patches].size = 5;
	memcpy(entry_patches[nr_entry_patches].content,
	       (const void *)rip,
	       5);
	nr_entry_patches++;

	mprotect((void *)(rip & PAGE_MASK),
		 PAGE_SIZE * 2,
		 PROT_READ|PROT_WRITE|PROT_EXEC);
	*(unsigned char *)rip = 0xe9; /* jmp rel32 opcode */
	delta = trampoline - (rip + 5);
	assert(delta == (int)delta);
	*(int *)(rip + 1) = delta;
	mprotect((void *)(rip & PAGE_MASK),
		 PAGE_SIZE * 2,
		 PROT_READ|PROT_EXEC);
}

#if USE_STATS
static void
dump_stats(void)
{
	int i;
	int j;

	printf("CEP interpreter statistics:\n");
#define do_stat(name)					\
	printf("%-20s: %ld\n", #name, stats.name);
	enum_stats(do_stat)
#undef do_stat

	for (i = 0; i < plan.nr_entry_points; i++) {
		printf("Entry point %d tripped: ", i);
		for (j = 0; j < plan.entry_points[i]->nr_entry_ctxts; j++) {
			if (j != 0)
				printf(", ");
			printf("ctxt%d = %d", j, plan.entry_points[i]->ctxts[j]->cntr);
		}
		printf("\n");
	}
	for (i = 0; i < plan.nr_cfg_nodes; i++) {
		printf("CFG node %s visited %d times\n",
		       plan.cfg_nodes[i].id,
		       plan.cfg_nodes[i].cntr);
		for (j = 0; j < plan.cfg_nodes[i].nr_rx_msg; j++)
			printf("\tRX %x %d times\n",
			       plan.cfg_nodes[i].rx_msgs[j]->msg_id,
			       plan.cfg_nodes[i].rx_msgs[j]->event_count);
		for (j = 0; j < plan.cfg_nodes[i].nr_tx_msg; j++)
			printf("\tTX %x %d times\n",
			       plan.cfg_nodes[i].tx_msgs[j]->msg_id,
			       plan.cfg_nodes[i].tx_msgs[j]->event_count);
	}
}
#endif

static void (*real_free)(void *);

static void
activate(void)
{
	unsigned x, y;
	char buf[4096];
	ssize_t s;
	struct sigaction act;

	init_allocator();

	real_free = dlsym(RTLD_NEXT, "free");
	if (!real_free) {
		printf("Huh?  Can't find free()\n");
		abort();
	}

	s = readlink("/proc/self/exe", buf, sizeof(buf)-1);
	if (s == -1) {
		printf("Can't access /proc/self/exe; patch disabled\n");
		return;
	}
	buf[s] = 0;
	for (x = s; x > 0 && buf[x] != '/'; x--)
		;
	for (y = strlen(program_to_patch); y > 0 && program_to_patch[y] != '/'; y--)
		;

	if (strcmp(buf + x, program_to_patch + y)) {
		printf("This is a patch for %s, but we were invoked on %s; disabling.\n",
		       program_to_patch + y, buf + x);
		return;
	}

	if (getenv("SOS22_ENFORCER_RANDOMISE")) {
		struct timeval t;
		/* Stepping the PRNG while we're doing this gives
		 * marginally better mixing. */
		prng_state ^= getpid();
		gen_random();
		gettimeofday(&t, NULL);
		prng_state ^= t.tv_sec;
		gen_random();
		prng_state ^= t.tv_usec;
		gen_random();
	}

	if (getenv("SOS22_DISABLE_SIDECONDITIONS"))
		disable_sideconditions = 1;
	if (getenv("SOS22_DELAY_TX"))
		force_delay = -1;
	else if (getenv("SOS22_DELAY_RX"))
		force_delay = 1;
	if (getenv("SOS22_DISABLE_CTXT_CHECK"))
		skip_context_check = 1;

	printf("Patching %s\n", buf);

#if USE_STATS
	atexit(dump_stats);
#endif

	memset(&act, 0, sizeof(act));
	act.sa_sigaction = segv_sigaction;
	act.sa_flags = SA_ONSTACK | SA_SIGINFO;
	sigaction(SIGSEGV, &act, NULL);
	sigaction(SIGBUS, &act, NULL);

	alloc_thread_state_area();

	for (x = 0; x < plan.nr_patch_points; x++)
		patch_entry_point(plan.patch_points[x], alloc_trampoline(plan.patch_points[x]));

	hook_clone();
}

void free(void *ptr)
{
	if (ptr != NULL) {
		debug("free %p; last_freed %lx\n", ptr, last_freed);
		last_freed = (unsigned long)ptr;
	}
	real_free(ptr);
}

static void (*__init_activate)(void) __attribute__((section(".ctors"), unused, used)) = activate;
