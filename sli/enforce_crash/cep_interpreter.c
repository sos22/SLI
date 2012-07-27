/* An interpreter for crash enforcement plans.  This gets loaded into
   the target program andis then responsible for driving the program
   along the CEP. */
#include "cep_interpreter.h"

#include <asm/prctl.h>
#include <sys/prctl.h>
#include <sys/types.h>
#include <sys/mman.h>
#include <assert.h>
#include <err.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define PAGE_SIZE 4096ul
#define PAGE_MASK (~(PAGE_SIZE - 1))

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

struct low_level_state {
	cfg_label_t cfg_node;
};

struct high_level_state {
	int nr_ll_states;
	int nr_ll_states_alloced;
	struct low_level_state *ll_states;

	/* Memory allocations which get freed automatically when the
	 * interpreter exits. */
#define ARENA_SIZE (1ul << 10)
	unsigned current_arena_left;
	void *current_arena;
	void *head_arena;
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
	__DECL_REG(sp);
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
};

typedef void exit_routine_t(struct reg_struct *);

static exit_routine_t *find_exit_stub(unsigned long rip);

static int
have_cloned;

static int
lls_eq(const struct low_level_state *a, const struct low_level_state *b)
{
	return a->cfg_node == b->cfg_node;
}

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

static void *
alloc_nonexec(struct high_level_state *hls, size_t sz)
{
	void *res;
	void *new_arena;

	sz = (sz + 15) & ~15ul;
	if (sz > hls->current_arena_left) {
		new_arena =
			mmap(NULL,
			     ARENA_SIZE,
			     PROT_READ|PROT_WRITE|PROT_EXEC,
			     MAP_PRIVATE|MAP_32BIT|MAP_ANONYMOUS,
			     -1,
			     0);
		*(void **)new_arena = hls->current_arena;
		hls->current_arena = new_arena;
		hls->current_arena_left = ARENA_SIZE - 16;
		assert(sz <= hls->current_arena_left);
	}
	res = hls->current_arena + ARENA_SIZE - hls->current_arena_left;
	hls->current_arena_left -= sz;
	return res;
}

static int
__fetch_guest(size_t sz, void *dst, unsigned long addr)
{
#warning should catch the fault here...
	memcpy(dst, (const void *)addr, sz);
	return 1;
}

#define fetch_guest(host_ptr, guest_ptr) __fetch_guest(sizeof(*host_ptr), (void *)host_ptr, guest_ptr)

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

static int
alloc_lls_slot(struct high_level_state *hls)
{
	hls->nr_ll_states++;
	if (hls->nr_ll_states > hls->nr_ll_states_alloced) {
		struct low_level_state *new_ll_states;
		int new_nr_allocated;
		new_nr_allocated = hls->nr_ll_states_alloced + 8;
		new_ll_states = alloc_nonexec(hls, sizeof(struct low_level_state) * new_nr_allocated);
		memcpy(new_ll_states, hls->ll_states, sizeof(struct low_level_state) * hls->nr_ll_states_alloced);
		hls->ll_states = new_ll_states;
		hls->nr_ll_states_alloced = new_nr_allocated;
	}
	return hls->nr_ll_states - 1;
}

static void
start_thread(struct high_level_state *hls, struct low_level_state *lls)
{
	int i;
	for (i = 0; i < hls->nr_ll_states; i++)
		if (lls_eq(lls, &hls->ll_states[i]))
			return;
	i = alloc_lls_slot(hls);
	hls->ll_states[i] = *lls;
}

static void
start_low_level_thread(struct high_level_state *hls, cfg_label_t starting_label)
{
	struct low_level_state lls;
	printf("Should start from label %d\n", starting_label);
	lls.cfg_node = starting_label;
	start_thread(hls, &lls);
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
	printf("Fetched %d bytes from instr at %lx (%p)\n", to_copy, offset, ctxt->current_cfg_node->content);
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

static void
exit_interpreter(struct high_level_state *hls, struct reg_struct *regs)
{
	exit_routine_t *exit_routine;

	/* Tear down the memory allocator */
	while (hls->current_arena) {
		void *next = *(void **)hls->current_arena;
		munmap(hls->current_arena, ARENA_SIZE);
		hls->current_arena = next;
	}

	exit_routine = find_exit_stub(regs->rip);
	printf("Exit stub for %lx is at %p (regs %p)\n", regs->rip, exit_routine, regs);
	printf("Exit to %lx, rax %lx, rbp %lx\n", regs->rip, regs->rax, regs->rbp);
	exit_routine(regs);
	/* shouldn't get here */
	abort();
}

static void
clone_ll_state(struct high_level_state *hls, int dupe_internal_structures,
	       int ll_idx, cfg_label_t new_node)
{
	int i = alloc_lls_slot(hls);
	hls->ll_states[i] = hls->ll_states[ll_idx];
	hls->ll_states[i].cfg_node = new_node;
}

static void
exit_thread(struct low_level_state *ll)
{
	printf("Exit thread %d\n", ll->cfg_node);
}

static void
advance_hl_interpreter(struct high_level_state *hls, struct reg_struct *regs)
{
	int i, j, r;
	struct cep_emulate_ctxt emul_ctxt = {
		.ctxt = {
			.regs = regs,
			.addr_size = 64,
			.sp_size = 64,
			.force_writeback = 0,
		},
	};

	for (i = 0; i < plan.nr_entry_points; i++) {
		if (plan.entry_points[i]->orig_rip != regs->rip)
			continue;
		for (j = 0; j < plan.entry_points[i]->nr_entry_ctxts; j++) {
			if (ctxt_matches(plan.entry_points[i]->ctxts[j], regs))
				start_low_level_thread(hls, plan.entry_points[i]->ctxts[j]->cfg_label);
		}
	}

	assert(hls->nr_ll_states != 0);
	assert(hls->ll_states != NULL);
	emul_ctxt.current_cfg_node = &plan.cfg_nodes[hls->ll_states[0].cfg_node];

	printf("Emulate from %lx\n", regs->rip);
	r = x86_emulate(&emul_ctxt.ctxt, &emulator_ops);
	assert(r == X86EMUL_OKAY);

	printf("Next instr %lx\n", regs->rip);
	r = hls->nr_ll_states;
	for (i = 0; i < r; i++) {
		cfg_label_t cur_label = hls->ll_states[i].cfg_node;
		const struct cfg_instr *current_cfg_node = &plan.cfg_nodes[cur_label];
		int preserve = 0;
		for (j = 0; j < current_cfg_node->nr_successors; j++) {
			if (regs->rip == plan.cfg_nodes[current_cfg_node->successors[j]].rip) {
				printf("Advance to %d\n", current_cfg_node->successors[j]);
				clone_ll_state(hls, preserve, i, current_cfg_node->successors[j]);
				preserve = 1;
			} else {
				printf("Reject %d (%lx)\n",
				       current_cfg_node->successors[j],
				       plan.cfg_nodes[current_cfg_node->successors[j]].rip);
			}
		}
		if (!preserve)
			exit_thread(&hls->ll_states[i]);
	}
	hls->nr_ll_states -= r;
	memmove(hls->ll_states, hls->ll_states + r, sizeof(hls->ll_states[0]) * hls->nr_ll_states);
	if (hls->nr_ll_states == 0)
		exit_interpreter(hls, regs);
}

static void
start_interpreting(int entrypoint_idx, struct reg_struct *regs)
{
	struct high_level_state hls;
	const struct cep_entry_point *entry_point = plan.entry_points[entrypoint_idx];

	printf("Start interpreting idx %d, regs at %p\n", entrypoint_idx, regs);
	init_high_level_state(&hls);
	regs->rip = entry_point->orig_rip;
	regs->rsp = (unsigned long)regs + sizeof(regs) + 0x80;
	while (1)
		advance_hl_interpreter(&hls, regs);
	abort();
}

/* We have two types of trampolines, one for transitioning from client
   code into the interpreter and one for going from the interpreter to
   client code. */
asm(
"__trampoline_client_to_interp_start:\n"
"    lea -0x80(%rsp), %rsp\n"
"    pushf\n"
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
"    push %rsp\n" /* Gets fixed up later */
"    push %rbx\n"
"    push %rcx\n"
"    push %rdx\n"
"    push %rax\n"
"    push %rax\n" /* Leave space for rip */
"    movq %rsp, %rsi\n"
"__trampoline_client_to_interp_load_edi:\n"
"    mov $0x11223344, %edi\n"
"__trampoline_client_to_interp_load_rdx:\n"
"    movq $0x1122334455667788, %rdx\n"
"    jmp *%rdx\n"
"__trampoline_client_to_interp_end:\n"
"\n"
"__trampoline_interp_to_client_start:\n"
"    movq %rdi, %rsp\n"
"    popq %rax\n" /* RIP, but we have another plan for restoring that */
"    popq %rax\n"
"    popq %rdx\n"
"    popq %rcx\n"
"    popq %rbx\n"
"    popq %rbp\n" /* RSP, but we have another plan for restoring that */
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
"    lea 0x80(%rsp), %rsp\n"
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

	printf("tramp start %p, end %p, size %zx\n", &__trampoline_client_to_interp_end, &__trampoline_client_to_interp_start, tramp_size);
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
	printf("Trampoline at %p\n", buffer);
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
	/* There's a race here, but it doesn't really matter.  The
	   worst case is that we leak a trampoline, but they're small
	   and it doesn't happen very often (never, once you're passed
	   the initial startup phase). */
	cursor->next = head_exit_trampoline;
	head_exit_trampoline = cursor;
	return (exit_routine_t *)(cursor + 1);
}

/* This is hooked into clone() so that we're called instead of the
   usual child thread function.  The hcild thread function and its
   sole argument are passed in as @fn and @fn_arg.  Create our
   per-thread state area and then run the user function.  Note that we
   have to call __GI__exit ourselves, because of the way we're patched
   in. */
static void
clone_hook_c(int (*fn)(void *), void *fn_arg)
{
	void *state;
	int res;

	state = mmap(NULL, PAGE_SIZE * 1024, PROT_READ|PROT_WRITE,
		     MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
	arch_prctl(ARCH_SET_GS, (unsigned long)state);

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
	void *state;
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

	state = mmap(NULL, PAGE_SIZE * 1024, PROT_READ|PROT_WRITE,
		     MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
	arch_prctl(ARCH_SET_GS, (unsigned long)state);

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
