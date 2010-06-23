#define _GNU_SOURCE
#include <sys/mman.h>
#include <sys/ptrace.h>
#include <sys/user.h>
#include <sys/wait.h>
#include <assert.h>
#include <err.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ucontext.h>

static void *actual_patch;
static pthread_mutex_t mux;

void release_lock_c(void) __attribute__((visibility ("hidden")));

void
release_lock_c(void)
{
	pthread_mutex_unlock(&mux);
}

asm ("\
	/* We're called from the patch without saving any registers except rsi.\
	We are outside the stack redzone, though.  Go and save all the\
	call-clobbered registers and get into C. */\
	\
release_lock:\n\
	pushf\n\
	push %rax\n\
	push %rcx\n\
	push %rdx\n\
	push %rdi\n\
	push %r8\n\
	push %r9\n\
	push %r10\n\
	push %r11\n\
	call release_lock_c\n\
	pop %r11\n\
	pop %r10\n\
	pop %r9\n\
	pop %r8\n\
	pop %rdi\n\
	pop %rdx\n\
	pop %rcx\n\
	pop %rax\n\
	popf\n\
	ret\n\
");
static void *
malloc_executable(size_t s)
{
	return mmap(NULL, (s + PAGE_SIZE - 1) & ~(PAGE_SIZE - 1),
		    PROT_READ|PROT_WRITE|PROT_EXEC,
		    MAP_PRIVATE|MAP_32BIT|MAP_ANONYMOUS|MAP_EXECUTABLE,
		    -1,
		    0);
}

/* You might think that we should just use setcontext() here.  You'd
   be wrong, because setcontext(), for reasons which remain obscure,
   doesn't restore eax. */
static void
my_setcontext(ucontext_t *uc)
{
	sigprocmask(SIG_SETMASK, &uc->uc_sigmask, NULL);

	asm volatile(
		/* Switch to new stack and get out of the red zone */
		"movq 0x78(%%rsi), %%rsp\n"
		"lea -0x80(%%rsp), %%rsp\n"

		/* Restore almost all of the registers */
#define DO_REG(offset, reg) \
		"movq " #offset "(%%rsi), %%" #reg "\n"
		DO_REG(0x00, r8)
		DO_REG(0x08, r9)
		DO_REG(0x10, r10)
		DO_REG(0x18, r11)
		DO_REG(0x20, r12)
		DO_REG(0x28, r13)
		DO_REG(0x30, r14)
		DO_REG(0x38, r15)
		DO_REG(0x40, rdi)
		//DO_REG(0x48, rsi)
		DO_REG(0x50, rbp)
		DO_REG(0x58, rbx)
		DO_REG(0x60, rdx)
		DO_REG(0x68, rax)
		DO_REG(0x70, rcx)
		//DO_REG(0x78, rsp)

		/* Save the other registers on the stack */
		"pushq 0x80(%%rsi)\n" /* rip */
		"pushq 0x88(%%rsi)\n" /* rflags */

		/* Now restore RSI */
		DO_REG(0x48, rsi)
#undef DO_REG

		/* Finish up */
		"popf\n"
		"ret $0x80\n"
		:
		: "S" (uc->uc_mcontext.gregs)
		: "memory");
	abort();
}

static void
sigtrap_sigaction(int sig, siginfo_t *info, void *_ctxt)
{
	ucontext_t *ctxt = _ctxt;
	unsigned long rip = ctxt->uc_mcontext.gregs[REG_RIP];
	unsigned x;

	pthread_mutex_lock(&mux);

	ctxt->__fpregs_mem.mxcsr &= 0xffff;
	for (x = 0; x < sizeof(entry_points) / sizeof(entry_points[0]); x++) {
		if (rip == entry_points[x]) {
			/* This is one of ours, so we are allowed to
			 * redirect. */
			for (x = 0; x < sizeof(trans_table) / sizeof(trans_table[0]); x++) {
				if (trans_table[x].rip == rip) {
					ctxt->uc_mcontext.gregs[REG_RIP] =
						(unsigned long)actual_patch +
						trans_table[x].offset;
					my_setcontext(ctxt);
					abort();
				}
			}
			/* Shouldn't have an entry point which isn't
			   present in the patch. */
			abort();
		}
	}
	errx(1, "sigtrap at bad address %lx", rip);
}

static void
activate(void)
{
	unsigned x;
	struct sigaction sigact;
	pid_t child;

	pthread_mutex_init(&mux, NULL);

	actual_patch = malloc_executable(sizeof(patch_content));
	memcpy(actual_patch, patch_content, sizeof(patch_content));
	for (x = 0; x < sizeof(reloc) / sizeof(reloc[0]); x++) {
		const struct relocation *r = &reloc[x];
		unsigned long val;
		val = r->target + r->addend;
		if (r->relative)
			val -= (unsigned long)actual_patch + r->offset;
		assert(r->size <= 8);
		if (r->size < 8) {
			unsigned long mask;
			mask = (1ul << (r->size * 8)) - 1;
			assert( (val & ~mask) == 0 ||
				(val & ~mask) == ~mask );
			val &= mask;
		}
		memcpy(actual_patch + r->offset,
		       &val,
		       r->size);
	}

	/* Install the signal handler */
	/* XXX should really trap SIGSEGV and SIGBUS as well, so that
	   we can make the client see correct RIPs in the register
	   state on the stack XXX */
	sigact.sa_sigaction = sigtrap_sigaction;
	sigemptyset(&sigact.sa_mask);
	sigact.sa_flags = SA_SIGINFO;
	if (sigaction(SIGTRAP, &sigact, NULL) < 0)
		err(1, "installing SIGTRAP handler");

	/* Now go through and set up debug registers.  Need to do this
	 * from a new process, for kernel implementation reasons. */
	child = fork();
	if (child == 0) {
		pid_t parent;
		unsigned long d7;
		int status;

		parent = getppid();
		d7 = 0;
		if (ptrace(PTRACE_ATTACH, parent, 0, 0) < 0)
			err(1, "ptrace attach");
		if (waitpid(parent, &status, 0) < 0)
			err(1, "waiting for parent to stop");

		for (x = 0; x < sizeof(entry_points) / sizeof(entry_points[0]); x++) {
			printf("Add fixup %d %lx\n", x, entry_points[x]);
			if (ptrace(PTRACE_POKEUSER,
				   parent,
				   offsetof(struct user, u_debugreg[x]),
				   entry_points[x]) < 0)
				err(1, "ptrace %d", x);

			/* Enable the register.  They're in
			   instruction mode by default, which is what
			   we want, so just turning it on is
			   sufficient. */
			d7 |= 1 << (x * 2);
		}
		if (ptrace(PTRACE_POKEUSER,
			   parent,
			   offsetof(struct user, u_debugreg[7]),
			   d7) < 0)
			err(1, "ptrace 7");
		if (ptrace(PTRACE_DETACH, parent, 0, 0) < 0)
			err(1, "ptrace attach");
		_exit(0);
	} else {
		int status;

		if (waitpid(child, &status, 0) < 0)
			err(1, "waitpid()");
		if (!WIFEXITED(status) || WEXITSTATUS(status) != 0)
			errx(1, "bad status from child: %x", status);
	}

	/* We should now be ready to go. */
}

static void (*__init_activate)(void) __attribute__((section(".ctors"), unused, used)) = activate;
