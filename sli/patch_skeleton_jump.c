/* Patch skeleton which patches in jump instructions rather than
   relying on debug registers. */
#include <sys/mman.h>
#include <pthread.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

#define PAGE_SIZE 4096ul
#define PAGE_MASK (~(PAGE_SIZE - 1))

#include "patch_skeleton_common.c"

void acquire_lock_c(void) __attribute__((visibility ("hidden")));

void
acquire_lock_c(void)
{
	pthread_mutex_lock(&mux);
}

extern void acquire_lock_ll();
asm ("\
	/* We're called from the patch without saving any registers.\
	We are outside the stack redzone, though.  Go and save all the\
	call-clobbered registers and get into C. */\
	\
acquire_lock_ll:\n\
        .quad 1f\n\
1:\n\
	pushf\n\
	push %rax\n\
	push %rcx\n\
	push %rdx\n\
	push %rdi\n\
        push %rsi\n\
	push %r8\n\
	push %r9\n\
	push %r10\n\
	push %r11\n\
	call acquire_lock_c\n\
	pop %r11\n\
	pop %r10\n\
	pop %r9\n\
	pop %r8\n\
        pop %rsi\n\
	pop %rdi\n\
	pop %rdx\n\
	pop %rcx\n\
	pop %rax\n\
	popf\n\
	ret\n\
");

static void
activate(void)
{
	char *body;
	char *trampolines;
	unsigned x;
	long delta;
	unsigned y;
	char pathbuf[4097];

	readlink("/proc/self/exe", pathbuf, sizeof(pathbuf));
	for (x = 0; pathbuf[x]; x++)
		;
	while (x > 0 && pathbuf[x] != '/')
		x--;
	if (strcmp(pathbuf + x, "/mysqld"))
		return;

	pthread_mutex_init(&mux, NULL);

	body = build_patch(&patch);

	trampolines = malloc_executable(PAGE_SIZE);
	/* We need to patch each entry point so that it turns into a
	   jump instruction which targets a trampoline which does
	   this:

	   lea -128(%rsp), %rsp
	   pushq %rsi
	   movq $acquire_lock_ll, %rsi
	   call *%rsi
	   popq %rsi
	   lea 128(%rsp), %rsp
	   jmp relevant_offset_in_patch
	   1: acquire_lock_ll

	   Do so. */
	for (x = 0; x < patch.nr_entry_points; x++) {
		memcpy(trampolines,
		       "\x48\x8d\x64\x24\x80" /* lea -128(%rsp), %rsp */
		       "\x56" /* pushq %rsi */
		       "\x48\xbe\x00\x00\x00\x00\x00\x00\x00\x00" /* movq $imm64, %rsi */
		       "\xff\xd6" /* call *%rsi */
		       "\x5e" /* pop %rsi */
		       "\x48\x8d\xa4\x24\x80\x00\x00\x00" /* lea 128(%rsp), %rsp */
		       "\xe9\x00\x00\x00\x00" /* jmp rel32 */
		       ,
		       32);

		/* Patch in call address */
		assert(*(unsigned long *)(trampolines+8) == 0);
		*(unsigned long *)(trampolines+8) = (unsigned long)&acquire_lock_ll;

		/* Patch in jump address */
		for (y = 0; y < patch.nr_translations; y++) {
			if (patch.trans_table[y].rip == patch.entry_points[x]) {
				delta = (unsigned long)body + patch.trans_table[y].offset -
					((unsigned long)trampolines + 32);
				assert(delta == (int)delta);
				assert(*(int *)(trampolines+28) == 0);
				*(int *)(trampolines + 28) = delta;
				break;
			}
		}
		assert(y != patch.nr_translations);

		/* Trampoline is now correctly established.  Patch in
		 * a jump to it. */
		mprotect((void *)(patch.entry_points[x] & PAGE_MASK),
			 PAGE_SIZE * 2,
			 PROT_READ|PROT_WRITE|PROT_EXEC);
		*(unsigned char *)patch.entry_points[x] = 0xe9;
		delta = (unsigned long)trampolines - (patch.entry_points[x] + 5);
		assert(delta == (int)delta);
		*(int *)(patch.entry_points[x] + 1) = delta;
		mprotect((void *)(patch.entry_points[x] & PAGE_MASK),
			 PAGE_SIZE * 2,
			 PROT_READ|PROT_EXEC);

		trampolines += 32;
	}
}

static void (*__init_activate)(void) __attribute__((section(".ctors"), unused, used)) = activate;

