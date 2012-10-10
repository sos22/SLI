/* Patch skeleton which patches in jump instructions rather than
   relying on debug registers. */
#include <sys/mman.h>
#include <pthread.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

#define PAGE_SIZE 4096ul
#define PAGE_MASK (~(PAGE_SIZE - 1))

static const void *patch_body;

#include "patch_skeleton_common.c"

void acquire_lock_c(void) __attribute__((visibility ("hidden")));

void
acquire_lock_c(void)
{
	pthread_mutex_lock(&mux);
}

asm ("\
	/* We're called from the patch without saving any registers except rsi.\
	We are outside the stack redzone, though.  Go and save all the\
	call-clobbered registers and get into C. */\
	\
acquire_lock:\n\
	pushf\n\
	push %rax\n\
	push %rcx\n\
	push %rdx\n\
	push %rdi\n\
	push %r8\n\
	push %r9\n\
	push %r10\n\
	push %r11\n\
	call acquire_lock_c\n\
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

static void
activate(void)
{
	char *body;
	unsigned x;
	long delta;
	unsigned y;
	char pathbuf[4097];

	readlink("/proc/self/exe", pathbuf, sizeof(pathbuf));
	for (x = 0; pathbuf[x]; x++)
		;
	while (x > 0 && pathbuf[x] != '/')
		x--;
	if (strcmp(pathbuf + x, "/" BINARY_PATCH_FOR)) {
		printf("This is a patch for %s, but this is %s; disabled\n",
		       BINARY_PATCH_FOR, pathbuf + x + 1);
		return;
	}

	pthread_mutex_init(&mux, NULL);

	patch_body = body = build_patch(&patch);

	for (x = 0; x < patch.nr_entry_points; x++) {
		mprotect((void *)(patch.entry_points[x].rip & PAGE_MASK),
			 PAGE_SIZE * 2,
			 PROT_READ|PROT_WRITE|PROT_EXEC);
		*(unsigned char *)patch.entry_points[x].rip = 0xe9;
		delta = (unsigned long)body + patch.entry_points[x].offset -
			patch.entry_points[x].rip - 5;
		assert(delta == (int)delta);
		*(int *)(patch.entry_points[x].rip + 1) = delta;
		mprotect((void *)(patch.entry_points[x].rip & PAGE_MASK),
			 PAGE_SIZE * 2,
			 PROT_READ|PROT_EXEC);
	}
}

static void (*__init_activate)(void) __attribute__((section(".ctors"), unused, used)) = activate;

