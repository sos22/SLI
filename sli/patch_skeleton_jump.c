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

static void
activate(void)
{
	char *body;
	unsigned x;
	long delta;
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

