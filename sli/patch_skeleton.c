#include <sys/mman.h>
#include <assert.h>
#include <stdio.h>
#include <string.h>

#define PAGE_SIZE 4096

static void *actual_patch;

void release_lock_c(void) __attribute__((visibility ("hidden")));

void
release_lock_c(void)
{
}

asm ("\
	/* We're called from the patch without saving any registers.\
	We are outside the stack redzone, though.  Go and save all the\
	call-clobbered registers and get into C. */\
	\
release_lock:\n\
	pushf\n\
	push %rax\n\
	push %rcx\n\
	push %rdx\n\
	push %rsi\n\
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
	pop %rsi\n\
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

static void
activate(void)
{
	unsigned x;

	printf("Activated, %zd\n", sizeof(patch_content));
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
	*(unsigned *)(0xf001) = 0xdead;
}

static void (*__init_activate)(void) __attribute__((section(".ctors"), unused, used)) = activate;
