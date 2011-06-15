#include <assert.h>

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

static char *
build_patch(struct patch *patch)
{
	char *res = malloc_executable(sizeof(patch->content));
	unsigned x;

	memcpy(res, patch->content, patch->content_size);
	for (x = 0; x < patch->nr_relocations; x++) {
		const struct relocation *r = &patch->relocations[x];
		unsigned long val;
		val = r->target + r->addend;
		if (r->relative)
			val -= (unsigned long)res + r->offset;
		assert(r->size <= 8);
		if (r->size < 8) {
			unsigned long mask;
			mask = (1ul << (r->size * 8)) - 1;
			assert( (val & ~mask) == 0 ||
				(val & ~mask) == ~mask );
			val &= mask;
		}
		memcpy(res + r->offset,
		       &val,
		       r->size);
	}
	return res;
}

