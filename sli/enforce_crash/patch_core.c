static void happensBeforeEdge__before(int code);
static long happensBeforeEdge__after(int code);
static void clearMessage(int code);

struct relocation {
	unsigned offset;
	unsigned size;
	long addend;
	int relative;
	unsigned long target;
};

struct trans_table_entry {
	unsigned long rip;
	unsigned offset;
};

struct patch_entry_point {
	unsigned long orig_rip;
	unsigned offset_in_patch;
};

struct patch {
	const struct relocation *relocations;
	int nr_relocations;
	const struct trans_table_entry *trans_table;
	int nr_translations;
	struct patch_entry_point *entry_points;
	int nr_entry_points;
	const unsigned char *content;
	unsigned content_size;
};

#include the_patch

#include <asm/prctl.h>
#include <sys/prctl.h>
#include <sys/mman.h>
#include <sys/unistd.h>
#include <assert.h>
#include <err.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PAGE_SIZE 4096ul
#define PAGE_MASK (~(PAGE_SIZE - 1))

static void *
patch_address;
static volatile int
messages[MESSAGE_ID_END - MESSAGE_ID_BASE];
static int
message_counters[MESSAGE_ID_END - MESSAGE_ID_BASE];
static unsigned
max_stalls;

static void
happensBeforeEdge__before_c(int code)
{
	messages[code - MESSAGE_ID_BASE] = 1;
}
static long
happensBeforeEdge__after_c(int code)
{
	int cntr;
	int max;

	if (max_stalls == 0) {
		max = 0;
	} else if (message_counters[code - MESSAGE_ID_BASE] < 20) {
		max = max_stalls >> message_counters[code - MESSAGE_ID_BASE];
		message_counters[code - MESSAGE_ID_BASE]++;
	} else {
		max = 1;
	}
	for (cntr = 0; cntr < max && messages[code - MESSAGE_ID_BASE] == 0; cntr++)
		usleep(100);
	if (!messages[code - MESSAGE_ID_BASE]) {
		return 0;
	} else {
		return 1;
	}
}
static void
clearMessage_c(int code)
{
	messages[code - MESSAGE_ID_BASE] = 0;
}

#define mk_trampoline(name)						\
asm(								        \
"	/* We're called from the patch without saving any registers"    \
"          except rdi and rsi.  We are outside the stack redzone,"	\
"          though.  Go and save all the call-clobbered registers and"	\
"          get into C. */"						\
"	"								\
#name ":\n"								\
"	pushf\n"							\
"	push %rax\n"							\
"	push %rcx\n"							\
"	push %rdx\n"							\
"	push %r8\n"							\
"	push %r9\n"							\
"	push %r10\n"							\
"	push %r11\n"							\
"	call " #name "_c\n"						\
"	pop %r11\n"							\
"	pop %r10\n"							\
"	pop %r9\n"							\
"	pop %r8\n"							\
"	pop %rdx\n"							\
"	pop %rcx\n"							\
"	pop %rax\n"							\
"	popf\n"								\
"	ret\n"								\
	)
mk_trampoline(happensBeforeEdge__before);
asm(
"	/* We're called from the patch without saving any registers"
"          except rdi and rsi.  We are outside the stack redzone,"
"          though.  Go and save all the call-clobbered registers and"
"          get into C. */"
"	"
"happensBeforeEdge__after:\n"
"	pushf\n"
"	push %rcx\n"
"	push %rdx\n"
"	push %r8\n"
"	push %r9\n"
"	push %r10\n"
"	push %r11\n"
"	call happensBeforeEdge__after_c\n"
"	pop %r11\n"
"	pop %r10\n"
"	pop %r9\n"
"	pop %r8\n"
"	pop %rdx\n"
"	pop %rcx\n"
"	popf\n"
"	ret\n"
	);
mk_trampoline(clearMessage);

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
	char *res = malloc_executable(patch->content_size);
	unsigned x;

	if (res == MAP_FAILED)
		err(1, "cannot allocate %d bytes of executable memory", patch->content_size);

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

static void
activate(void)
{
	char *body;
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

	body = getenv("SOS22_ENFORCER_MAX_STALLS");
	if (!body) {
		printf("SOS22_ENFORCER_MAX_STALLS is not set!\n");
		abort();
	}
	max_stalls = atoi(body);
	if (max_stalls < 0 || max_stalls >= 100000)
		abort();

	state = mmap(NULL, PAGE_SIZE * 1024, PROT_READ|PROT_WRITE,
		     MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
	arch_prctl(ARCH_SET_GS, (unsigned long)state);

	body = build_patch(&ident);

	/* We need to patch each entry point so that it turns into a
	   jump instruction which targets the patch.  Do so. */
	for (x = 0; x < ident.nr_entry_points; x++) {
		mprotect((void *)(ident.entry_points[x].orig_rip & PAGE_MASK),
			 PAGE_SIZE * 2,
			 PROT_READ|PROT_WRITE|PROT_EXEC);
		*(unsigned char *)ident.entry_points[x].orig_rip = 0xe9; /* jmp rel32 opcode */
		delta = (unsigned long)body + ident.entry_points[x].offset_in_patch - (ident.entry_points[x].orig_rip + 5);
		assert(delta == (int)delta);
		*(int *)(ident.entry_points[x].orig_rip + 1) = delta;
		mprotect((void *)(ident.entry_points[x].orig_rip & PAGE_MASK),
			 PAGE_SIZE * 2,
			 PROT_READ|PROT_EXEC);
	}

	patch_address = body;
}

static void (*__init_activate)(void) __attribute__((section(".ctors"), unused, used)) = activate;

