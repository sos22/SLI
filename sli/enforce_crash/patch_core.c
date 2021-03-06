#undef DEBUG

void happensBeforeEdge__before(int code);
long happensBeforeEdge__after(int nr_codes, long *codes);
void clearMessage(int code);

struct relocation {
	unsigned offset;
	unsigned size;
	long addend;
	int relative;
	unsigned long target;
};

struct patch_entry_point {
	unsigned long orig_rip;
	unsigned offset_in_patch;
};

struct patch {
	const struct relocation *relocations;
	int nr_relocations;
	struct patch_entry_point *entry_points;
	int nr_entry_points;
	const unsigned char *content;
	unsigned content_size;
};

#include the_patch

#include <asm/prctl.h>
#include <sys/prctl.h>
#include <sys/mman.h>
#include <sys/time.h>
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
static unsigned
max_stalls;
static int
have_cloned;

/* These get used from inline assembly only.  Shut the compiler up. */
static void happensBeforeEdge__before_c(int code) __attribute__((unused));
static long happensBeforeEdge__after_c(int nr_codes, long *codes) __attribute__((unused));
static void clearMessage_c(int code) __attribute__((unused));
static void clone_hook_c(int (*fn)(void *), void *fn_arg) __attribute__((unused));

#ifdef DEBUG
#define _GNU_SOURCE
#include <sys/syscall.h>
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
#define debug(fmt, ...)				\
	printf("%f: %d: " fmt "\n",		\
		now(), gettid(),		\
	       ##__VA_ARGS__)
#else
#define debug(...) do {} while(0)
#endif
static void
happensBeforeEdge__before_c(int code)
{
	debug("Send %x", code);
	messages[code - MESSAGE_ID_BASE] = 1;
}
static long
happensBeforeEdge__after_c(int nr_codes, long *codes)
{
	int cntr;
	int max;
	int i;

	debug("Receive %d messages", nr_codes);
	for (i = 0; i < nr_codes; i++)
		debug("\t%lx", codes[i]);
	if (!have_cloned)
		return 0;

	max = 1000;
	for (cntr = 0; cntr < max; cntr++) {
		for (i = 0; i < nr_codes; i++) {
			if (codes[i] < MESSAGE_ID_BASE || codes[i] >= MESSAGE_ID_END)
				abort();
			if (messages[codes[i] - MESSAGE_ID_BASE]) {
				debug("Received %lx", codes[i]);
				return codes[i];
			}
		}
		if (cntr != max - 1)
			usleep(100);
	}
	debug("Failed to receive messages");

	return 0;
}
static void
clearMessage_c(int code)
{
	usleep(10000);
	debug("Clear %x", code);
	messages[code - MESSAGE_ID_BASE] = 0;
}

/* Calling convention for happensBeforeEdge__before:

   -- RSI has already been stashed.
   -- RFLAGS has *not* been stashed.
   -- We're out of the client red zone.
   -- RDI is the ID if the message we're supposed to be sending.
   -- No other registers have been saved.
*/
asm(
"happensBeforeEdge__before:\n"
"       push %rax\n"
"       push %rcx\n"
"       push %rdx\n"
"       push %r8\n"
"       push %r9\n"
"       push %r10\n"
"       push %r11\n"
"       pushf\n"
"       call happensBeforeEdge__before_c\n"
"       popf\n"
"       pop %r11\n"
"       pop %r10\n"
"       pop %r9\n"
"       pop %r8\n"
"       pop %rdx\n"
"       pop %rcx\n"
"       pop %rax\n"
"       ret\n"
	);
/* Calling convention for happensBeforeEdge__after:

   -- We're out of the client zone.
   -- RDI contains the number of messages to receive
   -- The very top of the stack is the return address, and after
      that you have the IDs which we need to receive
   -- RFLAGS has already been saved
   -- RAX is used as a return value, either the ID of the
      message we received or zero if we received nothing.
   -- Nothing else is done for us.
*/
asm(
"happensBeforeEdge__after:\n"
"       push %rsi\n"
"       lea 16(%rsp), %rsi\n"
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
"	pop %rsi\n"
"	ret\n"
	);

/* clearMessage() calling convention:

   -- RDI is the message to clear
   -- We're clear of the client red zone
   -- Nothing else is stashed for us
*/
asm(
"clearMessage:\n"
"       push %rax\n"
"       push %rcx\n"
"       push %rdx\n"
"       push %rsi\n"
"       push %r8\n"
"       push %r9\n"
"       push %r10\n"
"       push %r11\n"
"       pushf\n"
"       call clearMessage_c\n"
"       popf\n"
"       pop %r11\n"
"       pop %r10\n"
"       pop %r9\n"
"       pop %r8\n"
"       pop %rsi\n"
"       pop %rdx\n"
"       pop %rcx\n"
"       pop %rax\n"
"       ret\n"
	);

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

extern void clone(void);

static void (*__GI__exit)(int res);

void arch_prctl(int, unsigned long);

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

/* For some reason, if this is non-static, gcc generates a very odd
   relocation for it, and we fail.  I don't understand why, or why the
   other things defined in assembly aren't affected, so just accept it
   for now and ignore the compiler warnings. */
static void clone_hook_asm();

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

	hook_clone();
}

static void (*__init_activate)(void) __attribute__((section(".ctors"), unused, used)) = activate;

