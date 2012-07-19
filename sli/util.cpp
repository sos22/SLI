#include <sys/types.h>
#include <sys/wait.h>
#include <err.h>
#include <signal.h>
#include <unistd.h>

#include "sli.h"
#include "offline_analysis.hpp"
#include "libvex_parse.h"
#include "timers.hpp"
#include "profile.hpp"

void
debugger_attach(void)
{
	volatile bool debugger_ready;
	debugger_ready = false;
	printf("Waiting for debugger in pid %d\n", getpid());
	while (!debugger_ready)
		sleep(1);
}

static __attribute__ ((noreturn)) void
failure_exit(void)
{
	abort();
}

static void
log_bytes(const char *buf, Int nbytes)
{
	fwrite(buf, nbytes, 1, stdout);
}

static void
handle_sigusr1(int )
{
	/* So that we can get profiling results etc. */
	exit(1);
}

void
init_sli(void)
{
	VexControl vcon;

	std::set_terminate(__gnu_cxx::__verbose_terminate_handler);

	vexInitHeap();
	LibVEX_default_VexControl(&vcon);
	vcon.iropt_level = 0;
	vcon.iropt_unroll_thresh = 0;
	vcon.guest_chase_thresh = 0;
	//vcon.guest_max_insns = 1;
	LibVEX_Init(failure_exit, log_bytes, 0, 0, &vcon);

	signal(SIGUSR1, handle_sigusr1);

	initialise_timers();
	initialise_profiling();
}

template <> unsigned long
__default_hash_function(const unsigned long &key)
{
	return key;
}

char *
readfile(int fd)
{
	size_t buf_allocated = 8192;
	char *buf = (char *)malloc(buf_allocated + 1);
	unsigned buf_used = 0;
	int r;

	while (1) {
		r = read(fd, buf + buf_used, buf_allocated - buf_used);
		if (r == 0)
			break;
		if (r < 0)
			err(1, "read(%d)", fd);
		buf_used += r;
		if (buf_used == buf_allocated) {
			buf_allocated += 8192;
			buf = (char *)realloc(buf, buf_allocated + 1);
		}
	}
	buf[buf_used] = 0;
	return buf;
}

IRExpr *
readIRExpr(int fd)
{
	char *buf = readfile(fd);
	IRExpr *r;
	const char *succ;
	if (!parseIRExpr(&r, buf, &succ))
		errx(1, "cannot parse %s as IRExpr", buf);
	parseThisChar(' ', succ, &succ);
	if (*succ)
		errx(1, "garbage after irexpr: %s", succ);
	free(buf);
	return r;
}

FILE *
fopenf(const char *mode, const char *fmt, ...)
{
	va_list args;
	va_start(args, fmt);
	char *path;
	int r = vasprintf(&path, fmt, args);
	(void)r;
	va_end(args);

	FILE *res = fopen(path, mode);
	free(path);
	return res;
}

void
__fail(const char *file, unsigned line, const char *fmt, ...)
{
	va_list args;
	va_start(args, fmt);
	char *msg;
	int r = vasprintf(&msg, fmt, args);
	(void)r;
	va_end(args);

	fprintf(_logfile, "%s:%d: Failed: %s\n", file, line, msg);
	fprintf(stderr, "%s:%d: Failed: %s\n", file, line, msg);
	fflush(0);
#undef abort
	abort();
}

#ifndef NDEBUG
void
sanityCheckIRExpr(IRExpr *e, const std::set<threadAndRegister, threadAndRegister::fullCompare> *live)
{
	e->sanity_check();
	if (live) {
		class _ : public IRExprTransformer {
			const std::set<threadAndRegister, threadAndRegister::fullCompare> *live;
			IRExpr *transformIex(IRExprGet *g) {
				if (g->reg.isTemp() ||
				    (g->reg.gen() != (unsigned)-1 &&
				     g->reg.gen() != 0))
					assert(live->count(g->reg));
				return NULL;
			}
		public:
			_(const std::set<threadAndRegister, threadAndRegister::fullCompare> *_live)
				: live(_live)
			{}
		} t(live);
		t.doit(e);
	}
}
#endif

/* This is mostly for the benefit of the debugger. */
void
printIRExpr(IRExpr *e)
{
	ppIRExpr(e, stdout);
	printf("\n");
}

/* Format an IRExpr into a string allocated on the IR heap. */
struct __nameIRExpr_context {
	size_t buffer_used;
	char *buffer;
};
static ssize_t
__nameIRExpr_write(void *cookie, const char *buffer, size_t sz)
{
	struct __nameIRExpr_context *c = (struct __nameIRExpr_context *)cookie;
	static struct libvex_allocation_site site = {0, __FILE__, __LINE__};
	if (!c->buffer)
		c->buffer = (char *)__LibVEX_Alloc_Bytes(&ir_heap, sz * 2, &site);
	else
		c->buffer = (char *)LibVEX_realloc(&ir_heap, c->buffer, c->buffer_used + sz);
	memcpy(c->buffer + c->buffer_used, buffer, sz);
	c->buffer_used += sz;
	return sz;
}
char *
nameIRExpr(IRExpr *a)
{
	cookie_io_functions_t functionTable;
	memset(&functionTable, 0, sizeof(functionTable));
	functionTable.write = __nameIRExpr_write;
	struct __nameIRExpr_context ctxt;
	ctxt.buffer_used = 0;
	ctxt.buffer = NULL;
	FILE *f = fopencookie(&ctxt, "w", functionTable);
	if (!f)
		err(1, "fopencookie() returned NULL?");
	ppIRExpr(a, f);
	fclose(f);
	return ctxt.buffer;
}

char *
flattenStringFragments(std::vector<const char *> fragments)
{
	size_t sz = 1;
	for (unsigned x = 0; x < fragments.size(); x++)
		sz += strlen(fragments[x]);
	char *res = (char *)LibVEX_Alloc_Bytes(sz);
	char *cursor = res;
	for (unsigned x = 0; x < fragments.size(); x++) {
		memcpy(cursor, fragments[x], strlen(fragments[x]));
		cursor += strlen(fragments[x]);
	}
	*cursor = 0;
	assert(cursor == res + sz-1);
	return res;
}

void
my_system(const char *arg1, ...)
{
	pid_t pid = fork();
	if (pid == -1)
		err(1, "fork(%s)", arg1);
	if (pid == 0) {
		va_list va;
		unsigned nr_args;

		va_start(va, arg1);
		for (nr_args = 1; va_arg(va, const char *); nr_args++)
			;
		va_end(va);

		const char **args = (const char **)calloc(sizeof(args[0]), nr_args + 1);
		args[0] = arg1;
		va_start(va, arg1);
		for (nr_args = 1; ; nr_args++) {
			args[nr_args] = va_arg(va, const char *);
			if (!args[nr_args])
				break;
		}
		execvp(arg1, (char *const *)args);
		err(1, "execvp(%s)", arg1);
	}

	int status;
	pid_t opid;
	opid = waitpid(pid, &status, 0);
	if (opid < 0) err(1, "waitpid() for %s", arg1);
	assert(opid == pid);
	if (WIFEXITED(status)) {
		if (WEXITSTATUS(status) == 0)
			return;
		errx(1, "%s returned %d", arg1, WEXITSTATUS(status));
	}
	if (WIFSIGNALED(status))
		errx(1, "%s died with signal %d", arg1, WTERMSIG(status));
	errx(1, "unknown wait status %x from %s", status, arg1);
}
