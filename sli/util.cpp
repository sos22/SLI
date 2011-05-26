#include <err.h>
#include <signal.h>
#include <unistd.h>

#include "sli.h"

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
handle_sigusr1(int ignore)
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
}

/* Like my_asprintf, but allocate from the VEX GC-able heap. */
char *
vex_vasprintf(const char *fmt, va_list args)
{
	char *r;
	int x = vasprintf(&r, fmt, args);

	char *r2 = (char *)LibVEX_Alloc_Bytes(x + 1);
	memcpy(r2, r, x + 1);
	free(r);
	return r2;
}
char *
vex_asprintf(const char *fmt, ...)
{
	va_list args;
	char *r;
	va_start(args, fmt);
	r = vex_vasprintf(fmt, args);
	va_end(args);
	return r;
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
	if (!parseIRExpr(&r, buf, &succ) || *succ)
		errx(1, "cannot parse %s as IRExpr", buf);
	free(buf);
	return r;
}
