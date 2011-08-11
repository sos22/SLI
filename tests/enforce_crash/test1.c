/* A simple test program which crashes after a while.  enforce_crash
   makes it crash just that little bit sooner. */
#include <assert.h>
#include <err.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

static long max_iterations;
static volatile long nr_iterations;
static int my_int;
static int *volatile the_ptr = &my_int;

static void
segv_handler(int ignore)
{
	/* Can't use printf, because we're in a signal handler, but
	   assembling it manually and then using write() directly is
	   allowed. */
	char buf[] = "000000000000000000000 iterations\n";
	int cntr = nr_iterations;
	int i = 19;
	ssize_t s;

	while (cntr) {
		assert(i >= 0);
		buf[i] = '0' + (cntr % 10);
		cntr /= 10;
		i--;
	}
	s = write(1, buf + i + 1, sizeof(buf) - 2 - i);
	(void)s;

	_exit(0);
}

static void read_section() __attribute__((noinline));
static void
read_section()
{
	if (the_ptr != NULL)
		(*the_ptr)++;
}

static void *
read_thread(void *ignore)
{
	while (max_iterations == -1 || nr_iterations < max_iterations) {
		read_section();
		nr_iterations++;
	}
	return NULL;
}

static void write_section(double delay) __attribute__((noinline));
static void
write_section(double delay)
{
	usleep(delay * 1e6);
	the_ptr = NULL;
	usleep(delay * 1e6);
	the_ptr = &my_int;
}

int
main(int argc, char *argv[])
{
	pthread_t t;
	double delay;

	if (argc < 2 || argc > 3) {
		fprintf(stderr,
"%s <delay> {<end>}\n"
"<delay> is in seconds, as a float, and up to 2\n"
"<end>, if present, is the number of iterations to run before giving up and reporting success\n",
			argv[0]);
		return 1;
	}

	delay = atof(argv[1]);
	printf("Delay is %f\n", delay);
	if (delay > 2)
		errx(1, "delay must be <= 2 seconds");
	max_iterations = -1;
	if (argc == 3) {
		max_iterations = atol(argv[2]);
		printf("Max iterations %ld\n", max_iterations);
	}
	signal(SIGSEGV, segv_handler);

	if (pthread_create(&t, NULL, read_thread, NULL) != 0)
		errx(1, "spawning read thread");

	while (max_iterations == -1 || nr_iterations < max_iterations)
		write_section(delay);

	return 0;
}
