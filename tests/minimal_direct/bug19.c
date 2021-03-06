#include <pthread.h>
#include <stdio.h>
#include <time.h>
#include <unistd.h>
#include <stdlib.h>

#include "test.h"

typedef void impl_t(void);

static impl_t *volatile
forcedunwind;
static int volatile
done_init;
static pthread_barrier_t
the_barrier;
static pthread_barrier_t
b2;

static void
_forcedunwind_impl(void)
{
}

static void
_Unwind_ForcedUnwind(void)
{
	impl_t *l;
	l = forcedunwind;
	if (l == NULL && !done_init) {
		forcedunwind = l = _forcedunwind_impl;
		done_init = 1;
	}
	l();
}

static void *
thr_main(void *ign)
{
	while (1) {
		pthread_barrier_wait(&the_barrier);
		STOP_ANALYSIS();
		_Unwind_ForcedUnwind();
		STOP_ANALYSIS();
		pthread_barrier_wait(&the_barrier);
		done_init = 0;
		forcedunwind = NULL;
		read_cntr++;

		pthread_barrier_wait(&b2);
		if (force_quit) {
			break;
		}
		pthread_barrier_wait(&b2);
	}
	return NULL;
}

int
main()
{
	pthread_t thr1;
	pthread_t thr2;
	int forever = 0;

	pthread_barrier_init(&the_barrier, NULL, 2);
	pthread_barrier_init(&b2, NULL, 3);
	pthread_create(&thr1, NULL, thr_main, NULL);
	pthread_create(&thr2, NULL, thr_main, NULL);

	time_t start_time = time(NULL);

	if (getenv("SOS22_RUN_FOREVER"))
		forever = 1;
	while (forever || time(NULL) < start_time + 10) {
		pthread_barrier_wait(&b2);
		pthread_barrier_wait(&b2);
	}

	force_quit = true;
	pthread_barrier_wait(&b2);
	pthread_join(thr1, NULL);
	pthread_join(thr2, NULL);

	printf("Survived, %d read events and %d write events\n",
	       read_cntr, write_cntr);

	return 0;
}
