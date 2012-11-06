#include <pthread.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#include "test.h"

#define NR_PTRS 100
static volatile int global;

static void *
thr_main(void *ign)
{
	int x1;
	int x2;
	int x3;
	while (!force_quit) {
		STOP_ANALYSIS();
		x1 = global;
		x2 = global;
		x3 = global;
		assert(!(x1 == 0 && x2 == 1 && x3 == 2));
		STOP_ANALYSIS();
		read_cntr++;
	}
	return NULL;
}

int
main()
{
	pthread_t thr;
	time_t start_time = time(NULL);
	int forever = 0;

	pthread_create(&thr, NULL, thr_main, NULL);

	if (getenv("SOS22_RUN_FOREVER"))
		forever = 1;

	while (forever || time(NULL) < start_time + 10) {
		STOP_ANALYSIS();
		global = 0;
		global = 1;
		global = 2;
		STOP_ANALYSIS();
		write_cntr++;
	}

	force_quit = true;
	pthread_join(thr, NULL);

	printf("Survived, %d read events and %d write events\n",
	       read_cntr, write_cntr);
	return 0;
}
